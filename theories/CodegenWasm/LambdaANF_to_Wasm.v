From Wasm Require Import datatypes operations.
From CertiCoq Require Import LambdaANF.toplevel LambdaANF.cps_util.

From CertiCoq Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Utils Require Import bytestring MCString.
From Coq Require Import ZArith BinNat List Lia.

Require Import MSets.MSetAVL.
From Coq Require Import FMapAVL.
Require Import POrderedType.

Require Import LambdaANF.cps LambdaANF.cps_show.
Import MonadNotation.


(* Main file for compiler backend targeting Wasm. *)

(* memory can grow to at most 64KB * max_mem_pages *)
Definition max_mem_pages     := 30000%N.

(* ***** RESTRICTIONS ON lANF EXPRESSIONS ****** *)
Definition max_function_args := 20%Z.        (* should be possible to vary without breaking much *)
Definition max_num_functions := 1_000_000%Z. (* should be possible to vary without breaking much *)
Definition max_constr_args   := 50%Z.      (* should be possible to vary without breaking much *)

(* base id of type struct: add number of elems *)
Definition struct_type_base_idx : N := (Z.to_N max_function_args + 2)%N.
Definition struct_type_constr_idx : N := (struct_type_base_idx - 1)%N. (* {tag: i32, args: struct}*)

Definition max_constr_alloc_size := (max_constr_args * 4 + 4)%Z. (* bytes, don't change this *)

Definition assert (b : bool) (err : string) : error Datatypes.unit :=
  if b then Ret tt else Err err.

Definition get_ctor_ord (cenv : ctor_env) (t : ctor_tag) : error N:=
  match M.get t cenv with
  | Some c => Ret (ctor_ordinal c)
  | None => Err ("Constructor with tag " ++ (string_of_positive t) ++ " in constructor expression not found in constructor environment")%bs
  end.


(* enforces predicate expression_restricted in the proof file *)
Fixpoint check_restrictions (cenv : ctor_env) (e : exp) : error Datatypes.unit :=
  match e with
  | Econstr _ t ys e' =>
      ord <- get_ctor_ord cenv t ;;
      _ <- assert (Z.of_N ord <? Wasm_int.Int32.half_modulus)%Z "Constructor ordinal too large" ;;
      _ <- assert (Z.of_nat (Datatypes.length ys) <=? max_constr_args)%Z
             "found constructor with too many args, check max_constr_args";;
      check_restrictions cenv e'
  | Ecase x ms =>
      (* _ <- check_case_list_ordinals cenv ms;; *)
      _ <- sequence (map (fun '(t, e') =>
                            ord <- get_ctor_ord cenv t ;;
                            _ <- assert (Z.of_N ord <? Wasm_int.Int32.half_modulus)%Z "Constructor ordinal too large" ;;
                            check_restrictions cenv e') ms) ;;
      Ret tt
  | Eproj _ _ _ _ e' => check_restrictions cenv  e'
  | Eletapp _ _ _ ys e' =>
      _ <- assert (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z
                "found function application with too many function params, check max_function_args";;
      check_restrictions cenv e'
  | Efun fds e' =>
      _ <- assert (Z.of_nat (numOf_fundefs fds) <? max_num_functions)%Z
                "too many functions, check max_num_functions";;
      _ <- ((fix iter (fds : fundefs) : error Datatypes.unit :=
              match fds with
              | Fnil => Ret tt
              | Fcons _ _ ys e' fds' =>
                  _ <- assert (Z.of_nat (length ys) <=? max_function_args)%Z
                       "found fundef with too many function args, check max_function_args";;
                  _ <- (iter fds');;
                  check_restrictions cenv e'
              end) fds);;
      check_restrictions cenv e'
  | Eapp _ _ ys => assert (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z
                        "found function application with too many function params, check max_function_args"
  | Eprim_val _ _ e' => check_restrictions cenv e'
  | Eprim _ _ _ e' => check_restrictions cenv e'
  | Ehalt _ => Ret tt
  end.

(* ***** FUNCTIONS and GLOBALS ****** *)

(*  In Wasm, functions and globals are referred to by their index in the order they are listed.
 *  For FFI/debugging, the module exports all functions.
 *  The names of translated lANF functions are prefixed with an underscore, others should not to avoid name clashes.
 *)

(* imported, print char/int to stdout *)
Definition write_char_function_idx : funcidx := 0%N.
Definition write_char_function_name := "write_char".
Definition write_int_function_idx : funcidx := 1%N.
Definition write_int_function_name := "write_int".

(* grow_mem: grow linear mem by number of bytes if necessary *)
Definition grow_mem_function_name := "todo_delete_this_function".
Definition grow_mem_function_idx : funcidx := 2%N.

(* main function: contains the translated main expression *)
Definition main_function_name := "main_function".
Definition main_function_idx : funcidx := 3%N.

(* then follow the translated functions,
   index of first translated lANF fun, a custom fun should be added before, and this var increased by 1
   (the proof will still break at various places)  *)
Definition num_custom_funs := 4.

(* global vars *)
Definition result_var        : globalidx := 0%N. (* final result *)

(* ***** MAPPINGS ****** *)
Definition localvar_env := M.tree localidx. (* maps variables to their id (id=index in list of local vars) *)
Definition fname_env    := M.tree funcidx. (* maps function variables to their id (id=index in list of functions) *)


(* ***** UTILS and BASIC TRANSLATIONS ****** *)

(* target type for generating functions, contains more info than the one from Wasm *)
Record wasm_function :=
  { fidx : funcidx
  ; export_name : string
  ; type : N
  ; locals : list value_type
  ; body : list basic_instruction
  }.

Definition nat_to_i32 (n : nat) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat n).

Definition nat_to_i64 (n : nat) :=
  Wasm_int.Int64.repr (BinInt.Z.of_nat n).

Definition N_to_i32 (n : N) :=
  Wasm_int.Int32.repr (Z.of_N n).

Definition nat_to_value (n : nat) :=
  VAL_int32 (nat_to_i32 n).

Definition nat_to_value64 (n : nat) :=
  VAL_int64 (nat_to_i64 n).

Definition Z_to_value (z : Z) :=
  VAL_int32 (Wasm_int.Int32.repr z).

Definition N_to_value (n : N) :=
  Z_to_value (Z.of_N n).

Definition translate_var (nenv : name_env) (lenv : localvar_env) (v : cps.var) (err : string)
  : error u32 :=
  match M.get v lenv with
  | Some n => Ret n
  | None => Err ("expected to find id for variable " ++ (show_tree (show_var nenv v)) ++ " in var/fvar mapping: " ++ err)
  end.

Definition is_function_var (fenv : fname_env) (v : cps.var) : bool :=
  match M.get v fenv with
  | Some _ => true
  | None => false
  end.

(* returns T_eqref *)
Definition instr_local_var_read (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (v : cps.var)
  : error (list basic_instruction) :=
  if is_function_var fenv v
    then fidx <- translate_var nenv fenv v "translate local var read: obtaining function id" ;;
         Ret [BI_const_num (N_to_value fidx); BI_ref_i31] (* passing id of function <var_name> *)

    else var <- translate_var nenv lenv v "instr_local_var_read: normal var";;
         Ret [BI_local_get var].


Definition get_ctor_arity (cenv : ctor_env) (t : ctor_tag) :=
  match M.get t cenv with
  | Some {| ctor_arity := n |} => Ret (N.to_nat n)
  | _ => Err "found constructor without ctor_arity set"
  end.

Definition generate_grow_mem_function : wasm_function :=
  {| fidx := grow_mem_function_idx
   ; export_name := grow_mem_function_name
   ; type := 1%N (* [T_eqref] -> [] *)
   ; locals := []
   ; body := [BI_unreachable]
   |}.


(* ***** TRANSLATE FUNCTION CALLS ****** *)

(* every function has type: T_eqref^{#args} -> [] *)

Fixpoint pass_function_args (nenv : name_env) (lenv: localvar_env) (fenv : fname_env) (args : list cps.var) : error (list basic_instruction) :=
  match args with
  | [] => Ret []
  | a0 :: args' =>
      a0' <- instr_local_var_read nenv lenv fenv a0;;
      args'' <- pass_function_args nenv lenv fenv args';;
      Ret (a0' ++ args'')
  end.

Definition translate_call (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (f : cps.var) (args : list cps.var) (tailcall : bool)
  : error (list basic_instruction) :=
  instr_pass_params <- pass_function_args nenv lenv fenv args;;
  instr_fidx <- instr_local_var_read nenv lenv fenv f;;
  let call := (fun num_args : nat => if tailcall then BI_return_call_indirect 0%N (N.of_nat num_args)
                                                 else BI_call_indirect 0%N (N.of_nat num_args)) in
  Ret (instr_pass_params ++ instr_fidx ++
      [ BI_ref_cast (T_abs T_i31ref)
      ; BI_i31_get_u
      ; call (length args)
      ]).
  (* all fns return nothing, type = num args *)

(* **** TRANSLATE PRIMITIVE VALUES **** *)

Definition translate_primitive_value (p : AstCommon.primitive) : error Wasm_int.Int64.int :=
  match projT1 p as tag return prim_value tag -> error Wasm_int.Int64.T with
  | AstCommon.primInt => fun i => Ret (Wasm_int.Int64.repr (Uint63.to_Z i))
  | AstCommon.primFloat => fun f => Err "TODO"
  end (projT2 p).

(* **** TRANSLATE PRIMITIVE OPERATIONS **** *)

Definition primInt63ModPath : Kernames.modpath :=
  Kernames.MPfile ["Coq"%bs ; "Numbers"%bs ; "Cyclic"%bs ; "Int63"%bs ; "PrimInt63"%bs ].


Definition primInt63Add  : Kernames.kername := (primInt63ModPath, "add"%bs).
Definition primInt63Sub  : Kernames.kername := (primInt63ModPath, "sub"%bs).
Definition primInt63Mul  : Kernames.kername := (primInt63ModPath, "mul"%bs).
Definition primInt63Div  : Kernames.kername := (primInt63ModPath, "div"%bs).
Definition primInt63Mod  : Kernames.kername := (primInt63ModPath, "mod"%bs).
Definition primInt63Land : Kernames.kername := (primInt63ModPath, "land"%bs).
Definition primInt63Lor  : Kernames.kername := (primInt63ModPath, "lor"%bs).
Definition primInt63Lxor : Kernames.kername := (primInt63ModPath, "lxor"%bs).
Definition primInt63Lsl  : Kernames.kername := (primInt63ModPath, "lsl"%bs).
Definition primInt63Lsr  : Kernames.kername := (primInt63ModPath, "lsr"%bs).

(*Definition apply_binop_and_store_i64 (op : basic_instruction) y1 y2 :=
  [ BI_global_get global_mem_ptr (* Address to store the result of the operation *)
  ; BI_local_get y1
  ; BI_ref_cast (T_abs T_i31ref)
  ; BI_i31_get_u
  ; BI_load T_i64 None 2%N 0%N
  ; BI_local_get y2
  ; BI_ref_cast (T_abs T_i31ref)
  ; BI_i31_get_u
  ; BI_load T_i64 None 2%N 0%N
  ; op
  (* Ensure that value fits in 63 bits *)
  ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus))
  ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
  ; BI_store T_i64 None 2%N 0%N
  ; BI_global_get global_mem_ptr (* value to be stored in the let binding ('return value') *)
  ; BI_ref_i31
  (* Increment global memory pointer to next free memory segment  *)
  ; BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value 8)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_set global_mem_ptr ].

Definition translate_primitive_arith_op nenv lenv kname y1 y2 : error (list basic_instruction) :=
    y1_var <- translate_var nenv lenv y1 "translate primitive integer arithmetic operation 1st argument" ;;
    y2_var <- translate_var nenv lenv y2 "translate primitive integer arithmetic operation 2nd argument" ;;
    if Kername.eqb kname primInt63Add then
      Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i BOI_add)) y1_var y2_var)
          (* else if Kername.eqb kname primInt63Sub then *)
          (*        Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i BOI_sub)) y1_var y2_var) *)
          (* else if Kername.eqb kname primInt63Mul then *)
          (*        Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i BOI_mul)) y1_var y2_var) *)
          (* else if Kername.eqb kname primInt63Div then *)
          (*        Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i (BOI_div SX_U))) y1_var y2_var) *)
          (* else if Kername.eqb kname primInt63Mod then *)
          (*        Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i (BOI_rem SX_U))) y1_var y2_var) *)
          (* else if Kername.eqb kname primInt63Land then *)
          (*        Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i BOI_and)) y1_var y2_var) *)
          (* else if Kername.eqb kname primInt63Lor then *)
          (*        Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i BOI_or)) y1_var y2_var) *)
          (* else if Kername.eqb kname primInt63Lxor then *)
          (*        Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i BOI_xor)) y1_var y2_var) *)
          (* else if Kername.eqb kname primInt63Lsl then *)
          (*        Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i BOI_shl)) y1_var y2_var) *)
          (* else if Kername.eqb kname primInt63Lsr then *)
          (*        Ret (apply_binop_and_store_i64 (BI_binop T_i64 (Binop_i (BOI_shr SX_U))) y1_var y2_var) *)
    else
      Err ("Unknown primitive arithmetic operator: " ++ (Kernames.string_of_kername kname))%bs.


Definition translate_primitive_operation (nenv : name_env) (lenv : localvar_env) (x_var : localidx) (p : (kername * string * bool * nat)) (args : list var) : error (list basic_instruction) :=
  let '(kname, _, _, _) := p in
  match args with
  | [ y1 ; y2 ] =>
      op_instrs <- translate_primitive_arith_op nenv lenv kname y1 y2 ;;
      Ret (op_instrs ++ [ BI_local_set x_var ])
  | _ =>
      Err "Only primitive operations with two arguments are supported"
  end. *)

Fixpoint create_case_nested_if_chain (boxed : bool) (v : localidx) (es : list (N * list basic_instruction)) : list basic_instruction :=
  match es with
  | [] => [ BI_unreachable ]
  | (ord, instrs) :: tl =>
      (* if boxed (pointer), then load tag from memory;
         otherwise, the unboxed representation is (ord << 1) + 1 = 2 * ord + 1.
       *)
        (if boxed then
           [ BI_local_get v
           ; BI_ref_cast (T_index struct_type_constr_idx)
           ; BI_struct_get struct_type_constr_idx 0%N
           ; BI_const_num (N_to_value ord)]
         else
           [ BI_local_get v
           ; BI_ref_cast (T_abs T_i31ref)
           ; BI_i31_get_u
           ; BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N))]) ++
        [ BI_relop T_i32 (Relop_i ROI_eq)
        ; BI_if (BT_valtype None) instrs (create_case_nested_if_chain boxed v tl) ]
  end.

(* ***** TRANSLATE EXPRESSIONS (except fundefs) ****** *)

Fixpoint translate_body (nenv : name_env) (cenv : ctor_env) (lenv: localvar_env) (fenv : fname_env) (penv : prim_env) (e : exp) : error (list basic_instruction) :=
   match e with
   | Efun fundefs e' => Err "unexpected nested function definition"
   | Econstr x tg ys e' =>
      following_instr <- translate_body nenv cenv lenv fenv penv e' ;;
      x_var <- translate_var nenv lenv x "translate_body constr";;
      match ys with
      | [] =>
          ord <- get_ctor_ord cenv tg ;;
          Ret ([ BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N))
               ; BI_ref_i31
               ; BI_local_set x_var
               ] ++ following_instr)
      | _ => (* n > 0 ary constructor  *)
          (* Boxed representation *)
          ord <- get_ctor_ord cenv tg ;;
          instr_pass_args <- pass_function_args nenv lenv fenv ys;;
          Ret ([ BI_const_num (nat_to_value (N.to_nat ord))] ++ (* tag *)
               instr_pass_args ++
               [ BI_struct_new (struct_type_base_idx + N.of_nat (length ys))%N
               ; BI_struct_new struct_type_constr_idx
               ; BI_local_set x_var
               ] ++ following_instr)
      end
   | Ecase x arms =>
      let fix translate_case_branch_expressions (arms : list (ctor_tag * exp))
        : error (list (N * list basic_instruction) * list (N  * list basic_instruction)) :=
        match arms with
        | [] => Ret ([], [])
        | (t, e)::tl =>
            instrs <- translate_body nenv cenv lenv fenv penv e ;;
            '(arms_boxed, arms_unboxed) <- translate_case_branch_expressions tl ;;
            ord <- get_ctor_ord cenv t ;;
            arity <- get_ctor_arity cenv t ;;
            if arity =? 0 then
              Ret (arms_boxed, (ord, instrs) :: arms_unboxed)
            else
              Ret ((ord, instrs) :: arms_boxed, arms_unboxed)
        end
      in
      x_var <- translate_var nenv lenv x "translate_body case" ;;
      '(arms_boxed, arms_unboxed) <- translate_case_branch_expressions arms ;;
      Ret ([ BI_local_get x_var
           ; BI_ref_test (T_abs T_i31ref)
           ; BI_if (BT_valtype None)
               (create_case_nested_if_chain false x_var arms_unboxed)
               (create_case_nested_if_chain true x_var arms_boxed)
           ] : list basic_instruction)

   | Eproj x tg n y e' =>
      following_instr <- translate_body nenv cenv lenv fenv penv e' ;;
      y_var <- translate_var nenv lenv y "translate_body proj y";;
      x_var <- translate_var nenv lenv x "translate_body proj x";;
      arity <- get_ctor_arity cenv tg ;;
      let tidx := (N.of_nat arity + struct_type_base_idx)%N in

      Ret ([ BI_local_get y_var
           ; BI_ref_cast (T_index struct_type_constr_idx)
           ; BI_struct_get struct_type_constr_idx 1%N
           ; BI_ref_cast (T_index tidx)
           ; BI_struct_get tidx n%N
           ; BI_local_set x_var
           ] ++ following_instr)

   | Eletapp x f ft ys e' =>
      x_var <- translate_var nenv lenv x "translate_body proj x";;
      following_instr <- translate_body nenv cenv lenv fenv penv e' ;;
      instr_call <- translate_call nenv lenv fenv f ys false;;

      Ret (instr_call ++ [ BI_global_get result_var
                         ; BI_local_set x_var
                         ] ++ following_instr)

   | Eapp f ft ys => translate_call nenv lenv fenv f ys true

(*
   | Eprim_val x p e' =>
       following_instrs <- translate_body nenv cenv lenv fenv penv e' ;;
       x_var <- translate_var nenv lenv x "translate_body prim val" ;;
       val <- translate_primitive_value p ;;
       Ret ([ BI_const_num (N_to_value page_size)
            ; BI_ref_i31
            ; BI_call grow_mem_function_idx
            ; BI_global_get result_out_of_mem
            ; BI_const_num (nat_to_value 1)
            ; BI_relop T_i32 (Relop_i ROI_eq)
            ; BI_if (BT_valtype None)
                [ BI_return ]
                []
            ; BI_global_get global_mem_ptr
            ; BI_const_num (VAL_int64 val)
            ; BI_store T_i64 None 2%N 0%N
            ; BI_global_get global_mem_ptr
            ; BI_ref_i31
            ; BI_local_set x_var
            ; BI_global_get global_mem_ptr
            ; BI_const_num (nat_to_value 8)
            ; BI_binop T_i32 (Binop_i BOI_add)
            ; BI_global_set global_mem_ptr
            ] ++ following_instrs) *)

            (*   | Eprim x p ys e' => (* Err "temp" *)
       match M.get p penv with
       | None => Err "Primitive operation not found in prim_env"
       | Some p' =>
           following_instrs <- translate_body nenv cenv lenv fenv penv e';;
           x_var <- translate_var nenv lenv x "translate_exp prim op" ;;
           instrs <- translate_primitive_operation nenv lenv x_var p' ys ;;
           Ret ( [ BI_const_num (N_to_value page_size)
                 ; BI_ref_i31
                 ; BI_call grow_mem_function_idx
                 ; BI_global_get result_out_of_mem
                 ; BI_const_num (nat_to_value 1)
                 ; BI_relop T_i32 (Relop_i ROI_eq)
                 ; BI_if (BT_valtype None)
                     [ BI_return ]
                     []
               ] ++ instrs ++ following_instrs)
               end *)
   | Ehalt x =>
     x_var <- translate_var nenv lenv x "translate_body halt";;
     Ret [ BI_local_get x_var; BI_global_set result_var; BI_return ]
   | _ => Err "not supported yet"
   end.


(* ***** TRANSLATE FUNCTIONS ****** *)

(* unique, vars are only assigned once *)
Fixpoint collect_local_variables (e : exp) : list cps.var :=
  match e with
  | Efun _ e' => collect_local_variables e'
  | Econstr x _ _ e' => x :: collect_local_variables e'
  | Ecase _ arms => flat_map (fun a => collect_local_variables (snd a)) arms
  | Eproj x _ _ _ e' => x :: collect_local_variables e'
  | Eletapp x _ _ _ e' => x :: collect_local_variables e'
  | Eprim x _ _ e' => x :: collect_local_variables e'
  | Eprim_val x _ e' => x :: collect_local_variables e'
  | Eapp _ _ _ => []
  | Ehalt _ => []
  end.

(* create mapping from vars to nats counting up from start_id, used for both fns and vars *)
Fixpoint create_var_mapping (start_id : u32) (vars : list cps.var) (env : M.tree u32) : M.tree u32 :=
   match vars with
   | [] => env
   | v :: l' => let mapping := create_var_mapping (1 + start_id)%N l' env in
                M.set v start_id mapping
   end.

Definition create_local_variable_mapping (vars : list cps.var) : localvar_env :=
  create_var_mapping 0%N vars (M.empty _).

Definition function_export_name (nenv : name_env) (v : cps.var) : string :=
  let bytes := String.print ("_" ++ show_tree (show_var nenv v)) in
  String.parse (map (fun b => match b with
                              | "."%byte => "_"%byte
                              |_ => b
                              end)
                    bytes).

Definition translate_function (nenv : name_env) (cenv : ctor_env) (fenv : fname_env) (penv : prim_env)
                              (f : cps.var) (args : list cps.var) (body : exp) : error wasm_function :=
  let locals := collect_local_variables body in
  let lenv := create_local_variable_mapping (args ++ locals) in

  fn_idx <- translate_var nenv fenv f "translate function" ;;
  body_res <- translate_body nenv cenv lenv fenv penv body ;;
  Ret {| fidx := fn_idx
       ; export_name := function_export_name nenv f
       ; type := N.of_nat (length args)
       ; locals := map (fun _ => T_ref (T_heap (T_abs T_eqref))) locals
       ; body := body_res
       |}.

Fixpoint translate_functions (nenv : name_env) (cenv : ctor_env) (fenv : fname_env) (penv : prim_env)
                             (fds : fundefs) : error (list wasm_function) :=
  match fds with
  | Fnil => Ret []
  | Fcons x tg xs e fds' =>
      fn <- translate_function nenv cenv fenv penv x xs e ;;
      following <- translate_functions nenv cenv fenv penv fds' ;;
      Ret (fn :: following)
  end.




(* ***** MAIN: GENERATE COMPLETE WASM_MODULE FROM lambdaANF EXP ****** *)

Definition collect_function_vars (e : cps.exp) : list cps.var :=
    match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) : list cps.var :=
          match fds with
          | Fnil => []
          | Fcons x _ _ e' fds' => x :: (iter fds')
          end) fds
    | _ => []
    end.

(* maps function names to ids (id=index in function list of module) *)
Definition create_fname_mapping (e : exp) : fname_env :=
  let fun_vars := collect_function_vars e in
  create_var_mapping (N.of_nat num_custom_funs) fun_vars (M.empty _).

Fixpoint list_function_types (n : nat) : list function_type :=
  match n with
  | 0 => [Tf [] []]
  | S n' => (Tf [] []) :: map (fun t => match t with Tf args rt => Tf (T_ref (T_heap (T_abs T_eqref)) :: args) rt end) (list_function_types n')
  end.

(* n: number of constr args, probably slow for bigger n *)
Fixpoint list_struct_types (n : nat) : list struct_type :=
  let teq := Build_field_type MUT_const (T_ref (T_heap (T_abs T_eqref))) in
  match n with
  | 0 => []
  | S n' => (Ts []) :: map (fun t => match t with Ts ts => Ts (ts ++ [teq]) end)
                           (list_struct_types n')
  end.

(* for indirect calls maps fun ids to themselves *)
Fixpoint table_element_mapping (len : nat) (startidx : nat) : list module_element :=
  match len with
  | 0 => []
  | S len' => {| modelem_mode := ME_active 0%N [BI_const_num (nat_to_value startidx)]
               ; modelem_init := [[ BI_ref_func (N.of_nat startidx) ]]
               ; modelem_type := T_heap_null (T_abs T_funcref)
               |} :: (table_element_mapping len' (S startidx))
  end.

Definition LambdaANF_to_Wasm (nenv : name_env) (cenv : ctor_env) (penv : prim_env) (e : exp) : error (module * fname_env * localvar_env) :=
  _ <- check_restrictions cenv e;;

  let fname_mapping := create_fname_mapping e in

  let grow_mem_function := generate_grow_mem_function in

  (* ensure toplevel exp is an Efun*)
  let top_exp := match e with
                 | Efun _ _ => e
                 | _ => Efun Fnil e
                 end in

  fns <- match top_exp with
         | Efun fds exp => translate_functions nenv cenv fname_mapping penv fds
         | _ => Err "unreachable"
         end ;;

  main_expr <- match top_exp with
               | Efun _ exp => Ret exp
               | _ => Err "unreachable"
               end;;
  let main_vars := collect_local_variables main_expr in
  let main_lenv := create_local_variable_mapping main_vars in
  main_instr <- translate_body nenv cenv main_lenv fname_mapping penv main_expr ;;

  let main_function := {| fidx := main_function_idx
                        ; export_name := main_function_name
                        ; type := 0%N (* [] -> [] *)
                        ; locals := map (fun _ => T_ref (T_heap (T_abs T_eqref))) main_vars
                        ; body := main_instr
                        |}
  in
  let functions := [grow_mem_function; main_function] ++ fns in

  let exports := map (fun f => {| modexp_name := String.print f.(export_name)
                                ; modexp_desc := MED_func (f.(fidx))
                                |}) functions (* function exports for debug names *)
                 ++ {| modexp_name := String.print "result"
                     ; modexp_desc := MED_global result_var
                    |} :: nil
  in

  let elements := table_element_mapping (2 + length functions) 0 in (* 2 imported funcs, grow_mem, main included in functions *)

  let functions_final := map (fun f => {| modfunc_type := f.(type)
                                        ; modfunc_locals := f.(locals)
                                        ; modfunc_body := f.(body)
                                       |}) functions in
  let module :=
      {| mod_types := map CT_func (list_function_types (Z.to_nat max_function_args)) (* more than required, doesn't hurt*)
        ++ CT_struct (Ts [Build_field_type MUT_const (T_num T_i32); Build_field_type MUT_const (T_ref (T_heap (T_abs T_eqref)))]) (* tag + args *)
        :: map CT_struct (list_struct_types (Z.to_nat max_constr_args))

       ; mod_funcs := functions_final
       ; mod_tables := [ {| modtab_type := {| tt_limits := {| lim_min := N.of_nat (List.length fns + num_custom_funs)
                                                            ; lim_max := None |}
                                            ; tt_elem_type := T_heap_null (T_abs T_funcref)
                                            |} |}]

       ; mod_globals := {| modglob_type := {| tg_mut := MUT_var; tg_t := T_ref (T_heap (T_abs T_eqref))|}  (* result_var *)
                         ; modglob_init := [BI_const_num (Z_to_value (-1)); BI_ref_i31]
                         |} :: nil

       ; mod_elems := elements
       ; mod_mems := []
       ; mod_datas := []
       ; mod_start := None

       ; mod_imports := {| imp_module := String.print "env"
                         ; imp_name := String.print write_char_function_name
                         ; imp_desc := MID_func 1%N
                         |} ::
                        {| imp_module := String.print "env"
                         ; imp_name := String.print write_int_function_name
                         ; imp_desc := MID_func 1%N
                         |} :: nil
       ; mod_exports := exports
   |}
       in
       (* also return mappings to access them in proof *)
       Ret (module, fname_mapping, main_lenv).
