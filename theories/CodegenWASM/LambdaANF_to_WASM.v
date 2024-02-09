From Wasm Require Import datatypes operations.
From CertiCoq Require Import LambdaANF.toplevel LambdaANF.cps_util.

From CertiCoq Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Utils Require Import bytestring MCString.
From Coq Require Import ZArith List.

Require Import MSets.MSetAVL.
From Coq Require Import FMapAVL.
Require Import POrderedType.

Require Import LambdaANF.cps LambdaANF.cps_show.
Import MonadNotation.


(* Main file for compiler backend targeting WASM. *)

(* memory can grow to at most 64KB * max_mem_pages *)
Definition max_mem_pages     := 5000%N.

(* ***** RESTRICTIONS ON constructors and functions ****** *)
Definition max_constr_args   := 1024%Z.      (* should be possible to vary without breaking much *)
Definition max_function_args := 100%Z.       (* should be possible to vary without breaking much *)
Definition max_num_functions := 1_000_000%Z. (* should be possible to vary without breaking much *)


Definition assert (b : bool) (err : string) : error Datatypes.unit :=
  if b then Ret tt else Err err.

(* enforces predicate expression_restricted in the proof file *)
Fixpoint check_restrictions (e : exp) : error Datatypes.unit:=
  match e with
  | Econstr _ _ ys e' =>
       _ <- assert (Z.of_nat (Datatypes.length ys) <=? max_constr_args)%Z
                 "found constructor with too many args, check max_constr_args";;
       check_restrictions e'
  | Ecase x ms =>
      _ <- sequence (map (fun p =>
                        _ <- assert (Z.of_nat (Pos.to_nat (fst p)) <? Wasm_int.Int32.modulus)%Z
                                  "found case with tag >= i32.max";;
                        check_restrictions (snd p)) ms);; Ret tt
  | Eproj _ _ _ _ e' => check_restrictions e'
  | Eletapp _ _ _ ys e' =>
      _ <- assert (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z
                "found function application with too many function params, check max_function_args";;
      check_restrictions e'
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
                  check_restrictions e'
              end) fds);;
      check_restrictions e'
  | Eapp _ _ ys => assert (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z
                        "found function application with too many function params, check max_function_args"
  | Eprim_val _ _ e' => check_restrictions e'
  | Eprim _ _ _ e' => check_restrictions e'
  | Ehalt _ => Ret tt
   end.

(* ***** HARDCODED FUNCTION IDs ****** *)
(*  In Wasm, functions are referred to by their index (in the list of functions of a module).

    _idx  : idx in list of wasm functions
    _var  : cps.var
    _name : export name

    first 4 functions hardcoded:
    0,1) imported: print char/int to stdout
      2) debug: write S-expr of constr to stdout
      3) main function: contains the translated main expression
     ... then follow the translated functions
 *)

(* imported, for printing result *)
Definition write_char_function_idx : immediate := 0.
Definition write_char_function_name := "$write_char".
Definition write_int_function_idx : immediate := 1.
Definition write_int_function_name := "$write_int".

Definition constr_pp_function_name : string := "$pretty_print_constructor".
Definition constr_pp_function_idx : immediate := 2.
Definition main_function_name := "$main_function".
Definition main_function_idx : immediate := 3.

(* ***** MAPPINGS ****** *)
Definition localvar_env := M.tree nat. (* maps variables to their id (id=index in list of local vars) *)
Definition fname_env    := M.tree nat. (* maps function variables to their id (id=index in list of functions) *)


(* ***** UTILS and BASIC TRANSLATIONS ****** *)

(* global vars *)
Definition global_mem_ptr    : immediate := 0. (* ptr to free memory, increased when new 'objects' are allocated, there is no GC *)
Definition constr_alloc_ptr  : immediate := 1. (* ptr to beginning of constr alloc in linear mem *)
Definition result_var        : immediate := 2. (* final result *)
Definition result_out_of_mem : immediate := 3.

(* target type for generating functions, contains more info than the one from Wasm *)
Record wasm_function :=
  { fidx : immediate
  ; export_name : string
  ; type : function_type
  ; locals : list value_type
  ; body : list basic_instruction
  }.

(* generates list of n arguments *)
Fixpoint arg_list (n : nat) : list (immediate * value_type) :=
  match n with
  | 0 => []
  | S n' => arg_list n' ++ [(n', T_i32)]
  end.

Definition nat_to_i32 (n : nat) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat n).

Definition N_to_i32 (n : N) :=
  Wasm_int.Int32.repr (Z.of_N n).

Definition nat_to_value (n : nat) :=
  VAL_int32 (nat_to_i32 n).

Definition Z_to_value (z : Z) :=
  VAL_int32 (Wasm_int.Int32.repr z).

Definition N_to_value (n : N) :=
  Z_to_value (Z.of_N n).

Definition translate_var (nenv : name_env) (lenv : localvar_env) (v : cps.var) (err : string): error immediate :=
  match M.get v lenv with
  | Some n => Ret n
  | None => Err ("expected to find id for variable " ++ (show_tree (show_var nenv v)) ++ " in var/fvar mapping: " ++ err)
  end.

(* ***** GENERATE PRETTY PRINTER FUNCTION FOR CONSTRUCTOR-S-EXPRESSIONS ****** *)

Module S_pos := MSetAVL.Make Positive_as_OT.

Fixpoint collect_constr_tags' (e : exp) {struct e} : S_pos.t :=
  match e with
  | Efun fds e' => S_pos.union (collect_constr_tags' e')
          ((fix iter (fds : fundefs) : S_pos.t :=
            match fds with
            | Fnil => S_pos.empty
            | Fcons _ _ _ e'' fds' =>
                S_pos.union (collect_constr_tags' e'') (iter fds')
            end) fds)
  | Econstr _ tg _ e' => S_pos.add tg (collect_constr_tags' e')
  | Ecase _ arms => fold_left (fun _s a => S_pos.union _s (S_pos.add (fst a) (collect_constr_tags' (snd a)))) arms S_pos.empty
  | Eproj _ _ _ _ e' => collect_constr_tags' e'
  | Eletapp _ _ _ _ e' => collect_constr_tags' e'
  | Eprim _ _ _ e' => collect_constr_tags' e'
  | Eprim_val _ _ e' => collect_constr_tags' e'
  | Eapp _ _ _ => S_pos.empty
  | Ehalt _ => S_pos.empty
  end.

Definition collect_constr_tags (e : exp) : list ctor_tag :=
  S_pos.elements (collect_constr_tags' e).

Definition instr_write_string (s : string) : list basic_instruction :=
  let fix to_ascii_list s' :=
    match s' with
    | String.EmptyString => []
    | String.String b s'' => Byte.to_nat b :: to_ascii_list s''
    end in
  flat_map (fun c => [BI_const (nat_to_value c); BI_call write_char_function_idx]) (to_ascii_list s).

Definition get_ctor_arity (cenv : ctor_env) (t : ctor_tag) :=
  match M.get t cenv with
  | Some {| ctor_arity := n |} => Ret (N.to_nat n)
  | _ => Err "found constructor without ctor_arity set"
  end.

(* prints constructors as S-expressions *)
Definition generate_constr_pp_function (cenv : ctor_env) (nenv : name_env) (e : cps.exp) : error wasm_function :=
  let constr_ptr := 0 (* fun param *) in
  let tmp := 1        (* local var *) in
  let tags := collect_constr_tags e in
  let self_fn_idx := constr_pp_function_idx in

  let fix gen_rec_calls (calls : nat) (arity : nat) : list basic_instruction :=
    match calls with
    | 0 => if arity =? 0 then [ BI_return ] else (instr_write_string ")") ++ [ BI_return ]
    | S calls' => [ BI_get_local tmp
                  ; BI_const (nat_to_value 4)
                  ; BI_binop T_i32 (Binop_i BOI_add)
                  ; BI_set_local tmp
                  ; BI_get_local tmp
                  ; BI_load T_i32 None 2%N 0%N (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
                  ; BI_call self_fn_idx
                  ] ++ (gen_rec_calls calls' arity)
    end in

  let get_ctor_id_instrs (arity : nat) :=
    if arity =? 0 then
      [ BI_const (nat_to_value 1) ; BI_binop T_i32 (Binop_i (BOI_shr SX_S)) ]
    else
      [ BI_load T_i32 None 2%N 0%N ] (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
  in

  let get_ctor_print_instrs (name  : string) (arity : nat) :=
    if arity =? 0 then
      instr_write_string (String.append " " name) ++ [ BI_return ]
    else
      instr_write_string (String.append " (" name) ++
        BI_get_local constr_ptr :: BI_set_local tmp :: gen_rec_calls arity arity
  in

  let gen_print_constr_block (c : ctor_tag) : error (list basic_instruction) :=
    let ctor_id := Pos.to_nat c in
    let ctor_name := show_tree (show_con cenv c) in
    ctor_arity <- get_ctor_arity cenv c ;;
    ctor_id_instrs <- Ret (get_ctor_id_instrs ctor_arity) ;;
    ctor_print_instrs <- Ret (get_ctor_print_instrs ctor_name ctor_arity) ;;
    Ret ([ BI_const (nat_to_value ctor_id) ; BI_get_local constr_ptr ] ++
           ctor_id_instrs ++
           [ BI_relop T_i32 (Relop_i ROI_eq) ;
             BI_if (Tf nil nil)
               ctor_print_instrs
               []
           ])
  in

  blocks <- sequence (map gen_print_constr_block tags) ;;

  let body := (concat blocks) ++
              (instr_write_string " <can't print constr: ") ++ (* e.g. could be fn-pointer or env-pointer *)
              [ BI_get_local constr_ptr
              ; BI_call write_int_function_idx
              ] ++ instr_write_string ">" in

  let _ := ")"  (* hack to fix syntax highlighting bug *)

  in
  Ret {| fidx := self_fn_idx
       ; export_name := constr_pp_function_name
       ; type := Tf [T_i32] []
       ; locals := [T_i32]
       ; body := body
       |}.


Definition is_function_var (fenv : fname_env) (v : cps.var) : bool :=
  match M.get v fenv with
  | Some _ => true
  | None => false
  end.

Definition instr_local_var_read (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (v : cps.var) : error basic_instruction :=
  if is_function_var fenv v
    then fidx <- translate_var nenv fenv v "translate local var read: obtaining function id" ;;
         Ret (BI_const (nat_to_value fidx)) (* passing id of function <var_name> *)

    else var <- translate_var nenv lenv v "instr_local_var_read: normal var";;
         Ret (BI_get_local var).


(* ***** TRANSLATE FUNCTION CALLS ****** *)

(* every function has type: T_i32^{#args} -> [] *)

Fixpoint pass_function_args (nenv : name_env) (lenv: localvar_env) (fenv : fname_env) (args : list cps.var) : error (list basic_instruction) :=
  match args with
  | [] => Ret []
  | a0 :: args' =>
      a0' <- instr_local_var_read nenv lenv fenv a0;;
      args'' <- pass_function_args nenv lenv fenv args';;
      Ret (a0' :: args'')
  end.

Definition translate_call (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (f : cps.var) (args : list cps.var) : error (list basic_instruction) :=
  instr_pass_params <- pass_function_args nenv lenv fenv args;;
  instr_fidx <- instr_local_var_read nenv lenv fenv f;;
  Ret (instr_pass_params ++ [instr_fidx] ++ [BI_call_indirect (length args)]). (* all fns return nothing, typeidx = num args *)


(* Example placement of constructors in the linear memory:
     data Bintree := Leaf | Node Bintree Value Bintree

     Leaf: --> +---+
               |T_l|
               +---+

     Node: --> +---+---+---+---+
               |T_n| L | V | R |
               +---+---+---+---+
    T_l, T_n unique constructor tags
    L, V, R pointers to linear memory
*)

(* a page is 2^16 bytes *)
Definition grow_memory_if_necessary (required_bytes : N) : list basic_instruction :=
  (* required number of total pages *)
  [ BI_get_global global_mem_ptr
  ; BI_const (N_to_value required_bytes)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_const (Z_to_value (Z.pow 2 16))
  ; BI_binop T_i32 (Binop_i (BOI_div SX_S))

  (* current number of pages *)
  ; BI_current_memory
  ; BI_relop T_i32 (Relop_i (ROI_ge SX_S))
  (* allocate one page if necessary *)
  ; BI_if (Tf nil nil) [ BI_const (nat_to_value 1)
                       ; BI_grow_memory (* returns -1 on alloc failure *)
                       ; BI_const (Z_to_value (-1))
                       ; BI_relop T_i32 (Relop_i ROI_eq)
                       ; BI_if (Tf nil nil) [ BI_const (nat_to_value 1); BI_set_global result_out_of_mem ]
                                            [ ]
                       ]
                       []
  ].

(* store argument pointers in memory *)
Fixpoint set_constructor_args (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (args : list cps.var) (current : nat) : error (list basic_instruction) :=
  match args with
  | [] => Ret []
  | y :: ys => read_y <- instr_local_var_read nenv lenv fenv y;;
               remaining <- set_constructor_args nenv lenv fenv ys (1 + current);;

               Ret ([ BI_get_global constr_alloc_ptr
                    ; BI_const (nat_to_value (4 * (1 + current))) (* plus 1 : skip tag *)
                    ; BI_binop T_i32 (Binop_i BOI_add)
                    ; read_y
                    ; BI_store T_i32 None 2%N 0%N (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)

                    (* increase gmp by 4 *)
                    ; BI_get_global global_mem_ptr
                    ; BI_const (nat_to_value 4)
                    ; BI_binop T_i32 (Binop_i BOI_add)
                    ; BI_set_global global_mem_ptr

                    ] ++ remaining)
  end.


Definition store_constructor (nenv : name_env) (cenv : ctor_env) (lenv : localvar_env) (fenv : fname_env) (c : ctor_tag) (ys : list cps.var) : error (list basic_instruction) :=
  let ctor_id := Pos.to_nat c in
  set_constr_args <- set_constructor_args nenv lenv fenv ys 0;;
  Ret ([ BI_get_global global_mem_ptr
       ; BI_set_global constr_alloc_ptr

       (* set tag *)
       ; BI_get_global constr_alloc_ptr
       ; BI_const (nat_to_value ctor_id)
       ; BI_store T_i32 None 2%N 0%N (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)

       (* increase gmp by 4 *)
       ; BI_get_global global_mem_ptr
       ; BI_const (nat_to_value 4)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_set_global global_mem_ptr

       ] ++ set_constr_args).

Fixpoint create_case_nested_if_chain (y : immediate) (es : list (ctor_tag * bool * list basic_instruction)) : list basic_instruction :=
  match es with
  | [] => [ BI_unreachable ]
  | (t, boxed, instrs) :: tl =>
      (* if boxed (pointer), then load tag from memory;
         otherwise, obtain tag from unboxed representation ( tag = (repr >> 1) ) *)
      let tag_instrs := (if boxed then
                          [ BI_load T_i32 None 2%N 0%N ]
                        else
                          [ BI_const (nat_to_value 1) ; BI_binop T_i32 (Binop_i (BOI_shr SX_S)) ])
      in
      ( BI_get_local y :: tag_instrs ++
      [ BI_const (nat_to_value (Pos.to_nat t))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (Tf nil nil) instrs (create_case_nested_if_chain y tl)
      ])
  end.

(* ***** TRANSLATE EXPRESSIONS (except fundefs) ****** *)

Fixpoint translate_exp (nenv : name_env) (cenv : ctor_env) (lenv: localvar_env) (fenv : fname_env) (e : exp) : error (list basic_instruction) :=
   match e with
   | Efun fundefs e' => Err "unexpected nested function definition"
   | Econstr x tg ys e' =>
      following_instr <- translate_exp nenv cenv lenv fenv e' ;;
      x_var <- translate_var nenv lenv x "translate_exp constr";;
      match ys with
      | [] => Ret ([ BI_const (nat_to_value (Pos.to_nat tg)) (* Nullary constructor *)
                   (* Unboxed representation ( (tag << 1) + 1 ) *)
                   ; BI_const (nat_to_value 1)
                   ; BI_binop T_i32 (Binop_i BOI_shl)
                   ; BI_const (nat_to_value 1)
                   ; BI_binop T_i32 (Binop_i BOI_add)
                   ; BI_set_local x_var ] ++ following_instr)
      | _ => (* n > 0 ary constructor  *)
          (* Boxed representation *)
          store_constr <- store_constructor nenv cenv lenv fenv tg ys;;
          (* Ret (grow_memory_if_necessary ((length ys + 1) * 4) ++ *)
          Ret (grow_memory_if_necessary page_size ++
                 [ BI_get_global result_out_of_mem
                 ; BI_const (nat_to_value 1)
                 ; BI_relop T_i32 (Relop_i ROI_eq)
                 ; BI_if (Tf [] [])
                     []
                     (store_constr ++
                     [ BI_get_global constr_alloc_ptr
                     ; BI_set_local x_var
                     ] ++ following_instr)
                 ])
      end
   | Ecase x arms =>
      let fix translate_case_branch_expressions (v : immediate) (arms : list (ctor_tag * exp))
        : error (list (ctor_tag * bool * list basic_instruction)) :=
        match arms with
        | [] => Ret [ ]
        | (t, e)::tl =>
            e' <- translate_exp nenv cenv lenv fenv e;;
            arity <- get_ctor_arity cenv t ;;
            tl' <- translate_case_branch_expressions v tl;;
            Ret ((t, (0 <? arity), e') :: tl')
        end
      in
      x_var <- translate_var nenv lenv x "translate_exp case" ;;
      branch_instrs <- translate_case_branch_expressions x_var arms ;;
      Ret (create_case_nested_if_chain x_var branch_instrs)

   | Eproj x tg n y e' =>
      following_instr <- translate_exp nenv cenv lenv fenv e' ;;
      y_var <- translate_var nenv lenv y "translate_exp proj y";;
      x_var <- translate_var nenv lenv x "translate_exp proj x";;

      Ret ([ BI_get_local y_var
           ; BI_const (nat_to_value (((N.to_nat n) + 1) * 4)) (* skip ctor_id and previous constr arguments *)
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; BI_load T_i32 None 2%N 0%N (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
           ; BI_set_local x_var
           ] ++ following_instr)

   | Eletapp x f ft ys e' =>
      x_var <- translate_var nenv lenv x "translate_exp proj x";;
      following_instr <- translate_exp nenv cenv lenv fenv e' ;;
      instr_call <- translate_call nenv lenv fenv f ys ;;

      Ret (instr_call ++ [ BI_get_global result_out_of_mem
                         ; BI_if (Tf nil nil)
                            []
                            ([BI_get_global result_var; BI_set_local x_var] ++ following_instr)
                         ])

   | Eapp f ft ys =>
      instr_call <- translate_call nenv lenv fenv f ys ;;

      Ret instr_call (* tail calls are not supported in Wasm 1.0: normal function, TODO once WasmCert has tailcalls, generate one here *)

   | Eprim_val x p e' => Err "translating prim_val to WASM not supported yet"
   | Eprim x p ys e' => Err "translating prim to WASM not supported yet"
   | Ehalt x =>
     x_var <- translate_var nenv lenv x "translate_exp halt";;
     Ret [ BI_get_local x_var; BI_set_global result_var ]
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
Fixpoint create_var_mapping (start_id : nat) (vars : list cps.var) (env : M.tree nat) : M.tree nat :=
   match vars with
   | [] => env
   | v :: l' => let mapping := create_var_mapping (1 + start_id) l' env in
                M.set v start_id mapping
   end.

Definition create_local_variable_mapping (vars : list cps.var) : localvar_env :=
  create_var_mapping 0 vars (M.empty _).


Definition translate_function (nenv : name_env) (cenv : ctor_env) (fenv : fname_env)
                              (name : cps.var) (args : list cps.var) (body : exp) : error wasm_function :=

  let locals := collect_local_variables body in
  let lenv := create_local_variable_mapping (args ++ locals) in

  body_res <- translate_exp nenv cenv lenv fenv body ;;

  let arg_types := map (fun _ => T_i32) args in
  fn_var <- translate_var nenv fenv name "translate function" ;;

  Ret
  {| fidx := fn_var
   ; export_name := show_tree (show_var nenv name)
   ; type := Tf arg_types []
   ; locals := map (fun _ => T_i32) locals
   ; body := body_res
   |}.

(* ***** MAIN: GENERATE COMPLETE WASM_MODULE FROM lambdaANF EXP ****** *)

Definition collect_function_vars (e : cps.exp) : list cps.var :=
    match e with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) : list cps.var :=
          match fds with
          | Fnil => []
          | Fcons x _ _ _ fds' => x :: (iter fds')
          end) fds
    | _ => []
    end.

(* maps function names to ids (id=index in function list of module) *)
Definition create_fname_mapping (e : exp) : fname_env :=
  let fun_vars := collect_function_vars e in
  create_var_mapping 4 fun_vars (M.empty _).

Fixpoint list_function_types (n : nat) : list function_type :=
  match n with
  | 0 => [Tf [] []]
  | S n' => (Tf [] []) :: map (fun t => match t with Tf args rt => Tf (T_i32 :: args) rt end) (list_function_types n')
  end.

(* for indirect calls maps fun ids to themselves *)
Fixpoint table_element_mapping (len : nat) (startidx : nat) : list module_element :=
  match len with
  | 0 => []
  | S len' => {| modelem_table := Mk_tableidx 0
               ; modelem_offset := [ BI_const (nat_to_value startidx) ]
               ; modelem_init := [ Mk_funcidx startidx ]
               |} :: (table_element_mapping len' (S startidx))
  end.


Definition LambdaANF_to_WASM (nenv : name_env) (cenv : ctor_env) (e : exp) : error (module * fname_env * localvar_env) :=
  _ <- check_restrictions e;;

  let fname_mapping := create_fname_mapping e in

  constr_pp_function <- generate_constr_pp_function cenv nenv e;;

  let top_exp := match e with
                 | Efun _ _ => e
                 | _ => Efun Fnil e
                 end in

  fns <-
    match top_exp with
    | Efun fds exp => (* fundefs only allowed here (uppermost level) *)
      (fix iter (fds : fundefs) : error (list wasm_function) :=
          match fds with
          | Fnil => Ret []
          | Fcons x tg xs e fds' =>
             fn <- translate_function nenv cenv fname_mapping x xs e ;;
             following <- iter fds' ;;
             Ret (fn :: following)
          end) fds
    | _ => Err "unreachable"
  end ;;

  main_expr <- match top_exp with
               | Efun _ exp => Ret exp
               | _ => Err "unreachable"
               end;;

  let main_vars := collect_local_variables main_expr in
  let main_lenv := create_local_variable_mapping main_vars in

  main_instr <- translate_exp nenv cenv main_lenv fname_mapping main_expr ;;

  let main_function := {| fidx := main_function_idx
                        ; export_name := main_function_name
                        ; type := Tf [] []
                        ; locals := map (fun _ => T_i32) main_vars
                        ; body := main_instr
                        |}
  in
  let functions := [constr_pp_function; main_function] ++ fns in
  let exports := map (fun f => {| modexp_name := String.print f.(export_name)
                                ; modexp_desc := MED_func (Mk_funcidx f.(fidx))
                                |}) functions (* function exports for debug names *)
                 ++ {| modexp_name := String.print "result_out_of_mem"
                     ; modexp_desc := MED_global (Mk_globalidx result_out_of_mem)
                     |} ::
                    {| modexp_name := String.print "bytes_used"
                     ; modexp_desc := MED_global (Mk_globalidx global_mem_ptr)
                     |} ::
                    {| modexp_name := String.print "result"
                     ; modexp_desc := MED_global (Mk_globalidx result_var)
                     |} :: nil in

  let elements := table_element_mapping (length fns + 4) 0 in

  let functions_final := map (fun f => {| modfunc_type := Mk_typeidx (match f.(type) with Tf args _ => length args end)
                                        ; modfunc_locals := f.(locals)
                                        ; modfunc_body := f.(body)
                                        |}) functions in
  let module :=
      {| mod_types := list_function_types (Z.to_nat max_function_args) (* more than required, doesn't hurt*)

       ; mod_funcs := functions_final
       ; mod_tables := [ {| modtab_type := {| tt_limits := {| lim_min := N.of_nat (List.length fns + 4)
                                                            ; lim_max := None |}
                                            ; tt_elem_type := ELT_funcref
                                            |} |}]

       ; mod_mems := {| lim_min := 1%N                (* initial memory size in pages (1 page = 2^16 = 64 KiB), is grown as needed *)
                      ; lim_max := Some max_mem_pages (* set to ensure, i32 ptr doesn't overflow, but memory grow fails instead *)
                      |} :: nil

       ; mod_globals := {| modglob_type := {| tg_mut := MUT_mut; tg_t := T_i32 |}  (* global_mem_ptr *)
                         ; modglob_init := [BI_const (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_mut; tg_t := T_i32 |}  (* constr_alloc_ptr *)
                         ; modglob_init := [BI_const (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_mut; tg_t := T_i32 |}  (* result_var *)
                         ; modglob_init := [BI_const (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_mut; tg_t := T_i32 |}  (* out of memory indicator *)
                         ; modglob_init := [BI_const (nat_to_value 0)]
                         |} :: nil

       ; mod_elem := elements
       ; mod_data := []
       ; mod_start := None

       ; mod_imports := {| imp_module := String.print "env"
                         ; imp_name := String.print write_char_function_name
                         ; imp_desc := ID_func 1
                         |} ::
                        {| imp_module := String.print "env"
                         ; imp_name := String.print write_int_function_name
                         ; imp_desc := ID_func 1
                         |} :: nil

       ; mod_exports := exports
       |}
       in
       (* also return mappings to access them in proof *)
       Ret (module, fname_mapping, main_lenv).
