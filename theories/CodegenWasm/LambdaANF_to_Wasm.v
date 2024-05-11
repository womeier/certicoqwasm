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
Definition max_constr_args   := 1024%Z.      (* should be possible to vary without breaking much *)

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

Definition write_int64_function_idx : funcidx := 2%N.
Definition write_int64_function_name := "write_int64".


(* grow_mem: grow linear mem by number of bytes if necessary *)
Definition grow_mem_function_name := "grow_mem_if_necessary".
Definition grow_mem_function_idx : funcidx := 3%N.

(* main function: contains the translated main expression *)
Definition main_function_name := "main_function".
Definition main_function_idx : funcidx := 4%N.


(* then follow the translated functions,
   index of first translated lANF fun, a custom fun should be added before, and this var increased by 1
   (the proof will still break at various places)  *)
Definition num_custom_funs := 5.

(* global vars *)
Definition global_mem_ptr    : globalidx := 0%N. (* ptr to free memory, increased when new 'objects' are allocated, there is no GC *)
Definition constr_alloc_ptr  : globalidx := 1%N. (* ptr to beginning of constr alloc in linear mem *)
Definition result_var        : globalidx := 2%N. (* final result *)
Definition result_out_of_mem : globalidx := 3%N.
Definition tmp1              : globalidx := 4%N.
Definition tmp2              : globalidx := 5%N.
Definition tmp3              : globalidx := 6%N.
Definition tmp4              : globalidx := 7%N.

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

(* generates list of n arguments *)
Fixpoint arg_list (n : nat) : list (localidx * value_type) :=
  match n with
  | 0 => []
  | S n' => arg_list n' ++ [(N.of_nat n', T_num T_i32)]
  end.

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

Definition instr_local_var_read (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (v : cps.var)
  : error basic_instruction :=
  if is_function_var fenv v
    then fidx <- translate_var nenv fenv v "translate local var read: obtaining function id" ;;
         Ret (BI_const_num (N_to_value fidx)) (* passing id of function <var_name> *)

    else var <- translate_var nenv lenv v "instr_local_var_read: normal var";;
         Ret (BI_local_get var).



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

Definition instr_write_newline : list basic_instruction :=
  [ BI_const_num (nat_to_value 10) ; BI_call write_char_function_idx ].

Definition instr_write_string (s : string) : list basic_instruction :=
  let fix to_ascii_list s' :=
    match s' with
    | String.EmptyString => []
    | String.String b s'' => Byte.to_nat b :: to_ascii_list s''
    end in
  flat_map (fun c => [BI_const_num (nat_to_value c); BI_call write_char_function_idx]) (to_ascii_list s).

Definition get_ctor_arity (cenv : ctor_env) (t : ctor_tag) :=
  match M.get t cenv with
  | Some {| ctor_arity := n |} => Ret (N.to_nat n)
  | _ => Err "found constructor without ctor_arity set"
  end.

(* ***** GENERATE FUNCTION TO GROW LINEAR MEMORY ****** *)

(* a page is 2^16 bytes, expected num of required bytes in local 0 *)
Definition grow_memory_if_necessary : list basic_instruction :=
  (* required number of total pages *)
  [ BI_global_get global_mem_ptr
  ; BI_local_get 0%N
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_const_num (Z_to_value (Z.pow 2 16))
  ; BI_binop T_i32 (Binop_i (BOI_div SX_S))

  (* current number of pages *)
  ; BI_memory_size
  ; BI_relop T_i32 (Relop_i (ROI_ge SX_S))
  (* allocate one page if necessary *)
  ; BI_if (BT_valtype None)
      [ BI_const_num (nat_to_value 1)
      ; BI_memory_grow (* returns -1 on alloc failure *)
      ; BI_const_num (Z_to_value (-1))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (BT_valtype None)
         [ BI_const_num (nat_to_value 1); BI_global_set result_out_of_mem ]
         []
      ]
      []
  ].

Definition generate_grow_mem_function : wasm_function :=
  {| fidx := grow_mem_function_idx
   ; export_name := grow_mem_function_name
   ; type := 1%N (* [i32] -> [] *)
   ; locals := []
   ; body := grow_memory_if_necessary
   |}.


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

Definition translate_call (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (f : cps.var) (args : list cps.var) (tailcall : bool)
  : error (list basic_instruction) :=
  instr_pass_params <- pass_function_args nenv lenv fenv args;;
  instr_fidx <- instr_local_var_read nenv lenv fenv f;;
  let call := (fun num_args : nat => if tailcall then BI_return_call_indirect 0%N (N.of_nat num_args)
                                                 else BI_call_indirect 0%N (N.of_nat num_args)) in
  Ret (instr_pass_params ++ [instr_fidx] ++ [call (length args)]).
  (* all fns return nothing, type = num args *)

(* **** TRANSLATE PRIMITIVE VALUES **** *)

Definition translate_primitive_value (p : AstCommon.primitive) : error Wasm_int.Int64.int :=
  match projT1 p as tag return prim_value tag -> error Wasm_int.Int64.T with
  | AstCommon.primInt => fun i => Ret (Wasm_int.Int64.repr (Uint63.to_Z i))
  | AstCommon.primFloat => fun f => Err "TODO"
  end (projT2 p).

(* ***** TRANSLATE CONSTRUCTOR ALLOCATION ****** *)

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

(* store argument pointers in memory *)
Fixpoint set_constructor_args (nenv : name_env) (lenv : localvar_env) (fenv : fname_env) (args : list cps.var) (current : nat) : error (list basic_instruction) :=
  match args with
  | [] => Ret []
  | y :: ys => read_y <- instr_local_var_read nenv lenv fenv y;;
               remaining <- set_constructor_args nenv lenv fenv ys (1 + current);;

               Ret ([ BI_global_get constr_alloc_ptr
                    ; BI_const_num (nat_to_value (4 * (1 + current))) (* plus 1 : skip tag *)
                    ; BI_binop T_i32 (Binop_i BOI_add)
                    ; read_y
                    ; BI_store T_i32 None 2%N 0%N (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)

                    (* increase gmp by 4 *)
                    ; BI_global_get global_mem_ptr
                    ; BI_const_num (nat_to_value 4)
                    ; BI_binop T_i32 (Binop_i BOI_add)
                    ; BI_global_set global_mem_ptr

                    ] ++ remaining)
  end.


Definition store_constructor (nenv : name_env) (cenv : ctor_env) (lenv : localvar_env) (fenv : fname_env) (c : ctor_tag) (ys : list cps.var) : error (list basic_instruction) :=
  ord <- get_ctor_ord cenv c ;;
  set_constr_args <- set_constructor_args nenv lenv fenv ys 0;;
  Ret ([ BI_global_get global_mem_ptr
       ; BI_global_set constr_alloc_ptr

       (* set tag *)
       ; BI_global_get constr_alloc_ptr
       ; BI_const_num (nat_to_value (N.to_nat ord))
       ; BI_store T_i32 None 2%N 0%N (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
       (* increase gmp by 4 *)
       ; BI_global_get global_mem_ptr
       ; BI_const_num (nat_to_value 4)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_global_set global_mem_ptr

       ] ++ set_constr_args).

(* **** TRANSLATE PRIMITIVE OPERATIONS **** *)

Definition primInt63ModPath : Kernames.modpath :=
  Kernames.MPfile [ "PrimInt63"%bs ; "Int63"%bs ; "Cyclic"%bs ; "Numbers"%bs ; "Coq"%bs ].

Definition primInt63Add       : Kernames.kername := (primInt63ModPath, "add"%bs).
Definition primInt63Addc      : Kernames.kername := (primInt63ModPath, "addc"%bs).
Definition primInt63Addcarryc : Kernames.kername := (primInt63ModPath, "addcarryc"%bs).
Definition primInt63Sub       : Kernames.kername := (primInt63ModPath, "sub"%bs).
Definition primInt63Subc      : Kernames.kername := (primInt63ModPath, "subc"%bs).
Definition primInt63Subcarryc : Kernames.kername := (primInt63ModPath, "subcarryc"%bs).
Definition primInt63Mul       : Kernames.kername := (primInt63ModPath, "mul"%bs).
Definition primInt63Mulc      : Kernames.kername := (primInt63ModPath, "mulc"%bs).
Definition primInt63Div       : Kernames.kername := (primInt63ModPath, "div"%bs).
Definition primInt63Mod       : Kernames.kername := (primInt63ModPath, "mod"%bs).
Definition primInt63Land      : Kernames.kername := (primInt63ModPath, "land"%bs).
Definition primInt63Lor       : Kernames.kername := (primInt63ModPath, "lor"%bs).
Definition primInt63Lxor      : Kernames.kername := (primInt63ModPath, "lxor"%bs).
Definition primInt63Lsl       : Kernames.kername := (primInt63ModPath, "lsl"%bs).
Definition primInt63Lsr       : Kernames.kername := (primInt63ModPath, "lsr"%bs).
Definition primInt63Compare   : Kernames.kername := (primInt63ModPath, "compare"%bs).
Definition primInt63Eqb       : Kernames.kername := (primInt63ModPath, "eqb"%bs).
Definition primInt63Ltb       : Kernames.kername := (primInt63ModPath, "ltb"%bs).
Definition primInt63Leb       : Kernames.kername := (primInt63ModPath, "leb"%bs).
Definition primInt63Head0 : Kernames.kername := (primInt63ModPath, "head0"%bs).
Definition primInt63Tail0 : Kernames.kername := (primInt63ModPath, "tail0"%bs).
Definition primInt63Addmuldiv : Kernames.kername := (primInt63ModPath, "addmuldiv"%bs).
Definition primInt63Diveucl   : Kernames.kername := (primInt63ModPath, "diveucl"%bs).
Definition primInt63Diveucl_21   : Kernames.kername := (primInt63ModPath, "diveucl_21"%bs).

Definition maxuint31 := VAL_int64 (Wasm_int.Int64.repr 2147483647%Z).
Definition maxuint63 := VAL_int64 (Wasm_int.Int64.repr 9223372036854775807%Z).
Definition uint63modulus := VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus).

Definition load_local_i64 (i : localidx) : list basic_instruction :=
  [ BI_local_get i ; BI_load T_i64 None 2%N 0%N ].

Definition increment_global_mem_ptr i :=
  [ BI_global_get global_mem_ptr
  ; BI_const_num (nat_to_value i)
  ; BI_binop T_i32 (Binop_i BOI_add)
  ; BI_global_set global_mem_ptr
  ].

Definition apply_binop_and_store_i64 (op : list basic_instruction) y1 y2 :=
  BI_global_get global_mem_ptr :: (* Address to store the result of the operation *)
  load_local_i64 y1 ++            (* Load the arguments onto the stack *)
  load_local_i64 y2 ++
  op ++
  BI_store T_i64 None 2%N 0%N  :: (* Store the result *)
  BI_global_get global_mem_ptr :: (* Put the address where the result was stored on the stack *)
  increment_global_mem_ptr 8.

(* Assume argument is stored in gidx *)
Definition make_carry (ord : nat) (gidx : N) : list basic_instruction :=
  [ BI_global_get global_mem_ptr
    ; BI_global_get gidx
    ; BI_store T_i64 None 2%N 0%N
    ; BI_global_get global_mem_ptr
    ; BI_const_num (nat_to_value 8)
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_global_set constr_alloc_ptr
    ; BI_global_get constr_alloc_ptr
    ; BI_const_num (nat_to_value ord)
    ; BI_store T_i32 None 2%N 0%N
    ; BI_global_get global_mem_ptr
    ; BI_const_num (nat_to_value 12)
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_global_get global_mem_ptr
    ; BI_store T_i32 None 2%N 0%N
    ; BI_global_get constr_alloc_ptr
  ] ++ increment_global_mem_ptr 16.

(* Assume 1st argument is stored in global gidx1, 2nd argument in global gidx2 *)
Definition make_product (gidx1 gidx2 : N) : list basic_instruction :=
  [ BI_global_get global_mem_ptr
    ; BI_global_get gidx1
    ; BI_store T_i64 None 2%N 0%N
    ; BI_global_get global_mem_ptr
    ; BI_const_num (nat_to_value 8)
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_global_get gidx2
    ; BI_store T_i64 None 2%N 0%N
    ; BI_global_get global_mem_ptr
    ; BI_const_num (nat_to_value 16)
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_global_set constr_alloc_ptr
    ; BI_global_get constr_alloc_ptr
    ; BI_const_num (nat_to_value 0)
    ; BI_store T_i32 None 2%N 0%N

    ; BI_global_get global_mem_ptr
    ; BI_const_num (nat_to_value 20)
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_global_get global_mem_ptr
    ; BI_store T_i32 None 2%N 0%N

    ; BI_global_get global_mem_ptr
    ; BI_const_num (nat_to_value 24)
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_global_get global_mem_ptr
    ; BI_const_num (nat_to_value 8)
    ; BI_binop T_i32 (Binop_i BOI_add)
    ; BI_store T_i32 None 2%N 0%N

    ; BI_global_get constr_alloc_ptr
  ] ++ increment_global_mem_ptr 28.

Definition translate_primitive_arith_op nenv lenv kname y1 y2 : error (list basic_instruction) :=
    y1_var <- translate_var nenv lenv y1 "translate primitive integer arithmetic operation 1st argument" ;;
    y2_var <- translate_var nenv lenv y2 "translate primitive integer arithmetic operation 2nd argument" ;;
    if Kername.eqb kname primInt63Add then
      Ret (apply_binop_and_store_i64
             [ BI_binop T_i64 (Binop_i BOI_add)
             ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus))
             ; BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ] y1_var y2_var)
    else if Kername.eqb kname primInt63Sub then
      Ret (apply_binop_and_store_i64
             [ BI_binop T_i64 (Binop_i BOI_sub)
             ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus))
             ; BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ] y1_var y2_var)
    else if Kername.eqb kname primInt63Mul then
      Ret (apply_binop_and_store_i64
             [ BI_binop T_i64 (Binop_i BOI_mul)
             ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus))
             ; BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ] y1_var y2_var)
    else if Kername.eqb kname primInt63Div then
      Ret ([ BI_local_get y2_var
            ; BI_load T_i64 None 2%N 0%N
            ; BI_testop T_i64 TO_eqz
            ; BI_if (BT_valtype None)
                [ BI_global_get global_mem_ptr
                ; BI_const_num (nat_to_value64 0)
                ; BI_store T_i64 None 2%N 0%N
                ]
                [ BI_global_get global_mem_ptr
                ; BI_local_get y1_var
                ; BI_load T_i64 None 2%N 0%N
                ; BI_local_get y2_var
                ; BI_load T_i64 None 2%N 0%N
                ; BI_binop T_i64 (Binop_i (BOI_div SX_U))
                ; BI_store T_i64 None 2%N 0%N
                ]
            ; BI_global_get global_mem_ptr
            ] ++ increment_global_mem_ptr 8)
    else if Kername.eqb kname primInt63Land then
      Ret (apply_binop_and_store_i64 [ BI_binop T_i64 (Binop_i BOI_and) ] y1_var y2_var)
    else if Kername.eqb kname primInt63Lor then
      Ret (apply_binop_and_store_i64 [ BI_binop T_i64 (Binop_i BOI_or) ] y1_var y2_var)
    else if Kername.eqb kname primInt63Lsl then
           Ret(BI_global_get global_mem_ptr ::
                 load_local_i64 y2_var ++
                 [ BI_const_num (nat_to_value64 64)
                   ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
                   ; BI_if (BT_valtype (Some (T_num T_i64)))
                       (load_local_i64 y1_var ++
                          load_local_i64 y2_var ++
                          [ BI_binop T_i64 (Binop_i BOI_shl)
                            ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus))
                            ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
                       ])
                       [ BI_const_num (nat_to_value64 0) ]
                   ; BI_store T_i64 None 2%N 0%N
                   ; BI_global_get global_mem_ptr
                   ] ++ increment_global_mem_ptr 8)

    else if Kername.eqb kname primInt63Lsr then
           Ret(BI_global_get global_mem_ptr ::
                 load_local_i64 y2_var ++
                 [ BI_const_num (nat_to_value64 64)
                   ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
                   ; BI_if (BT_valtype (Some (T_num T_i64)))
                       (load_local_i64 y1_var ++
                          load_local_i64 y2_var ++
                          [ BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ])
                       [ BI_const_num (nat_to_value64 0) ]
                   ; BI_store T_i64 None 2%N 0%N
                   ; BI_global_get global_mem_ptr
                   ] ++ increment_global_mem_ptr 8)

    else if Kername.eqb kname primInt63Eqb then
      (* Assumptions about constructor environment for primitive operations that return bools:
         1. ordinal(true) = 0
         2. ordinal(false) = 1 *)
      Ret ([ BI_local_get y1_var
           ; BI_load T_i64 None 2%N 0%N
           ; BI_local_get y2_var
           ; BI_load T_i64 None 2%N 0%N
           ; BI_relop T_i64 (Relop_i ROI_eq)
           ; BI_if (BT_valtype (Some (T_num T_i32)))
               [ BI_const_num (nat_to_value 1) ] (* 2 * ordinal(true) + 1 *)
               [ BI_const_num (nat_to_value 3) ] (* 2 * ordinal(false) + 1 *)
           ])

    else if Kername.eqb kname primInt63Ltb then
      Ret ([ BI_local_get y1_var
           ; BI_load T_i64 None 2%N 0%N
           ; BI_local_get y2_var
           ; BI_load T_i64 None 2%N 0%N
           ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
           ; BI_if (BT_valtype (Some (T_num T_i32)))
               [ BI_const_num (nat_to_value 1) ] (* 2 * ordinal(true) + 1 *)
               [ BI_const_num (nat_to_value 3) ] (* 2 * ordinal(false) + 1 *)
           ])

    else if Kername.eqb kname primInt63Leb then
      Ret ([ BI_local_get y1_var
           ; BI_load T_i64 None 2%N 0%N
           ; BI_local_get y2_var
           ; BI_load T_i64 None 2%N 0%N
           ; BI_relop T_i64 (Relop_i (ROI_le SX_U))
           ; BI_if (BT_valtype (Some (T_num T_i32)))
               [ BI_const_num (nat_to_value 1) ] (* 2 * ordinal(true) + 1 *)
               [ BI_const_num (nat_to_value 3) ] (* 2 * ordinal(false) + 1 *)
           ])
    else if Kername.eqb kname primInt63Compare then
      Ret ([ BI_local_get y1_var
           ; BI_load T_i64 None 2%N 0%N
           ; BI_local_get y2_var
           ; BI_load T_i64 None 2%N 0%N
           ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
           ; BI_if (BT_valtype (Some (T_num T_i32)))
               [ BI_const_num (nat_to_value 3) ] (* 2 * ordinal(Lt) + 1 *)
               (load_local_i64 y1_var ++
                  load_local_i64 y2_var ++
                  [ BI_relop T_i64 (Relop_i ROI_eq)
                    ; BI_if (BT_valtype (Some (T_num T_i32)))
                        [ BI_const_num (nat_to_value 1) ]
                        [ BI_const_num (nat_to_value 5) ]
                  ])
          ])
    else if Kername.eqb kname primInt63Lxor then
      Ret (apply_binop_and_store_i64 [ BI_binop T_i64 (Binop_i BOI_xor) ] y1_var y2_var)

    else if Kername.eqb kname primInt63Mod then
      Ret ([ BI_local_get y2_var
            ; BI_load T_i64 None 2%N 0%N
            ; BI_testop T_i64 TO_eqz
            ; BI_if (BT_valtype None)
                [ BI_global_get global_mem_ptr
                  ; BI_local_get y1_var
                  ; BI_load T_i64 None 2%N 0%N
                  ; BI_store T_i64 None 2%N 0%N
                ]
                [ BI_global_get global_mem_ptr
                ; BI_local_get y1_var
                ; BI_load T_i64 None 2%N 0%N
                ; BI_local_get y2_var
                ; BI_load T_i64 None 2%N 0%N
                ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
                ; BI_store T_i64 None 2%N 0%N
                ]
            ; BI_global_get global_mem_ptr
            ] ++ increment_global_mem_ptr 8)

    else if Kername.eqb kname primInt63Addc then
           Ret (load_local_i64 y1_var ++
                  load_local_i64 y2_var ++
                  [ BI_binop T_i64 (Binop_i BOI_add)
                    ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus))
                    ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
                    ; BI_global_set tmp1
                    ; BI_global_get tmp1
                  ] ++ load_local_i64 y1_var ++
                  [ BI_relop T_i64 (Relop_i (ROI_lt SX_U))
                    ; BI_if (BT_valtype (Some (T_num T_i32)))
                        (make_carry 1 tmp1)
                        (make_carry 0 tmp1)
                  ])

    else if Kername.eqb kname primInt63Addcarryc then
           Ret (load_local_i64 y1_var ++
                  load_local_i64 y2_var ++
                  [ BI_binop T_i64 (Binop_i BOI_add)
                    ; BI_const_num (nat_to_value64 1)
                    ; BI_binop T_i64 (Binop_i BOI_add)
                    ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus))
                    ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
                    ; BI_global_set tmp1
                    ; BI_global_get tmp1
                  ] ++
                  load_local_i64 y1_var ++
                  [ BI_relop T_i64 (Relop_i (ROI_le SX_U))
                    ; BI_if (BT_valtype (Some (T_num T_i32)))
                        (make_carry 1 tmp1)
                        (make_carry 0 tmp1)
                  ])

    else if Kername.eqb kname primInt63Subc then
           Ret (load_local_i64 y1_var ++
                  load_local_i64 y2_var ++
                  [ BI_binop T_i64 (Binop_i BOI_sub)
                    ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus))
                    ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
                    ; BI_global_set tmp1
                  ] ++
                  load_local_i64 y2_var ++
                  load_local_i64 y1_var ++
                  [ BI_relop T_i64 (Relop_i (ROI_le SX_U))
                    ; BI_if (BT_valtype (Some (T_num T_i32)))
                        (make_carry 0 tmp1)
                        (make_carry 1 tmp1)
                  ])

    else if Kername.eqb kname primInt63Subcarryc then
           Ret (load_local_i64 y1_var ++
                  load_local_i64 y2_var ++
                  [ BI_binop T_i64 (Binop_i BOI_sub)
                    ; BI_const_num (nat_to_value64 1)
                    ; BI_binop T_i64 (Binop_i BOI_sub)
                    ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus))
                    ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
                    ; BI_global_set tmp1
                  ] ++
                  load_local_i64 y2_var ++
                  load_local_i64 y1_var ++
                  [ BI_relop T_i64 (Relop_i (ROI_lt SX_U))
                    ; BI_if (BT_valtype (Some (T_num T_i32)))
                        (make_carry 0 tmp1)
                        (make_carry 1 tmp1)
                  ])

    else if Kername.eqb kname primInt63Mulc then
           Ret (load_local_i64 y1_var ++
                  [ BI_const_num (nat_to_value64 62) ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_testop T_i64 TO_eqz ] ++
                  load_local_i64 y2_var ++
                  [ BI_const_num (nat_to_value64 62) ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_testop T_i64 TO_eqz ] ++
                  [ BI_binop T_i32 (Binop_i BOI_or)
                    ; BI_if (BT_valtype None)
                        (load_local_i64 y2_var ++
                           [ BI_global_set tmp3 ])
                        (load_local_i64 y2_var ++
                           [ BI_const_num (VAL_int64 (Wasm_int.Int64.repr 4611686018427387904%Z))
                             ; BI_binop T_i64 (Binop_i BOI_xor)
                             ; BI_global_set tmp3 ])
                  ] ++

                  (* tmp1 <- let hx = x >> 31 *)
                  load_local_i64 y1_var ++
                  [ BI_const_num (nat_to_value64 31) ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_global_set tmp1 ] ++
                  (* tmp2 <- let lx = x & ((1 << 31) - 1) *)
                  load_local_i64 y1_var ++
                  [ BI_const_num maxuint31 ; BI_binop T_i64 (Binop_i BOI_and) ; BI_global_set tmp2 ] ++
                  (* tmp4 <- let hy =  y >> 31 *)
                  [ BI_global_get tmp3 ; BI_const_num (nat_to_value64 31) ; BI_binop T_i64 (Binop_i (BOI_shr SX_U)) ; BI_global_set tmp4 ] ++
                  (* tmp3 <- let ly = y & ((1 << 31) - 1) *)
                  [ BI_global_get tmp3 ; BI_const_num maxuint31 ; BI_binop T_i64 (Binop_i BOI_and) ; BI_global_set tmp3 ] ++
                  [ BI_global_get tmp1 ; BI_global_get tmp4 ; BI_binop T_i64 (Binop_i BOI_mul) ] ++
                  [ BI_global_get tmp1 ; BI_global_get tmp3 ; BI_binop T_i64 (Binop_i BOI_mul) ] ++
                  [ BI_global_get tmp2 ; BI_global_get tmp4 ; BI_binop T_i64 (Binop_i BOI_mul) ] ++
                  [ BI_global_get tmp2 ; BI_global_get tmp3 ; BI_binop T_i64 (Binop_i BOI_mul) ] ++
                  (* tmp4 <- let lxy = lx * ly
                     tmp3 <- let lxhy = lx * hy
                     tmp2 <- let hxly = hx * ly
                     tmp1 <- let hxy  = hx * hy *)
                  [ BI_global_set tmp4
                    ; BI_global_set tmp3
                    ; BI_global_set tmp2
                    ; BI_global_set tmp1
                  ]  ++ 
                  (instr_write_string "tmp1 = ") ++ [ BI_global_get tmp1 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (instr_write_string "tmp2 = ") ++ [ BI_global_get tmp2 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (instr_write_string "tmp3 = ") ++ [ BI_global_get tmp3 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (instr_write_string "tmp4 = ") ++ [ BI_global_get tmp4 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (* tmp4 <- let l = lxy | (hxy << 62) = tmp4 | (tmp1 << 62) *)
                  [ BI_global_get tmp4
                    ; BI_global_get tmp1
                    ; BI_const_num (nat_to_value64 62)
                    ; BI_binop T_i64 (Binop_i BOI_shl)
                    ; BI_const_num maxuint63
                    ; BI_binop T_i64 (Binop_i BOI_and)
                    ; BI_binop T_i64 (Binop_i BOI_or)
                    ; BI_global_set tmp4
                  ] ++
                  (instr_write_string "tmp4 = ") ++ [ BI_global_get tmp4 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (* tmp1 <- let h = hxy >> 1 = tmp1 >> 1 *)
                  [ BI_global_get tmp1
                    ; BI_const_num (nat_to_value64 1)
                    ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
                    ; BI_global_set tmp1
                  ] ++
                  (instr_write_string "tmp1 = ") ++ [ BI_global_get tmp1 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (* tmp3 <- let hl = hxly + lxhy = tmp2 + tmp3 *)
                  [ BI_global_get tmp2
                    ; BI_global_get tmp3
                    ; BI_binop T_i64 (Binop_i BOI_add)
                    ; BI_const_num maxuint63
                    ; BI_binop T_i64 (Binop_i BOI_and)
                    ; BI_global_set tmp3
                  ] ++
                  (instr_write_string "tmp3 = ") ++ [ BI_global_get tmp3 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (* tmp1 <- let h = if hl < hxly then h + (1 << 31) else h *)
                  [ BI_global_get tmp3
                    ; BI_global_get tmp2
                    ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
                    ; BI_if (BT_valtype None)
                        [ BI_global_get tmp1
                          ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr 2147483648%Z))
                          ; BI_binop T_i64 (Binop_i BOI_add)
                          ; BI_const_num maxuint63
                          ; BI_binop T_i64 (Binop_i BOI_and)
                          ; BI_global_set tmp1
                        ]
                        [ ]
                  ] ++
                  (instr_write_string "tmp1 = ") ++ [ BI_global_get tmp1 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (* tmp2 <- let hl' = hl << 31 *)
                  [ BI_global_get tmp3
                    ; BI_const_num (nat_to_value64 31)
                    ; BI_binop T_i64 (Binop_i BOI_shl)
                    ; BI_const_num maxuint63
                    ; BI_binop T_i64 (Binop_i BOI_and)
                    ; BI_global_set tmp2
                  ] ++
                  (instr_write_string "tmp2 = ") ++ [ BI_global_get tmp2 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (* tmp4 <- let l = l + hl' *)
                  [ BI_global_get tmp4
                    ; BI_global_get tmp2
                    ; BI_binop T_i64 (Binop_i BOI_add)
                    ; BI_const_num maxuint63
                    ; BI_binop T_i64 (Binop_i BOI_and)
                    ; BI_global_set tmp4
                  ] ++
                  (instr_write_string "tmp4 = ") ++ [ BI_global_get tmp4 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (* tmp1 <- let h = if l < hl' then h + 1 else h *)
                  [ BI_global_get tmp4
                    ; BI_global_get tmp2
                    ; BI_relop T_i64 (Relop_i (ROI_lt SX_U))
                    ; BI_if (BT_valtype None)
                        [ BI_global_get tmp1
                          ; BI_const_num (nat_to_value64 1)
                          ; BI_binop T_i64 (Binop_i BOI_add)
                          ; BI_const_num maxuint63
                          ; BI_binop T_i64 (Binop_i BOI_and)
                          ; BI_global_set tmp1
                        ]
                        [ ]
                  ] ++
                  (instr_write_string "tmp1 = ") ++ [ BI_global_get tmp1 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  (* tmp1 <- let h = h + (hl >> 32) *)
                  [ BI_global_get tmp1
                    ; BI_global_get tmp3
                    ; BI_const_num (nat_to_value64 32)
                    ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
                    ; BI_binop T_i64 (Binop_i BOI_add)
                    ; BI_const_num maxuint63
                    ; BI_binop T_i64 (Binop_i BOI_and)
                    ; BI_global_set tmp1 ] ++
                  (instr_write_string "tmp1 = ") ++ [ BI_global_get tmp1 ; BI_call write_int64_function_idx ] ++ instr_write_newline ++
                  make_product tmp1 tmp4)

    else if Kername.eqb kname primInt63Diveucl then
           (* Assumptions about constructor representation of prod: ordinal(pair) = 0. *)
      Ret ([ BI_local_get y1_var
            ; BI_load T_i64 None 2%N 0%N
            ; BI_testop T_i64 TO_eqz
            ; BI_if (BT_valtype None)
                [ BI_const_num (nat_to_value64 0)
                  ; BI_global_set tmp1
                  ; BI_const_num (nat_to_value64 0)
                  ; BI_global_set tmp2
                ]
                [ BI_local_get y2_var
                  ; BI_load T_i64 None 2%N 0%N
                  ; BI_testop T_i64 TO_eqz
                  ; BI_if (BT_valtype None)
                      [ BI_const_num (nat_to_value64 0)
                        ; BI_global_set tmp1
                        ; BI_local_get y1_var
                        ; BI_load T_i64 None 2%N 0%N
                        ; BI_global_set tmp2
                      ]
                      (load_local_i64 y1_var ++
                         load_local_i64 y2_var ++
                         [ BI_binop T_i64 (Binop_i (BOI_div SX_U)) ; BI_global_set tmp1 ] ++
                         load_local_i64 y1_var ++
                         load_local_i64 y2_var ++
                         [ BI_binop T_i64 (Binop_i (BOI_rem SX_U)) ; BI_global_set tmp2 ])
                ]
          ] ++ make_product tmp1 tmp2)
    else
      Err ("Unknown primitive arithmetic operator: " ++ (Kernames.string_of_kername kname))%bs.

Definition translate_primitive_operation (nenv : name_env) (lenv : localvar_env) (p : (kername * string * bool * nat)) (args : list var) : error (list basic_instruction) :=
  let '(kname, _, _, _) := p in
  match args with
  | [ y ] =>
      y_var <- translate_var nenv lenv y "translate primitive operands single operand";;
      if Kername.eqb kname primInt63Head0 then
        (* head0 y computes the leading number of zeros in y
           OBS: need to subtract 1 since we're dealing with 63-bit integers *)
        Ret (BI_global_get global_mem_ptr ::
                load_local_i64 y_var ++
                [ BI_unop T_i64 (Unop_i UOI_clz)
                  ; BI_const_num (nat_to_value64 1)
                  ; BI_binop T_i64 (Binop_i BOI_sub)
                  ; BI_store T_i64 None 2%N 0%N
                  ; BI_global_get global_mem_ptr
                ] ++
                increment_global_mem_ptr 8)

      else if Kername.eqb kname primInt63Tail0 then
             (* tail0 y computes the trailing number of zeros in y
                OBS: if y is 0, then result is 63 (can't just use wasm ctz op) ) *)
             Ret (BI_global_get global_mem_ptr ::
                    load_local_i64 y_var ++
                    [ BI_testop T_i64 TO_eqz
                      ; BI_if (BT_valtype (Some (T_num T_i64)))
                          [ BI_const_num (nat_to_value64 63) ]
                          (load_local_i64 y_var ++ [ BI_unop T_i64 (Unop_i UOI_ctz) ])
                      ; BI_store T_i64 None 2%N 0%N
                      ; BI_global_get global_mem_ptr ] ++
                    increment_global_mem_ptr 8)
      else
        Err ("Unknown primitive unary operator: " ++ (Kernames.string_of_kername kname))%bs

  | [ y1 ; y2 ] => translate_primitive_arith_op nenv lenv kname y1 y2

  | [ y1 ; y2 ; y3 ] =>
      y1_var <- translate_var nenv lenv y1 "translate primitive operands 1st operand" ;;
      y2_var <- translate_var nenv lenv y2 "translate primitive operands 2nd operand" ;;
      y3_var <- translate_var nenv lenv y3 "translate primitive operands 3rd operand" ;;
      if Kername.eqb kname primInt63Diveucl_21 then
        let loop_body :=
          (* tmp1 <- nh := (nh << 1) | (nl >> 62)  *)
          [ BI_global_get tmp1
            ; BI_const_num (nat_to_value64 1)
            ; BI_binop T_i64 (Binop_i BOI_shl)
            ; BI_global_get tmp2
            ; BI_const_num (nat_to_value64 62)
            ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
            ; BI_binop T_i64 (Binop_i BOI_or)
            ; BI_global_set tmp1

            (* tmp2 <- nl := nl << 1 *)
            ; BI_global_get tmp2
            ; BI_const_num (nat_to_value64 1)
            ; BI_binop T_i64 (Binop_i BOI_shl)
            ; BI_const_num maxuint63
            ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))
            ; BI_global_set tmp2

            (* tmp3 <- q := q << 1 *)
            ; BI_global_get tmp3
            ; BI_const_num (nat_to_value64 1)
            ; BI_binop T_i64 (Binop_i BOI_shl)
            ; BI_const_num maxuint63
            ; BI_binop T_i64 (Binop_i BOI_and)
            ; BI_global_set tmp3

            (* if nh >= y then
               tmp3 <- q := q | 1
               tmp1 <- nh := nh - y *)
            ; BI_global_get tmp1
            ; BI_global_get tmp4
            ; BI_relop T_i64 (Relop_i (ROI_ge SX_U))
            ; BI_if (BT_valtype None)
                [ BI_global_get tmp3
                  ; BI_const_num (nat_to_value64 1)
                  ; BI_binop T_i64 (Binop_i BOI_or)
                  ; BI_global_set tmp3
                  ; BI_global_get tmp1
                  ; BI_global_get tmp4
                  ; BI_binop T_i64 (Binop_i BOI_sub)
                  ; BI_global_set tmp1
                ]
                [ ]
          ]
        in
        Ret (
            load_local_i64 y3_var ++
              [ BI_const_num maxuint63
                ; BI_binop T_i64 (Binop_i BOI_and)
                ; BI_global_set tmp4
              ] ++
              load_local_i64 y1_var ++
              [ BI_const_num maxuint63
                ; BI_binop T_i64 (Binop_i BOI_and)
                ; BI_global_set tmp1
              ] ++
              [ BI_global_get tmp4
                ; BI_global_get tmp1
                ; BI_relop T_i64 (Relop_i (ROI_le SX_U))
                 ; BI_if (BT_valtype (Some (T_num T_i32)))
                     ([ BI_const_num (nat_to_value64 0) ; BI_global_set tmp1 ] ++
                        make_product tmp1 tmp1)
                     (load_local_i64 y2_var ++
                        [ BI_global_set tmp2
                          ; BI_const_num (nat_to_value64 0)
                          ; BI_global_set tmp3
                        ] ++ (List.flat_map (fun x => x) (List.repeat loop_body 63)) ++
                        [ BI_global_get tmp1
                          ; BI_const_num maxuint63
                          ; BI_binop T_i64 (Binop_i BOI_and)
                          ; BI_global_set tmp1
                        ] ++ make_product tmp3 tmp1)
               ])

      else if Kername.eqb kname primInt63Addmuldiv then
           Ret (BI_global_get global_mem_ptr ::
                load_local_i64 y1_var ++
                [ BI_const_num (nat_to_value64 63)
                ; BI_relop T_i64 (Relop_i (ROI_gt SX_U))
                ; BI_if (BT_valtype (Some (T_num T_i64)))
                    [ BI_const_num (nat_to_value64 0) ]
                    (* Compute x << p on the stack *)
                    (load_local_i64 y2_var ++
                     load_local_i64 y1_var ++
                     [ BI_binop T_i64 (Binop_i BOI_shl)
                       ; BI_const_num maxuint63
                       ; BI_binop T_i64 (Binop_i BOI_and)
                       (* ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus)) *)
                       (* ; BI_binop T_i64 (Binop_i (BOI_rem SX_U)) *)
                     ] ++
                     (* Put y on the stack *)
                     load_local_i64 y3_var ++
                     (* Compute 63 - p on the stack *)
                     [ BI_const_num (nat_to_value64 63) ] ++
                     load_local_i64 y1_var ++
                     [ BI_binop T_i64 (Binop_i BOI_sub)
                     (* Compute y >> (63 - p) on the stack *)
                     ; BI_binop T_i64 (Binop_i (BOI_shr SX_U))
                     (* Finally, compute (x << p) | (y >> (63 - p)) on the stack *)
                     ; BI_binop T_i64 (Binop_i BOI_or) ])
                     (* Take the result modulo 2^63 to account for overflow *)
                     (* ; BI_const_num (VAL_int64 (Wasm_int.Int64.repr Wasm_int.Int64.half_modulus)) *)
                     (* ; BI_binop T_i64 (Binop_i (BOI_rem SX_U))]) *)
                ; BI_store T_i64 None 2%N 0%N
                ; BI_global_get global_mem_ptr
                ] ++ increment_global_mem_ptr 8)
         else
           Err ("Unknown primitive arithmetic operator: " ++ (Kernames.string_of_kername kname))%bs

  | _ =>
      Err "Only primitive operations with 1, 2 or 3 arguments are supported"
  end.

Fixpoint create_case_nested_if_chain (boxed : bool) (v : localidx) (es : list (N * list basic_instruction)) : list basic_instruction :=
  match es with
  | [] => [ BI_unreachable ]
  | (ord, instrs) :: tl =>
      (* if boxed (pointer), then load tag from memory;
         otherwise, the unboxed representation is (ord << 1) + 1 = 2 * ord + 1.
       *)
      BI_local_get v ::
        (if boxed then
           [ BI_load T_i32 None 2%N 0%N ; BI_const_num (nat_to_value (N.to_nat ord)) ]
         else
           [ BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N)) ]) ++
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
          Ret ([ BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N)) ; BI_local_set x_var ] ++ following_instr)
      | _ => (* n > 0 ary constructor  *)
          (* Boxed representation *)
          store_constr <- store_constructor nenv cenv lenv fenv tg ys;;
          Ret ([ BI_const_num (N_to_value page_size)
               ; BI_call grow_mem_function_idx
               ; BI_global_get result_out_of_mem
               ; BI_const_num (nat_to_value 1)
               ; BI_relop T_i32 (Relop_i ROI_eq)
               ; BI_if (BT_valtype None)
                 [ BI_return ]
                 []
               ] ++ store_constr ++
               [ BI_global_get constr_alloc_ptr
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
           ; BI_const_num (nat_to_value 1)
           ; BI_binop T_i32 (Binop_i BOI_and)
           ; BI_testop T_i32 TO_eqz
           ; BI_if (BT_valtype None)
               (create_case_nested_if_chain true x_var arms_boxed)
               (create_case_nested_if_chain false x_var arms_unboxed)
           ])

   | Eproj x tg n y e' =>
      following_instr <- translate_body nenv cenv lenv fenv penv e' ;;
      y_var <- translate_var nenv lenv y "translate_body proj y";;
      x_var <- translate_var nenv lenv x "translate_body proj x";;

      Ret ([ BI_local_get y_var
           ; BI_const_num (nat_to_value (((N.to_nat n) + 1) * 4)) (* skip ctor_id and previous constr arguments *)
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; BI_load T_i32 None 2%N 0%N (* 0: offset, 2: 4-byte aligned, alignment irrelevant for semantics *)
           ; BI_local_set x_var
           ] ++ following_instr)

   | Eletapp x f ft ys e' =>
      x_var <- translate_var nenv lenv x "translate_body proj x";;
      following_instr <- translate_body nenv cenv lenv fenv penv e' ;;
      instr_call <- translate_call nenv lenv fenv f ys false;;

      Ret (instr_call ++ [ BI_global_get result_out_of_mem
                         ; BI_if (BT_valtype None)
                            [ BI_return ]
                            []
                         ; BI_global_get result_var
                         ; BI_local_set x_var
                         ] ++ following_instr)

   | Eapp f ft ys => translate_call nenv lenv fenv f ys true

   | Eprim_val x p e' =>
       following_instrs <- translate_body nenv cenv lenv fenv penv e' ;;
       x_var <- translate_var nenv lenv x "translate_body prim val" ;;
       val <- translate_primitive_value p ;;
       Ret ([ BI_const_num (N_to_value page_size)
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
            ; BI_local_set x_var
            ; BI_global_get global_mem_ptr
            ; BI_const_num (nat_to_value 8)
            ; BI_binop T_i32 (Binop_i BOI_add)
            ; BI_global_set global_mem_ptr
            ] ++ following_instrs)

   | Eprim x p ys e' => (* Err "temp" *)
       match M.get p penv with
       | None => Err "Primitive operation not found in prim_env"
       | Some p' =>
           following_instrs <- translate_body nenv cenv lenv fenv penv e';;
           x_var <- translate_var nenv lenv x "translate_exp prim op" ;;
           prim_op_instrs <- translate_primitive_operation nenv lenv p' ys ;;
           Ret (([ BI_const_num (N_to_value page_size)
                 ; BI_call grow_mem_function_idx
                 ; BI_global_get result_out_of_mem
                 ; BI_const_num (nat_to_value 1)
                 ; BI_relop T_i32 (Relop_i ROI_eq)
                 ; BI_if (BT_valtype None)
                     [ BI_return ]
                     []
                 ] ++ prim_op_instrs ++ [ BI_local_set x_var ])  ++ following_instrs)
       end
   | Ehalt x =>
     x_var <- translate_var nenv lenv x "translate_body halt";;
     Ret [ BI_local_get x_var; BI_global_set result_var; BI_return ]
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
       ; locals := map (fun _ => T_num T_i32) locals
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
  | S n' => (Tf [] []) :: map (fun t => match t with Tf args rt => Tf (T_num T_i32 :: args) rt end) (list_function_types n')
  end.

(* for indirect calls maps fun ids to themselves *)
Fixpoint table_element_mapping (len : nat) (startidx : nat) : list module_element :=
  match len with
  | 0 => []
  | S len' => {| modelem_mode := ME_active 0%N [BI_const_num (nat_to_value startidx)]
               ; modelem_init := [[ BI_ref_func (N.of_nat startidx) ]]
               ; modelem_type := T_funcref
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
                        ; locals := map (fun _ => T_num T_i32) main_vars
                        ; body := main_instr
                        |}
  in
  let functions := [grow_mem_function; main_function] ++ fns in

  let exports := map (fun f => {| modexp_name := String.print f.(export_name)
                                ; modexp_desc := MED_func (f.(fidx))
                                |}) functions (* function exports for debug names *)
                 ++ {| modexp_name := String.print "result_out_of_mem"
                     ; modexp_desc := MED_global result_out_of_mem
                     |} ::
                    {| modexp_name := String.print "bytes_used"
                     ; modexp_desc := MED_global global_mem_ptr
                     |} ::
                    {| modexp_name := String.print "result"
                     ; modexp_desc := MED_global result_var
                    |} ::
                    {| modexp_name := String.print "memory"
                     ; modexp_desc := MED_mem 0%N
                    |} :: nil
  in

  let elements := table_element_mapping (length fns + num_custom_funs) 0 in

  let functions_final := map (fun f => {| modfunc_type := f.(type)
                                        ; modfunc_locals := f.(locals)
                                        ; modfunc_body := f.(body)
                                       |}) functions in

  let ftys := (list_function_types (Z.to_nat max_function_args)) in  
  let write_int64_fty := Tf [(T_num T_i64)] [] in
  let write_int64_fty_idx := List.length ftys in 
  let module :=
      {| mod_types := ftys ++ [ write_int64_fty ] (* more than required, doesn't hurt*)

       ; mod_funcs := functions_final
       ; mod_tables := [ {| modtab_type := {| tt_limits := {| lim_min := N.of_nat (List.length fns + num_custom_funs)

                                                            ; lim_max := None |}
                                            ; tt_elem_type := T_funcref
                                            |} |}]

       ; mod_mems := {| modmem_type :=
                         {| lim_min := 1%N  (* initial memory size in pages (1 page = 2^16 = 64 KiB), is grown as needed *)
                          ; lim_max := Some max_mem_pages (* to ensure, i32 ptr doesn't overflow, but memory grow fails instead *)
                          |}
                      |} :: nil

       ; mod_globals := {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}  (* global_mem_ptr *)
                         ; modglob_init := [BI_const_num (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}  (* constr_alloc_ptr *)
                         ; modglob_init := [BI_const_num (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}  (* result_var *)
                         ; modglob_init := [BI_const_num (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}  (* out of memory indicator *)
                         ; modglob_init := [BI_const_num (nat_to_value 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}  (* tmp1 *)
                         ; modglob_init := [BI_const_num (nat_to_value64 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}  (* tmp2 *)
                         ; modglob_init := [BI_const_num (nat_to_value64 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}  (* tmp3 *)
                         ; modglob_init := [BI_const_num (nat_to_value64 0)]
                         |} ::
                        {| modglob_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}  (* tmp4 *)
                         ; modglob_init := [BI_const_num (nat_to_value64 0)]
                         |} :: nil


       ; mod_elems := elements
       ; mod_datas := []
       ; mod_start := None

       ; mod_imports := {| imp_module := String.print "env"
                         ; imp_name := String.print write_char_function_name
                         ; imp_desc := MID_func 1%N
                         |} ::
                        {| imp_module := String.print "env"
                         ; imp_name := String.print write_int_function_name
                         ; imp_desc := MID_func 1%N
                        |} ::
                        {| imp_module := String.print "env"
                         ; imp_name := String.print write_int64_function_name
                         ; imp_desc := MID_func (N.of_nat write_int64_fty_idx)
                        |}
                        :: nil
       ; mod_exports := exports
       |}
       in
       (* also return mappings to access them in proof *)
       Ret (module, fname_mapping, main_lenv).
