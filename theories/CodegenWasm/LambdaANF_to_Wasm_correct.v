(* Proof of correctness of the Wasm code generation phase of CertiCoq,
   this file is based on the proof for the Clight backend.

 > Codegen relation: relates expressions to Wasm instructions
 > Value relation:   relates LambdaANF values to Wasm values
 > Environment relation: for vars free in the expression: provides value stored in the local vars
                         containing the result of previous execution steps, and func indides for functions
                         it is also called "memory relation" in Clight)

 > Main statement: relates LambdaANF states to Wasm states according
                   to operational semantics

  TODO: consider reusing functions from certicoq for collecting variables
  TODO: consider using Ensemble like the Clight backend
 *)
Set Printing Compact Contexts.

From compcert Require Import Coqlib.

Require Import LambdaANF.cps LambdaANF.eval LambdaANF.cps_util LambdaANF.List_util
               LambdaANF.Ensembles_util LambdaANF.identifiers
               LambdaANF.shrink_cps_corresp.


Require Import Coq.Program.Program Coq.Sets.Ensembles
               Coq.Logic.Decidable Coq.Lists.ListDec
               Coq.Relations.Relations Relations.Relation_Operators Lia
               EqdepFacts.

Require Import compcert.lib.Integers compcert.common.Memory.

From CertiCoq.CodegenWasm Require Import LambdaANF_to_Wasm_primitives LambdaANF_to_Wasm LambdaANF_to_Wasm_utils.

From Wasm Require Import datatypes operations host memory_list opsem
                         type_preservation instantiation_spec
                         instantiation_properties properties common numerics.
Import Wasm_int.

Require Import Libraries.maps_util.
From Coq Require Import List Nnat Uint63.

(* Avoid unfolding during proofs *)
Opaque Uint63.to_Z.

From MetaCoq Require Import Common.Kernames.

Import ssreflect eqtype ssrbool eqtype.
Import LambdaANF.toplevel LambdaANF.cps compM.
Import bytestring.
Import ExtLib.Structures.Monad MonadNotation.
Import bytestring.
Import ListNotations SigTNotations.
Import seq.

(* Restrictions on LambdaANF expressions, s.t. everything fits in Wasm i32s *)
Section SIZE_RESTRICTED.

(* TODO: incorporate into expression_restricted *)
(* all constructors in the exp exists in cenv and are applied to
   the right number of args *)
Definition correct_cenv_of_exp: LambdaANF.cps.ctor_env -> exp -> Prop :=
    fun cenv e =>
      Forall_constructors_in_e (fun x t ys =>
                                  match (M.get t cenv) with
                                  | Some (Build_ctor_ty_info _ _ _ a ord) =>
                                    N.of_nat (length ys) = a
                                  | None => False
                                  end) e.

(* All constructors in the constr. env satisfy the following:
   1. The ordinals of all nullary constructors are different
   2. The ordinals of all non-nullary constructors are different *)
Definition cenv_restricted (cenv : ctor_env) : Prop :=
  forall t name iname it a ord,
    M.get t cenv = Some (Build_ctor_ty_info name iname it a ord) ->
    forall t',
      t <> t' ->
      (a = 0%N -> ~ (exists name' iname', M.get t' cenv = Some (Build_ctor_ty_info name' iname' it 0%N ord))) /\
        ((0 < a)%N -> ~ (exists name' iname' a', M.get t' cenv = Some (Build_ctor_ty_info name' iname' it a' ord))).

Definition ctor_ordinal_restricted (cenv : ctor_env) (t : ctor_tag) : Prop :=
  forall n, get_ctor_ord cenv t = Ret n ->
      (Z.of_N n < Wasm_int.Int32.half_modulus)%Z.

Inductive expression_restricted : ctor_env -> cps.exp -> Prop :=
| ER_constr : forall x t ys e cenv,
    ctor_ordinal_restricted cenv t ->
      (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z ->
      expression_restricted cenv e ->
      expression_restricted cenv (Econstr x t ys e)
  | ER_case : forall x ms cenv,
      Forall (fun p =>
                ctor_ordinal_restricted cenv (fst p) /\
                        expression_restricted cenv (snd p)) ms ->
      expression_restricted cenv (Ecase x ms)
  | ER_proj : forall x t n y e cenv,
      expression_restricted cenv e ->
      expression_restricted cenv (Eproj x t n y e)
  | ER_letapp : forall f x ft ys e cenv,
      expression_restricted cenv e ->
      (Z.of_nat (Datatypes.length ys) <= max_function_args)%Z ->
      expression_restricted cenv (Eletapp x f ft ys e)
  | ER_fun : forall e fds cenv,
      expression_restricted cenv e ->
      (forall f t ys e', find_def f fds = Some (t, ys, e') ->
                   Z.of_nat (length ys) <= max_function_args /\
                   expression_restricted cenv e')%Z ->
      (Z.of_nat (numOf_fundefs fds) <= max_num_functions)%Z ->
      expression_restricted cenv (Efun fds e)
  | ER_app : forall f ft ys cenv,
      (Z.of_nat (Datatypes.length ys) <= max_function_args)%Z ->
      expression_restricted cenv (Eapp f ft ys)
  | ER_prim_val : forall x p e cenv,
      expression_restricted cenv e ->
      expression_restricted cenv (Eprim_val x p e)
  | ER_prim : forall x p ys e cenv,
      expression_restricted cenv e ->
      expression_restricted cenv (Eprim x p ys e)
  | ER_halt : forall x cenv,
      expression_restricted cenv (Ehalt x).

Local Hint Constructors expression_restricted : core.

Theorem check_restrictions_expression_restricted {cenv} : forall e e',
  check_restrictions cenv e = Ret () ->
  subterm_or_eq e' e -> expression_restricted cenv e'.
Proof.
  have IH := exp_mut
    (fun e => check_restrictions cenv e = Ret () -> forall e',
                subterm_or_eq e' e -> expression_restricted cenv e')
    (fun fds => ((fix iter (fds : fundefs) : error Datatypes.unit :=
                   match fds with
                   | Fnil => Ret ()
                   | Fcons _ _ ys e' fds' =>
                       _ <- assert (Z.of_nat (length ys) <=? max_function_args)%Z
                            "found fundef with too many function args, check max_function_args";;
                       _ <- (iter fds');;
                       check_restrictions cenv e'
                   end) fds) = Ret () -> forall e' e'',
               dsubterm_fds_e e' fds -> subterm_or_eq e'' e' -> expression_restricted cenv e'').
  intros. eapply IH; eauto; clear IH; try intros.
  { (* Econstr *)
    rename H3 into Hsub, H1 into IHe. inv H2.
    destruct (get_ctor_ord cenv t) eqn:Hord. inv H3.
    destruct (Z.of_N n <? Wasm_int.Int32.half_modulus)%Z eqn:Htupper. 2: inv H3.
    destruct (Z.of_nat (Datatypes.length l) <=? max_constr_args)%Z eqn:Hlen. 2: inv H3.
    cbn in H3. clear H.
    apply Z.ltb_lt in Htupper.
    apply Z.leb_le in Hlen. apply clos_rt_rtn1 in Hsub. inv Hsub. constructor; auto.
    unfold ctor_ordinal_restricted. intros. replace n0 with n by congruence. auto.
    apply IHe; auto. apply rt_refl. inv H. apply IHe; auto. now apply clos_rtn1_rt. }
  { (* Ecase nil *)
    rename H2 into Hsub.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor. apply Forall_nil.
    now inv H2. }
  { (* Ecase cons *)
    rename H4 into Hsub, H1 into IHe, H2 into IHe0. inv H3.
    clear H0 H e. rename e0 into e.
    destruct (get_ctor_ord cenv c) eqn:Hord. inv H2.
    destruct ((Z.of_N n <? Wasm_int.Int32.half_modulus)%Z) eqn:Hupper. 2: inv H2.
    cbn in H2. destruct (check_restrictions cenv e) eqn:Hrestr. inv H2.
    destruct (sequence _ ) eqn:Hseq; inv H2. destruct u.
    assert (check_restrictions cenv (Ecase v l) = Ret ()). {
      unfold check_restrictions. simpl. now rewrite Hseq. }
    assert (expression_restricted cenv (Ecase v l)). {
       apply IHe0; auto. apply rt_refl. }
    apply clos_rt_rtn1 in Hsub. inv Hsub.
    { constructor. apply Forall_cons. simpl. split.
      unfold ctor_ordinal_restricted. intros.
      now replace n0 with n by congruence.
      apply IHe; auto. apply rt_refl. now inv H0. }

    inv H1. destruct H5.
    { inv H1. apply IHe; auto. now apply clos_rtn1_rt. }
    { apply IHe0; auto. apply clos_rtn1_rt in H2.
      assert (subterm_or_eq y (Ecase v l)). {
        constructor. now econstructor. }
      now eapply rt_trans. }
  }
  { (* Eproj *)
    rename H3 into Hsub, H1 into IHe. inv H2. clear H e H0.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor. apply IHe; auto. apply rt_refl.
    inv H. apply IHe; auto. now apply clos_rtn1_rt. }
  { (* Eletapp *)
    rename H3 into Hsub, H1 into IHe. inv H2. clear H H0 e.
    destruct (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z eqn:Hlen. 2: inv H3.
    apply Z.leb_le in Hlen. apply clos_rt_rtn1 in Hsub. inv Hsub. constructor; auto.
    apply IHe; auto. apply rt_refl. inv H. apply IHe; auto.
    now apply clos_rtn1_rt. }
  { (* Efun *)
    rename H1 into IHfds, H2 into IHe, H4 into Hsub. inv H3.
    destruct (Z.of_nat (numOf_fundefs f2) <=? max_num_functions)%Z eqn:HmaxFns. 2: inv H2.
    cbn in H2.
    destruct ((fix iter (fds : fundefs) := _) f2) eqn:Hfds. inv H2. destruct u.
    apply clos_rt_rtn1 in Hsub. inv Hsub.
    { constructor.
      - apply IHe; auto. apply rt_refl.
      - intros. split.
        { clear IHfds H0 H IHe HmaxFns H2. clear e0 e e'.
          rename e'0 into e, f2 into fds.
          generalize dependent f. revert t ys e.
          induction fds; intros. 2: inv H1.
          cbn in H1. destruct (M.elt_eq f0 v).
          + (* f0=v *)
            inv H1. cbn in Hfds.
            destruct (Z.of_nat (Datatypes.length ys) <=? max_function_args)%Z eqn:Hlen.
            2: inv Hfds. now apply Z.leb_le in Hlen.
          + (* f0<>v *)
            cbn in Hfds.
            destruct (Z.of_nat (Datatypes.length l) <=? max_function_args)%Z.
            2:inv Hfds. cbn in Hfds.
            destruct ((fix iter (fds : fundefs) := _) fds) eqn:Hfds'. inv Hfds.
            destruct u. eapply IHfds; eauto.
        }
        apply find_def_dsubterm_fds_e in H1. eapply IHfds; eauto. apply rt_refl.
      - now apply Z.leb_le in HmaxFns.
    } inv H1.
    { apply clos_rtn1_rt in H3. eapply IHfds; eauto. }
    { apply IHe; auto. apply clos_rtn1_rt in H3. assumption. }
  }
  { (* Eapp *)
    rename H2 into Hsub. inv H1.
    destruct (Z.of_nat (Datatypes.length l) <=? max_function_args)%Z eqn:Hlen. 2: inv H3.
    apply Z.leb_le in Hlen. apply clos_rt_rtn1 in Hsub. now inv Hsub. }
  { (* Eprim_val *)
    rename H3 into Hsub, H1 into IHe. inv H2. clear H e H0.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor. apply IHe; auto. apply rt_refl.
    inv H. apply IHe; auto. now apply clos_rtn1_rt. }
  { (* Eprim *)
    rename H3 into Hsub, H1 into IHe. inv H2. clear H e H0.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor. apply IHe; auto. apply rt_refl.
    inv H. apply IHe; auto. now apply clos_rtn1_rt. }
  { (* Ehalt *)
    rename H2 into Hsub.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor. inv H2. }
  { (* base case 1 *)
    rename H2 into IHfds, H1 into IHe.
    cbn in H3. destruct (Z.of_nat (Datatypes.length l) <=? max_function_args)%Z.
    2:inv H3. cbn in H3.
    destruct ((fix iter (fds : fundefs) := _) f5) eqn:Hfds. inv H3. destruct u.
    inv H4.
    { apply IHe; auto. }
    { eapply IHfds; eauto. }
  }
  { (* base case 2 *) inv H2. }
Qed.

End SIZE_RESTRICTED.


(* Codegen relation *)
Section CODEGEN.

Variable cenv : LambdaANF.cps.ctor_env.
Variable funenv : LambdaANF.cps.fun_env.
Variable fenv : CodegenWasm.LambdaANF_to_Wasm.fname_env.
Variable nenv : LambdaANF.cps_show.name_env.
Variable penv : LambdaANF.toplevel.prim_env.

(* list can be empty *)
Inductive Forall_statements_in_seq' {A} :
  (nat -> A -> list basic_instruction -> Prop) -> list A ->
                           list basic_instruction -> nat -> Prop :=
| Fsis_nil : forall (R: nat  -> A -> list basic_instruction -> Prop) n,
   Forall_statements_in_seq' R [] [] n
| Fsis_cons : forall R v vs s s' n,
   Forall_statements_in_seq' R vs s' (S n) ->  R n v s ->
   Forall_statements_in_seq' R (v::vs) (s ++ s') n.

(* This is true for R, vs and S iff forall i, R i (nth vs) (nth s)
   > nth on statement is taken as nth on a list of sequenced statement (;) *)
Definition Forall_statements_in_seq {A} :
  (nat  -> A -> list basic_instruction -> Prop) -> list A ->
                                   list basic_instruction -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s 0.

(* like Forall_statements_in_seq, but starting from index 1 *)
Definition Forall_statements_in_seq_from_1 {A} :
  (nat  -> A -> list basic_instruction -> Prop) -> list A ->
                                   list basic_instruction -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s 1.

Inductive repr_var {lenv} : positive -> localidx -> Prop :=
| repr_var_V : forall s err_str i,
    translate_var nenv lenv s err_str = Ret i ->
    repr_var s i.

Inductive repr_funvar : positive -> funcidx -> Prop :=
| repr_funvar_FV : forall s i errMsg,
    translate_var nenv fenv s errMsg = Ret i ->
    repr_funvar s i.

Inductive repr_read_var_or_funvar {lenv} : positive -> basic_instruction -> Prop :=
| repr_var_or_funvar_V : forall p i,
    repr_var (lenv:=lenv) p i -> repr_read_var_or_funvar p (BI_local_get i)
| repr_var_or_funvar_FV : forall p i,
    repr_funvar p i -> repr_read_var_or_funvar p (BI_const_num (N_to_value i)).




(* constr_alloc_ptr: pointer to linear_memory[p + 4 + 4*n] = value v *)
Inductive set_nth_constr_arg {lenv} : nat -> var -> list basic_instruction -> Prop :=
  Make_nth_proj: forall (v : var) n instr,
    repr_read_var_or_funvar (lenv:=lenv) v instr ->
    set_nth_constr_arg n v
      [ BI_global_get constr_alloc_ptr
      ; BI_const_num (nat_to_value ((1 + n) * 4))
      ; BI_binop T_i32 (Binop_i BOI_add)
      ; instr
      ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0)
      ; BI_global_get global_mem_ptr
      ; BI_const_num (nat_to_value 4)
      ; BI_binop T_i32 (Binop_i BOI_add)
      ; BI_global_set global_mem_ptr
      ].

(* args are pushed on the stack before calling a function *)
Inductive repr_fun_args_Wasm {lenv} : list LambdaANF.cps.var ->
                                         list basic_instruction -> Prop :=
(* base case: no args *)
| FA_nil :
    repr_fun_args_Wasm [] []
(* arg is local var *)
| FA_cons_var : forall a a' args instr,
    repr_var (lenv:=lenv) a a' ->
    repr_fun_args_Wasm args instr ->
    repr_fun_args_Wasm (a :: args) ([BI_local_get a'] ++ instr)
(* arg is function -> lookup id for handling indirect calls later *)
| FA_cons_fun : forall a a' args instr,
    repr_funvar a a' ->
    repr_fun_args_Wasm args instr ->
    repr_fun_args_Wasm (a :: args) ([BI_const_num (N_to_value a')] ++ instr).

Inductive repr_asgn_constr_Wasm {lenv} : localidx -> ctor_tag -> list var -> list basic_instruction -> list basic_instruction ->  Prop :=
| Rconstr_asgn_boxed :
  forall x' t vs sargs scont arity ord,
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret arity ->
    arity > 0 ->
    (* store args *)
    Forall_statements_in_seq (set_nth_constr_arg (lenv:=lenv)) vs sargs ->

    repr_asgn_constr_Wasm x' t vs scont
      ([ BI_const_num (N_to_value page_size)
       ; BI_call grow_mem_function_idx
       ; BI_global_get result_out_of_mem
       ; BI_const_num (nat_to_value 1)
       ; BI_relop T_i32 (Relop_i ROI_eq)
       ; BI_if (BT_valtype None)
           (* grow mem failed *)
           [ BI_return ]
           []
       ; BI_global_get global_mem_ptr
       ; BI_global_set constr_alloc_ptr
       ; BI_global_get constr_alloc_ptr
       ; BI_const_num (nat_to_value (N.to_nat ord))
       ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0)
       ; BI_global_get global_mem_ptr
       ; BI_const_num (nat_to_value 4)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_global_set global_mem_ptr
       ] ++ sargs ++ [BI_global_get constr_alloc_ptr; BI_local_set x'] ++ scont)

| Rconstr_asgn_unboxed :
  forall x' t scont ord,
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret 0 ->
    repr_asgn_constr_Wasm x' t [] scont
      ([ BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N))
       ; BI_local_set x' ] ++ scont ).


Inductive repr_case_boxed: localidx -> list (N * list basic_instruction) -> list basic_instruction -> Prop :=
| Rcase_boxed_nil: forall v, repr_case_boxed v [] [ BI_unreachable ]
| Rcase_boxed_cons: forall v ord instrs brs instrs_more,
    repr_case_boxed v brs instrs_more ->
    repr_case_boxed v ((ord, instrs) :: brs)
      [ BI_local_get v
      ; BI_load T_i32 None 2%N 0%N
      ; BI_const_num (nat_to_value (N.to_nat ord))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (BT_valtype None)
          instrs
          instrs_more ].

Inductive repr_case_unboxed: localidx -> list (N * list basic_instruction) -> list basic_instruction -> Prop :=
| Rcase_unboxed_nil: forall v, repr_case_unboxed v [] [ BI_unreachable ]
| Rcase_unboxed_cons: forall v ord instrs brs instrs_more,
    repr_case_unboxed v brs instrs_more ->
    repr_case_unboxed v ((ord, instrs) :: brs)
      [ BI_local_get v
      ; BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)%N))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (BT_valtype None)
          instrs
          instrs_more
      ].


Inductive repr_primitive_unary_operation : primop -> localidx -> list basic_instruction -> Prop :=
| Rprim_head0: forall x,
    repr_primitive_unary_operation PrimInt63head0 x (head0_instrs global_mem_ptr x)

| Rprim_tail0: forall x,
    repr_primitive_unary_operation PrimInt63tail0 x (tail0_instrs global_mem_ptr x).

Inductive repr_primitive_binary_operation : primop -> localidx -> localidx -> list basic_instruction -> Prop :=
| Rprim_add : forall x y,
    repr_primitive_binary_operation PrimInt63add x y
      (apply_binop_and_store_i64 global_mem_ptr BOI_add x y true)

| Rprim_sub : forall x y,
    repr_primitive_binary_operation PrimInt63sub x y
      (apply_binop_and_store_i64 global_mem_ptr BOI_sub x y true)

| Rprim_mul : forall x y,
    repr_primitive_binary_operation PrimInt63mul x y
      (apply_binop_and_store_i64 global_mem_ptr BOI_mul x y true)

| Rprim_div : forall x y,
    repr_primitive_binary_operation PrimInt63div x y (div_instrs global_mem_ptr x y)

| Rprim_mod : forall x y,
    repr_primitive_binary_operation PrimInt63mod x y (mod_instrs global_mem_ptr x y)

| Rprim_land : forall x y,
    repr_primitive_binary_operation PrimInt63land x y
      (apply_binop_and_store_i64 global_mem_ptr BOI_and x y false)

| Rprim_lor : forall x y,
    repr_primitive_binary_operation PrimInt63lor x y
      (apply_binop_and_store_i64 global_mem_ptr BOI_or x y false)

| Rprim_lxor : forall x y,
    repr_primitive_binary_operation PrimInt63lxor x y
      (apply_binop_and_store_i64 global_mem_ptr BOI_xor x y false)

| Rprim_lsl : forall x y,
    repr_primitive_binary_operation PrimInt63lsl x y (shift_instrs global_mem_ptr x y BOI_shl true)

| Rprim_lsr : forall x y,
    repr_primitive_binary_operation PrimInt63lsr x y (shift_instrs global_mem_ptr x y (BOI_shr SX_U) false)

| Rprim_eqb : forall x y,
    repr_primitive_binary_operation PrimInt63eqb x y
      (make_boolean_valued_comparison x y ROI_eq)

| Rprim_ltb : forall x y,
    repr_primitive_binary_operation PrimInt63ltb x y
      (make_boolean_valued_comparison x y (ROI_lt SX_U))

| Rprim_leb : forall x y,
    repr_primitive_binary_operation PrimInt63leb x y
      (make_boolean_valued_comparison x y (ROI_le SX_U))

| Rprim_compare : forall x y,
    repr_primitive_binary_operation PrimInt63compare x y (compare_instrs x y)

| Rprim_addc : forall x y,
    repr_primitive_binary_operation PrimInt63addc x y
      (apply_exact_add_operation global_mem_ptr glob_tmp1 x y false)

| Rprim_addcarryc : forall x y,
    repr_primitive_binary_operation PrimInt63addcarryc x y
      (apply_exact_add_operation global_mem_ptr glob_tmp1 x y true)

| Rprim_subc : forall x y,
    repr_primitive_binary_operation PrimInt63subc x y
      (apply_exact_sub_operation global_mem_ptr glob_tmp1 x y false)

| Rprim_subcarryc : forall x y,
    repr_primitive_binary_operation PrimInt63subcarryc x y
      (apply_exact_sub_operation global_mem_ptr glob_tmp1 x y true)

| Rprim_mulc : forall x y,
    repr_primitive_binary_operation PrimInt63mulc x y
      (mulc_instrs global_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 x y)

| Rprim_diveucl : forall x y,
    repr_primitive_binary_operation PrimInt63diveucl x y
      (diveucl_instrs global_mem_ptr glob_tmp1 glob_tmp2 x y).

Inductive repr_primitive_ternary_operation : primop -> localidx -> localidx -> localidx -> list basic_instruction -> Prop :=
| Rprim_diveucl_21 : forall xh xl y,
    repr_primitive_ternary_operation PrimInt63diveucl_21 xh xl y
      (diveucl_21_instrs global_mem_ptr glob_tmp1 glob_tmp2 glob_tmp3 glob_tmp4 xh xl y)

| Rprim_addmuldiv : forall p x y,
    repr_primitive_ternary_operation PrimInt63addmuldiv p x y
      (addmuldiv_instrs global_mem_ptr  p x y).

Inductive repr_primitive_operation {lenv} : primop -> list positive  -> list basic_instruction -> Prop :=
| Rprim_unop :
  forall op x x' instr,
    repr_var (lenv:=lenv) x x' ->
    repr_primitive_unary_operation op x' instr ->
    repr_primitive_operation op [ x ] instr

| Rprim_binop :
  forall op x x' y y' instr,
    repr_var (lenv:=lenv) x x' ->
    repr_var (lenv:=lenv) y y' ->
    repr_primitive_binary_operation op x' y' instr ->
    repr_primitive_operation op [ x ; y ] instr

| Rprim_ternop :
  forall op x x' y y' z z' instr,
    repr_var (lenv:=lenv) x x' ->
    repr_var (lenv:=lenv) y y' ->
    repr_var (lenv:=lenv) z z' ->
    repr_primitive_ternary_operation op x' y' z' instr ->
    repr_primitive_operation op [ x ; y ; z ] instr.

(* CODEGEN RELATION: relatates LambdaANF expression and result of translate_body *)
Inductive repr_expr_LambdaANF_Wasm {lenv} : LambdaANF.cps.exp -> list basic_instruction -> Prop :=
| R_halt_e: forall x x',
    repr_var (lenv:=lenv) x x' ->
    repr_expr_LambdaANF_Wasm (Ehalt x)
      [ BI_local_get x'
      ; BI_global_set result_var
      ; BI_return
      ]
| Rproj_e: forall x x' t n y y' e e',
    repr_expr_LambdaANF_Wasm e e' ->
    repr_var (lenv:=lenv) x x' ->
    repr_var (lenv:=lenv) y y' ->
    repr_expr_LambdaANF_Wasm (Eproj x t n y e)
      ([ BI_local_get y'
       ; BI_const_num (nat_to_value (((N.to_nat n) + 1) * 4))
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_load T_i32 None (N_of_nat 2) (N_of_nat 0)
       ; BI_local_set x'
       ] ++ e')

| Rconstr_e: forall x x' t vs e instrs e',
    repr_expr_LambdaANF_Wasm e e' ->
    repr_var (lenv:=lenv) x x' ->
    repr_asgn_constr_Wasm (lenv:=lenv) x' t vs e' instrs ->
    repr_expr_LambdaANF_Wasm (Econstr x t vs e) instrs

| Rcase_e : forall y y' cl brs1 brs2 e1' e2',
    repr_var (lenv:=lenv) y y' ->
    repr_branches y' cl brs1 brs2 ->
    repr_case_boxed y' brs1 e1' ->
    repr_case_unboxed y' brs2 e2' ->
    repr_expr_LambdaANF_Wasm (Ecase y cl)
      [ BI_local_get y'
      ; BI_const_num (nat_to_value 1)
      ; BI_binop T_i32 (Binop_i BOI_and)
      ; BI_testop T_i32 TO_eqz
      ; BI_if (BT_valtype None)
          e1'
          e2'
      ]

| R_app_e : forall v instr t args args',
    (* args are provided properly *)
    repr_fun_args_Wasm (lenv:=lenv) args args' ->
    (* instr reduces to const containing funidx to call *)
    repr_read_var_or_funvar (lenv:=lenv) v instr ->
    repr_expr_LambdaANF_Wasm (Eapp v t args) (args' ++
                                                [instr] ++
                                                [BI_return_call_indirect 0%N (N.of_nat (length args))])

| R_letapp_e : forall x x' v instr t args args' e e',
    (* translated assigned var *)
    repr_var (lenv:=lenv) x x' ->
    (* following expression *)
    repr_expr_LambdaANF_Wasm e e' ->
    (* args are provided properly *)
    repr_fun_args_Wasm (lenv:=lenv) args args' ->
    (* instr reduces to const containing funidx to call *)
    repr_read_var_or_funvar (lenv:=lenv) v instr ->
    repr_expr_LambdaANF_Wasm (Eletapp x v t args e)
      (args' ++
       [ instr
       ; BI_call_indirect 0%N (N.of_nat (length args))
       ; BI_global_get result_out_of_mem
       ; BI_if (BT_valtype None)
           (* grow mem failed *)
           [ BI_return ]
           []
       ; BI_global_get result_var
       ; BI_local_set x'
       ] ++ e')

| R_prim_val : forall x x' p v e e',
    repr_var (lenv:=lenv) x x' ->
    repr_expr_LambdaANF_Wasm e e' ->
    translate_primitive_value p = Ret v ->
    repr_expr_LambdaANF_Wasm (Eprim_val x p e)
      ([ BI_const_num (N_to_value page_size)
       ; BI_call grow_mem_function_idx
       ; BI_global_get result_out_of_mem
       ; BI_const_num (nat_to_value 1)
       ; BI_relop T_i32 (Relop_i ROI_eq)
       ; BI_if (BT_valtype None)
           (* grow mem failed *)
           [ BI_return ]
           []
       ; BI_global_get global_mem_ptr
       ; BI_const_num (VAL_int64 v)
       ; BI_store T_i64 None 2%N 0%N
       ; BI_global_get global_mem_ptr
       ; BI_local_set x'
       ; BI_global_get global_mem_ptr
       ; BI_const_num (nat_to_value 8)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_global_set global_mem_ptr
        ] ++ e')

| R_prim : forall x x' p op_name s b n op ys e e' prim_instrs,
    repr_var (lenv:=lenv) x x' ->
    repr_expr_LambdaANF_Wasm e e' ->
    M.get p penv = Some (op_name, s, b, n) ->
    KernameMap.find op_name primop_map = Some op ->
    repr_primitive_operation (lenv:=lenv) op ys prim_instrs ->
    repr_expr_LambdaANF_Wasm (Eprim x p ys e)
      (([ BI_const_num (N_to_value page_size)
        ; BI_call grow_mem_function_idx
        ; BI_global_get result_out_of_mem
        ; BI_const_num (nat_to_value 1)
        ; BI_relop T_i32 (Relop_i ROI_eq)
        ; BI_if (BT_valtype None)
            (* grow mem failed *)
            [ BI_return ]
            []
         ] ++ prim_instrs ++ [ BI_local_set x' ]) ++  e')

with repr_branches {lenv}: localidx -> list (ctor_tag * exp) -> list (N * list basic_instruction) -> list (N * list basic_instruction) -> Prop :=
| Rbranch_nil : forall x, repr_branches x [] [ ] [ ]

| Rbranch_cons_boxed : forall x cl t e ord n e' brs1 brs2,
    repr_branches x cl brs1 brs2 ->
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret n ->
    0 < n ->
    repr_expr_LambdaANF_Wasm e e' ->
    repr_branches x ((t, e) :: cl) ((ord,e') :: brs1) brs2

| Rbranch_cons_unboxed : forall x cl t e ord n e' brs1 brs2,
    repr_branches x cl brs1 brs2 ->
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret n ->
    n = 0 ->
    repr_expr_LambdaANF_Wasm e e' ->
    repr_branches x ((t, e) :: cl) brs1 ((ord,e') :: brs2).

Scheme repr_expr_LambdaANF_Wasm_mut := Induction for repr_expr_LambdaANF_Wasm Sort Prop
    with repr_branches_mut :=
      Induction for repr_branches Sort Prop.


Lemma pass_function_args_correct {lenv} : forall l instr,
  pass_function_args nenv lenv fenv l = Ret instr ->
  @repr_fun_args_Wasm lenv l instr.
Proof.
  induction l; intros; first by inv H; constructor.
  cbn in H. destruct (instr_local_var_read nenv lenv fenv a) eqn:Hvar. inv H.
  destruct (pass_function_args nenv lenv fenv l) eqn:prep. inv H. inv H.
  unfold instr_local_var_read in Hvar.
  destruct (is_function_var fenv a) eqn:Hfname.
  - destruct (translate_var nenv fenv a _) eqn:fun_var; inv Hvar.
          constructor. econstructor. eassumption.
      apply IHl; auto.
  - destruct (translate_var nenv lenv a _) eqn:var_var; inv Hvar.
          constructor. econstructor. eassumption. apply IHl; auto.
Qed.

Ltac separate_instr :=
  cbn;
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end.

Lemma set_nth_constr_arg_correct {lenv} : forall  l instr n,
  set_constructor_args nenv lenv fenv l n = Ret instr ->
  Forall_statements_in_seq' (@set_nth_constr_arg lenv) l instr n.
Proof.
  induction l; intros.
  - inv H. econstructor; auto.
  - cbn in H. destruct (instr_local_var_read nenv lenv fenv a) eqn:Hvar. inv H.
  destruct (set_constructor_args nenv lenv fenv l (S n)) eqn:Harg. inv H. inv H.
  separate_instr. do 8! rewrite catA. constructor. auto.
  replace ((nat_to_value (S (n + S (n + S (n + S (n + 0))))))) with
          ((nat_to_value ((1 + n) * 4))) by (f_equal; lia).
  constructor.
  unfold instr_local_var_read in Hvar.
  destruct (is_function_var fenv a) eqn:Hfn.
  - destruct (translate_var nenv fenv a _) eqn:Hvar'. inv Hvar. inv Hvar.
    constructor. now econstructor.
  - destruct (translate_var nenv lenv a _) eqn:Hloc. inv Hvar. inv Hvar.
    constructor. now econstructor.
Qed.

Theorem translate_body_correct {lenv} :
    forall e instructions,
      correct_cenv_of_exp cenv e ->
    translate_body nenv cenv lenv fenv penv e = Ret instructions ->
    @repr_expr_LambdaANF_Wasm lenv e instructions.
Proof.
  induction e using exp_ind'; intros instr Hcenv; intros.
  - (* Econstr *)
    simpl in H.
    destruct (translate_body nenv cenv lenv fenv penv e) eqn:H_eqTranslate; inv H.
    destruct (translate_var nenv lenv v _) eqn:H_translate_var. inv H1.
    destruct l as [|v0 l'].

    + (* Nullary constructor *)
      destruct (get_ctor_ord cenv t) eqn:Hord; inv H1.
      eapply Rconstr_e with (e':=l0); eauto.
      apply IHe; auto.
      assert (subterm_e e (Econstr v t [] e) ). { constructor; constructor. }
      eapply Forall_constructors_subterm. eassumption. assumption.
      econstructor; eauto.
      eapply Rconstr_asgn_unboxed; eauto.
      apply Forall_constructors_in_constr in Hcenv.
      destruct (cenv ! t) eqn:Hc; auto. destruct c. inv Hcenv.
      unfold get_ctor_arity. now rewrite Hc.
    + (* Non-nullary constructor *)
      remember (v0 :: l') as l.
      destruct (store_constructor nenv cenv lenv fenv t l) eqn:Hstore_constr; inv H1.
      unfold store_constructor in Hstore_constr.
      destruct (get_ctor_ord cenv t) eqn:Hord; first by inv Hstore_constr.
      destruct (set_constructor_args nenv lenv fenv (v0 :: l') 0) eqn:Hconstrargs; first by inv Hstore_constr.
      inversion Hstore_constr.
      repeat rewrite <- app_assoc.
      eapply Rconstr_e with (e' := l0); eauto.
      apply IHe.
      assert (subterm_e e (Econstr v t (v0 :: l') e) ). { constructor; constructor. }
      eapply Forall_constructors_subterm. eassumption. assumption. reflexivity.
      econstructor. eassumption.
      apply Forall_constructors_in_constr in Hcenv; auto.
      destruct (cenv ! t) eqn:Hc. 2:auto. destruct c. inv Hcenv.
      separate_instr. do 7! rewrite catA. (* first 8 instr belong to sgrow *)
      apply Rconstr_asgn_boxed with (arity:=S (length l')); eauto.
      unfold get_ctor_arity. rewrite Hc. f_equal. cbn. lia. lia.
      apply set_nth_constr_arg_correct.
      by assumption.
  - (* Ecase nil *)
    simpl in H. destruct (translate_var nenv lenv v _) eqn:Hvar; inv H.
    econstructor; try by constructor. now econstructor.
  - (* Ecase const *)
    simpl in H.
    destruct (translate_var nenv lenv v _) eqn:Hvar. inv H.
    destruct (translate_body nenv cenv lenv fenv penv e) eqn:He. inv H.
    destruct (translate_body nenv cenv lenv fenv penv (Ecase v l)) eqn:Hl.
    simpl in Hl. destruct (_ l) eqn:Hm. inv H. rewrite Hvar in Hl. destruct p. inv Hl.
    assert (correct_cenv_of_exp cenv (Ecase v l)). {
      intros ?????. eapply Hcenv. apply rt_then_t_or_eq in H0. inv H0. inv H1.
      apply t_then_rt. apply subterm_case. by eauto.
    }
    specialize (IHe0 l1 H0). clear H0. specialize (IHe0 Logic.eq_refl).
    simpl in Hl.
    destruct (_ l) eqn:Hm. inv H. rewrite Hvar in Hl. inv Hl. destruct p.
    assert (correct_cenv_of_exp cenv e). {
      intro; intros. eapply Hcenv. eapply rt_trans. eauto. constructor.
      econstructor. now left.
    }
    specialize (IHe l0 H0). assert (Ret l0 = Ret l0) by reflexivity. specialize (IHe H2). clear H0  H2.
    inv IHe0. inv H1.
    unfold create_case_nested_if_chain in H5.
    unfold create_case_nested_if_chain in H7.
    destruct (get_ctor_ord cenv c) eqn:Hord. inv H.
    rename n into ord.
    destruct (get_ctor_arity cenv c) eqn:Har. inv H.
    destruct n eqn:Hn.
    + (* Unboxed branch *)
      inv H. destruct l3. econstructor; eauto. econstructor; eauto. econstructor; eauto. cbn in H7.
      by repeat (econstructor; eauto).
    + (* Boxed branch *)
        inv H. by destruct l2; econstructor; eauto; econstructor; eauto; try lia.
  - (* Eproj *)
    simpl in H.
    destruct (translate_body nenv cenv lenv fenv penv e) eqn:He. inv H.
    destruct (translate_var nenv lenv v0 _) eqn:Hy. inv H.
    destruct (translate_var nenv lenv v _) eqn:Hx. inv H.
    injection H => instr'. subst. clear H. constructor. apply IHe; auto.
    unfold correct_cenv_of_exp in Hcenv.
    eapply Forall_constructors_subterm. eassumption.
    unfold subterm_e. constructor. constructor.
    econstructor; eauto. by econstructor; eauto.
  - (* Eletapp *)
    simpl in H.
    destruct (translate_var nenv lenv x _) eqn:Hvar. inv H.
    destruct (translate_body nenv cenv lenv fenv penv e) eqn:H_eqTranslate. inv H.
    unfold translate_call in H.
    destruct (pass_function_args nenv lenv fenv ys) eqn:Hargs. inv H.
    destruct (instr_local_var_read nenv lenv fenv f) eqn:Hloc. inv H. inv H.
    rewrite <- app_assoc. constructor. econstructor. eassumption.
    apply IHe; auto.
    eapply Forall_constructors_subterm; eauto. constructor. constructor.
    apply pass_function_args_correct. assumption.
    unfold instr_local_var_read in Hloc.
    destruct (is_function_var fenv f) eqn:Hfname.
    + destruct (translate_var nenv fenv f _) eqn:fun_var; inv Hloc.
      constructor. econstructor. eassumption.
    + destruct (translate_var  nenv lenv f _) eqn:var_var; inv Hloc.
      constructor. now econstructor.
  - (* Efun *) by inv H.
  - (* Eapp *)
    simpl in H. unfold translate_call in H.
    destruct (pass_function_args nenv lenv fenv l) eqn:Hargs. inv H.
    destruct (instr_local_var_read nenv lenv fenv v) eqn:Hloc. inv H. inv H. constructor.
    apply pass_function_args_correct. assumption.
    unfold instr_local_var_read in Hloc.
    destruct (is_function_var fenv v) eqn:Hfname.
    + destruct (translate_var nenv fenv v _) eqn:fun_var; inv Hloc.
      constructor. now econstructor.
    + destruct (translate_var  nenv lenv v _) eqn:var_var; inv Hloc.
      constructor. now econstructor.
  - (* Eprim_val *)
    inv H.
    destruct (translate_body nenv cenv lenv fenv penv e) eqn:H_eqTranslate. inv H1.
    destruct (translate_var nenv lenv v _) eqn:Hvar. inv H1.
    destruct (translate_primitive_value p) eqn:Hprim. inv H1.
    inversion H1.
    separate_instr. do 7! rewrite catA. (* first 8 instr belong to sgrow *)
    apply R_prim_val.
    + econstructor; eauto.
    + assert (Hcenv': correct_cenv_of_exp cenv e). {
        intro; intros. eapply Hcenv. eapply rt_trans. eauto. constructor.
        now econstructor.
      }
      now eapply IHe.
    + now assumption.
  - (* Eprim *)
    inv H.
    destruct (M.get p penv) eqn:Hp. 2: inv H1.
    destruct (translate_body nenv cenv lenv fenv penv e) eqn:H_eqTranslate. inv H1.
    destruct (translate_var nenv lenv v _) eqn:Hvar. inv H1.
    destruct (translate_primitive_operation _) eqn:Hprimop. inv H1.
    unfold translate_primitive_operation in Hprimop.
    do 3 destruct p0.
    destruct (KernameMap.find _) eqn:Hker. 2: inv Hprimop.
    inv H1.
    eapply R_prim; eauto.
    econstructor; eauto.
    assert (Hcenv': correct_cenv_of_exp cenv e). {
      intro; intros. eapply Hcenv. eapply rt_trans. eauto. constructor.
      now econstructor.
    }
    now eapply IHe.
    simpl in Hprimop.
    destruct l. inv Hprimop.
    destruct l.
    { (* Unary operations *)
      destruct (translate_var nenv lenv v0 _) eqn:Hx. inv Hprimop.
      unfold translate_primitive_unary_op in Hprimop.
      destruct p0; inv Hprimop; econstructor; econstructor; eauto.
    }
    destruct l.
    { (* Binary operations *)
      destruct (translate_var nenv lenv v0 _) eqn:Hx. inv Hprimop.
      destruct (translate_var nenv lenv v1 _) eqn:Hy. inv Hprimop.
      unfold translate_primitive_binary_op in Hprimop.
      destruct p0; try inv Hprimop; econstructor; econstructor; eauto.
    }
    destruct l. 2: inv Hprimop.
    (* Ternary ops *)
    destruct (translate_var nenv lenv v0 _) eqn:Hx. inv Hprimop.
    destruct (translate_var nenv lenv v1 _) eqn:Hy. inv Hprimop.
    destruct (translate_var nenv lenv v2 _) eqn:Hz. inv Hprimop.
    unfold translate_primitive_ternary_op in Hprimop.
    destruct p0; try inv Hprimop; econstructor; econstructor; eauto.
  - (* Ehalt *)
    simpl in H. destruct (translate_var nenv lenv v _) eqn:Hvar. inv H.
    injection H => instr'. subst. constructor. now econstructor.
Qed.

End CODEGEN.


Section MAIN.

Variable cenv : LambdaANF.cps.ctor_env.
Variable funenv : LambdaANF.cps.fun_env.
Variable fenv : CodegenWasm.LambdaANF_to_Wasm.fname_env.
Variable nenv : LambdaANF.cps_show.name_env.
Variable penv : LambdaANF.toplevel.prim_env.
Let repr_expr_LambdaANF_Wasm := @repr_expr_LambdaANF_Wasm cenv fenv nenv.
Let repr_funvar := @repr_funvar fenv nenv.

Context `{ho : host}.

(* VALUE RELATION *)
(* immediate is pointer to linear memory or function id *)
Inductive repr_val_LambdaANF_Wasm : LambdaANF.cps.val -> store_record -> moduleinst -> wasm_value -> Prop :=
| Rconstr_unboxed_v : forall v (t : ctor_tag) (sr : store_record) inst ord,
    get_ctor_ord cenv t = Ret ord ->
    (ord * 2 + 1 = v)%N ->
    (-1 < Z.of_N v < Wasm_int.Int32.modulus)%Z ->
    get_ctor_arity cenv t = Ret 0 ->
    repr_val_LambdaANF_Wasm (Vconstr t []) sr inst (Val_unboxed v)

| Rconstr_boxed_v : forall v t vs (sr : store_record) inst gmp m (addr : u32) arity ord,
    (* simple memory model: gmp is increased whenever new mem is needed,
       gmp only increases *)
    sglob_val sr inst global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
    (* constr arity > 0 *)
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret arity ->
    arity > 0 ->
    (* addr in bounds of linear memory (later INV: gmp + 4 < length of memory) *)
    (addr + 4 <= gmp)%N ->
    (exists n, addr = 2 * n)%N ->
    (* store_record contains memory *)
    smem sr inst = Some m ->
    (* constructor tag is set, see LambdaANF_to_W, constr alloc structure*)
    v = (nat_to_i32 (N.to_nat ord)) ->
    load_i32 m addr = Some (VAL_int32 v) ->
    (* arguments are set properly *)
    repr_val_constr_args_LambdaANF_Wasm vs sr inst (4 + addr)%N ->
    repr_val_LambdaANF_Wasm (Vconstr t vs) sr inst (Val_ptr addr)

| Rfunction_v : forall fds f func sr inst tag xs e e' idx,
      repr_funvar f idx ->
      find_def f fds = Some (tag, xs, e) ->
      func = {| modfunc_type := N.of_nat (length xs)
              ; modfunc_locals := repeat (T_num T_i32) (length (collect_local_variables e))
              ; modfunc_body := e'
              |} ->
      (* find runtime representation of function *)
      lookup_N sr.(s_funcs) idx = Some (FC_func_native (Tf (repeat (T_num T_i32) (length xs)) []) inst func) ->
      repr_expr_LambdaANF_Wasm penv (create_local_variable_mapping (xs ++ collect_local_variables e)) e e' ->
      repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f) sr inst (Val_funidx idx)

|  Rprim_v : forall n sr inst gmp m addr,
    sglob_val sr inst global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
    (addr+8 <= gmp)%N ->
    (exists n, addr = 2 * n)%N ->
    smem sr inst = Some m ->
    load_i64 m addr = Some (VAL_int64 (Z_to_i64 (Uint63.to_Z n))) ->
    repr_val_LambdaANF_Wasm (Vprim (primInt n)) sr inst (Val_ptr addr)

with repr_val_constr_args_LambdaANF_Wasm : list LambdaANF.cps.val -> store_record -> moduleinst -> u32 -> Prop :=
     | Rnil_l: forall sr fr addr,
        repr_val_constr_args_LambdaANF_Wasm nil sr fr addr

     | Rcons_l: forall v wal vs sr inst m addr gmp,
        (* store_record contains memory *)
        smem sr inst = Some m ->

        sglob_val sr inst global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
        (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
        (addr + 4 <= gmp)%N ->

        (* constr arg is ptr related to value v *)
        load_i32 m addr = Some (VAL_int32 (wasm_value_to_i32 wal)) ->
        repr_val_LambdaANF_Wasm v sr inst wal ->

        (* following constr args are also related *)
        repr_val_constr_args_LambdaANF_Wasm vs sr inst (4 + addr)%N ->
        repr_val_constr_args_LambdaANF_Wasm (v::vs) sr inst addr.

Scheme repr_val_LambdaANF_Wasm_mut := Induction for repr_val_LambdaANF_Wasm Sort Prop
  with repr_val_constr_args_LambdaANF_Wasm_mut :=
    Induction for repr_val_constr_args_LambdaANF_Wasm Sort Prop.

Lemma val_relation_func_depends_on_funcs : forall val s s' inst i,
  s_funcs s = s_funcs s' ->
  repr_val_LambdaANF_Wasm val s  inst (Val_funidx i) ->
  repr_val_LambdaANF_Wasm val s' inst (Val_funidx i).
Proof.
  intros ? ? ? ? ? Hfuncs Hval.
  inv Hval. now econstructor; eauto.
Qed.


(* TODO move somewhere else *)
Ltac simpl_eq :=
  repeat lazymatch goal with
  | H: nat_to_i32 _ = nat_to_i32 _ |- _ =>
        injection H as H
  | H: N_to_i32 _ = N_to_i32 _ |- _ =>
        injection H as H
  | H: _ = Wasm_int.Int32.Z_mod_modulus _ |- _ =>
         rewrite Wasm_int.Int32.Z_mod_modulus_id in H; last lia
  | H: Wasm_int.Int32.Z_mod_modulus _ = _ |- _ =>
          rewrite Wasm_int.Int32.Z_mod_modulus_id in H; last lia
  | H: Z.of_nat _ = Z.of_nat _ |- _ =>
         apply Nat2Z.inj in H
  | H: Z.of_N _ = Z.of_N _ |- _ =>
         apply N2Z.inj in H
  end.

Ltac solve_eq_global x y :=
  assert (x = y); first
    (try assert (N_to_i32 x = N_to_i32 y) by congruence; simpl_eq; done); subst y.

(* TODO add case when global was updated etc. *)
Ltac solve_eq_mem m1 m2 :=
  assert (m1 = m2) by congruence; subst m2.

(* proves and substitutes equality on given vars, the first one is kept *)
Ltac solve_eq x y :=
  lazymatch goal with
  (* equality on global mems *)
  | H: smem ?s _ = Some x |- _ => solve_eq_mem x y
  (* equality on globals *)
  | H: _ |- _ => solve_eq_global x y
  end.

Lemma val_relation_depends_on_mem_smaller_than_gmp_and_funcs :
  forall v sr sr' m m' inst gmp gmp' value,
    sr.(s_funcs) = sr'.(s_funcs) ->
    smem sr inst = Some m ->
    smem sr' inst = Some m' ->
    (* memories agree on values < gmp *)
    sglob_val sr inst global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    (Z.of_N gmp + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
    sglob_val sr' inst global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp'))) ->
    (Z.of_N gmp' + 8 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
    (gmp' >= gmp)%N ->
    (forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m' a) ->
    (forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m' a) ->

    repr_val_LambdaANF_Wasm v sr inst value ->
    repr_val_LambdaANF_Wasm v sr' inst value.
Proof.
  intros. inv H9.
  (* Nullary constructor value *)
  { now econstructor. }
  (* Non-nullary constructor value *)
  {
  have indPrinciple := repr_val_constr_args_LambdaANF_Wasm_mut
  (fun (v : cps.val) (s : store_record) (inst : moduleinst) (w : wasm_value)
       (H: repr_val_LambdaANF_Wasm v s inst w) =>
       (forall a s' m m',
          s_funcs s = s_funcs s' ->
          smem s inst = Some m ->
          smem s' inst = Some m' ->
          (* memories agree on values < gmp *)
          sglob_val s inst global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
          (Z.of_N gmp + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
          sglob_val s' inst global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp'))) ->
          (Z.of_N gmp' + 8 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
          (gmp' >= gmp)%N ->
          (forall a, (a + 4<= gmp)%N -> load_i32 m a = load_i32 m' a) ->
          (forall a, (a + 8<= gmp)%N -> load_i64 m a = load_i64 m' a) ->
              repr_val_LambdaANF_Wasm v s' inst w)
    )
  (fun (l : seq cps.val) (s : store_record) (inst : moduleinst) (addr : u32)
       (H: repr_val_constr_args_LambdaANF_Wasm l s inst addr) =>
       (forall a s' m m',
          s_funcs s = s_funcs s' ->
          smem s inst = Some m ->
          smem s' inst = Some m' ->
          (* memories agree on values < gmp *)
          sglob_val s inst global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
          (Z.of_N gmp + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
          sglob_val s' inst global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp'))) ->
          (Z.of_N gmp' + 8 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
          (gmp' >= gmp)%N ->
          (forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m' a) ->
          (forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m' a) ->
             repr_val_constr_args_LambdaANF_Wasm l s' inst addr)
  ). have H20' := H20.
    eapply indPrinciple in H20; intros; clear indPrinciple; try eassumption; try lia.
    { solve_eq gmp0 gmp.
      solve_eq m m0.
      econstructor; try eassumption. lia. lia. reflexivity.
      rewrite <- H7. assumption. lia. }
    { now econstructor. }
    { solve_eq gmp gmp0. solve_eq gmp gmp1.
      solve_eq m m0. solve_eq m1 m2.
      econstructor; eauto. lia. rewrite <- H28; auto; try lia. }
    { econstructor; eauto. congruence. }
    { econstructor; eauto.
      solve_eq gmp gmp1. lia.
      solve_eq m1 m2. rewrite <- H28. assumption. solve_eq gmp gmp1. lia. }
    { econstructor. }
    { solve_eq gmp gmp0. solve_eq gmp gmp1.
      econstructor; eauto; try lia.
      rewrite <- H29. assert (m1 = m2) by congruence. subst m2. eassumption.
      lia. eapply H9; eauto; lia. }
    { solve_eq m m0. lia. }
    { solve_eq m m0. apply H7. lia. }
    { solve_eq m m0. apply H8. lia. }
  }
  (* function *)
  { econstructor; eauto. by rewrite <- H. }
  (* primitive value *)
  { econstructor; eauto. lia. solve_eq gmp gmp0. lia. solve_eq m m0.
    rewrite <- H8. assumption. solve_eq gmp gmp0. lia. }
Qed.


(* RESULT RELATION *)
Definition result_val_LambdaANF_Wasm (val : LambdaANF.cps.val) (sr : store_record) (inst : moduleinst) : Prop :=
     (exists res_i32 wasmval,
       (* global var *result_var* contains correct return value *)
       sglob_val sr inst result_var = Some (VAL_num (VAL_int32 res_i32))
         /\ wasm_value_to_i32 wasmval = res_i32
         /\ repr_val_LambdaANF_Wasm val sr inst wasmval
         /\ (sglob_val sr inst result_out_of_mem = Some (VAL_num (nat_to_value 0))))
  \/ (sglob_val sr inst result_out_of_mem = Some (VAL_num (nat_to_value 1))).


(* ENVIRONMENT RELATION (also named memory relation in C-backend) *)

Definition stored_in_locals {lenv} (x : cps.var) (v : wasm_value) (f : frame ) :=
  exists i,
  (forall err, translate_var nenv lenv x err = Ret i) /\
  lookup_N f.(f_locs) i = Some (VAL_num (VAL_int32 (wasm_value_to_i32 v))).

Definition rel_env_LambdaANF_Wasm {lenv} (e : exp) (rho : LambdaANF.eval.env)
                    (sr : store_record) (fr : frame) (fds : fundefs) :=
        (forall x f v fds' rho',
            rho ! x = Some v ->
            (* f is var in fds, v is either a Vfun or Vconstr value *)
            subval_or_eq (Vfun rho' fds' f) v ->
            (* fds only on toplevel, thus the two equalities *)
            rho' = M.empty _ /\ fds' = fds /\ name_in_fundefs fds f)
        /\
        (forall f errMsg,
            name_in_fundefs fds f ->
            (* i is index of function f *)
            exists i, translate_var nenv fenv f errMsg = Ret i /\
            (* function def is related to function index *)
            repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f) sr (f_inst fr) (Val_funidx i))
        /\
        (* free variables are related to local var containing a
           memory pointer or a function index *)
        (forall x,
            occurs_free e x ->
            (* not a function var *)
            find_def x fds = None ->
            (exists v w,
               rho ! x = Some v /\
               stored_in_locals (lenv:=lenv) x w fr /\
               repr_val_LambdaANF_Wasm v sr (f_inst fr) w)).

(* INVARIANT *)

Notation i32_glob gidx := (In gidx [ result_var ; result_out_of_mem ; global_mem_ptr ; constr_alloc_ptr ]).
Notation i64_glob gidx := (In gidx [ glob_tmp1 ; glob_tmp2 ; glob_tmp3 ; glob_tmp4 ]).

Definition globals_all_mut32 s f := forall gidx g g0,
    i32_glob gidx ->
    lookup_N (inst_globals (f_inst f)) gidx = Some g ->
    lookup_N (s_globals s) g = Some g0 ->
    exists val,
      g0 = {| g_type := {| tg_mut := MUT_var; tg_t := T_num T_i32 |}
           ; g_val := VAL_num (VAL_int32 val)
           |}.
    
Definition globals_all_mut64 s f := forall gidx g g0,
    i64_glob gidx ->
    lookup_N (inst_globals (f_inst f)) gidx = Some g ->
    lookup_N (s_globals s) g = Some g0 ->
    exists val,
      g0 = {| g_type := {| tg_mut := MUT_var; tg_t := T_num T_i64 |}
             ; g_val := VAL_num (VAL_int64 val)
             |}.

Definition globals_all_mut s f :=
    globals_all_mut32 s f /\ globals_all_mut64 s f.

Definition global_var_w var (s : store_record) (f : frame) := forall val,
  exists s',
    supdate_glob s (f_inst f) var (VAL_num val) = Some s'.

Definition global_var_r var (s : store_record) (f : frame) :=
   exists v, sglob_val s (f_inst f) var = Some (VAL_num v).

Definition INV_result_var_writable := global_var_w result_var.
Definition INV_result_var_out_of_mem_writable := global_var_w result_out_of_mem.
Definition INV_global_mem_ptr_writable := global_var_w global_mem_ptr.
Definition INV_constr_alloc_ptr_writable := global_var_w constr_alloc_ptr.
Definition INV_globals_all_mut := globals_all_mut.
Definition INV_i64_glob_tmps_writable (s : store_record) (f : frame) := forall gidx, i64_glob gidx -> global_var_w gidx s f.
(* indicates all good *)
Definition INV_result_var_out_of_mem_is_zero s f :=
  sglob_val s (f_inst f) result_out_of_mem = Some (VAL_num (VAL_int32 (nat_to_i32 0))).

Definition INV_linear_memory sr fr :=
  inst_mems (f_inst fr) = [0%N] /\
  exists m, smem sr (f_inst fr) = Some m
   /\ exists size, mem_size m = size
   /\ mem_max_opt m = Some max_mem_pages
   /\ (size <= max_mem_pages)%N.

Definition INV_global_mem_ptr_in_linear_memory s f := forall gmp_v m,
  smem s (f_inst f) = Some m ->
  sglob_val s (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
  (-1 < Z.of_N gmp_v < Wasm_int.Int32.modulus)%Z ->
  (* enough space to store an i32 *)
  (gmp_v + 8 <= mem_length m)%N.

Definition INV_constr_alloc_ptr_in_linear_memory s f := forall addr t m,
  sglob_val s (f_inst f) constr_alloc_ptr = Some (VAL_num (VAL_int32 addr)) ->
  exists m', store m (Wasm_int.N_of_uint i32m addr) 0%N
                     (bits (nat_to_value (Pos.to_nat t))) 4 = Some m'.

Definition INV_locals_all_i32 f := forall i v,
  nth_error (f_locs f) i = Some v -> exists v', v = VAL_num (VAL_int32 v').

Definition INV_num_functions_bounds sr fr :=
  (Z.of_nat num_custom_funs <= Z.of_nat (length (s_funcs sr)) <= max_num_functions + Z.of_nat num_custom_funs)%Z /\
  length (inst_elems (f_inst fr)) <= Z.to_nat max_num_functions + num_custom_funs.

Definition INV_inst_globals_nodup f :=
  NoDup (inst_globals (f_inst f)).

Definition INV_table_id sr fr := forall f i errMsg,
  translate_var nenv fenv f errMsg = Ret i ->
  stab_elem sr (f_inst fr) 0%N i = Some (VAL_ref_func i).

Definition INV_fvar_idx_inbounds sr := forall fvar fIdx,
  repr_funvar fvar fIdx ->
  (fIdx < N.of_nat (length (s_funcs sr)))%N.

Definition INV_types (fr : frame) := forall i,
  (Z.of_N i <= max_function_args)%Z ->
  lookup_N (inst_types (f_inst fr)) i = Some (Tf (List.repeat (T_num T_i32) (N.to_nat i)) [::]).

Definition INV_global_mem_ptr_multiple_of_two s f := forall gmp_v m,
  smem s (f_inst f) = Some m ->
  sglob_val s (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
  (-1 < Z.of_N gmp_v < Wasm_int.Int32.modulus)%Z ->
  exists n, (gmp_v = 2 * n)%N.

Definition INV_exists_func_grow_mem (sr : store_record) (fr : frame) :=
  lookup_N sr.(s_funcs) grow_mem_function_idx =
  Some (FC_func_native (Tf [T_num T_i32] []) (f_inst fr) {| modfunc_type := 1%N (* [i32] -> [] *)
                                                          ; modfunc_locals := []
                                                          ; modfunc_body := grow_memory_if_necessary |}).

Definition INV_inst_funcs_id sr f := forall i,
  (i < N.of_nat (length (s_funcs sr)))%N ->
  lookup_N (inst_funcs (f_inst f)) i = Some i.

(* invariants that need to hold throughout the execution of the Wasm program,
   doesn't hold anymore when memory runs out -> just abort

   also depends on fenv, shouldn't depend on lenv *)
Definition INV (s : store_record) (f : frame) :=
    INV_result_var_writable s f
 /\ INV_result_var_out_of_mem_writable s f
 /\ INV_result_var_out_of_mem_is_zero s f
 /\ INV_global_mem_ptr_writable s f
 /\ INV_constr_alloc_ptr_writable s f
 /\ INV_globals_all_mut s f
 /\ INV_linear_memory s f
 /\ INV_global_mem_ptr_in_linear_memory s f
 /\ INV_locals_all_i32 f
 /\ INV_num_functions_bounds s f
 /\ INV_inst_globals_nodup f
 /\ INV_table_id s f
 /\ INV_types f
 /\ INV_global_mem_ptr_multiple_of_two s f
 /\ INV_exists_func_grow_mem s f
 /\ INV_inst_funcs_id s f
 /\ INV_i64_glob_tmps_writable s f.

Lemma globs_disjoint : forall i i',
    i32_glob i -> i64_glob i' -> (i < i')%N.
Proof.
  cbn. 
  intros ?? [?|[?|[?|[?|?]]]] [?|[?|[?|[?|?]]]]; cbv delta in * |-; subst; lia.
Qed.

Lemma update_global_preserves_globals_all_mut : forall sr sr' i f num,
  NoDup (inst_globals (f_inst f)) ->
  ((i32_glob i /\ typeof_num num = T_i32) \/ (i64_glob i /\ typeof_num num = T_i64)) ->
  globals_all_mut sr f ->
  supdate_glob sr (f_inst f) i (VAL_num num) = Some sr' ->
  globals_all_mut sr' f.
Proof.
  intros ????? Hnodup Hi Hmut Hupd.
  unfold globals_all_mut, globals_all_mut32, globals_all_mut64 in *.
  destruct Hmut as [Hmut32 Hmut64].
  destruct Hi as [(Hi & Hi32) | (Hi & Hi64)]; 
    split; intros ??? Hgidx Hinstglobs Hstoreglobs; 
    unfold supdate_glob, supdate_glob_s, sglob_ind in Hupd. 
  (* discharge absurd cases *)
  2, 3: destruct (N.eq_dec gidx i) as [Heq | Hneq];
  [subst gidx; now assert (i < i)%N by now eapply (globs_disjoint _ i); eauto|];
  destruct (lookup_N (inst_globals (f_inst f)) i) eqn:Heqn;[|inv Hupd]; 
  cbn in Hupd;destruct (lookup_N (s_globals sr) g1) eqn:Heqn';[|inv Hupd];
  inv Hupd; cbn in Hstoreglobs; unfold lookup_N in *;
  erewrite set_nth_nth_error_other in Hstoreglobs; eauto;
  [intro Hcontra; apply N2Nat.inj in Hcontra; subst g1; apply Hneq; rewrite <- Heqn in Hinstglobs; unfold lookup_N in Heqn, Hinstglobs; eapply NoDup_nth_error in Hinstglobs; eauto; [lia|now apply nth_error_Some]|]; now apply nth_error_Some.
  all: destruct (lookup_N (inst_globals (f_inst f)) i) eqn:Heqn; [|inv Hupd]; cbn in Hupd;
    destruct (lookup_N (s_globals sr) g1) eqn:Heqn';[|inv Hupd]; inv Hupd; cbn in Hstoreglobs;
    destruct (N.lt_total g g1) as [Heq | [Heq | Heq]]; unfold lookup_N in *.
  (* Discharge cases where the global index is different from the one being updated *)
  1,3,4,6: erewrite set_nth_nth_error_other in Hstoreglobs; eauto; [lia|now apply nth_error_Some].
  - (* i32 globals *)
    subst. erewrite set_nth_nth_error_same in Hstoreglobs; eauto. inv Hstoreglobs.
    destruct num; unfold typeof_num in Hi32; try discriminate.
    assert (g2.(g_type) = {| tg_mut := MUT_var; tg_t := T_num T_i32 |}). {
      apply Hmut32 with (gidx:=i) in Heqn'; auto. destruct Heqn'. now subst. }
    now rewrite H.
  - (* i64 globals *)
    subst. erewrite set_nth_nth_error_same in Hstoreglobs; eauto. inv Hstoreglobs.
    destruct num; unfold typeof_num in Hi64; try discriminate.
    assert (g2.(g_type) = {| tg_mut := MUT_var; tg_t := T_num T_i64 |}). {
      apply Hmut64 with (gidx:=i) in Heqn'; auto. destruct Heqn'. now subst. }
    now rewrite H.
Qed.


Lemma update_global_preserves_global_var_w : forall i j sr sr' f num,
    global_var_w i sr f ->
    supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
    global_var_w i sr' f.
Proof.
  intros ? ? ? ? ? ? HG. unfold global_var_w. intro. unfold global_var_w in HG.
  unfold supdate_glob, supdate_glob_s, sglob_ind in *.
    destruct (lookup_N (inst_globals (f_inst f)) i) eqn:Heqn. cbn in HG. 2: cbn in HG; eauto.
    cbn in HG. destruct (lookup_N (s_globals sr) g) eqn:Heqn'.
    { cbn in H. edestruct HG as [? H1]. clear H1.
      destruct (lookup_N (inst_globals (f_inst f)) j) eqn:Heqn''. 2: inv H. cbn in H.
      destruct (lookup_N (s_globals sr) g1) eqn:Heqn'''. 2: inv H. cbn in H. inv H. cbn.
      destruct (lookup_N (set_nth _ (s_globals sr) _ _)) eqn:Heqn''''; cbn; eauto.
       exfalso. cbn in HG.
     assert (N.to_nat g1 < length (s_globals sr)) as Hl. {
       apply nth_error_Some. intro. unfold lookup_N in Heqn'''. congruence. }
     unfold lookup_N in *.
     apply nth_error_Some in Heqn''''. congruence.
     erewrite nth_error_set_nth_length; eauto.
     apply nth_error_Some. cbn in Heqn'''.
     congruence.
    }
     cbn in HG. edestruct HG. eauto. inv H0.
     Unshelve. auto.
Qed.

Lemma update_global_preserves_result_var_out_of_mem_is_zero : forall i sr sr' f num,
  INV_result_var_out_of_mem_is_zero sr f ->
  INV_inst_globals_nodup f ->
  result_out_of_mem <> i ->
  supdate_glob sr (f_inst f) i (VAL_num num) = Some sr' ->
  INV_result_var_out_of_mem_is_zero sr' f.
Proof.
  unfold INV_result_var_out_of_mem_is_zero. intros.
  eapply update_global_get_other; eauto.
Qed.

Lemma update_global_preserves_linear_memory : forall j sr sr' f  num,
  INV_linear_memory sr f ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_linear_memory sr' f.
Proof.
  intros.
  unfold supdate_glob, sglob_ind, supdate_glob_s in H0.
  destruct (lookup_N (inst_globals (f_inst f))) eqn:Heqn. 2: inv H0. cbn in H0.
  destruct (lookup_N (s_globals sr) g). 2: inv H0. cbn in H0. inv H0.
  assumption.
Qed.

Lemma update_global_preserves_num_functions_bounds : forall j sr sr' f  num,
  INV_num_functions_bounds sr f ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_num_functions_bounds sr' f.
Proof.
  unfold INV_num_functions_bounds. intros.
  assert (s_funcs sr = s_funcs sr') as Hfuncs. {
   unfold supdate_glob, supdate_glob_s in H0.
   destruct (sglob_ind sr (f_inst f) j). 2:inv H0. cbn in H0.
   destruct (lookup_N (s_globals sr) g). 2: inv H0. inv H0. reflexivity. }
   rewrite Hfuncs in H. apply H.
Qed.

Lemma update_global_preserves_global_mem_ptr_in_linear_memory : forall j sr sr' f m num,
  INV_global_mem_ptr_in_linear_memory sr f ->
  INV_inst_globals_nodup f ->
  smem sr (f_inst f) = Some m ->
  (j = global_mem_ptr ->
   forall n, num = VAL_int32 (N_to_i32 n) /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z -> n + 8 <= mem_length m)%N ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_global_mem_ptr_in_linear_memory sr' f.
Proof.
  unfold INV_global_mem_ptr_in_linear_memory.
  intros ? ? ? ? ? ? Hinv Hnodup Hmem  Hcond Hupd ? ? Hm Hglob Hunbound.
  assert (m = m0). { apply update_global_preserves_memory in Hupd. congruence. }
  subst m0. destruct (N.eq_dec j global_mem_ptr).
  { (* g = global_mem_ptr *)
     have H' := update_global_get_same _ _ _ _ _ Hupd.
     specialize (Hcond e).
     rewrite -e in Hglob. rewrite H' in Hglob. inv Hglob.     
     specialize (Hcond gmp_v (conj Logic.eq_refl Hunbound)).
     lia.
  }
  { (* g <> global_mem_ptr *)
    assert (Hgmp_r : sglob_val sr (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))). {
    unfold sglob_val, sglob, sglob_ind in Hglob |- *.
    destruct (lookup_N (inst_globals (f_inst f)) global_mem_ptr) eqn:Heqn.
      2: inv Hglob. cbn in Hglob.
    destruct (lookup_N (s_globals sr') g) eqn:Heqn'; inv Hglob. cbn.
    unfold supdate_glob, supdate_glob_s, sglob_ind in Hupd.
    destruct (lookup_N (inst_globals (f_inst f)) j) eqn:Heqn''. 2: inv Hupd.
    cbn in Hupd. destruct (lookup_N (s_globals sr) g1) eqn:Heqn'''; inv Hupd.
    cbn in Heqn'. unfold lookup_N in *.
    erewrite set_nth_nth_error_other in Heqn'; eauto.
    rewrite Heqn'. reflexivity. intro. subst. apply n.
    assert (g = g1) by lia. subst g1. clear H.
    apply N2Nat.inj.
    eapply NoDup_nth_error; eauto; try congruence.
    now apply nth_error_Some. now apply nth_error_Some. } auto. }
Qed.

Lemma update_global_preserves_table_id : forall j sr sr' f m num,
  INV_table_id sr f ->
  INV_inst_globals_nodup f ->
  smem sr (f_inst f) = Some m ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_table_id sr' f.
Proof.
  unfold INV_table_id, stab_elem. intros.
  apply H in H3.
  destruct (inst_tables (f_inst f)). inv H3. rewrite -H3.
  unfold supdate_glob, supdate_glob_s in H2.
  destruct (sglob_ind sr (f_inst f) j). 2: inv H2.
  cbn in H2. destruct (lookup_N (s_globals sr) g); inv H2. reflexivity.
Qed.

Lemma update_global_preserves_types : forall j sr sr' f m num,
  INV_types f ->
  INV_inst_globals_nodup f ->
  smem sr (f_inst f) = Some m ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_types f.
Proof.
  unfold INV_types, stab_elem. intros.
  apply H in H3. now rewrite -H3.
Qed.


Lemma update_global_preserves_global_mem_ptr_multiple_of_two : forall j sr sr' f m num,
    INV_global_mem_ptr_multiple_of_two sr f ->
    INV_inst_globals_nodup f ->
    smem sr (f_inst f) = Some m ->
    (j = global_mem_ptr -> forall n, 
        num = VAL_int32 (N_to_i32 n) /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z -> exists n', n = 2  * n')%N ->
    supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
    INV_global_mem_ptr_multiple_of_two sr' f.
Proof.
  unfold INV_global_mem_ptr_multiple_of_two.
  intros j sr sr' f m num. intros Hinv Hnodups Hnth Hj Hupd.
  intros gmp_v m0 ? Hglob Hrange'.
  assert (m = m0). { apply update_global_preserves_memory in Hupd.  congruence. }
  subst m0. destruct (N.eq_dec j global_mem_ptr).
  { (* g = global_mem_ptr *)
    have H' := update_global_get_same _ _ _ _ _ Hupd.
    subst j.
    rewrite H' in Hglob. injection Hglob as Hglob.
    now destruct (Hj Logic.eq_refl gmp_v (conj Hglob Hrange')).    
  }
  { (* g <> global_mem_ptr *)
    assert (Hgmp_r : sglob_val sr (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))). {
    unfold sglob_val, sglob, sglob_ind in Hglob.
    unfold sglob_val, sglob, sglob_ind.
    destruct (lookup_N (inst_globals (f_inst f)) global_mem_ptr) eqn:Heqn.
      2: inv Hglob. cbn in Hglob.
    destruct (lookup_N (s_globals sr') g) eqn:Heqn'; inv Hglob. cbn.
    unfold supdate_glob, supdate_glob_s, sglob_ind in Hupd.
    destruct (lookup_N (inst_globals (f_inst f)) j) eqn:Heqn''. 2: inv Hupd.
    cbn in Hupd. destruct (lookup_N (s_globals sr) g1) eqn:Heqn'''; inv Hupd.
    cbn in Heqn'. unfold lookup_N in *. erewrite set_nth_nth_error_other in Heqn'; eauto.
    rewrite Heqn'. reflexivity. intro. subst. apply n.
    assert (g = g1) by lia. subst g1.
    apply N2Nat.inj. eapply NoDup_nth_error; eauto; try congruence.
    now apply nth_error_Some. now apply nth_error_Some. }
    eapply Hinv; eauto.
  }
Qed.

Lemma update_global_preserves_exists_func_grow_mem : forall j sr sr' fr f  num,
  INV_exists_func_grow_mem sr fr ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_exists_func_grow_mem sr' fr.
Proof.
  unfold INV_exists_func_grow_mem. intros.
  assert (s_funcs sr = s_funcs sr') as Hfuncs. {
   unfold supdate_glob, supdate_glob_s in H0.
   destruct (sglob_ind sr (f_inst f) j). 2:inv H0. cbn in H0.
   destruct (lookup_N (s_globals sr) g). 2: inv H0. inv H0. reflexivity. }
   rewrite Hfuncs in H. apply H.
Qed.

Lemma update_global_preserves_inst_funcs_id : forall j sr sr' fr f  num,
  INV_inst_funcs_id sr fr ->
  supdate_glob sr (f_inst f) j (VAL_num num) = Some sr' ->
  INV_inst_funcs_id sr' fr.
Proof.
  unfold INV_inst_funcs_id. intros.
  assert (s_funcs sr = s_funcs sr') as Hfuncs. {
   unfold supdate_glob, supdate_glob_s in H0.
   destruct (sglob_ind sr (f_inst f) j). 2:inv H0. cbn in H0.
   destruct (lookup_N (s_globals sr) g). 2: inv H0. inv H0. reflexivity. }
   rewrite Hfuncs in H. by apply H.
Qed.

Lemma update_global_preserves_i64_glob_tmps_writable : forall j sr sr' fr num,
  INV_i64_glob_tmps_writable sr fr ->
  supdate_glob sr (f_inst fr) j (VAL_num num) = Some sr' ->
  INV_i64_glob_tmps_writable sr' fr.
Proof.
  unfold INV_i64_glob_tmps_writable. intros.
  apply H in H1.
  now apply update_global_preserves_global_var_w with (j:=j) (sr:=sr) (num:=num).
Qed.


Corollary update_global_preserves_INV : forall sr sr' i f m num,
  (i32_glob i /\ typeof_num num = T_i32) \/ (i64_glob i /\ typeof_num num = T_i64) ->
  INV sr f ->
  (* if result_out_of_mem is set, INV doesn't need to hold anymore *)
  result_out_of_mem <> i ->
  (* if updated gmp, new value in mem *)
  smem sr (f_inst f) = Some m ->
  (i = global_mem_ptr -> forall n, num = VAL_int32 (N_to_i32 n) /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z -> n + 8 <= mem_length m)%N ->
  (i = global_mem_ptr -> forall n, num = VAL_int32 (N_to_i32 n) /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z -> exists n', n = 2  * n')%N ->
  supdate_glob sr (f_inst f) i (VAL_num num) = Some sr' ->
  INV sr' f.
Proof with eassumption.
  intros. unfold INV. destruct H0 as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [?  ?]]]]]]]]]]]]]]]].
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_result_var_out_of_mem_is_zero...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_globals_all_mut...
  split. eapply update_global_preserves_linear_memory...
  split. eapply update_global_preserves_global_mem_ptr_in_linear_memory...
  split. assumption.
  split. eapply update_global_preserves_num_functions_bounds...
  split. assumption.
  split. eapply update_global_preserves_table_id...
  split. eapply update_global_preserves_types...
  split. eapply update_global_preserves_global_mem_ptr_multiple_of_two with (sr:=sr); eauto.
  split. eapply update_global_preserves_exists_func_grow_mem...
  split. eapply update_global_preserves_inst_funcs_id...
  eapply update_global_preserves_i64_glob_tmps_writable...
Qed.

Corollary update_local_preserves_INV : forall sr f f' x' v,
  INV sr f ->
  x' < length (f_locs f) ->
  f' = {| f_locs := set_nth (VAL_num (VAL_int32 v)) (f_locs f) x' (VAL_num (VAL_int32 v))
        ; f_inst := f_inst f
        |} ->
  INV sr f'.
Proof with eauto.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]. subst.
  repeat (split; auto).
  { unfold INV_locals_all_i32 in *. cbn. intros.
    destruct (Nat.eq_dec x' i).
    (* i=x' *) subst. apply nth_error_Some in H0. apply notNone_Some in H0. destruct H0.
    erewrite set_nth_nth_error_same in H1; eauto. inv H1. eauto.
    (* i<>x' *) rewrite set_nth_nth_error_other in H1; auto. apply H9 in H1. assumption. }
Qed.

Corollary change_locals_preserves_INV : forall sr f f' l,
  INV sr f ->
  INV_locals_all_i32 f' ->
  f' = {| f_locs := l
        ; f_inst := f_inst f
        |} ->
  INV sr f'.
Proof with eauto.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]. subst.
  repeat (split; auto).
Qed.

Corollary init_locals_preserves_INV : forall sr f f' args n,
  INV sr f ->
  f' = {| f_locs := [seq (VAL_num (N_to_value a)) | a <- args] ++
                      repeat (VAL_num (nat_to_value 0)) n
        ; f_inst := f_inst f
        |} ->
  INV sr f'.
Proof with eauto.
  intros. subst.
  eapply change_locals_preserves_INV; eauto.
  { unfold INV_locals_all_i32 in *. cbn. intros.
    destruct (Nat.ltb_spec i (length args)).
    { (* i < length args *)
      rewrite nth_error_app1 in H0. 2: {
         now rewrite length_is_size size_map -length_is_size. }
      apply nth_error_In in H0.
      apply in_map_iff in H0. destruct H0 as [x [Heq Hin]]. subst.
      eexists. reflexivity. }
    { (* i >= length args *)
      assert (Hlen: i < Datatypes.length ([seq (VAL_num (N_to_value a)) | a <- args]
                                          ++ repeat (VAL_num (nat_to_value 0)) n)). {
        apply nth_error_Some. congruence. }
      rewrite app_length length_is_size size_map -length_is_size repeat_length in Hlen.
      rewrite nth_error_app2 in H0. 2: {
        now rewrite length_is_size size_map -length_is_size. }
      have H' := H0.
      rewrite nth_error_repeat in H'.
        2: { rewrite length_is_size size_map -length_is_size. lia. }
      inv H'. eexists. reflexivity. }
  }
Qed.

(* writable implies readable *)
Lemma global_var_w_implies_global_var_r : forall (s : store_record) fr var,
    i32_glob var \/ i64_glob var ->
    globals_all_mut s fr ->
    global_var_w var s fr ->
    global_var_r var s fr.
Proof.
  intros s fr i Hi Hmut GVW.
  destruct Hi as [Hi32 | Hi64].  
  destruct exists_i32 as [x _].
  unfold global_var_w, global_var_r, supdate_glob, sglob_val, sglob, sglob_ind in GVW |- *. cbn in GVW |- *.
  destruct GVW with (val:=VAL_int32 x).
  unfold global_var_r, sglob_val, sglob, sglob_ind.
  destruct ((lookup_N (inst_globals (f_inst fr)) i)) eqn:Hv. 2: inv H.
  cbn in H. cbn. unfold supdate_glob_s in H.
  destruct (lookup_N (s_globals s) g) eqn:Hg. 2: inv H. cbn.
  cbn in H.
  inv H.
  unfold globals_all_mut in *.
  destruct Hmut as [Hmut32 _].
  apply (Hmut32 i g g0 Hi32 Hv) in Hg.
  destruct Hg.
  inv H. eexists.
  reflexivity.
  assert (exists (v : i64), True) as Hex
      by now exists (Wasm_int.Int64.repr 1); constructor.
  destruct Hex as [x _].
  unfold global_var_w, global_var_r, supdate_glob, sglob_val, sglob, sglob_ind in GVW |- *. cbn in GVW |- *.
  destruct GVW with (val:=VAL_int64 x).
  unfold global_var_r, sglob_val, sglob, sglob_ind.
  destruct ((lookup_N (inst_globals (f_inst fr)) i)) eqn:Hv. 2: inv H.
  cbn in H. cbn. unfold supdate_glob_s in H.
  destruct (lookup_N (s_globals s) g) eqn:Hg. 2: inv H. cbn.
  cbn in H.
  inv H.
  unfold globals_all_mut in *.
  destruct Hmut as [_ Hmut64].
  apply (Hmut64 i g g0 Hi64 Hv) in Hg.
  destruct Hg.
  inv H. eexists.
  reflexivity.
Qed.

Lemma update_mem_preserves_global_var_w : forall i s f s' m vd,
   global_var_w i s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   global_var_w i s' f.
Proof.
  intros.
  unfold global_var_w.
  intros. unfold upd_s_mem in H0. subst. destruct H with (val:=val).
  unfold supdate_glob, sglob_ind, supdate_glob_s in *. cbn in *.
  destruct (lookup_N (inst_globals (f_inst f)) i). 2: inv H0. cbn in *.
  destruct (lookup_N (s_globals s) g). 2: inv H0. cbn in *. eexists. reflexivity.
Qed.

Lemma update_mem_preserves_result_var_out_of_mem_is_zero : forall s f s' m vd,
   INV_result_var_out_of_mem_is_zero s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_result_var_out_of_mem_is_zero s' f.
Proof.
  unfold INV_result_var_out_of_mem_is_zero, sglob_val, sglob, sglob_ind, nat_to_i32.
  intros. subst. cbn in *.
  destruct (inst_globals (f_inst f)). inv H.
  destruct l. inv H. destruct l. inv H. destruct l. inv H. assumption.
Qed.

Lemma update_mem_preserves_all_mut : forall s s' f m vd,
   globals_all_mut s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   globals_all_mut s' f.
Proof.
  unfold globals_all_mut, globals_all_mut32, globals_all_mut64. intros.
  unfold upd_s_mem in H0. assert (s_globals s = s_globals s') as Hglob. {
   subst. destruct s. reflexivity. }
  destruct H as [Hmut32 Hmut64].
  split.
  - rewrite Hglob in Hmut32; eapply Hmut32; eauto.
  - rewrite Hglob in Hmut64; eapply Hmut64; eauto.
Qed.

Lemma update_mem_preserves_linear_memory : forall s s' f m vd,
   INV_linear_memory s f  ->
   mem_max_opt m = Some max_mem_pages ->
   (exists size, mem_size m = size /\ size <= max_mem_pages)%N ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_linear_memory s' f.
Proof.
  unfold INV_linear_memory.
  intros s s' f m m' [H1 [m'' [H2 [size [H3 H4]]]]] H' [size' [H6 H7]] H8.
  split =>//.
  exists m. split.
  - subst.
    unfold smem in *. rewrite H1 in H2. cbn in H2. rewrite H1. cbn.
    destruct (s_mems s)=>//.
  - exists size'. repeat split; auto.
Qed.

Lemma update_mem_preserves_global_mem_ptr_in_linear_memory : forall s s' f m m',
   INV_global_mem_ptr_in_linear_memory s f ->
   INV_global_mem_ptr_writable s f ->
   INV_globals_all_mut s f ->
   smem s (f_inst f) = Some m ->
   inst_mems (f_inst f) = [0%N] ->
   (mem_length m' >= mem_length m)%N ->
   upd_s_mem s (set_nth m' (s_mems s) 0 m') = s' ->
   INV_global_mem_ptr_in_linear_memory s' f.
Proof.
  unfold INV_global_mem_ptr_in_linear_memory.
  intros ????? H Hinv Hinv' ?????????. subst.
  unfold smem in *.
  destruct (s_mems s) eqn:Hm'.
  { rewrite -> H0 in *. destruct (lookup_N _ _)=>//. unfold lookup_N in *. destruct (N.to_nat m1)=>//. }
  eapply update_mem_preserves_global_var_w in Hinv; eauto.
  apply global_var_w_implies_global_var_r in Hinv.
  assert (gmp_v + 8 <= mem_length m)%N. { unfold smem in *. apply H; auto. }
  cbn in H4. rewrite H1 in H4. inv H4. lia.
  left. cbn. right; right; now constructor.
  eapply update_mem_preserves_all_mut; eauto.
  Unshelve. assumption. assumption.
Qed.

Lemma update_mem_preserves_global_constr_alloc_ptr_in_linear_memory : forall s s' f m m' vd,
   INV_constr_alloc_ptr_in_linear_memory s f  ->
   INV_constr_alloc_ptr_writable s f ->
   INV_globals_all_mut s f ->
   smem s (f_inst f) = Some m ->
   (mem_length m' >= mem_length m)%N ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m') = s' ->
   INV_constr_alloc_ptr_in_linear_memory s' f.
Proof.
  unfold INV_constr_alloc_ptr_in_linear_memory.
  intros ? ? ? ? ? ? H Hinv Hinv' ? ? ? ? ? ? ?.
  eapply update_mem_preserves_global_var_w in Hinv; eauto.
  apply global_var_w_implies_global_var_r in Hinv.
  unfold global_var_r in Hinv. destruct Hinv as [v Hv].
  rewrite H3 in Hv. inv Hv.
  eapply H in H3; eauto.
  left; right; right; right; now constructor.
  now eapply update_mem_preserves_all_mut.
Qed.

Lemma update_mem_preserves_num_functions_bounds : forall s s' f m vd,
   INV_num_functions_bounds s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_num_functions_bounds s' f.
Proof.
  unfold INV_num_functions_bounds. intros. subst. assumption.
Qed.

Lemma update_mem_preserves_table_id : forall s s' f m vd,
   INV_table_id s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_table_id s' f.
Proof.
  unfold INV_table_id. intros. subst. apply H in H1. rewrite -H1. reflexivity.
Qed.

Lemma update_mem_preserves_types : forall s s' f m vd,
  INV_types f ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  INV_types f.
Proof.
  unfold INV_types. intros. subst. auto.
Qed.

Lemma update_mem_preserves_fvar_idx_inbounds : forall s s' m vd,
  INV_fvar_idx_inbounds s ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
  INV_fvar_idx_inbounds s'.
Proof.
  unfold INV_fvar_idx_inbounds. intros. subst. eauto.
Qed.

Lemma update_mem_preserves_global_mem_ptr_multiple_of_two : forall s s' f m m' vd,
  INV_global_mem_ptr_multiple_of_two s f ->
  smem s (f_inst f)  = Some m ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m') = s' ->
  INV_global_mem_ptr_multiple_of_two s' f.
Proof.
  unfold INV_global_mem_ptr_multiple_of_two.
  intros. subst.
  eapply H; eauto.
Qed.

Lemma update_mem_preserves_exists_func_grow_mem : forall s s' f m vd,
   INV_exists_func_grow_mem s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_exists_func_grow_mem s' f.
Proof.
  unfold INV_exists_func_grow_mem. intros. subst. cbn. assumption.
Qed.

Lemma update_mem_preserves_inst_funcs_id : forall s s' f m vd,
   INV_inst_funcs_id s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_inst_funcs_id s' f.
Proof.
  unfold INV_inst_funcs_id. intros ?????? <- ??; auto.
Qed.

Corollary update_mem_preserves_INV : forall s s' f m m' vd,
  INV s f ->
  smem s (f_inst f) = Some m ->
  (mem_length m' >= mem_length m)%N ->
  mem_max_opt m' = Some max_mem_pages ->
  (exists size, mem_size m' = size /\ size <= max_mem_pages)%N ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m') = s' ->
  INV s' f.
Proof with eassumption.
  intros. unfold INV.
  destruct H as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]]].
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_result_var_out_of_mem_is_zero...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_all_mut...
  split. eapply update_mem_preserves_linear_memory...
  split. eapply update_mem_preserves_global_mem_ptr_in_linear_memory; eauto. apply H10.
  split. assumption.
  split. eapply update_mem_preserves_num_functions_bounds...
  split. assumption.
  split. eapply update_mem_preserves_table_id...
  split. eapply update_mem_preserves_types...
  split. eapply update_mem_preserves_global_mem_ptr_multiple_of_two...
  split. eapply update_mem_preserves_exists_func_grow_mem...
  split. eapply update_mem_preserves_inst_funcs_id...
  unfold INV_i64_glob_tmps_writable. intros. eapply update_mem_preserves_global_var_w; eauto.
Qed.

Corollary sgrow_mem_preserves_INV : forall sr sr' fr bytes size,
  INV sr fr ->
  smem_grow sr (f_inst fr) bytes = Some (sr', size) ->
  INV sr' fr.
Proof.
  intros ????? Hinv Hgrow.
  have I := Hinv. destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM [? [? [HglobNodup _]]]]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m [Hm2 [size' [Hm3 [Hm4 Hm5]]]]]].
  unfold smem_grow, smem in Hgrow, Hm2.
  rewrite Hm1 in Hgrow, Hm2. cbn in Hgrow, Hm2. rewrite Hm2 in Hgrow.
  destruct (mem_grow m bytes) eqn:Hgrow'=>//. inv Hgrow.
  eapply update_mem_preserves_INV with (m:=m) (m':=m0); eauto.
  - unfold smem. rewrite Hm1 Hm2. reflexivity.
  - apply mem_grow_increases_length in Hgrow'. lia.
  - erewrite mem_grow_preserves_max_pages; eauto.
  - exists (mem_size m0). split=>//.
    have Hgrow := Hgrow'.
    unfold mem_grow in Hgrow'.
    destruct ((mem_size m + bytes <=? mem_limit_bound)%N)=>//.
    unfold mem_max_opt in Hm4. rewrite Hm4 in Hgrow'.
    destruct ((mem_size m + bytes <=? max_mem_pages)%N) eqn:Hsize=>//. clear Hgrow'.
    apply mem_grow_increases_size in Hgrow. rewrite Hgrow.
    apply N.leb_le in Hsize. lia.
Qed.

(** The lemmas [r_eliml] and [r_elimr] are relicts,
    kept for compatability for now, TODO rework (use new context representation) **)
Lemma r_eliml : forall hs s f es hs' s' f' es' lconst,
  const_list lconst ->
  reduce hs s f es hs' s' f' es' ->
  reduce hs s f (lconst ++ es) hs' s' f' (lconst ++ es').
Proof.
  move => hs s f es hs' s' f' es' lconst HConst H.
  apply const_es_exists in HConst. destruct HConst as [vs ?].
  eapply r_label with (lh:=LH_base vs []). eassumption.
  - cbn. rewrite cats0. congruence.
  - cbn. rewrite cats0. congruence.
Qed.

Lemma r_elimr: forall hs s f es hs' s' f' es' les,
  reduce hs s f es hs' s' f' es' ->
  reduce hs s f (es ++ les) hs' s' f' (es' ++ les).
Proof.
  move => hs s f es hs' s' f' es' les H.
  eapply r_label with (lh:=LH_base [] les); eauto.
Qed.

Lemma reduce_trans_label' : forall instr instr' hs hs' sr sr' fr fr' i (lh : lholed i),
  reduce_trans (hs, sr, fr, instr) (hs', sr', fr', instr') ->
  reduce_trans (hs,  sr,  fr, lfill lh instr) (hs', sr', fr', lfill lh instr').
Proof.
  intros.
  apply clos_rt_rt1n in H.
  remember (hs, sr, fr, instr) as x. remember (hs', sr', fr', instr') as x'.
  generalize dependent hs. generalize dependent hs'.
  revert fr fr' sr sr' instr instr'.
  induction H; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[? ?] ?] ?].
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[instr])).
    eapply rt_step. eapply r_label with (k:=i) (lh:=lh); eauto.
    now apply IHclos_refl_trans_1n.
Qed.

Lemma reduce_trans_label : forall instr hs hs' sr sr' fr fr',
  reduce_trans (hs,  sr, fr, instr) (hs', sr', fr', []) ->
  reduce_trans (hs,  sr, fr, [:: AI_label 0 [::] instr]) (hs', sr', fr', [::]).
Proof.
  intros.
  remember (LH_rec [] 0 [] (LH_base [] []) []) as lh.
  have H' := reduce_trans_label' instr [] _ _ _ _ _ _ _ lh. subst lh. cbn in H'.
  rewrite cats0 in H'. eapply rt_trans. eapply H'; auto. eassumption.
  eapply rt_step. constructor. now apply rs_label_const.
Qed.

Lemma reduce_trans_label0 : forall instr instr' hs hs' sr sr' fr fr',
  reduce_trans (hs,  sr, fr, instr) (hs', sr', fr', instr') ->
  reduce_trans (hs,  sr, fr, [:: AI_label 0 [::] instr]) (hs', sr', fr', [:: AI_label 0 [::] instr']).
Proof.
  intros.
  remember (LH_rec [] 0 [] (LH_base [] []) []) as lh.
  have H' := reduce_trans_label' instr instr' _ _ _ _ _ _ _ lh. subst lh. cbn in H'.
  do 2! rewrite cats0 in H'. eapply rt_trans. eapply H'; auto. eassumption.
  apply rt_refl.
Qed.

Lemma reduce_trans_label1 : forall instr instr' hs hs' sr sr' fr fr',
  reduce_trans (hs,  sr, fr, instr) (hs', sr', fr', instr') ->
  reduce_trans (hs,  sr, fr, [:: AI_label 1 [::] instr]) (hs', sr', fr', [:: AI_label 1 [::] instr']).
Proof.
  intros.
  remember (LH_rec [] 1 [] (LH_base [] []) []) as lh.
  have H' := reduce_trans_label' instr instr' _ _ _ _ _ _ _ lh. subst lh. cbn in H'.
  do 2! rewrite cats0 in H'. eapply rt_trans. eapply H'; auto. eassumption.
  apply rt_refl.
Qed.


Lemma reduce_trans_frame : forall instructions hs hs' sr sr' fr fr' f0,
  reduce_trans (hs,  sr, fr, instructions) (hs', sr', fr', []) ->
  reduce_trans (hs,  sr, f0, [:: AI_frame 0 fr instructions]) (hs', sr', f0, [::]).
Proof.
  intros.
  apply clos_rt_rt1n in H.
  remember (hs, sr, fr, instructions) as x. remember (hs', sr', fr', [::]) as x'.
  generalize dependent state. generalize dependent sr. generalize dependent fr.
  generalize dependent fr'. generalize dependent sr'. revert instructions hs hs'.
  induction H; intros; subst.
  - inv Heqx. constructor. constructor. now apply rs_local_const.
  - destruct y as [[[? ?] ?] ?].
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[instr])).
    eapply rt_step. eapply r_frame. apply H.
    now eapply IHclos_refl_trans_1n.
Qed.

(* TODO rename and consolidate lemmas above *)
Lemma reduce_trans_frame' : forall instr instr' hs hs' sr sr' fr fr' f0,
  reduce_trans (hs, sr, fr, instr) (hs', sr', fr', instr') ->
  reduce_trans (hs,  sr, f0, [:: AI_frame 0 fr instr]) (hs', sr', f0, [:: AI_frame 0 fr' instr']).
Proof.
  intros.
  apply clos_rt_rt1n in H.
  remember (hs, sr, fr, instr) as x. remember (hs', sr', fr', instr') as x'.
  generalize dependent hs. generalize dependent hs'. revert instr instr' fr fr' f0 sr sr'.
  induction H; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[? ?] ?] ?].
    have IH := IHclos_refl_trans_1n _ _ _ _ _ _ _ _ Logic.eq_refl _ Logic.eq_refl.
    eapply rt_trans with (y := (?[hs], ?[sr], f0, [:: AI_frame 0 ?[f'] ?[instr]])).
    2: by apply IH.
    eapply rt_step. now eapply r_frame.
Qed.

Ltac separate_instr :=
  cbn;
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end.

(* isolate instr. + n leading args, e.g. with n=2 for add:
   [const 1, const 2, add, remaining instr] => [const 1, const 2, add]  *)
Ltac elimr_nary_instr n :=
  let H := fresh "H" in
  match n with
  | 0 => lazymatch goal with
         | |- reduce _ _ _ ([:: ?instr])        _ _ _ _ => idtac
         | |- reduce _ _ _ ([:: ?instr] ++ ?l3) _ _ _ _ => apply r_elimr
         end
  | 1 => lazymatch goal with
         | |- reduce _ _ _ ([::$VN ?c1] ++ [:: ?instr])        _ _ _ _ => idtac
         | |- reduce _ _ _ ([::$VN ?c1] ++ [:: ?instr] ++ ?l3) _ _ _ _ =>
            assert ([::$VN c1] ++ [:: instr] ++ l3 =
                    [:: $VN c1; instr] ++ l3) as H by reflexivity; rewrite H;
                                                       apply r_elimr; clear H
         end
  | 2 => lazymatch goal with
         | |- reduce _ _ _ ([::$VN ?c1] ++ [::$VN ?c2] ++ [:: ?instr])        _ _ _ _ => idtac
         | |- reduce _ _ _ ([::$VN ?c1] ++ [::$VN ?c2] ++ [:: ?instr] ++ ?l3) _ _ _ _ =>
            assert ([::$VN c1] ++ [:: $VN c2] ++ [:: instr] ++ l3 =
                    [::$VN c1; $VN c2; instr] ++ l3) as H by reflexivity; rewrite H;
                                                       apply r_elimr; clear H
         end
  end.

Ltac dostep :=
  eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s] ++ ?[t]));
  first (apply rt_step; separate_instr).

(* only returns single list of instructions *)
Ltac dostep' :=
   eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s]));
   first (apply rt_step; separate_instr).

Ltac dostep_nary n :=
  dostep; first elimr_nary_instr n.

Ltac dostep_nary_eliml n n' :=
  dostep; first ((do n'! (apply r_eliml; auto)); elimr_nary_instr n).

Ltac dostep_nary' n :=
  dostep'; first elimr_nary_instr n.

Ltac simpl_modulus_in H :=
  unfold Wasm_int.Int32.modulus, Wasm_int.Int64.modulus, Wasm_int.Int32.half_modulus, Wasm_int.Int64.half_modulus, two_power_nat in H; cbn in H.
Ltac simpl_modulus :=
  unfold Wasm_int.Int64.max_unsigned, Wasm_int.Int32.modulus, Wasm_int.Int64.modulus, Wasm_int.Int32.half_modulus, Wasm_int.Int64.half_modulus, two_power_nat.

Ltac simpl_modulus64_in H :=
  unfold Wasm_int.Int64.max_unsigned, Wasm_int.Int64.half_modulus, Wasm_int.Int64.modulus, two_power_nat in H.

(* Print caseConsistent. *)
Lemma caseConsistent_findtag_In_cenv:
  forall cenv t e l,
    caseConsistent cenv l t ->
    findtag l t = Some e ->
    exists (a aty:BasicAst.name) (ty:ind_tag) (n:N) (i:N),
      M.get t cenv = Some (Build_ctor_ty_info a aty ty n i).
Proof.
  destruct l; intros.
  - inv H0.
  - inv H. destruct info.
    exists ctor_name, ctor_ind_name, ctor_ind_tag,ctor_arity,ctor_ordinal; auto.
Qed.

Lemma app_trans: forall s f es s' f' es' les hs hs',
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  reduce_trans (hs, s, f, (es ++ les)) (hs', s', f', (es' ++ les)).
Proof.
  intros. apply clos_rt_rt1n in H. remember (hs, s, f, es) as x.
  remember (hs', s', f', es') as x'. generalize dependent hs. generalize dependent hs'.
  revert s s' f f' es es'. induction H; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[hs0 s0] f0] es0].
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[l])). apply rt_step.
    eapply r_label with (k:=0) (lh:=LH_base [] les). apply H.
    reflexivity. reflexivity.
    apply IHclos_refl_trans_1n; auto.
Qed.

Lemma app_trans_const : forall hs hs' s s' f f' es es' lconst,
  const_list lconst ->
  reduce_trans (hs, s, f, es) (hs', s', f', es') ->
  reduce_trans (hs, s, f, (lconst ++ es)) (hs', s', f', (lconst ++ es')).
Proof.
  intros ? ? ? ? ? ? ? ? ? Hconst Hred. apply clos_rt_rt1n in Hred.
  remember (hs, s, f, es) as x. remember (hs', s', f', es') as x'.
  generalize dependent hs. generalize dependent hs'. generalize dependent lconst.
  revert s s' f f' es es'.
  induction Hred; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[hs'' s''] f''] es''].
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[instr])).
    apply rt_step. apply r_eliml. cbn. now rewrite Hconst. eassumption.
    apply IHHred; auto.
Qed.

Lemma decode_int32_bounds : forall b m addr,
  load m addr 0%N 4 = Some b ->
  (-1 < decode_int b < Wasm_int.Int32.modulus)%Z.
Proof.
  intros.
  (* length b = 4 bytes *)
  unfold load, those in H.
  destruct (addr + (0 + N.of_nat 4) <=? mem_length m)%N. 2: inv H.
  unfold read_bytes in H. cbn in H.
  destruct (memory_list.mem_lookup (addr + 0 + 0)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 1)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 2)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 3)%N (meminst_data m)). 2: inv H.
  inv H.
  unfold decode_int, int_of_bytes, rev_if_be, Wasm_int.Int32.modulus, two_power_nat.
  destruct Archi.big_endian;
    destruct b0, b1, b2, b3; cbn;
      unfold Byte.modulus, Byte.wordsize, two_power_nat, Wordsize_8.wordsize in *;
        cbn in *; lia.
Qed.

Lemma decode_int64_bounds : forall b m addr,
  load m addr 0%N 8 = Some b ->
  (-1 < decode_int b < Wasm_int.Int64.modulus)%Z.
Proof.
  intros.
  (* length b = 8 bytes *)
  unfold load, those in H.
  destruct (addr + (0 + N.of_nat 8) <=? mem_length m)%N. 2: inv H.
  unfold read_bytes in H. cbn in H.
  destruct (memory_list.mem_lookup (addr + 0 + 0)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 1)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 2)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 3)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 4)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 5)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 6)%N (meminst_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (addr + 0 + 7)%N (meminst_data m)). 2: inv H.
  inv H.
  unfold decode_int, int_of_bytes, rev_if_be, Wasm_int.Int64.modulus, two_power_nat.
  destruct Archi.big_endian;
    destruct b0, b1, b2, b3, b4, b5, b6, b7; cbn;
      unfold Byte.modulus, Byte.wordsize, two_power_nat, Wordsize_8.wordsize in *;
        cbn in *; lia.
Qed.

Lemma value_bounds : forall wal v sr fr,
  INV_num_functions_bounds sr fr ->
  repr_val_LambdaANF_Wasm v sr (f_inst fr) wal ->
 (-1 < Z.of_N (wasm_value_to_u32 wal) < Wasm_int.Int32.modulus)%Z.
Proof.
  intros ? ? ? ? [Hbound1 Hbound2] H.
  inv H.
  - (* constr. value unboxed *) cbn. lia.
  - (* constr. value boxed *) cbn. lia.
  - (* function value *)
    cbn.
    assert (N.to_nat idx < length (s_funcs sr)). { apply nth_error_Some. unfold lookup_N in *. congruence. }
    unfold INV_num_functions_bounds in Hbound1.
    unfold max_num_functions, num_custom_funs in *. simpl_modulus. cbn. lia.
  - (* prim. value boxed *) cbn. lia.
Qed.

Lemma extract_constr_arg : forall n vs v sr fr addr m,
  INV_num_functions_bounds sr fr ->
  nthN vs n = Some v ->
  smem sr (f_inst fr) = Some m ->
  (* addr points to the first arg after the constructor tag *)
  repr_val_constr_args_LambdaANF_Wasm vs sr (f_inst fr) addr ->
  exists bs wal, load m (addr + 4 * n)%N 0%N 4 = Some bs /\
             VAL_int32 (wasm_value_to_i32 wal) = wasm_deserialise bs T_i32 /\
             repr_val_LambdaANF_Wasm v sr (f_inst fr) wal.
Proof.
  intros n vs v sr fr addr m Hinv H H1 H2. generalize dependent v.
  generalize dependent n. generalize dependent m. remember (f_inst fr) as inst.
  generalize dependent fr.
  induction H2; intros; subst. 1: inv H.
  generalize dependent v0.
  induction n using N.peano_ind; intros.
  - (* n = 0 *)
    inv H7. assert (m = m0) by congruence. subst m0. rewrite N.add_comm. unfold load_i32 in H3.
    destruct (load m addr 0%N 4) eqn:Hl; inv H3. exists b. exists wal.
    repeat split. rewrite <- Hl. now rewrite N.add_comm. unfold wasm_value_to_i32.
    have H'' := value_bounds wal.
    unfold wasm_deserialise. f_equal. f_equal.
    have H' := decode_int32_bounds _ _ _ Hl. simpl_eq.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H8; auto.
    eapply value_bounds; eauto. assumption.
  - (* n = succ n0 *)
    cbn in H7.
    destruct (N.succ n) eqn:Hn; first by lia. rewrite <-Hn in *.
    replace (N.succ n - 1)%N with n in H7 by lia. clear Hn p.
    edestruct IHrepr_val_constr_args_LambdaANF_Wasm; eauto.
    destruct H8 as [wal' [Hl [Heq Hval]]].
    exists x. exists wal'. split. rewrite -Hl. f_equal. lia. split; eauto.
Qed.

Lemma memory_grow_success : forall m sr fr,
  INV_linear_memory sr fr ->
  smem sr (f_inst fr) = Some m ->
  (mem_size m + 1 <=? max_mem_pages)%N ->
  exists s' size, smem_grow sr (f_inst fr) 1 = Some (s', size).
Proof.
  intros m sr fr Hinv H Hsize. unfold smem_grow, mem_grow.
  have Hm := H. unfold smem in H.
  destruct (lookup_N (inst_mems (f_inst fr)) 0)=>//.
  rewrite H.
  assert ((mem_size m + 1 <=? mem_limit_bound)%N) as H'. {
    unfold mem_limit_bound. unfold max_mem_pages in Hsize. apply N.leb_le.
    apply N.leb_le in Hsize. unfold mem_limit_bound in Hsize. lia.
  } rewrite H'. clear H'.
  unfold INV_linear_memory in Hinv. destruct Hinv as [H1 [m' [H2 [size [H4 [H5 H6]]]]]].
  solve_eq m m'. unfold mem_max_opt in H5. rewrite H5.
  rewrite Hsize. cbn. eauto.
Qed.

Lemma memory_grow_reduce_need_grow_mem : forall state s f gmp m,
  nth_error (f_locs f) 0 = Some (VAL_num (N_to_value page_size)) ->
  (* INV only for the properties on s,
     the one on f won't hold anymore when we switch to reference types (WasmGC), TODO consider
     having INV only depend on s
  *)
  INV s f ->
  (* need more memory *)
  sglob_val s (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
  smem s (f_inst f) = Some m ->
  (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
  ~~ Wasm_int.Int32.lt
       (Wasm_int.Int32.repr
          (Wasm_int.Int32.signed
             (Wasm_int.Int32.iadd (N_to_i32 gmp)
                (N_to_i32 page_size)) ÷ 65536))
       (Wasm_int.Int32.repr (Z.of_N (mem_size m))) = true ->
  exists s', reduce_trans
   (state, s, f, [seq AI_basic i | i <- grow_memory_if_necessary])
   (state, s', f, [])
   /\ s_funcs s = s_funcs s'
   /\ (forall wal val, repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
                       repr_val_LambdaANF_Wasm val s' (f_inst f) wal)
   (* enough memory to alloc. constructor *)
   /\ ((INV s' f /\
       (forall m, smem s' (f_inst f) = Some m ->
          sglob_val s' (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) /\
          (Z.of_N gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z))
       \/ (sglob_val s' (f_inst f) result_out_of_mem = Some (VAL_num (VAL_int32 (N_to_i32 1))))).
Proof with eauto.
  (* grow memory if necessary *)
  intros state sr fr gmp m Hloc Hinv Hgmp Hm HgmpBound HneedMoreMem.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM [? [? [HglobNodup HinvRest]]]]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m' [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
  assert (m = m') by congruence. subst m'.

  assert (global_var_r global_mem_ptr sr fr) as H2.
  { apply global_var_w_implies_global_var_r; auto.
    left; right; right; now constructor.
  }
  have H' := HgmpInM _ _ Hm2 Hgmp HgmpBound.
  (* need to grow memory *)
  destruct (N.leb_spec (size + 1) max_mem_pages); unfold max_mem_pages in *.
  (* grow memory success *)
  assert (mem_size m + 1 <= page_limit)%N. { unfold page_limit. lia. }
  assert (Hsize: (mem_size m + 1 <=? max_mem_pages)%N).
  { subst. apply N.leb_le. now unfold max_mem_pages. }

  have Hgrow := memory_grow_success _ _ _ INVlinmem Hm2 Hsize.
  destruct Hgrow as [s' [size' Hgrow]].
  { eexists. split.
    (* load global_mem_ptr *)
    dostep_nary 0. apply r_global_get. eassumption.
    eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
    apply r_eliml=>//. elimr_nary_instr 0. apply r_local_get. eassumption.
    (* add required bytes *)
    dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
    dostep_nary 2. constructor. apply rs_binop_success. cbn. unfold is_left.
    rewrite zeq_false. reflexivity.
    { (*TODO code duplication *)
      intro HA. unfold Wasm_int.Int32.unsigned, Wasm_int.Int32.iadd, Wasm_int.Int32.add,
                    Wasm_int.Int32.unsigned in HA;
      cbn in HA.
      assert ((Wasm_int.Int32.signed
        (Wasm_int.Int32.repr
           (Wasm_int.Int32.intval (N_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z).
      apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
      have H'' := signed_upper_bound (Wasm_int.Int32.intval (N_to_i32 gmp) + Z.of_N page_size).
      simpl_modulus_in H''. cbn. lia. cbn in H4. lia. }
    dostep. apply r_eliml; auto.
    elimr_nary_instr 0. eapply r_memory_size...
    dostep_nary 2. constructor. apply rs_relop.

    dostep'. constructor. subst.
    rewrite HneedMoreMem. apply rs_if_true. intro H3'. inv H3'.

    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    cbn. apply reduce_trans_label.
    dostep_nary 1. eapply r_memory_grow_success. apply Hgrow.
    dostep_nary 2. constructor. apply rs_relop. cbn.
    dostep'. constructor. apply rs_if_false.

    assert (size >= 0)%N. { subst. cbn. auto. lia. }
    { unfold Wasm_int.Int32.eq. cbn. rewrite zeq_false. reflexivity. intro.
      subst. cbn in *. unfold page_limit in *.
      unfold smem, smem_grow in Hgrow, Hm2.
      rewrite Hm1 in Hgrow, Hm2. cbn in Hgrow.
      destruct (s_mems sr)=>//.
      destruct (mem_grow m0 1)=>//. inv Hgrow. injection Hm2 as ->.
      rewrite Wasm_int.Int32.Z_mod_modulus_id in H5.
      lia. simpl_modulus. cbn. lia. }
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    apply reduce_trans_label. cbn. apply rt_refl.
    intros. split. eapply smem_grow_preserves_funcs; eauto. split.
    { (* value relation preserved *)
      intros.
      unfold smem_grow in Hgrow. rewrite Hm1 in Hgrow, Hm2. cbn in Hgrow.
      destruct (s_mems sr) eqn:Hm'=>//.
      unfold smem in Hm. rewrite Hm1 Hm' in Hm. injection Hm as ->.
      destruct (mem_grow m 1) eqn:Hgrow'=>//. inv Hgrow.
      eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H4.
      - reflexivity.
      - unfold smem. rewrite Hm1 Hm'. reflexivity.
      - unfold smem. rewrite Hm1. reflexivity.
      - eassumption.
      - subst. apply mem_length_upper_bound in Hm5; cbn in Hm5. simpl_modulus; cbn.
        apply mem_grow_increases_length in Hgrow'. lia.
      - rewrite <- Hgmp. reflexivity.
      - subst. apply mem_length_upper_bound in Hm5; cbn in Hm5.
        apply mem_grow_increases_length in Hgrow'. simpl_modulus; cbn; lia.
      - lia.
      - intros. eapply mem_grow_preserves_original_values; eauto; unfold page_limit; lia.
      - intros. eapply mem_grow_preserves_original_values; eauto; unfold page_limit; lia.
    } left. split.
    { (* invariant *)
      eapply sgrow_mem_preserves_INV; eauto. }
    { (* enough memory available *)
      intros. split.
      - erewrite <- smem_grow_peserves_globals; eauto.
      - unfold smem, smem_grow in Hgrow, H4, Hm2.
        rewrite Hm1 in H4, Hgrow, Hm2. cbn in H4, Hgrow, Hm2. rewrite Hm2 in Hgrow.
        destruct (mem_grow m 1) eqn:Hgrow'=>//. inv Hgrow. cbn in H4.
        destruct (s_mems sr)=>//. injection Hm2 as ->. injection H4 as ->.
        apply mem_grow_increases_length in Hgrow'. lia.
    }
  }

  { (* growing memory fails *)
    edestruct INVresM_w as [sr'' HresM].
    eexists. split.
    (* load global_mem_ptr *)
    dostep_nary 0. apply r_global_get. eassumption.
    eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
    apply r_eliml=>//. elimr_nary_instr 0. apply r_local_get. eassumption.
    (* add required bytes *)
    dostep_nary 2. constructor.
    apply rs_binop_success. reflexivity.
    dostep_nary 2. constructor.
    apply rs_binop_success. cbn. unfold is_left.
    rewrite zeq_false. reflexivity.
    { (*TODO code duplication *)
      intro HA. unfold Wasm_int.Int32.unsigned, Wasm_int.Int32.iadd, Wasm_int.Int32.add,
                    Wasm_int.Int32.unsigned in HA;
      cbn in HA.
      assert ((Wasm_int.Int32.signed
        (Wasm_int.Int32.repr  (* arbitrary number *)
           (Wasm_int.Int32.intval (N_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z).
      apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
      have H'' := signed_upper_bound (Wasm_int.Int32.intval (N_to_i32 gmp) + Z.of_N page_size).
      cbn. simpl_modulus_in H''. lia. cbn in H3. lia. }
    dostep. apply r_eliml; auto.
    elimr_nary_instr 0. eapply r_memory_size...

    dostep_nary 2. constructor. apply rs_relop.

    dostep'. constructor. subst. rewrite HneedMoreMem. apply rs_if_true. discriminate.
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    apply reduce_trans_label.
    dostep_nary 1. eapply r_memory_grow_failure; try eassumption.
    { (* TODO cleanup *)
      unfold smem_grow. rewrite Hm1. unfold smem in Hm2. rewrite Hm1 in Hm2. cbn.
      rewrite Hm2. unfold mem_grow.
      destruct ((mem_size m + 1 <=? mem_limit_bound)%N)=>//.
      unfold mem_max_opt in Hm4. rewrite Hm4. subst size.
      destruct ((mem_size m + 1 <=? 30000)%N) eqn:Hcontra=>//.
      apply N.leb_le in Hcontra. lia. }
    dostep_nary 2. constructor. apply rs_relop. cbn.
    dostep'. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    apply reduce_trans_label. cbn.
    dostep_nary' 1. apply r_global_set with (v:=VAL_num (nat_to_value 1)). eassumption. apply rt_refl.
    (* correct resulting environment *)
    split. eapply update_global_preserves_funcs; eassumption.
    split.
    { (* val relation preserved *)
      intros. subst size.
      have Hlength := mem_length_upper_bound _ Hm5.
      unfold page_size, max_mem_pages in Hlength. cbn in Hlength.
      eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H3; eauto.
      - eapply update_global_preserves_funcs. eassumption.
      - erewrite <- update_global_preserves_memory; eassumption.
      - simpl_modulus. cbn. lia.
      - eapply update_global_get_other; try apply HresM; eauto. now intro.
      - simpl_modulus. cbn. lia.
      - lia.
   }
   intros. right. eapply update_global_get_same. eassumption. }
Qed.

Lemma memory_grow_reduce_already_enough_mem : forall state s f gmp m,
  nth_error (f_locs f) 0 = Some (VAL_num (N_to_value page_size)) ->
  (* INV only for the properties on s *)
  INV s f ->
  sglob_val s (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
  smem s (f_inst f) = Some m ->
  (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z ->
  (* already enough memory *)
  ~~ Wasm_int.Int32.lt
       (Wasm_int.Int32.repr
          (Wasm_int.Int32.signed
             (Wasm_int.Int32.iadd (N_to_i32 gmp)
                (N_to_i32 page_size)) ÷ 65536))
       (Wasm_int.Int32.repr (Z.of_N (mem_size m))) = false ->
  exists s', reduce_trans
   (state, s, f, [seq AI_basic i | i <- grow_memory_if_necessary])
   (state, s', f, [])
   /\ s_funcs s = s_funcs s'
   /\ (forall wal val, repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
                       repr_val_LambdaANF_Wasm val s' (f_inst f) wal)
   (* enough memory to alloc. constructor *)
   /\ ((INV s' f /\
       (forall m, smem s' (f_inst f) = Some m ->
          sglob_val s' (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) /\
          (Z.of_N gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z))
       \/ (sglob_val s' (f_inst f) result_out_of_mem = Some (VAL_num (VAL_int32 (nat_to_i32 1))))).
Proof with eauto.
  destruct exists_i32 as [my_i32 _].
  (* grow memory if necessary *)
  intros state sr fr gmp m Hlocs Hinv Hgmp Hm HgmpBound HenoughMem.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmut [INVlinmem [HgmpInM _]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m' [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
  assert (m' = m) by congruence. subst m'.

  have H' := HgmpInM _ _ Hm2 Hgmp HgmpBound.
  (* enough space already *)
  exists sr. split.
  (* load global_mem_ptr *)
  dostep_nary 0. apply r_global_get. eassumption.
  eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
  apply r_eliml=>//. elimr_nary_instr 0. apply r_local_get. eassumption.
  (* add required bytes *)
  dostep_nary 2. constructor.
  apply rs_binop_success. reflexivity.
  dostep_nary 2. constructor.
  apply rs_binop_success. cbn. unfold is_left.
  rewrite zeq_false. reflexivity.
  { (*TODO code duplication *)
    intro HA. unfold Wasm_int.Int32.unsigned, Wasm_int.Int32.iadd, Wasm_int.Int32.add,
                    Wasm_int.Int32.unsigned in HA;
    cbn in HA.
    assert ((Wasm_int.Int32.signed
      (Wasm_int.Int32.repr
           (Wasm_int.Int32.intval (N_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z).
    apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
    have H'' := signed_upper_bound (Wasm_int.Int32.intval (N_to_i32 gmp) + Z.of_N page_size).
    simpl_modulus_in H''. cbn. lia. cbn in H. lia. }
  dostep. apply r_eliml; auto.
  elimr_nary_instr 0. eapply r_memory_size...

  dostep_nary 2. constructor. apply rs_relop.

  dostep'. constructor. subst.
  rewrite HenoughMem. apply rs_if_false. reflexivity.

  dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto. cbn.
  apply reduce_trans_label. apply rt_refl. split. reflexivity. split. auto.
  left. split. assumption.

  (* enough space *)
  { intros. unfold max_mem_pages in *. subst size.
    split. assumption.
    assert (m = m0). { cbn in Hm2. rewrite H in Hm2. now inv Hm2. } subst m0.
    unfold Wasm_int.Int32.lt in HenoughMem.
    destruct (zlt _ _) as [Ha|Ha]. 2: inv HenoughMem. clear HenoughMem.
    unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in Ha. cbn in Ha.

    rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: {
      simpl_modulus. cbn.
      apply mem_length_upper_bound in Hm5; cbn in Hm5. lia. }

    remember (Wasm_int.Int32.signed (Wasm_int.Int32.repr (Z.of_N gmp + 65536)) ÷ 65536)%Z as y.
    unfold Wasm_int.Int32.signed, Wasm_int.Int32.unsigned in Heqy.
    have Hlength := mem_length_upper_bound _ Hm5.
    unfold page_size, max_mem_pages in Hlength. cbn in Hlength.

    rewrite zlt_true in Heqy. 2: {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. lia. simpl_modulus. cbn. lia. }

    unfold Wasm_int.Int32.signed in Heqy. cbn in Heqy.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in Heqy. 2: { simpl_modulus. cbn. lia. }
    cbn in Heqy. replace (Z.of_nat (Pos.to_nat 65536)) with 65536%Z in Heqy by lia.
    rewrite (Z.quot_add (Z.of_N gmp) 1 65536) in Heqy; try lia.

    remember (Wasm_int.Int32.signed
        (Wasm_int.Int32.repr (Z.of_N (mem_size m)))) as n.
    unfold Wasm_int.Int32.signed in Ha.
    subst y. unfold Wasm_int.Int32.signed in Ha. cbn in Ha.

    rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: {
      assert ((Z.of_N gmp ÷ 65536 < 100000)%Z) as H''. { apply Z.quot_lt_upper_bound; lia. }
      simpl_modulus. cbn.
      assert (Z.of_N gmp ÷ 65536  >= 0)%Z. {
        rewrite Zquot.Zquot_Zdiv_pos; try lia. apply Z_div_ge0; lia.
      } lia. }

    rewrite small_signed_repr_n_n in Heqn; last by unfold max_mem_pages; lia.
    unfold Wasm_int.Int32.signed in Heqn. cbn in Heqn.

    (* 100000 arbitrary *)
    assert ((Z.of_N gmp ÷ 65536 < 100000)%Z) as H''. { apply Z.quot_lt_upper_bound; lia. }
    assert (Z.of_N gmp ÷ 65536  >= 0)%Z. { rewrite Zquot.Zquot_Zdiv_pos; try lia.
    apply Z_div_ge0; lia. }

    rewrite zlt_true in Ha; try lia. subst.

    rewrite N2Z.inj_div in Ha.
    cbn in Ha.
    rewrite Zquot.Zquot_Zdiv_pos in Ha; try lia.
    remember (Z.of_N gmp) as q.
    remember (Z.of_N (mem_length m)) as r.

    assert (Hsimpl: (65536 > 0)%Z) by lia.
    edestruct (Zdiv_eucl_exist Hsimpl q) as [[z z0] [H1' H2']].
    rewrite H1' in Ha.
    rewrite (Z.add_comm _ z0) in Ha.
    rewrite Z.mul_comm in Ha.
    rewrite Z.div_add in Ha; try lia.
    rewrite (Zdiv_small z0) in Ha; try lia. cbn in Ha. rewrite H1'.
    edestruct (Zdiv_eucl_exist Hsimpl r) as [[z1 z2] [H1'' H2'']].
    rewrite H1'' in Ha.
    rewrite (Z.add_comm _ z2) in Ha.
    rewrite Z.mul_comm in Ha.
    rewrite Z.div_add in Ha; try lia.
    rewrite (Zdiv_small z2) in Ha; lia.
   }
Qed.

Lemma result_var_i32_glob : i32_glob result_var.
Proof. now constructor. Qed. 

Lemma result_out_of_mem_i32_glob : i32_glob result_out_of_mem.
Proof. right; now constructor. Qed. 

Lemma gmp_i32_glob : i32_glob global_mem_ptr. 
Proof. right; right; now constructor. Qed.

Lemma cap_i32_glob : i32_glob constr_alloc_ptr.
Proof. right; right; right; now constructor. Qed. 

Lemma i32_glob_implies_i32_val : forall sr fr gidx,
    i32_glob gidx ->
    global_var_w gidx sr fr ->
    INV_globals_all_mut sr fr ->
    exists v,
      sglob_val sr (f_inst fr) gidx = Some (VAL_num (VAL_int32 v)).
Proof.
  intros ??? Hi32 Hread Hmut.
  destruct (global_var_w_implies_global_var_r sr fr gidx (or_introl Hi32) Hmut Hread) as [v Hv].
  unfold sglob_val, sglob, sglob_ind in Hv |- *.
  destruct (lookup_N (inst_globals (f_inst fr)) gidx) eqn:Hinst_glob. 2: inv Hv.
  destruct (lookup_N (s_globals sr) g) eqn:Hsr_glob. 2: inv Hv.
  destruct Hmut as [Hmut32 _].
  destruct (Hmut32 gidx g g0 Hi32 Hinst_glob Hsr_glob) as [vi32 Hvi32]. inv Hv. inv H0.
  now exists vi32.
Qed.

Lemma memory_grow_reduce : forall state s f,
  nth_error (f_locs f) 0 = Some (VAL_num (N_to_value page_size)) ->
  (* INV only for the properties on s *)
  INV s f ->
  exists gmp s', reduce_trans
   (state, s, f, [seq AI_basic i | i <- grow_memory_if_necessary])
   (state, s', f, [])
   /\ s_funcs s = s_funcs s'
   /\ (forall wal val, repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
                       repr_val_LambdaANF_Wasm val s' (f_inst f) wal)
   (* enough memory to alloc. constructor *)
   /\ ((INV s' f /\
       (forall m, smem s' (f_inst f) = Some m ->
          sglob_val s' (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) /\
          (Z.of_N gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z))
       \/ (sglob_val s' (f_inst f) result_out_of_mem = Some (VAL_num (VAL_int32 (nat_to_i32 1))))).
Proof with eauto.
  (* grow memory if necessary *)
  intros state sr fr Hlocs Hinv.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmut [INVlinmem [HgmpInM [? ?]]]]]]]]].
  destruct INVlinmem as [Hm1 [m [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
  assert (global_var_r global_mem_ptr sr fr) as H2.
  { apply global_var_w_implies_global_var_r; auto.
  left; right; right; now constructor.
  } 
  destruct H2 as [g Hgmp_r].  
  destruct (i32_glob_implies_i32_val _ _ _ gmp_i32_glob INVgmp_w INVmut) as [g' Hg'].
  destruct (i32_exists_N g') as [gmp [HgmpEq HgmpBound]]. subst g'.
  replace g with (VAL_int32 (N_to_i32 gmp)) in * by now rewrite Hg' in Hgmp_r.
  exists gmp.
  destruct ((~~ Wasm_int.Int32.lt
                 (Wasm_int.Int32.repr
                   (Wasm_int.Int32.signed
                     (Wasm_int.Int32.iadd (N_to_i32 gmp)
                        (N_to_i32 page_size)) ÷ 65536))
                 (Wasm_int.Int32.repr (Z.of_N (mem_size m))))) eqn:HneedMoreMem.
  2: rename HneedMoreMem into HenoughMem.
  { (* need to grow memory *)
    have H' := memory_grow_reduce_need_grow_mem state _ _ _ _ Hlocs
                                  Hinv Hgmp_r Hm2 HgmpBound HneedMoreMem. apply H'. }
  { (* enough space already *)
     have H' := memory_grow_reduce_already_enough_mem state _ _ _ _ Hlocs
                                  Hinv Hgmp_r Hm2 HgmpBound HenoughMem. apply H'. }
Qed.

(* TODO use automation instead *)
Lemma N_to_i32_eq_modulus: forall n m,
  (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z ->
  (-1 < Z.of_N m < Wasm_int.Int32.modulus)%Z ->
  Some (VAL_num (VAL_int32 (N_to_i32 n))) = Some (VAL_num (VAL_int32 (N_to_i32 m))) ->
  n = m.
Proof.
  intros. inv H1. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H3; try lia.
Qed.

Lemma N_to_i32_plus : forall n m x,
  (-1 < Z.of_N x < Wasm_int.Int32.modulus)%Z ->
  (-1 < Z.of_N (n+m) < Wasm_int.Int32.modulus)%Z ->
  Wasm_int.Int32.iadd (N_to_i32 n) (N_to_i32 m) = N_to_i32 x ->
  (m + n = x)%N.
Proof.
  intros. inv H1. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H3; try lia.
  repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
Qed.

Lemma memory_store_preserves_globals (sr : store_record) (fr : frame) :
  forall g gv sr' m,
    sglob_val sr (f_inst fr) g = Some gv ->
    sr' = upd_s_mem sr (set_nth m sr.(s_mems) 0 m) ->
    sglob_val sr' (f_inst fr) g = Some gv.
Proof.
  intros; subst sr'.
  unfold upd_s_mem, sglob_val, sglob, sglob_ind in H |- *; cbn.
  now destruct (lookup_N (inst_globals (f_inst fr))) eqn:Hinstglob.
Qed.

Lemma store_constr_args_reduce {lenv} : forall ys offset vs sargs state rho fds s f m v_cap,
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  INV s f ->
  smem s (f_inst f) = Some m ->
  sglob_val s (f_inst f) constr_alloc_ptr = Some (VAL_num (VAL_int32 (N_to_i32 v_cap))) ->
  (v_cap + page_size < mem_length m)%N ->
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  (-1 < Z.of_nat (length ys + offset) < 2 * max_constr_args)%Z ->
  sglob_val s (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (4 + (4*(N.of_nat offset)) + v_cap)))%N) ->
  Forall_statements_in_seq' (@set_nth_constr_arg fenv nenv lenv) ys sargs offset ->
  get_list ys rho = Some vs ->
  (* from environment relation: ys are available as locals in frame f *)
  (forall y, In y ys -> find_def y fds = None ->
                                  (exists v6 val, M.get y rho = Some v6
                                     /\ @stored_in_locals lenv y val f
                                     /\ repr_val_LambdaANF_Wasm v6 s (f_inst f) val)) ->
  (* correspondence of fenv and fds *)
  (forall y y' v, rho ! y = Some v -> repr_funvar y y' ->
         repr_val_LambdaANF_Wasm v s (f_inst f) (Val_funidx y')) ->
  exists s', reduce_trans
                  (state, s, f, [seq AI_basic i | i <- sargs])
                  (state, s', f, [])
            /\ INV s' f
            (* constructor args val *)
            /\ sglob_val s' (f_inst f) constr_alloc_ptr = Some (VAL_num (VAL_int32 (N_to_i32 v_cap)))
            /\ (0 <= Z.of_N v_cap < Wasm_int.Int32.modulus)%Z
            /\ repr_val_constr_args_LambdaANF_Wasm vs s' (f_inst f) (4 + (4*(N.of_nat offset)) + v_cap)%N
            /\ sglob_val s' (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 ((4 + (4*(N.of_nat offset)) + v_cap) + 4 * N.of_nat (length ys)))))
            /\ s_funcs s = s_funcs s'
            /\ (forall (wal : wasm_value) (val : cps.val),
                    repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
                    repr_val_LambdaANF_Wasm val s' (f_inst f) wal)
            (* previous mem including tag unchanged *)
            /\ exists m', smem s' (f_inst f) = Some m'
                       /\ mem_length m = mem_length m'
                       /\ forall a, (a <= v_cap + 4 * N.of_nat offset)%N -> load_i32 m a = load_i32 m' a.
Proof.
  induction ys; intros offset vs sargs state rho fds s f m v_cap HenvsDisjoint HfenvWf Hinv
                       Hm Hcap Hlen Hargs Hoffset Hgmp H Hvs HmemR HfVal.
  { inv H. inv Hvs. exists s. split. apply rt_refl. split. assumption.
    have I := Hinv. destruct I as [_ [_ [_ [Hgmp_r [Hcap_r [Hmut _]]]]]].    
    destruct (i32_glob_implies_i32_val s f constr_alloc_ptr cap_i32_glob Hcap_r Hmut) as [v Hv].
    edestruct i32_exists_N as [x [Hx ?]]. erewrite Hx in Hv. clear Hx v.
    destruct (i32_glob_implies_i32_val s f global_mem_ptr gmp_i32_glob Hgmp_r Hmut) as [v' Hv'].
    edestruct i32_exists_N as [x' [Hx' ?]]. erewrite Hx' in Hv'. clear Hx' v'.
    split. eassumption.
     have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hinv_linmem _]]]]]]].
    destruct Hinv_linmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
    assert (m = m') by congruence. subst m' size.
    apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
    split. simpl_modulus. cbn. lia. split. econstructor.
    split. rewrite Hgmp. do 4! f_equal. cbn. lia.
    split. auto. split. auto.
    exists m. auto. }
  { inv H. inv H6. rename s' into instr_args. rename a into y.
    destruct vs. { cbn in Hvs. destruct (rho ! y). 2: inv Hvs. destruct (get_list ys rho); inv Hvs. }
    assert (Hgetlist: get_list ys rho = Some vs). {
      cbn in Hvs. destruct (rho ! y). 2: inv Hvs. destruct (get_list ys rho); inv Hvs; auto. }
    assert (Hrhoy: rho ! y = Some v). {
      cbn in Hvs. destruct (rho ! y). 2: inv Hvs.
      destruct (get_list ys rho); inv Hvs; auto. }
    clear Hvs. rename Hgetlist into Hvs.
    (* instr reduces to const related to value *)
    assert (Hinstr: exists wal,
      reduce_trans (state, s, f, [AI_basic instr])
                   (state, s, f, [AI_basic (BI_const_num (VAL_int32 (wasm_value_to_i32 wal)))]) /\
      repr_val_LambdaANF_Wasm v s (f_inst f) wal). {
        inv H. rename i into y'.
      { (* var *)
        assert (Htmp: In y (y :: ys)) by (cbn; auto).
        assert (HfdNone: find_def y fds = None). {
          inv H0. rewrite (HfenvWf_None _ HfenvWf). unfold translate_var in H.
          destruct (lenv ! y) eqn:Hy. rewrite Hy in H. inv H. now apply HenvsDisjoint in Hy. now rewrite Hy in H. }
        destruct (HmemR _ Htmp HfdNone) as [val [wal [Hrho [[y0' [Htv Hly']] Hy_val]]]].
        assert (val = v) by congruence. subst v. clear Hrhoy.
        assert (y' = y0'). { inv H0. congruence. } subst y0'.
        clear Htmp. exists wal.
        split; auto.
        constructor. apply r_local_get with (v:=VAL_num (VAL_int32 (wasm_value_to_i32 wal))); eassumption.
      }
      { (* fun idx *)
        eapply HfVal in Hrhoy; eauto. exists (Val_funidx i). split. apply rt_refl. eassumption.
      }
    }
    destruct Hinstr as [wal [HinstrRed HinstrVal]].
    {
      (* invariants *)
      have I := Hinv. destruct I as [_ [_ [_ [Hinv_gmp [Hinv_cap [Hinv_mut [Hinv_linmem
                                    [Hinv_gmpM [_ [_ [Hinv_nodup _]]]]]]]]]]].
      destruct (i32_glob_implies_i32_val s f constr_alloc_ptr cap_i32_glob Hinv_cap Hinv_mut) as [cap ?].
      destruct (i32_glob_implies_i32_val s f global_mem_ptr gmp_i32_glob Hinv_gmp Hinv_mut) as [gmp ?].
      destruct Hinv_linmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst size.

      assert (m = m') by congruence. subst m'. clear Hmem2.

      destruct (i32_exists_N cap) as [x1 [Hx ?]]. subst cap. rename x1 into cap.
      destruct (i32_exists_N gmp) as [x1 [Hx' ?]]. subst gmp. rename x1 into gmp.
      assert (exists m0, store m (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd
                                   (N_to_i32 v_cap)
                                   (nat_to_i32 (S (S (S (S (offset * 4)))))))) 0%N
                        (bits (VAL_int32 (wasm_value_to_i32 wal))) 4 = Some m0) as Hm0. {
       intros. edestruct enough_space_to_store as [m3 Hstore]. 2: { exists m3.
          replace 4 with (length (bits (VAL_int32 (wasm_value_to_i32 wal)))) by auto.
          apply Hstore. } rewrite N.add_0_r.
       replace ((length (bits (VAL_int32 (wasm_value_to_i32 wal))))) with 4 by reflexivity.
       unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
       remember (S (S (S (S (offset * 4))))) as n.
       have H' := mem_length_upper_bound _ Hmem5. cbn in H'.
       assert (Z.of_nat offset < 2 * max_constr_args)%Z by lia.
       assert (Z.of_nat n + 4 < Z.of_N page_size)%Z. { cbn in H5.
        assert (N.of_nat n < 10000)%N.  lia. cbn. lia. } cbn.
       repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia.
      }

      (* prepare IH *)
      assert (Hmaxargs : (Z.of_nat (length ys) <= max_constr_args)%Z). {
      cbn in Hargs. lia. } clear Hargs.

      assert (Hoff: (length (y :: ys) + offset) = length ys + (S offset)). { cbn. lia. }
      rewrite Hoff in Hoffset. clear Hoff.

      destruct Hm0 as [m0 Hm0].
      remember (upd_s_mem s (set_nth m0 (s_mems s) 0 m0)) as s'.
      (* TODO cleanup *)
      assert (Hm0': smem_store s (f_inst f)
                      (Wasm_int.N_of_uint i32m
                         (Wasm_int.Int32.iadd (N_to_i32 v_cap)
                            (nat_to_i32 (S (S (S (S (offset * 4)))))))) 0%N
                      (VAL_int32 (wasm_value_to_i32 wal)) T_i32 = Some s'). {
       unfold smem_store. remember (nat_to_i32 _) as xdf. rewrite Hmem1.
       unfold smem in Hm. rewrite Hmem1 in Hm. destruct (s_mems s)=>//.
       injection Hm as ->. cbn. cbn in Hm0. rewrite Hm0. subst. reflexivity. }

      assert (Hinv' : INV s' f). {
        eapply update_mem_preserves_INV. 6: subst; reflexivity. assumption. eassumption.
        apply mem_store_preserves_length in Hm0. lia.
        apply mem_store_preserves_max_pages in Hm0. congruence.
        eexists. split. reflexivity.
        apply mem_store_preserves_length in Hm0. unfold mem_size in Hmem5.
        now rewrite Hm0 in Hmem5. }

      have I := Hinv'. destruct I as [_ [_ [_ [Hgmp_w [_ [_ [_ [? [_ [_ [_ [_ [_ [Hgmp_mult_two _]]]]]]]]]]]]]].
      destruct (Hgmp_w (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp) (N_to_i32 4)))) as [s_before_IH ?].
      assert (Hmem_before_IH : smem s_before_IH (f_inst f) = Some m0). {
        subst s'. erewrite <- update_global_preserves_memory; try eassumption.
        cbn. cbn. unfold smem in Hm. rewrite Hmem1 in Hm.
        destruct (s_mems s)=>//. injection Hm as ->. unfold smem. by rewrite Hmem1. }

      assert (Hinv_before_IH : INV s_before_IH f). {
        apply update_global_preserves_INV with (sr:=s') (i:=global_mem_ptr) (num:=VAL_int32 (N_to_i32 (gmp+4))) (m:=m0).
       left; split; [right; right; now constructor|now cbn].
       assumption.
       unfold result_out_of_mem, global_mem_ptr. lia.
       unfold upd_s_mem in Heqs'.
       subst s'.
       unfold smem in Hm |- *. rewrite Hmem1 in Hm |- *. cbn in Hm |- *.
       destruct (s_mems s)=>//. 
       move => _. intros.
       destruct H7 as [Heqn Hnbound].
       assert (gmp+ 4 = n)%N. {
         have H' := Hinv_gmpM _ _ Hm H1 H4.
         assert (Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z. {
           have H'' := mem_length_upper_bound _ Hmem5. unfold max_mem_pages, page_size in H''. simpl_modulus. cbn. lia. }
         inversion Heqn.
         repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H9.
         now rewrite <-N2Z.inj_iff.
         assumption.
         lia. }
       subst n.
       assert (-1 < Z.of_nat (4 + 4 * offset + N.to_nat v_cap) < Wasm_int.Int32.modulus)%Z. {
         cbn in Hoffset. unfold max_constr_args in Hmaxargs.
         unfold page_size in Hlen. cbn in Hlen.
         simpl_modulus. apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
         cbn. lia. }
       assert (Hnats : (N.of_nat (4 + 4 * offset + N.to_nat v_cap) =  (4 + 4 * N.of_nat offset + v_cap))%N). {
         rewrite Nat2N.inj_add.
         rewrite Nat2N.inj_add.         
         rewrite N2Nat.id.
         rewrite Nat2N.inj_mul.
         now replace (N.of_nat 4) with 4%N by now cbn. }
       rewrite -Hnats in Hgmp.
      assert (gmp = N.of_nat (4 + 4 * offset + N.to_nat v_cap))%N. { 
        apply N_to_i32_eq_modulus; auto.        
        now rewrite <-Hgmp. }
      cbn. unfold page_size in Hlen. cbn in Hoffset. 
      rewrite Hnats in H8. 
      subst gmp. 
      apply mem_store_preserves_length in Hm0.
      lia.
      move => _.
      intros.
      replace n with (gmp + 4)%N.
      destruct (Hgmp_mult_two gmp m0) as [n' Htwo]; eauto.
      subst s'. unfold smem in Hm |- *. rewrite Hmem1 in Hm |- *. cbn in Hm |- *.
      destruct (s_mems s)=>//.
      eapply memory_store_preserves_globals; eauto.
      exists (2 + n')%N. lia.
      destruct H7.
      inv H7.
      repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H10; try lia.
      have H' := Hinv_gmpM _ _ Hm H1 H4.
      assert (Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z. {
        have H'' := mem_length_upper_bound _ Hmem5. unfold max_mem_pages, page_size in H''. simpl_modulus. cbn. lia. }
      simpl_modulus. simpl_modulus_in H7. cbn. lia. 
      unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in H6.
      cbn in H6.
      repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H6; try lia.
      replace 4%Z with (Z.of_N 4) in H6 by lia.
      rewrite -N2Z.inj_add in H6. 
      now unfold N_to_i32. } 
      assert (Hcap_before_IH: sglob_val s_before_IH (f_inst f) constr_alloc_ptr = Some (VAL_num (VAL_int32 (N_to_i32 v_cap)))). {
        subst. eapply update_global_get_other; try apply H6; auto. now intro. }

      assert (Hlen_m0: (v_cap + page_size < mem_length m0)%N). {
        apply mem_store_preserves_length in Hm0.
        unfold mem_length, memory_list.mem_length in *. congruence. }

      assert (HrelE_before_IH: (forall y : var,
        In y ys ->
        find_def y fds = None ->
        exists (v6 : cps.val) (val : wasm_value),
          rho ! y = Some v6 /\
          @stored_in_locals lenv y val f /\
          repr_val_LambdaANF_Wasm v6 s_before_IH (f_inst f) val)). {
        intros y0 H7 HfdNone. assert (Htmp : In y0 (y :: ys)) by (right; assumption).
        destruct (HmemR _ Htmp HfdNone) as [val' [wal' [? [? ?]]]].
        subst s'. exists val', wal'. repeat split; try assumption.

        { edestruct i32_exists_N as [? [Hn ?]]. erewrite Hn in H6.
          rewrite H1 in Hgmp.
          assert (-1 < Z.of_nat (4 + 4 * offset + N.to_nat v_cap) < Wasm_int.Int32.modulus)%Z. {
         cbn in Hoffset. unfold max_constr_args in Hmaxargs.
         unfold page_size in Hlen. cbn in Hlen.
         simpl_modulus. apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
         cbn. lia. }

         assert (gmp = N.of_nat (4 + 4 * offset + N.to_nat v_cap))%N. {
           apply N_to_i32_eq_modulus; auto. rewrite Hgmp. do 4! f_equal. lia. }
         clear Hgmp.

         assert ((4 + 4 * N.of_nat offset + v_cap) + 4 = x)%N. {
           assert ((-1 < Z.of_N (4 + 4 * N.of_nat offset + v_cap + 4) < Wasm_int.Int32.modulus)%Z).
             { apply mem_store_preserves_length in Hm0.
               apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
               cbn in Hoffset. unfold page_size in *.
               assert (Z.of_N gmp + 4 < Wasm_int.Int32.modulus)%Z by (simpl_modulus; cbn; lia). lia. }
             apply N_to_i32_plus in Hn; lia. } subst x. clear Hn.

          apply mem_length_upper_bound in Hmem5. cbn in Hmem5. cbn in Hoffset. clear H12.
          unfold page_size in Hlen_m0. cbn in Hlen_m0.
          assert (mem_length m0 = mem_length m). { now apply mem_store_preserves_length in Hm0. }

          eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H10; subst.
          apply update_global_preserves_funcs in H6. rewrite -H6. reflexivity.
          eassumption. eassumption. eassumption.
          have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [INVgmp_M _]]]]]]]].
          have H' := INVgmp_M _ _ Hm H1 H4. simpl_modulus. cbn. lia.
          eapply update_global_get_same in H6. eassumption.
          split; first lia. simpl_modulus. cbn. lia.
          lia.
          intros. assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. lia. } destruct Hex.
          rewrite H14. symmetry. erewrite load_store_load_i32; try apply Hm0; auto.
          unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add. remember (S (S (S (S (offset * 4))))) as n.
          cbn. subst.
          repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id); try lia.
          intros. assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64. lia. } destruct Hex.
          rewrite H14. symmetry. erewrite load_store_load_i64; try apply Hm0; auto.
          unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add. remember (S (S (S (S (offset * 4))))) as n.
          cbn. subst.
          repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id); try lia. }
      }
      assert (Hgmp_before_IH: sglob_val s_before_IH (f_inst f) global_mem_ptr =
  Some (VAL_num (VAL_int32 (N_to_i32 (4 + 4 * N.of_nat (S offset) + v_cap))))). {
        subst.
        apply update_global_get_same in H6. rewrite H6. f_equal. f_equal.

        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add. unfold N_to_i32. repeat f_equal.
        remember (Z.of_N (4 + 4 * N.of_nat (S offset) + v_cap)) as x. cbn.
        rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. unfold nat_to_i32. f_equal.
        assert ((-1 < Z.of_nat (4 + 4 * offset + N.to_nat v_cap) < Wasm_int.Int32.modulus)%Z). {
          cbn in Hoffset. unfold page_size in Hlen_m0. cbn in Hlen_m0.
          unfold max_constr_args in Hmaxargs.
          apply mem_store_preserves_length in Hm0.
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
          split; try lia. simpl_modulus. cbn. lia. }
        rewrite Hgmp in H1. apply N_to_i32_eq_modulus in H1; try lia.
      }

     assert (HfVal_before_IH: (forall (y : positive) (y' : funcidx) (v : cps.val),
       rho ! y = Some v -> repr_funvar y y' ->
       repr_val_LambdaANF_Wasm v s_before_IH (f_inst f) (Val_funidx y'))).
     { intros. have H' := HfVal _ _ _ H7 H8.
       eapply val_relation_func_depends_on_funcs; last apply H'. subst.
       now apply update_global_preserves_funcs in H6. }

      have IH := IHys _ _ _ state _ _ _ _ _ _ HenvsDisjoint HfenvWf Hinv_before_IH Hmem_before_IH
                 Hcap_before_IH Hlen_m0 Hmaxargs Hoffset Hgmp_before_IH H3 Hvs HrelE_before_IH HfVal_before_IH.
      clear IHys Hmem_before_IH Hinv_before_IH HrelE_before_IH Hcap_before_IH.
      destruct IH as [sr [Hred [Hinv'' [Hv1 [? [Hv2 [? [? [? [m1 [Hm1 [? ?]]]]]]]]]]]].
      assert (sglob_val s (f_inst f) constr_alloc_ptr
            = sglob_val (upd_s_mem s (set_nth m0 (s_mems s) 0 m0)) (f_inst f) constr_alloc_ptr)
      as Hglob_cap by reflexivity.
      have HlenBound := mem_length_upper_bound _ Hmem5. cbn in HlenBound.

      rewrite H0 in Hcap. apply N_to_i32_eq_modulus in Hcap; try lia. subst v_cap.
      eexists. split.
      (* reduce *)
      dostep_nary 0. apply r_global_get. rewrite Hglob_cap. eassumption.
      dostep_nary 2. constructor. constructor. reflexivity.
      eapply rt_trans. apply app_trans_const; auto. apply app_trans. eassumption.

      dostep_nary 2. eapply r_store_success; eassumption.
      dostep_nary 0. apply r_global_get. subst s'. eassumption.
      dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
      dostep_nary 1. apply r_global_set with (v:=VAL_num (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp) (nat_to_i32 4)))). subst. eassumption.
      apply Hred.
      split. assumption. split. assumption. split. simpl_modulus. cbn. lia. split.
      econstructor. apply Hm1. eassumption. { simpl_modulus.
        apply mem_length_upper_bound in Hmem5. cbn in Hmem5, Hoffset.
        remember (Z.of_N (4 + 4 * N.of_nat (S offset) + cap + 4 * N.of_nat (Datatypes.length ys))) as ndfs'. cbn. subst. lia. } lia.

      { (* load val *)
        rewrite -H12; try lia.
        apply store_load_i32 in Hm0=>//.
        assert ((4 + 4 * N.of_nat offset + cap)%N =
                (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (N_to_i32 cap)
                            (nat_to_i32 (S (S (S (S (offset * 4))))))))) as Har. {
          remember (S (S (S (S (offset * 4))))) as o.
          remember ((4 + 4 * N.of_nat offset + cap)%N) as o'. cbn.
          assert (Z.of_nat offset < 2 * max_constr_args)%Z as HarOffset by lia. cbn in HarOffset.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
      }
        rewrite deserialise_bits in Hm0=>//. rewrite Har. eassumption. }

      { rewrite H1 in Hgmp.
        assert ((-1 < Z.of_nat (4 + 4 * offset + N.to_nat cap) < Wasm_int.Int32.modulus)%Z). {
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          cbn in Hoffset. simpl_modulus. cbn. lia. }
        apply N_to_i32_eq_modulus in Hgmp; auto. subst gmp.

        apply H10.
        eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s);
          try apply Hy_val; try eassumption.
        - subst. apply update_global_preserves_funcs in H6. cbn in H6. congruence.
        - apply update_global_preserves_memory in H6. rewrite <- H6.
          cbn. unfold smem. rewrite Hmem1. cbn. subst s'.
          unfold smem in Hm. by destruct (s_mems s).
        - have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [Hgmp_M _]]]]]]]].
          have H' := Hgmp_M _ _ Hm H1 H4. apply mem_length_upper_bound in Hmem5.
          cbn in Hmem5. simpl_modulus. cbn. cbn in H'. lia.
        - simpl_modulus. cbn in Hoffset. unfold max_constr_args in Hmaxargs.
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          apply mem_store_preserves_length in Hm0.
          remember (4 + 4 * N.of_nat (S offset) + cap)%N as nfd. cbn. lia.
        - lia.
        - intros.
          assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load.
            unfold page_size in Hlen; cbn in Hlen. cbn in Hoffset. lia.
          } destruct Hex.
          symmetry. erewrite load_store_load_i32; try apply Hm0 ; eauto.
          remember (S (S (S (S (offset * 4))))) as n. cbn in Hoffset. cbn.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
        - intros.
          assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64.
            unfold page_size in Hlen; cbn in Hlen. cbn in Hoffset. lia.
          } destruct Hex.
          symmetry. erewrite load_store_load_i64; try apply Hm0 ; eauto.
          remember (S (S (S (S (offset * 4))))) as n. cbn in Hoffset. cbn.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. lia.
      }

      (* TODO: contains duplication: cleanup *)
      replace (4 + (4 + 4 * N.of_nat offset + cap))%N with (4 + 4 * N.of_nat (S offset) + cap)%N by lia.
      apply Hv2.
      split. subst. auto. rewrite H8. do 4! f_equal.
      replace (4 + 4 * N.of_nat (S offset) + cap)%N with (4 + (4 + 4 * N.of_nat offset + cap))%N by lia.
       remember (4 + 4 * N.of_nat offset + cap)%N as m'.
       replace (Datatypes.length (y :: ys)) with (1 + (Datatypes.length ys)) by now cbn. lia.
      split. apply update_global_preserves_funcs in H6. subst s'. cbn in H6. congruence.
      split. {
        intros. apply H10.
        assert (Heq: N_to_i32 gmp = (N_to_i32 (4 + 4 * N.of_nat offset + cap))%N) by congruence.
        assert ((-1 < Z.of_N (4 + 4 * N.of_nat offset + cap) < Wasm_int.Int32.modulus)%Z).
        { cbn in Hoffset. unfold max_constr_args in Hmaxargs.
          remember (4 + 4 * N.of_nat offset + cap)%N as ndf. simpl_modulus. cbn. lia. }
        assert (Htmp: (Some (VAL_num (VAL_int32 (N_to_i32 gmp))) =
                       Some (VAL_num (VAL_int32 (N_to_i32 (4 + 4 * N.of_nat offset + cap)))))%N) by congruence.

        apply N_to_i32_eq_modulus in Htmp; auto. subst gmp.

        eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H13;
          try eassumption.
        - apply update_global_preserves_funcs in H6. subst s'. cbn in H6.
          congruence.
        - apply update_global_preserves_memory in H6. rewrite <- H6.
          unfold smem. rewrite Hmem1. unfold smem in Hm. rewrite Hmem1 in Hm.
          destruct (s_mems s)=>//. subst s'. reflexivity.
        - have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [Hgmp_M _]]]]]]]].
          have H' := Hgmp_M _ _ Hm H1 H4. apply mem_length_upper_bound in Hmem5.
          cbn in Hmem5. remember (4 + 4 * N.of_nat offset + cap)%N as df. simpl_modulus. cbn. lia.
        - simpl_modulus. cbn in Hoffset. unfold max_constr_args in Hmaxargs.
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          apply mem_store_preserves_length in Hm0.
          remember (Z.of_N (4 + 4 * N.of_nat (S offset) + cap)) as mdf. cbn. lia.
        - lia.
        { intros.
          assert (Hex: exists v, load_i32 m a = Some v). {
          have Hm0'' := Hm0.
          apply enough_space_to_load. unfold store in Hm0''.
          destruct ((Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (N_to_i32 cap)
                        (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 +
                   N.of_nat 4 <=? mem_length m)%N) eqn:Har. 2: inv Hm0''.
             cbn in Hoffset. apply mem_store_preserves_length in Hm0.
             unfold page_size in Hlen_m0. lia. } destruct Hex.
          assert (Har: (a + 4 <=
              Wasm_int.N_of_uint i32m
                (Wasm_int.Int32.iadd (N_to_i32 cap)
                   (nat_to_i32 (S (S (S (S (offset * 4))))))))%N). {
            unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
            remember ((S (S (S (S (offset * 4)))))) as o. cbn.
            cbn in Hoffset.
            repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia. }

          have Ht := load_store_load_i32 _ _ _ _ _ _ _ Har H16 Hm0.
          clear Har. rewrite Ht; auto. }
        { intros.
          assert (Hex: exists v, load_i64 m a = Some v). {
            have Hm0'' := Hm0.
            apply enough_space_to_load_i64. unfold store in Hm0''.
            destruct ((Wasm_int.N_of_uint i32m
             (Wasm_int.Int32.iadd (N_to_i32 cap)
                (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 +
           N.of_nat 4 <=? mem_length m)%N) eqn:Har. 2: inv Hm0''.
            cbn in Hoffset. apply mem_store_preserves_length in Hm0.
            unfold page_size in Hlen_m0. lia. } destruct Hex.
          assert (Har: (a + 8 <=
                          Wasm_int.N_of_uint i32m
                            (Wasm_int.Int32.iadd (N_to_i32 cap)
                               (nat_to_i32 (S (S (S (S (offset * 4))))))))%N). {
            unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
            remember ((S (S (S (S (offset * 4)))))) as o. cbn.
            cbn in Hoffset.
            repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. }

          have Ht := load_store_load_i64 _ _ _ _ _ _ _ Har H16 Hm0.
          clear Har. rewrite Ht; auto. }
      }

      exists m1. split. assumption.
      split. apply mem_store_preserves_length in Hm0. congruence.
      { intros.
        assert (exists v, load_i32 m a = Some v). {
          have Hm0'' := Hm0.
          apply enough_space_to_load. unfold store in Hm0''.
          destruct ((Wasm_int.N_of_uint i32m
             (Wasm_int.Int32.iadd (N_to_i32 cap)
                (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 +
           N.of_nat 4 <=? mem_length m)%N) eqn:Har. 2: inv Hm0''.
             cbn in Hoffset. apply mem_store_preserves_length in Hm0.
             unfold page_size in Hlen_m0. lia.
        } destruct H14. rewrite -H12; try lia.

        cbn in Hoffset. unfold max_constr_args in Hmaxargs.
        symmetry. erewrite load_store_load_i32; try apply Hm0; eauto.
        remember (S (S (S (S (offset * 4))))) as n.
        cbn. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia. } } }
Qed.

Lemma store_constr_reduce {lenv} : forall state s f rho fds ys (vs : list cps.val) t n sargs m gmp_v ord,
    get_ctor_ord cenv t = Ret ord ->
  get_ctor_arity cenv t = Ret n ->
  n > 0 ->
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  INV s f ->
  (* enough memory available *)
  smem s (f_inst f) = Some m ->
  sglob_val s (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
  (Z.of_N gmp_v + Z.of_N page_size < Z.of_N (mem_length m))%Z ->
  (* from memory relation: ys available as local vars *)
  (forall y : var,
         In y ys ->
         find_def y fds = None ->
         exists (v6 : cps.val) (val : wasm_value),
           rho ! y = Some v6 /\
           @stored_in_locals lenv y val f /\
           repr_val_LambdaANF_Wasm v6 s (f_inst f) val) ->
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  Forall_statements_in_seq (@set_nth_constr_arg fenv nenv lenv) ys sargs ->
  get_list ys rho = Some vs ->

  (* function indices: value relation *)
  (forall (y : positive) (y' : funcidx) (v : cps.val),
         rho ! y = Some v ->
         repr_funvar y y' ->
         repr_val_LambdaANF_Wasm v s (f_inst f) (Val_funidx y')) ->

  exists s', reduce_trans
    (state, s, f,
      [:: AI_basic (BI_global_get global_mem_ptr)] ++
      [:: AI_basic (BI_global_set constr_alloc_ptr)] ++
      [:: AI_basic (BI_global_get constr_alloc_ptr)] ++
      [:: AI_basic (BI_const_num (nat_to_value (N.to_nat ord)))] ++
      [:: AI_basic (BI_store T_i32 None 2%N 0%N)] ++
      [:: AI_basic (BI_global_get global_mem_ptr)] ++
      [:: AI_basic (BI_const_num (nat_to_value 4))] ++
      [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add))] ++
      [:: AI_basic (BI_global_set global_mem_ptr)] ++
      [seq AI_basic i | i <- sargs]) (state, s', f, []) /\
    INV s' f /\
    s_funcs s = s_funcs s' /\
    (forall (wal : wasm_value) (val : cps.val),
      repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
      repr_val_LambdaANF_Wasm val s' (f_inst f) wal) /\
      (* cap points to value *)
    (exists cap_v wasmval, sglob_val s' (f_inst f) constr_alloc_ptr = Some (VAL_num (VAL_int32 cap_v))
          /\ wasm_value_to_i32 wasmval = cap_v
          /\ repr_val_LambdaANF_Wasm (Vconstr t vs) s' (f_inst f) wasmval).
Proof.
  intros ????????????? HordSome HarrSome HarrGt0 HenvsDisjoint HfenvWf Hinv HenoughM1 HenoughM2 HenoughM3
                      HmemR Hmaxargs Hsetargs Hrho HfVal.

  have I := Hinv. destruct I as [_ [_ [_ [INVgmp_w [INVcap_w [INVmut [INVmem [_ [_ [_ [INV_instglobs [_ [_ [INV_gmp_mult_two _]]]]]]]]]]]]]].
  have INVgmp_r := global_var_w_implies_global_var_r _ _ _ (or_introl gmp_i32_glob) INVmut INVgmp_w.

  assert(HgmpBound: (-1 < Z.of_N gmp_v < Wasm_int.Int32.modulus)%Z). {
    destruct INVmem as [Hmem1 [m' [Hmem2 [? [<- [Hmem4 Hmem5]]]]]]. solve_eq m m'.
    apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
    simpl_modulus. cbn. simpl_modulus_in HenoughM3. lia. }

  destruct (INV_gmp_mult_two gmp_v m) as [n0 Hgmp_mult_two]; eauto. clear INV_gmp_mult_two.
  (* invariants after set_global cap *)
  destruct (INVcap_w (VAL_int32 (N_to_i32 gmp_v))) as [s' ?]. clear INVcap_w.
  (* INV after set_global cap *)
  assert (INV s' f) as Hinv'. {
    eapply update_global_preserves_INV; try apply H; auto.
    left. split. right; right; right; now constructor. now cbn.
    unfold result_out_of_mem, constr_alloc_ptr.
    lia.
    eassumption.
    all: intros Hcontra; inv Hcontra. }

   have I := Hinv'. destruct I as [_ [_ [_ [_ [INVcap_w'' [INVmut'' [INVlinmem'' _ ]]]]]]].

  (* invariants mem *)
  edestruct INVlinmem'' as [Hmem1'' [m' [Hmem2'' [size'' [Hmem3'' [Hmem4'' Hmem5'']]]]]].
  assert (m' = m). { apply update_global_preserves_memory in H. congruence. } subst m' size''.

  assert (exists mem, store m (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                              (bits (nat_to_value (N.to_nat ord)))
                              4 = Some mem) as Htest.
  { apply enough_space_to_store. cbn.
    assert ((Datatypes.length (serialise_i32 (nat_to_i32 (N.to_nat ord)))) = 4) as Hl.
    { unfold serialise_i32, encode_int, bytes_of_int, rev_if_be.
      destruct (Archi.big_endian); reflexivity. } rewrite Hl. clear Hl. cbn.
    rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
    destruct Hinv' as [_ [_ [_ [_ [_ [_ [Hlinmem [INVgmp_M _]]]]]]]].
    destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].

    assert (m' = m) by congruence. subst m'.
    assert (Hgmp_r : sglob_val s' (f_inst f) global_mem_ptr =
              Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))). { eapply update_global_get_other; try eassumption.
               unfold global_mem_ptr, constr_alloc_ptr. lia. }
    have Htest := INVgmp_M _ _ Hmem2 Hgmp_r. lia. }
  destruct Htest as [m' Hstore].
  remember (upd_s_mem s' (set_nth m' s'.(s_mems) 0 m')) as s_tag.
  assert (Hstore' : smem_store s' (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v))
                    0%N (nat_to_value (N.to_nat ord)) T_i32 = Some s_tag). {
    unfold smem_store. rewrite Hmem1''. cbn.
    unfold smem in Hmem2''. rewrite Hmem1'' in Hmem2''. destruct (s_mems s')=>//.
    injection Hmem2'' as ->. rewrite Hstore. subst s_tag. reflexivity. }

  assert (Hinv_tag : INV s_tag f). { subst.
    assert (mem_length m = mem_length m'). { apply mem_store_preserves_length in Hstore. congruence. }
    assert (mem_max_opt m = mem_max_opt m'). { apply mem_store_preserves_max_pages in Hstore. congruence. }
    eapply update_mem_preserves_INV. apply Hinv'. eassumption. erewrite <- H0. lia.
    congruence. exists (mem_size m); split; auto. unfold mem_size. congruence. reflexivity. }

  have I := Hinv_tag. destruct I as [_ [_ [_ [Hgmp_w _]]]].
  destruct (Hgmp_w (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 4)))) as [s_before_args ?].
  edestruct i32_exists_N as [gmp [HgmpEq HgmpBound']].
  erewrite HgmpEq in H0.
  assert (gmp = gmp_v + 4)%N. {
    inversion HgmpEq. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H2; try lia.
    unfold store in Hstore.
    destruct ((Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) + 0 +
            N.of_nat 4 <=? mem_length m)%N) eqn:Har. 2: inv Hstore.
    apply N.leb_le in Har. cbn in Har.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in Har; try lia.
    apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
    rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
    simpl_modulus. cbn. lia.
  } subst gmp.

 (* INV after set_global gmp *)
  assert (Hinv_before_args : INV s_before_args f). {
    eapply update_global_preserves_INV with (num:=(VAL_int32 (N_to_i32 (gmp_v + 4)))) (i:=global_mem_ptr).
    left; split; [right; right; now constructor|now cbn].
    eassumption. unfold result_out_of_mem, global_mem_ptr. lia.
    subst s_tag. unfold smem. rewrite Hmem1''. cbn. destruct (s_mems s')=>//.
    move => _. intros n1 [Heqn1 Hrangen1].
    unfold page_size in HenoughM3; cbn in HenoughM3.
    replace n1 with (gmp_v + 4)%N. 
    apply mem_store_preserves_length in Hstore. lia.
    inversion Heqn1.
    repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H2; try lia.
    move => _. intros n1 [Heqn1 Hrangen1].
    inv Heqn1.
    replace n1 with (2 * n0 + 4)%N. 
    exists (2 + n0)%N. lia.
    repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H2; try lia.
    assumption. }

  assert (Hmem: smem s_before_args (f_inst f) = Some m'). { subst s_tag. cbn.
    apply update_global_preserves_memory in H0. rewrite -H0. cbn.
    unfold smem. rewrite Hmem1''. by destruct (s_mems s')=>//. }
  assert (Hglob_cap: sglob_val s_before_args (f_inst f) constr_alloc_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))). {
    subst.
    replace (sglob_val (upd_s_mem s' (set_nth m' (s_mems s') 0 m')) (f_inst f) constr_alloc_ptr)
       with (sglob_val s' (f_inst f) constr_alloc_ptr) by reflexivity.
    apply update_global_get_same in H.
    eapply update_global_get_other in H0; eauto. now intro. }
  assert (HenoughM': (gmp_v + page_size < mem_length m')%N). {
    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
    destruct Hlinmem as [Hmem1 [m'' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
    assert (mem_length m = mem_length m'). {
      apply mem_store_preserves_length in Hstore.
      apply update_global_preserves_memory in H0, H.
      assert (m = m'') by congruence. subst m''. congruence. }
    lia.
   }

  assert (HlenBound: (-1 < Z.of_nat (Datatypes.length ys + 0) < 2 * max_constr_args)%Z). {
    rewrite Nat.add_0_r. cbn. unfold max_constr_args in Hmaxargs. lia. }

  assert (HrelE': forall y : var,
    In y ys ->
    find_def y fds = None ->
    exists (v6 : cps.val) (val : wasm_value),
      rho ! y = Some v6 /\
      @stored_in_locals lenv y val f /\
      repr_val_LambdaANF_Wasm v6 s_before_args (f_inst f) val). {
    intros y Hy Hfd. apply HmemR in Hy; auto. destruct Hy as [val [wal [Hrho' [Hylocal Hval]]]].
    exists val, wal. repeat (split; auto).

    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply Hval.
    { subst. apply update_global_preserves_funcs in H, H0. cbn. subst.
      assert (s_funcs (upd_s_mem s' (set_nth m' (s_mems s') 0 m')) = s_funcs s') by reflexivity. congruence. }
    { erewrite update_global_preserves_memory. 2: eassumption. eassumption. }
    { apply update_global_preserves_memory in H0. subst. rewrite <- H0. cbn.
      unfold smem. rewrite Hmem1''. by destruct (s_mems s')=>//. }
    { eassumption. }
    { apply mem_store_preserves_length in Hstore.
      subst. apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
      simpl_modulus. simpl_modulus_in HenoughM'. unfold page_size in HenoughM'. cbn. lia. }
    { subst. eapply update_global_get_same. eassumption. }
    { cbn in HlenBound. rewrite Nat.add_0_r in HlenBound.
      simpl_modulus_in HenoughM'. cbn in HenoughM'. unfold page_size in HenoughM'.
      remember (Z.of_N (2 * n0 + 4) + 8 <= Z.of_N (mem_length m'))%Z as jklj. simpl_modulus. cbn. subst.
      apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''. apply mem_store_preserves_length in Hstore.
      lia. }
    { lia. }
    { intros.
      assert (Hv: exists v, load_i32 m a = Some v). { apply enough_space_to_load. subst.
        simpl_modulus_in HenoughM'. apply mem_store_preserves_length in Hstore. lia. }
      destruct Hv as [? Hv].
      assert (load_i32 m' a = Some x). { eapply load_store_load_i32 ; try apply Hstore; eauto. cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. } congruence. }
    { intros.
      assert (Hv: exists v, load_i64 m a = Some v). { apply enough_space_to_load_i64. subst.
        simpl_modulus_in HenoughM'. apply mem_store_preserves_length in Hstore. lia. }
      destruct Hv as [? Hv].
      assert (load_i64 m' a = Some x). { eapply load_store_load_i64 ; try apply Hstore; eauto. cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. } congruence. }
  }

  assert (Hgmp_before_args : sglob_val  s_before_args (f_inst f) global_mem_ptr =
        Some (VAL_num (VAL_int32 (N_to_i32 (4 + gmp_v)%N)))).
  { apply update_global_get_same in H0. rewrite H0. do 4! f_equal. lia. }

  assert (HfVal_before_args: (forall (y : positive) (y' : funcidx) (v : cps.val),
         rho ! y = Some v ->
         repr_funvar y y' ->
         repr_val_LambdaANF_Wasm v s_before_args (f_inst f) (Val_funidx y'))).
  { intros. have H' := HfVal _ _ _ H1 H2.
    eapply val_relation_func_depends_on_funcs; last eassumption.
    apply update_global_preserves_funcs in H, H0. subst. now cbn in H0.
  }

  have Hargs := store_constr_args_reduce _ _ _ _ state _ _ _ _ _ _ HenvsDisjoint HfenvWf
                  Hinv_before_args Hmem Hglob_cap HenoughM' Hmaxargs HlenBound Hgmp_before_args
                    Hsetargs Hrho HrelE' HfVal_before_args.
  destruct Hargs as [s_final [Hred [Hinv_final [Hcap_v [? [Hargs_val [Hglobsame
                    [Hfuncs [HvalPreserved [m'' [Hm' [Hmemlen Hmemsame]]]]]]]]]]]].
  {
  cbn in Hargs_val. clear Hsetargs Hrho HenoughM' HlenBound.

  exists s_final. split.
  (* steps *)
  dostep_nary 0. apply r_global_get. eassumption.
  dostep_nary 1. apply r_global_set with (v:=VAL_num (VAL_int32 (N_to_i32 gmp_v))). eassumption. cbn.
  dostep_nary 0. apply r_global_get. eapply update_global_get_same. eassumption.
  (* write tag *)
  dostep_nary 2. eapply r_store_success. eassumption.
  dostep_nary 0. apply r_global_get. {
    subst s_tag. replace (sglob_val (upd_s_mem s' (set_nth m' (s_mems s') 0 m')))
                    with (sglob_val s') by reflexivity.
    eapply update_global_get_other with (j:= constr_alloc_ptr). assumption. now intro.
    2: eassumption. eassumption. }

  dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
  dostep_nary 1. apply r_global_set with (v:=VAL_num (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 4)))). subst. rewrite HgmpEq. eassumption.
  cbn. apply Hred. split. assumption.
  split. apply update_global_preserves_funcs in H, H0. subst s_tag. cbn in H0. congruence.
  split. {
    intros.
    assert (Hmeq: mem_length m = mem_length m') by
      apply mem_store_preserves_length in Hstore=>//.
    unfold page_size in HenoughM3; cbn in HenoughM3.
    apply HvalPreserved.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H2; eauto.
    apply update_global_preserves_funcs in H, H0. subst. cbn in H0. congruence.
    apply mem_length_upper_bound in Hmem5''; cbn in Hmem5''. simpl_modulus; cbn; lia.
    apply mem_store_preserves_length in Hstore.
    apply mem_length_upper_bound in Hmem5''; cbn in Hmem5''.
    split; try lia. simpl_modulus; cbn; lia.
    lia.

    { intros. assert (exists v, load_i32 m a = Some v). {
        apply enough_space_to_load. unfold store in Hstore.
        destruct ((Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) + 0 + N.of_nat 4 <=?
            mem_length m)%N%N). 2: inv Hstore. lia. } destruct H4.
      symmetry. erewrite load_store_load_i32; try apply Hstore; eauto.
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
    { intros. assert (exists v, load_i64 m a = Some v). {
        apply enough_space_to_load_i64. unfold store in Hstore.
        destruct ((Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) + 0 +
            N.of_nat 4 <=?
            mem_length m)%N). 2: inv Hstore. lia. } destruct H4.
      symmetry. erewrite load_store_load_i64; try apply Hstore; eauto.
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
  }
  (* constr value in memory *)
  eexists. eexists. split. eassumption.
  split.
  assert (wasm_value_to_i32 (Val_ptr gmp_v) = N_to_i32 gmp_v) by reflexivity. eassumption.
  econstructor; try eassumption. {
    assert (Hm'': smem s (f_inst f) = Some m).
    erewrite update_global_preserves_memory; eassumption.
    apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
    unfold page_size in HenoughM3; cbn in HenoughM3.
    unfold max_constr_args in Hmaxargs.
    remember ((4 + 4 * N.of_nat 0 + gmp_v + 4 * N.of_nat (Datatypes.length ys)))%N as dfd.
    simpl_modulus. cbn. lia. }
  lia. exists n0. auto.
  reflexivity.
  apply store_load_i32 in Hstore.
  rewrite deserialise_bits in Hstore; auto.
  assert ((Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) = gmp_v) as Heq. {
  unfold nat_to_i32. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
  rewrite Heq in Hstore.
  unfold nat_to_value in Hstore.
  unfold nat_to_i32 in Hstore.
  rewrite -Hmemsame. eassumption. lia. reflexivity. }
Qed.


Inductive const_val_list : list cps.val -> store_record -> frame -> list u32 -> Prop :=
  | CV_nil  : forall s f, const_val_list [] s f []
  | CV_cons : forall s f v vs n w ns,
       repr_val_LambdaANF_Wasm v s (f_inst f) w ->
       n = wasm_value_to_u32 w ->
       const_val_list vs s f ns ->
       const_val_list (v::vs) s f (n::ns).

Lemma map_const_const_list : forall args,
  const_list [seq AI_basic (BI_const_num (N_to_value a)) | a <- args].
Proof.
  induction args; auto.
Qed.

Lemma const_val_list_length_eq : forall vs s f ns,
  const_val_list vs s f ns -> length vs = length ns.
Proof.
  induction vs; intros.
  - inv H. reflexivity.
  - cbn. inv H. erewrite IHvs; eauto. reflexivity.
Qed.

Lemma const_val_list_nth_error : forall vs s f ns v j,
  const_val_list vs s f ns ->
  nth_error vs j = Some v ->
  exists w, repr_val_LambdaANF_Wasm v s (f_inst f) w /\
            nth_error [seq (VAL_num (N_to_value i)) | i <- ns] j =
               Some (VAL_num (VAL_int32 (wasm_value_to_i32 w))).
Proof.
  induction vs; intros.
  - destruct j; inv H0.
  - inv H. destruct j.
    { (* j=0*)
      inv H0. cbn.
      intros. exists w. eauto. }
    { (* j=S j'*)
      cbn. eapply IHvs; eauto. }
Qed.

Lemma rel_env_app_letapp {lenv} : forall f t ys rho sr fr fds x e,
  @rel_env_LambdaANF_Wasm lenv (Eletapp x f t ys e) rho sr fr fds ->
  @rel_env_LambdaANF_Wasm lenv (Eapp f t ys) rho sr fr fds.
Proof.
  intros ? ? ? ? ? ? ? ? ? [Hfun1 [Hfun2 Hvar]]. split; auto. split; auto.
  intros x' Hocc Hfd.
  assert (Hocc': occurs_free (Eletapp x f t ys e) x'). { inv Hocc; constructor; cbn; auto. }
  now destruct (Hvar _ Hocc' Hfd) as [v' [w [Hrho [Hloc Hval]]]].
Qed.

Lemma fun_args_reduce {lenv} : forall state fr sr fds (ys : seq cps.var) rho vs f t args_instr,
  INV sr fr ->
  get_list ys rho = Some vs ->
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  (forall a v, rho ! a = Some v -> find_def a fds <> None -> v = Vfun (M.empty cps.val) fds a) ->
  @rel_env_LambdaANF_Wasm lenv (Eapp f t ys) rho sr fr fds ->
  @repr_fun_args_Wasm fenv nenv lenv ys args_instr ->
  exists args,
    reduce_trans (state, sr, fr, map AI_basic args_instr)
                 (state, sr, fr, (map (fun a => AI_basic (BI_const_num (N_to_value a))) args))
    /\ const_val_list vs sr fr args.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? Hinv Hgetlist HenvsDisjoint HfenvWf HfenvRho HrelE Hargs.
  generalize dependent f. generalize dependent rho. generalize dependent sr.
  revert vs t fr state. induction Hargs; intros.
  { inv Hgetlist. exists []. cbn. split. apply rt_refl. constructor. }
  { (* var *) destruct vs.
    { cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist. }
    assert (HrelE': @rel_env_LambdaANF_Wasm lenv (Eapp f t args) rho sr fr fds). {
          destruct HrelE as [Hfun1 [Hfun2 Hvar]]. split. assumption. split. assumption.
          intros. assert (Hocc : (occurs_free (Eapp f t (a :: args)) x)). {
          inv H0. constructor. constructor. right. assumption.  }
           destruct (Hvar _ Hocc) as [val [wal [Hrho' [Hlocals Hval]]]]; auto. }
    assert (Hgetlist': get_list args rho = Some vs). {
      cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
    assert (Ha: rho ! a = Some v). {
      cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto.
    }
    have IH := IHHargs _ _ _ state _ Hinv _ Hgetlist' HfenvRho _ HrelE'.
    destruct IH as [args' [Hred HconstL]].
    unfold rel_env_LambdaANF_Wasm in HrelE.

    destruct HrelE as [_ [_ Hvar]].
    assert (Hocc: occurs_free (Eapp f t (a :: args)) a). { constructor. cbn. auto. }
    assert (Hf: find_def a fds = None). { apply HfenvWf_None with (f:=a) in HfenvWf.
      rewrite HfenvWf. inv H. unfold translate_var in H0.
      destruct (lenv ! a) eqn:Ha'; rewrite Ha' in H0; inv H0.
      now apply HenvsDisjoint in Ha'. }
    destruct (Hvar _ Hocc Hf) as [val [wal [Hrho' [Hlocs Hval]]]].
    assert (v = val) by congruence. subst val.
    destruct Hlocs as [a'' [Ha'' HlVar]]. destruct H. rewrite Ha'' in H. inv H.

    exists (wasm_value_to_u32 wal :: args'). cbn. split.
    dostep_nary 0. apply r_local_get. eassumption.
    separate_instr. apply app_trans_const; auto.
    econstructor; eauto.
  }
  { (* fun *) destruct vs.
    - cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist.
    - assert (HrelE': @rel_env_LambdaANF_Wasm lenv (Eapp f t args) rho sr fr fds). {
          destruct HrelE as [Hfun1 [Hfun2 Hvar]]. split. assumption. split. assumption.
          intros. assert (Hocc : (occurs_free (Eapp f t (a :: args)) x)). {
          inv H0. constructor. constructor. right. assumption. }
           destruct (Hvar _ Hocc) as [val [wal [Hrho' [Hlocals Hval]]]]; auto. }
      assert (Hgetlist': get_list args rho = Some vs). {
        cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
      assert (Ha: rho ! a = Some v). {
        cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
      have IH := IHHargs _ _ _ state _ Hinv _ Hgetlist' HfenvRho _ HrelE'.
      destruct IH as [args' [Hred HconstL]].

      exists (a' :: args'). split. cbn.
      apply app_trans_const with (lconst := [AI_basic (BI_const_num (N_to_value a'))]); auto.
      assert (v = Vfun (M.empty _) fds a). {
        specialize HfenvWf with a. inv H. unfold translate_var in H0.
        destruct (fenv ! a) eqn:Ha'; rewrite Ha' in H0; inv H0.
        destruct HfenvWf as [H H0]. edestruct H0; eauto.
        eapply HfenvRho; auto. congruence.
      }
      subst v.
      destruct HrelE as [Hfun1 [Hfun2 _]]. inv H.
      eapply Hfun1 in Ha. 2:apply rt_refl.
      destruct Ha as [_ [_ Ha]].
      apply Hfun2 with (errMsg:=errMsg) in Ha.
      destruct Ha as [a'' [HtransF Hrepr]]. econstructor; eauto.
      cbn. congruence.
   }
Qed.

Lemma translate_functions_numOf_fundefs_length : forall fds fns,
  translate_functions nenv cenv fenv penv fds = Ret fns ->
  numOf_fundefs fds = length fns.
Proof.
  induction fds; intros. 2: { now inv H. }
  simpl in H.
  destruct (translate_function nenv cenv fenv penv v l e). inv H.
  destruct (translate_functions _ _ _ _ fds). inv H. destruct fns; inv H. cbn. now rewrite -IHfds.
Qed.

Lemma collect_function_vars_length_numOf_fundefs_eq : forall fds e,
  length (collect_function_vars (Efun fds e)) = numOf_fundefs fds.
Proof.
  induction fds; intros; auto. cbn. f_equal. now eapply IHfds with (e:=e).
Qed.

(* a bit stronger than set_lists_In *)
Lemma set_lists_nth_error {A} : forall xs (vs : list A) rho rho' x v,
  set_lists xs vs rho = Some rho' ->
  In x xs ->
  rho' ! x = Some v ->
  exists k, nth_error vs k = Some v /\ nth_error xs k = Some x.
Proof.
  induction xs; intros.
  - inv H0.
  - destruct H0.
    + (* a=v *)
      subst a. destruct vs. inv H. cbn in H. destruct (set_lists xs vs rho) eqn:Heqn; inv H.
      rewrite M.gss in H1. inv H1. exists 0. now cbn.
    + (* a<>v *)
      destruct vs. inv H. cbn in H. destruct (set_lists xs vs rho) eqn:Heqn; inv H.
      destruct (var_dec a x).
      * subst. rewrite M.gss in H1; inv H1. exists 0; now cbn.
      * rewrite M.gso in H1; auto.
        destruct (IHxs _ _ _ _ _ Heqn H0 H1) as [k [Hk1 Hk2]]. exists (S k). now cbn.
Qed.

(* Supported primitive functions do not return functions *)
Definition prim_funs_env_returns_no_funvalues (prim_funs : M.t (list val -> option val)) : Prop :=
  forall rho fds f f' f0 vs v,
    M.get f prim_funs = Some f' ->
    f' vs = Some v ->
    ~ subval_or_eq (Vfun rho fds f0) v.

(* for fn values returned by the fn body of Eletapp, it holds that rho=M.empty etc. *)
Lemma step_preserves_empty_env_fds : forall rho e v c fds rho' fds' f'  (pfs : M.t (list val -> option val)),
  (forall (x : positive) (rho' : M.t val) (fds' : fundefs) (f' : var) (v0 : val),
	  rho ! x = Some v0 ->
	  subval_or_eq (Vfun rho' fds' f') v0 ->
	  fds' = fds /\ rho' = M.empty val /\ name_in_fundefs fds f') ->
	(forall e' e'' eAny fdsAny,
	  (subterm_or_eq e' e \/ (subterm_or_eq e' e'' /\ dsubterm_fds_e e'' fds))
	  -> e' <> Efun fdsAny eAny) ->
        prim_funs_env_returns_no_funvalues pfs ->
  bstep_e pfs cenv rho e v c ->
  subval_or_eq (Vfun rho' fds' f') v ->
  fds' = fds /\ rho' = M.empty val /\ name_in_fundefs fds f'.
Proof.
  intros ? ? ? ? ? ? ? ? ? Hrho HnoFd Hpfs Hstep Hsubval.
  generalize dependent f'. generalize dependent fds'. generalize dependent rho'.
  induction Hstep; intros; subst.
  - (* Econstr *)
    eapply IHHstep; try eassumption.
    + intros x0 ???? H0 H1. destruct (var_dec x0 x).
      * (* x = x0 *)
        subst x0. rewrite M.gss in H0. inv H0.
        apply subval_or_eq_fun in H1. destruct H1 as [v' [H2 H3]].
        have H' := get_list_In_val _ _ _ _ H H3. destruct H' as [y [HyIn Hrho']].
        have H' := Hrho _ _ _ _ _ Hrho' H2. by assumption.
      * (* x <> x0 *)
        rewrite M.gso in H0; auto.
        have H' := Hrho _ _ _ _ _ H0 H1. by assumption.
    + intros ? ? ? ? [H' | H']; last now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans; try eassumption.
      apply rt_step. by constructor.
  - (* Eproj *)
    eapply IHHstep; try eassumption.
    + intros. destruct (var_dec x x0).
      * (* x = x0 *)
        subst x0. rewrite M.gss in H1. symmetry in H1. inv H1.
        apply nthN_In in H0.
        have H' := subval_or_eq_constr _ _ _ t H2 H0.
        by eauto.
      * (* x <> x0*)
        by rewrite M.gso in H1; eauto.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans; try eassumption.
      apply rt_step. by constructor.
  - (* Ecase *)
    eapply IHHstep; try eassumption.
    intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
    eapply HnoFd. left. eapply rt_trans; try eassumption.
    apply rt_step. econstructor. now apply findtag_In_patterns.
  - (* Eapp *)
    assert (subval_or_eq (Vfun rho' fl f') (Vfun rho' fl f')). {
      constructor. constructor. now eapply find_def_name_in_fundefs.
    }
    have H' := Hrho _ _ _ _ _ H H3. destruct H'. subst.
    eapply IHHstep; try eassumption.
    + intros.
      assert (Hdec: decidable_eq var). { intros n m.
        unfold Decidable.decidable. now destruct (var_dec n m). }
      have H' := In_decidable Hdec x xs. destruct H'.
      * (* In x xs *)
        have H' := set_lists_In _ _ _ _ _ _ H7 H4 H2.
        destruct (get_list_In_val _ _ _ _ H0 H') as [y [HyIn HyRho]].
        by eauto.
      * (* ~In x xs *)
        have H' := set_lists_not_In _ _ _ _ _ H2 H7.
        rewrite H4 in H'.
        erewrite def_funs_find_def in H'. 2: {
          intro Hcontra. eapply def_funs_not_find_def  in Hcontra.
          erewrite Hcontra in H'. destruct H5. subst. inv H'. }
        inv H'.
        have H' := set_lists_not_In _ _ _ _ _ H2 H7.
        rewrite H4 in H'.
        apply subval_fun in H6. destruct H6 as [ff [Heq Hfundef]].
        now inv Heq.
        apply def_funs_spec in H'. destruct H' as [[? ?] | [? ?]]; auto.
        destruct H5. now subst.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. right. split. eassumption.
      now eapply find_def_dsubterm_fds_e.
  - (* Eletapp *)
    eapply IHHstep2; try eassumption.
    + intros x0 ???? H3 H4.
      destruct (var_dec x x0); last (* x <> x0 *) by rewrite M.gso in H3; eauto.
      (* x = x0 *)
      subst x0. rewrite M.gss in H3. symmetry in H3. inv H3.
      (* same as Eapp *)
      assert (subval_or_eq (Vfun rho' fl f') (Vfun rho' fl f')). {
        constructor. constructor. now eapply find_def_name_in_fundefs.
      }
      have H' := Hrho _ _ _ _ _ H H3. destruct H'. subst.
      eapply IHHstep1; try eassumption.
      * intros x0 ???? H5 H7. assert (Hdec: decidable_eq var). { intros n m.
          unfold Decidable.decidable. now destruct (var_dec n m). }
        have H' := In_decidable Hdec x0 xs. destruct H'.
        -- (* In x0 xs *)
           have H' := set_lists_In _ _ _ _ _ _ H8 H5 H2.
           destruct (get_list_In_val _ _ _ _ H0 H') as [y [HyIn HyRho]].
           by eauto.
        -- (* ~In x0 xs *)
           have H' := set_lists_not_In _ _ _ _ _ H2 H8.
           rewrite H5 in H'.
           erewrite def_funs_find_def in H'. 2: {
             intro Hcontra. eapply def_funs_not_find_def  in Hcontra.
             erewrite Hcontra in H'. inv H'. destruct H6. now subst. }
           inv H'.
           have H' := set_lists_not_In _ _ _ _ _ H2 H8.
           rewrite H5 in H'.
           apply subval_fun in H7. destruct H7 as [ff [Heq Hfundef]].
           now inv Heq.
           apply def_funs_spec in H'. destruct H' as [[? ?] | [? Hcontra]].
           assumption. destruct H6. now subst.
      * intros ???? [H' | H']; last now eapply HnoFd.
        eapply HnoFd. right. split. eassumption.
        now eapply find_def_dsubterm_fds_e.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans. eassumption.
      apply rt_step. by constructor.
  - (* Efun: absurd *)
    exfalso. eapply HnoFd. left. apply rt_refl. reflexivity.
  - (* Eprim_val *) eapply IHHstep; eauto.
    + intros x0 ???? H H0. destruct (var_dec x0 x).
      * (* x = x0 *)
        subst x0. rewrite M.gss in H. inv H.
        now apply subval_or_eq_fun_not_prim in H0.
      * (* x <> x0 *) rewrite M.gso in H; auto. by eauto.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans; try eassumption.
      apply rt_step. by constructor.
  - (* Eprim *)
    eapply IHHstep; eauto.
    + intros x0 ???? H2 H3.
      destruct (var_dec x0 x); last (* x <> x0 *) by rewrite M.gso in H2; eauto.
      subst x0. rewrite M.gss in H2.
      inversion H2. subst v0.
      have H' := Hpfs _ _ _ _ _ _ _ H0 H1.
      specialize (H' rho' fds'0 f'1). contradiction.
    + intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
      eapply HnoFd. left. eapply rt_trans; try eassumption.
      apply rt_step. by constructor.
  - (* Ehalt *) by eauto.
  Unshelve. all: assumption.
Qed.

Lemma repr_expr_LambdaANF_Wasm_no_Efun_subterm {lenv} : forall e_body eAny,
  @repr_expr_LambdaANF_Wasm penv lenv e_body eAny ->

  forall (e' eAny : exp) (fdsAny : fundefs),
  subterm_or_eq e' e_body ->
  e' <> Efun fdsAny eAny.
Proof.
  intros ? ? Hexpr. revert eAny Hexpr.
  induction e_body using exp_ind'; intros.
  - (* Econstr *)
    inv Hexpr.
    have H' := IHe_body _ H5.
    apply rt_then_t_or_eq in H. destruct H as [H | H]. congruence.
    apply clos_trans_tn1 in H. inv H. inv H0.
    eapply H'. apply rt_refl. inv H0.
    apply clos_tn1_trans in H1. eapply H'. by apply t_then_rt.
  - (* Ecase [] *)
    apply rt_then_t_or_eq in H. destruct H; first congruence.
    apply clos_trans_tn1 in H. inv H. { inv H0. inv H2. }
    inv H0. by inv H3.
  - (* Ecase cons *)
    inv Hexpr. inv H3.
    + (* boxed *)
      inv H4.
      apply rt_then_t_or_eq in H. destruct H as [H | H]; first congruence.
      apply clos_trans_tn1 in H. inv H.
      { inv H0. destruct H3 as [H3 | H3].
        - inv H3. eapply IHe_body; first eassumption. apply rt_refl.
        - eapply IHe_body0. eapply Rcase_e; eauto. eapply rt_step. now econstructor. }
      { apply clos_tn1_trans in H1. inv H0. destruct H4 as [H4 | H4].
        - inv H4. eapply IHe_body; try eassumption. now apply t_then_rt.
        - eapply IHe_body0. eapply Rcase_e; eauto. eapply rt_trans. now apply t_then_rt.
          apply rt_step. now econstructor. }
    + (* unboxed *)
      inv H6.
      apply rt_then_t_or_eq in H. destruct H as [? | H]; first congruence.
      apply clos_trans_tn1 in H. inv H.
      { inv H0. destruct H3 as [H3 | H3].
        - inv H3. eapply IHe_body; try eassumption. apply rt_refl.
        - eapply IHe_body0. eapply Rcase_e; eauto.
          eapply rt_step. now econstructor. }
      { apply clos_tn1_trans in H1. inv H0. destruct H5 as [H5 | H5].
        - inv H5. eapply IHe_body; try eassumption. now apply t_then_rt.
        - eapply IHe_body0. eapply Rcase_e; eauto. eapply rt_trans. now apply t_then_rt.
          apply rt_step. now econstructor. }
  - (* Eproj *)
    inv Hexpr.
    have H' := IHe_body _ H6.
    apply rt_then_t_or_eq in H. destruct H as [H | H]. congruence.
    apply clos_trans_tn1 in H. inv H. inv H0.
    eapply H'. apply rt_refl. inv H0.
    apply clos_tn1_trans in H1. eapply H'. by apply t_then_rt.
  - (* Eletapp *)
    inv Hexpr.
    have H' := IHe_body _ H7. apply rt_then_t_or_eq in H.
    destruct H as [H|H]; first congruence. apply clos_trans_tn1 in H. inv H.
    inv H0. eapply H'. apply rt_refl. inv H0.
    eapply H'. apply clos_tn1_trans in H1. by apply t_then_rt.
  - (* Efun *) by inv Hexpr.
  - (* Eapp *)
    apply rt_then_t_or_eq in H. inv H; first congruence.
    apply clos_trans_tn1 in H0. inv H0. inv H. by inv H.
  - (* Eprim_val *)
    inv Hexpr.
    have H' := IHe_body _ H5.
    apply rt_then_t_or_eq in H.
    destruct H as [H|H]. congruence.
    apply clos_trans_tn1 in H. inv H.
    inv H0. eapply H'. apply rt_refl. inv H0.
    eapply H'. apply clos_tn1_trans in H1. now apply t_then_rt.
  - (* Eprim *)
    inv Hexpr.
    have H' := IHe_body _ H5.
    apply rt_then_t_or_eq in H.
    destruct H as [H|H]. congruence.
    apply clos_trans_tn1 in H. inv H.
    inv H0. eapply H'. apply rt_refl. inv H0.
    eapply H'. apply clos_tn1_trans in H1. now apply t_then_rt.
  - (* Ehalt *)
    apply rt_then_t_or_eq in H. destruct H; first congruence.
    apply clos_trans_tn1 in H. inv H. inv H0. by inv H0.
Qed.

Fixpoint select_nested_if (boxed : bool) (v : localidx) (ord : N) (es : list (N * list basic_instruction)) : list basic_instruction :=
  match es with
  | [] => [ BI_unreachable ]
  | (ord0, _) :: es' =>
      if N.eqb ord0 ord then
        create_case_nested_if_chain boxed v es
      else
        select_nested_if boxed v ord es'
  end.

Lemma create_case_nested_if_chain_repr_case_unboxed : forall v brs es,
    repr_case_unboxed v brs es ->
    create_case_nested_if_chain false v brs = es.
Proof.
  intros v brs.
  generalize dependent v.
  induction brs; intros.
  - inv H. reflexivity.
  - destruct a. inv H.
    cbn. apply IHbrs in H5. now rewrite H5.
Qed.

Lemma create_case_nested_if_chain_repr_case_boxed : forall v brs es,
    repr_case_boxed v brs es ->
    create_case_nested_if_chain true v brs = es.
Proof.
  intros v brs.
  generalize dependent v.
  induction brs; intros.
  - inv H. reflexivity.
  - destruct a. inv H.
    cbn. apply IHbrs in H5. now rewrite H5.
Qed.

Lemma lholed_nested_label : forall k (lh : lholed k) es es',
  exists k' (lh' : lholed k'),
  lfill lh ([:: AI_label 0 [::] es] ++ es') = lfill lh' es.
Proof.
  intros. induction lh; cbn.
  - eexists. exists (LH_rec l 0 [] (LH_base [] []) (es' ++ l0)). cbn.
    by rewrite cats0.
  - destruct IHlh as [k' [lh' Heq]]. cbn.
    eexists. exists (LH_rec l n l0 lh' l1). cbn.
    now rewrite Heq.
Qed.

Lemma and_of_odd_and_1_1 : forall n,
    (-1 < Z.of_nat (N.to_nat (2 * n + 1)) < Wasm_int.Int32.modulus)%Z ->
    Wasm_int.Int32.iand (Wasm_int.Int32.repr (Z.of_N (2 * n + 1))) (Wasm_int.Int32.repr 1) = Wasm_int.Int32.one.
Proof.
  intros.
  unfold Wasm_int.Int32.iand, Wasm_int.Int32.and. cbn.
  destruct n. cbn. reflexivity.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; last lia. reflexivity.
Qed.

Lemma and_of_even_and_1_0 : forall n,
    (-1 < Z.of_N (2 * n) < Wasm_int.Int32.modulus)%Z ->
    Wasm_int.Int32.iand (Wasm_int.Int32.repr (Z.of_N (2 * n))) (Wasm_int.Int32.repr 1) = Wasm_int.Int32.zero.
Proof.
  intros ? H.
  unfold Wasm_int.Int32.iand, Wasm_int.Int32.and.
  - destruct n. now cbn.
  - remember (Z.of_N _) as fd. cbn.
    now rewrite Wasm_int.Int32.Z_mod_modulus_id; subst.
Qed.

Lemma ctor_ord_restricted : forall y cl t e ord,
    expression_restricted cenv (Ecase y cl) ->
    In (t, e) cl ->
    get_ctor_ord cenv t = Ret ord ->
    (-1 < Z.of_N ord < Wasm_int.Int32.half_modulus)%Z.
Proof.
  intros ????? Hr Hin Hord. inv Hr.
  rewrite Forall_forall in H1. apply H1 in Hin.
  destruct Hin as [Hr' _].
  simpl_modulus. cbn. cbn in Hr'.
  unfold ctor_ordinal_restricted in Hr'.
  apply Hr' in Hord. simpl_modulus_in Hord. destruct ord; lia.
Qed.

Lemma cases_same_ind_tag :
  forall cl t t' e' cinfo cinfo',
    caseConsistent cenv cl t ->
    findtag cl t' = Some e' ->
    M.get t cenv = Some cinfo ->
    M.get t' cenv = Some cinfo' ->
    (ctor_ind_tag cinfo = ctor_ind_tag cinfo').
Proof.
  induction cl.
  intros.
  inv H0.
  intros.
  inv H.
  inv H0.
  destruct (M.elt_eq t'0 t').
  {
    subst.
    replace cinfo with info by congruence.
    now replace cinfo' with info' by congruence.
  }
  now apply (IHcl t t' e' cinfo cinfo' H9 H3 H1 H2).
Qed.

Lemma nullary_ctor_ords_in_case_disjoint:
  forall cl t t' e e' ord ord',
    cenv_restricted cenv ->
    caseConsistent cenv cl t ->
    t <> t' ->
    findtag cl t = Some e ->
    findtag cl t' = Some e' ->
    get_ctor_arity cenv t = Ret 0 ->
    get_ctor_arity cenv t' = Ret 0 ->
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_ord cenv t' = Ret ord' ->
    ord <> ord'.
Proof.
  intros.
  unfold cenv_restricted in H.
  destruct (M.get t cenv) eqn:Ht.
  2: { unfold get_ctor_arity in H4. rewrite Ht in H4. inv H4. }
  destruct c.
  assert (ctor_arity = 0%N). {
    unfold get_ctor_arity in H4.
    rewrite Ht in H4.
    inv H4.
    lia.
  }
  assert (ctor_ordinal = ord). {
    unfold get_ctor_ord in H6.
    rewrite Ht in H6.
    inv H6.
    lia.
  }
  subst ctor_arity. subst ctor_ordinal.
  have H' := H t _ _ _ 0%N ord Ht t' H1.
  assert (H'' : 0%N = 0%N) by reflexivity.
  apply H' in H''.
  clear H'.
  destruct (M.get t' cenv) eqn:Ht'.
  2: { unfold get_ctor_arity in H5. rewrite Ht' in H5. inv H5. }
  destruct c.
  assert (ctor_arity = 0%N). {
    unfold get_ctor_arity in H5.
    rewrite Ht' in H5.
    inv H5.
    lia.
  }
  assert (ctor_ordinal = ord'). {
    unfold get_ctor_ord in H7.
    rewrite Ht' in H7.
    inv H7.
    lia.
  }
  subst ctor_arity. subst ctor_ordinal.

  assert (ctor_ind_tag = ctor_ind_tag0). {
    remember (
         {|
           ctor_name := ctor_name;
           ctor_ind_name := ctor_ind_name;
           ctor_ind_tag := ctor_ind_tag;
           ctor_arity := 0;
           ctor_ordinal := ord
         |}) as cinfo.
    remember (
          {|
            ctor_name := ctor_name0;
            ctor_ind_name := ctor_ind_name0;
            ctor_ind_tag := ctor_ind_tag0;
            ctor_arity := 0;
            ctor_ordinal := ord'
          |}) as cinfo'.
    have I := cases_same_ind_tag cl t t' e' cinfo cinfo' H0 H3 Ht Ht'.
    subst cinfo. subst cinfo'.
    cbn in I.
    assumption.
  }
  intro Hcontra.
  unfold not in H''.
  apply H''. exists ctor_name0, ctor_ind_name0. subst. reflexivity.
Qed.

Lemma nonnullary_ctor_ords_in_case_disjoint:
  forall cl t t' e e' a a' ord ord',
    cenv_restricted cenv ->
    caseConsistent cenv cl t ->
    t <> t' ->
    findtag cl t = Some e ->
    findtag cl t' = Some e' ->
    get_ctor_arity cenv t = Ret a ->
    get_ctor_arity cenv t' = Ret a' ->
    0 < a ->
    0 < a' ->
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_ord cenv t' = Ret ord' ->
    ord <> ord'.
Proof.
  intros.
  unfold cenv_restricted in H.
  destruct (M.get t cenv) eqn:Ht.
  2: { unfold get_ctor_arity in H4. rewrite Ht in H4. inv H4. }
  destruct c.
  assert (ctor_arity = N.of_nat a). {
    unfold get_ctor_arity in H4.
    rewrite Ht in H4.
    inv H4.
    lia.
  }
  assert (ctor_ordinal = ord). {
    unfold get_ctor_ord in H8.
    rewrite Ht in H8.
    inv H8.
    lia.
  }
  subst ctor_arity. subst ctor_ordinal.
  have H' := H t _ _ _ (N.of_nat a) ord Ht t' H1.
  destruct H' as [_ H'].
  assert (H'' : (0 < N.of_nat a)%N) by lia.
  apply H' in H''.
  clear H'.
  destruct (M.get t' cenv) eqn:Ht'.
  2: { unfold get_ctor_arity in H5. rewrite Ht' in H5. inv H5. }
  destruct c.
  assert (ctor_arity = N.of_nat a'). {
    unfold get_ctor_arity in H5.
    rewrite Ht' in H5.
    inv H5.
    lia.
  }
  assert (ctor_ordinal = ord'). {
    unfold get_ctor_ord in H9.
    rewrite Ht' in H9.
    inv H9.
    lia.
  }
  subst ctor_arity. subst ctor_ordinal.
  assert (ctor_ind_tag = ctor_ind_tag0). {
    remember (
         {|
           ctor_name := ctor_name;
           ctor_ind_name := ctor_ind_name;
           ctor_ind_tag := ctor_ind_tag;
           ctor_arity := N.of_nat a;
           ctor_ordinal := ord
         |}) as cinfo.
    remember (
          {|
            ctor_name := ctor_name0;
            ctor_ind_name := ctor_ind_name0;
            ctor_ind_tag := ctor_ind_tag0;
            ctor_arity := N.of_nat a';
            ctor_ordinal := ord'
          |}) as cinfo'.
    have I := cases_same_ind_tag cl t t' e' cinfo cinfo' H0 H3 Ht Ht'.
    subst cinfo. subst cinfo'.
    cbn in I.
    assumption.
  }
  intro Hcontra.
  unfold not in H''.
  apply H''. exists ctor_name0, ctor_ind_name0, (N.of_nat a'). subst. reflexivity.
Qed.

Lemma unboxed_nested_if_chain_reduces:
  forall cl fAny y t e v lenv brs1 brs2 e2' f hs sr ord,
    lookup_N (f_locs f) v = Some (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_unboxed (ord  * 2 + 1)%N)))) ->
    cenv_restricted cenv ->
    expression_restricted cenv (Ecase y cl) ->
    caseConsistent cenv cl t ->
    findtag cl t = Some e ->
    get_ctor_ord cenv t = Ret ord ->
    get_ctor_arity cenv t = Ret 0 ->
    @repr_branches cenv fenv nenv penv lenv v cl brs1 brs2 ->
    repr_case_unboxed v brs2 e2' ->
    exists e' e'',
      select_nested_if false v ord brs2 =
        [ BI_local_get v
        ; BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)))
        ; BI_relop T_i32 (Relop_i ROI_eq)
        ; BI_if (BT_valtype None)
            e'
            e'' ]
      /\ (forall k (lh : lholed k),
          exists k0 (lh0 : lholed k0),
            reduce_trans (hs, sr, fAny, [AI_frame 0 f (lfill lh (map AI_basic e2'))]) (hs, sr, fAny, [AI_frame 0 f (lfill lh0 (map AI_basic e'))]))
      /\ @repr_expr_LambdaANF_Wasm penv lenv e e'.
Proof.
  induction cl; first by move => ???????????????? //=.
  intros fAny y t e v lenv brs1 brs2 e2' f hs sr ord Hval HcenvRestr HcaseRestr HcaseConsistent Hfindtag Hord Hunboxed Hbranches Hunboxedcase.
  destruct a as [t0 e0].
  have HcaseRestr' := HcaseRestr.
  inv HcaseRestr.
  clear H1.
  have Hfindtag' := Hfindtag.
  cbn in Hfindtag.
  destruct (M.elt_eq t0 t).
  { (* t0 = t, enter the then-branch *)
    subst t0. inv Hfindtag.
    inv Hbranches.
    { (* Impossible case: t0 cannot be the tag of a non-nullary constructor *)
      assert (n=0) by congruence. lia. }
    inv Hunboxedcase.
    assert (ord0 = ord) by congruence. subst ord0.
    exists e', instrs_more.
    split. simpl.
    assert (create_case_nested_if_chain false v brs3 = instrs_more). { now apply create_case_nested_if_chain_repr_case_unboxed. }
    rewrite N.eqb_refl. now rewrite H.
    split=>//.
    intros.
    have Hlh := lholed_nested_label _ lh [seq AI_basic i | i <- e'] [::].
    destruct Hlh as [k' [lh' Hlheq]].
    exists k', lh'.
    (* Step through the if-then-else into the then-branch *)
    eapply reduce_trans_frame'.
    eapply rt_trans. apply reduce_trans_label'.
    dostep_nary 0. apply r_local_get. eauto.
    dostep_nary 2. constructor. apply rs_relop.
    dostep'. constructor. apply rs_if_true.
    {
      rewrite N.mul_comm.
      unfold wasm_value_to_i32, wasm_value_to_u32, nat_to_value, nat_to_i32.
      unfold Wasm_int.Int32.eq.
      rewrite N_nat_Z. rewrite zeq_true.
      intro Hcontra. inv Hcontra.
    }
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    apply rt_refl.
    rewrite Hlheq. apply rt_refl.
  }
  { (* t0 <> t, enter the else branch (induction hypothesis) *)
    assert (Hrestr : expression_restricted cenv (Ecase y cl)). {
      constructor.
      inv HcaseRestr'.
      now inv H1.
    }
    inv Hbranches.
    { (* t0 is the tag of a non-nullary constructor, not even in the nested if-chain *)
      inv HcaseConsistent. eapply IHcl; eauto. }
    {
      assert (HcaseConsistent' : caseConsistent cenv cl t). { inv HcaseConsistent. assumption. }
      inv Hunboxedcase.
      assert (Hord_neq : ord <> ord0). {

        eapply nullary_ctor_ords_in_case_disjoint with (cl:=((t0, e0)::cl)) (t:=t) (t':=t0) (e:=e) (e':=e0); auto.
        cbn. destruct (M.elt_eq t0 t0). auto. contradiction.
      }
      assert (Hord_neq' : ord0 <> ord) by auto.
      have IH := IHcl fAny y t e v lenv brs1 brs3 instrs_more f hs sr ord  Hval HcenvRestr Hrestr HcaseConsistent' Hfindtag Hord Hunboxed H2 H7.
      destruct IH as [e1' [e'' [Hsel [Hred Hrep]]]].
      exists e1', e''.
      split.
      unfold select_nested_if. apply N.eqb_neq in Hord_neq'. rewrite Hord_neq'. fold select_nested_if. assumption.
      split=>//.
      intros.
      have Hlh := lholed_nested_label _ lh [seq AI_basic i | i <- instrs_more] [::].
      destruct Hlh as [k' [lh' Hlheq]].
      have Hred' := Hred k' lh'.
      destruct Hred' as [k0 [lh0 Hstep]].
      exists k0, lh0.
      (* Step through the if-then-else into the else-branch *)
      eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'. eapply rt_trans.
      dostep_nary 0. apply r_local_get. eauto.
      dostep_nary 2. constructor. apply rs_relop.
      dostep'. constructor. apply rs_if_false.
      (* Check that (t0 << 1) + 1 <> (t << 1);
         requires some arithmetic gymnastics  *)
      {
        rewrite N.mul_comm. cbn.
        unfold wasm_value_to_i32, wasm_value_to_u32, nat_to_i32. unfold Wasm_int.Int32.eq.
        destruct ord. destruct ord0. destruct Hord_neq'. reflexivity.
        rewrite N_nat_Z.
        rewrite Wasm_int.Int32.unsigned_repr. 2: cbn; lia.
        rewrite zeq_false. reflexivity.
        rewrite Wasm_int.Int32.unsigned_repr.
        lia.
        unfold Wasm_int.Int32.max_unsigned.
        assert ((-1 < (Z.of_N (N.pos p)) < Wasm_int.Int32.half_modulus)%Z). {
          eapply ctor_ord_restricted with (cl:=((t0, e0)::cl)); eauto.
          cbn. destruct (M.elt_eq t0 t0). auto. contradiction.
        }
        simpl_modulus.
        simpl_modulus_in H.
        cbn.
        lia.
        destruct ord0.
        rewrite N_nat_Z.
        rewrite zeq_false. reflexivity.
        rewrite Wasm_int.Int32.unsigned_repr.
        rewrite Wasm_int.Int32.unsigned_repr. 2: cbn; lia.
        cbn. lia.
        assert ((-1 < (Z.of_N (N.pos p)) < Wasm_int.Int32.half_modulus)%Z). {
          eapply ctor_ord_restricted; eauto.
          eapply findtag_In; eauto.
        }
        simpl_modulus.
        simpl_modulus_in H.
        cbn.
        lia.
        rewrite zeq_false. reflexivity.
        rewrite N_nat_Z.
        rewrite Wasm_int.Int32.unsigned_repr.
        rewrite Wasm_int.Int32.unsigned_repr.
        cbn.
        intro Hcontra. congruence.
        assert ((-1 < (Z.of_N (N.pos p0)) < Wasm_int.Int32.half_modulus)%Z). {
          eapply ctor_ord_restricted with (cl:=((t0, e0)::cl)); eauto.
          cbn. destruct (M.elt_eq t0 t0). auto. contradiction.
        }
        simpl_modulus.
        simpl_modulus_in H.
        cbn.
        lia.
        assert ((-1 < (Z.of_N (N.pos p)) < Wasm_int.Int32.half_modulus)%Z). {
          eapply ctor_ord_restricted; eauto.
          eapply findtag_In; eauto.
        }
        simpl_modulus.
        simpl_modulus_in H.
        cbn.
        lia.
        }
      dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
      apply rt_refl. apply rt_refl.
      rewrite Hlheq.
      apply Hstep.
    }
  }
Qed.

Lemma boxed_nested_if_chain_reduces:
  forall cl fAny y t vs e addr v lenv brs1 brs2 e1' (hs : host_state) (sr : store_record) (f : frame) ord,
    INV_linear_memory sr f ->
    repr_val_LambdaANF_Wasm (Vconstr t vs) sr (f_inst f) (Val_ptr addr) ->
    lookup_N (f_locs f) v = Some (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr addr)))) ->
    cenv_restricted cenv ->
    expression_restricted cenv (Ecase y cl) ->
    caseConsistent cenv cl t ->
    get_ctor_ord cenv t = Ret ord ->
    findtag cl t = Some e ->
    @repr_branches cenv fenv nenv penv lenv v cl brs1 brs2 ->
    repr_case_boxed v brs1 e1' ->
    exists e' e'',
      select_nested_if true v ord brs1 =
        [ BI_local_get v
        ; BI_load T_i32 None 2%N 0%N
        ; BI_const_num (nat_to_value (N.to_nat ord))
        ; BI_relop T_i32 (Relop_i ROI_eq)
        ; BI_if (BT_valtype None)
            e'
            e'' ]
      /\ (forall k (lh : lholed k),
            exists k0 (lh0 : lholed k0),
            reduce_trans (hs, sr, fAny, [AI_frame 0 f (lfill lh (map AI_basic e1'))]) (hs, sr, fAny, [AI_frame 0 f (lfill lh0 (map AI_basic e'))]))
      /\ @repr_expr_LambdaANF_Wasm penv lenv e e'.
Proof.
  induction cl; first by move => ????????????????????? //=.
  intros fAny y t vs e addr v lenv brs1 brs2 e1' hs sr f ord Hmem Hval Hlocs HcenvRestr HcaseRestr HcaseConsistent Hord Hfindtag Hbranches Hboxedcase.
  destruct a as [t0 e0].
  have HcaseRestr' := HcaseRestr.
  inv HcaseRestr.
  have Hmem' := Hmem.
  destruct Hmem as [Hsmem [m [Hmem0 Hmemsize]]].
  have Hfindtag' := Hfindtag.
  have Hval' := Hval.
  assert (exists arity, get_ctor_arity cenv t = Ret arity /\ arity > 0). {
    inv Hval. by exists arity.
  }
  destruct H as [n [Hn Hngt0]].
  cbn in Hfindtag.
  destruct (M.elt_eq t0 t).
  { (* t0 = t, enter the then-branch *)
    subst t0. inv Hfindtag.
    inv Hbranches.
    2: { (* Impossible case: t cannot be the tag of a nullary constructor *)
      assert (n=0) by congruence. lia. }
    assert (ord0 = ord) by congruence. subst ord0.
    assert (n0 = n) by congruence. subst n0.
    clear Hn Hngt0.
    inv Hboxedcase.
    exists e', instrs_more.
    split. cbn.
    assert (create_case_nested_if_chain true v brs0 = instrs_more). { now apply create_case_nested_if_chain_repr_case_boxed. }
    rewrite N.eqb_refl. congruence.
    split=>//.
    intros.
    have Hlh := lholed_nested_label _ lh (map AI_basic e') [::].
    destruct Hlh as [k' [lh' Hlheq]].
    exists k', lh'.

    (* Step through the if-then-else into the then-branch *)
    eapply reduce_trans_frame'.
    eapply rt_trans. apply reduce_trans_label'.
    dostep_nary 0. apply r_local_get. eauto.
    inv Hval.
    solve_eq m m0.
    unfold load_i32 in H20.
    destruct (load m addr (N.of_nat 0) 4) eqn:Hload. 2: { cbn in Hload. rewrite Hload in H20. inv H20. }
    dostep_nary 1. eapply r_load_success; try eassumption.
    assert (addr = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
    }
    rewrite <- H. apply Hload.
    dostep_nary 2. constructor. apply rs_relop.
    dostep'. constructor. apply rs_if_true. {
      (* Check that ord = t *)
      cbn.
      unfold nat_to_i32.
      unfold Wasm_int.Int32.eq.
      cbn in Hload.
      rewrite Hload in H20.
      injection H20 => H20'.
      destruct (zeq (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (decode_int b)))
                  (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (N.to_nat ord))))) eqn:Heq.
      discriminate.
      replace ord0 with ord in H20' by congruence.
      contradiction.
    }
    dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto. apply rt_refl.
    rewrite Hlheq. apply rt_refl.
  }
  { (* t0 <> t, enter the else branch (induction hypothesis) *)
    assert (Hrestr : expression_restricted cenv (Ecase y cl)). {
      constructor.
      inv HcaseRestr'.
      now inv H1.
    }
    inv Hbranches.
    2: { (* t0 is the tag of a nullary constructor, not even in the nested if-chain *)
      inv HcaseConsistent. eapply IHcl; eauto. }
    {
      assert (HcaseConsistent' : caseConsistent cenv cl t). { inv HcaseConsistent. assumption. }
      inv Hboxedcase.
      have IH := IHcl fAny y t vs e addr v lenv brs0 brs2 instrs_more hs sr f ord Hmem' Hval Hlocs HcenvRestr Hrestr HcaseConsistent' Hord Hfindtag H3 H8.
      destruct IH as [e0' [e'' [Hsel [Hred Hrep]]]].
      exists e0', e''.
      split.
      unfold select_nested_if.
      assert (Hord_neq : ord <> ord0).
      {
        eapply nonnullary_ctor_ords_in_case_disjoint with (cl:=((t0, e0)::cl)) (t:=t) (t':=t0) (e:=e) (e':=e0) (a:=n) (a':=n1); auto.
        cbn. destruct (M.elt_eq t0 t0). auto. contradiction.
      }
      assert (Hord_neq' : ord0 <> ord) by auto.
      apply N.eqb_neq in Hord_neq'. rewrite Hord_neq'. fold select_nested_if. assumption.
      split=>//.
      intros.
      have Hlh := lholed_nested_label _ lh [seq AI_basic i | i <- instrs_more] [::].
      destruct Hlh as [k' [lh' Hlheq]].
      have Hred' := Hred k' lh'.
      destruct Hred' as [k0 [lh0 Hstep]].
      exists k0, lh0.

      (* Step through the if-then-else into the else-branch *)
      eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'. eapply rt_trans.
      dostep_nary 0. apply r_local_get. eauto.
      inv Hval.
      solve_eq m m0.
      unfold load_i32 in H20.
      destruct (load m addr (N.of_nat 0) 4) eqn:Hload. 2: { cbn in Hload. rewrite Hload in H20. inv H20. }
      dostep_nary 1. eapply r_load_success; try eassumption.
      assert (addr = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))) as H. {
        cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
      }
      rewrite <- H. apply Hload.
      dostep_nary 2. constructor. apply rs_relop.
      dostep'. constructor. apply rs_if_false.
      { (* Check that the ord of t0 is not equal to ord of t;
         requires some arithmetic gymnastics  *)
        assert (ord1 = ord) by congruence.
        subst ord1.
        assert ((-1 < Z.of_N ord < Wasm_int.Int32.half_modulus)%Z). {
          have Hr := Forall_forall (fun p : ctor_tag * exp =>
                                      ctor_ordinal_restricted cenv (fst p) /\
                                        expression_restricted cenv (snd p)) ((t0, e0) :: cl).
          inv HcaseRestr'.
          destruct Hr as [Hr' _].
          apply Hr' with (x:=(t, e)) in H2. cbn. unfold ctor_ordinal_restricted in H2.
          cbn in H2.
          destruct H2 as [HordRestr _].
          apply HordRestr in Hord.
          cbn in Hord.
          lia.
          inv Hfindtag.
          destruct (M.elt_eq t0 t).
          { subst t0. inv H1. now constructor. }
          { apply findtag_In in H0. now apply List.in_cons. }
        }
        assert ((-1 < Z.of_N ord0 < Wasm_int.Int32.half_modulus)%Z). {
          have Hr := Forall_forall (fun p : ctor_tag * exp =>
                                      ctor_ordinal_restricted cenv (fst p) /\
                                        expression_restricted cenv (snd p)) ((t0, e0) :: cl).
          inv HcaseRestr'.
          destruct Hr as [Hr' _].
          apply Hr' with (x:=(t0, e0)) in H17. cbn.
          destruct H17 as [HordRestr _].
          apply HordRestr in H4.
          cbn in H4.
          lia.
          now constructor.
        }

        cbn.
        unfold nat_to_i32.
        unfold Wasm_int.Int32.eq.
        cbn in Hload.
        rewrite Hload in H20.
        injection H20 => H20'.
        destruct (zeq (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (decode_int b)))
                    (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (N.to_nat ord0))))); auto.
        inv e1.
        assert (ord <> ord0).
        {
        eapply nonnullary_ctor_ords_in_case_disjoint with (cl:=((t0, e0)::cl)) (t:=t) (t':=t0) (e:=e) (e':=e0) (a:=n) (a':=n1); auto.
        cbn. destruct (M.elt_eq t0 t0). auto. contradiction.

        }
        rewrite H20' in H17.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in H17.
        2: { simpl_modulus. cbn. simpl_modulus_in H. lia. }
        rewrite Wasm_int.Int32.Z_mod_modulus_id in H17.
        2: { simpl_modulus. cbn. simpl_modulus_in H0. lia. }
        lia.
      }
      dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
      eapply rt_refl. apply rt_refl.
      rewrite Hlheq.
      apply Hstep.
    }
  }
Qed.

(* Helper tactic to solve the cases for simple binary arithmetic operators like add, sub, mul etc.
   Proves that the instructions reduces to a constant that is related to the result of applying the operator. *)
Local Ltac solve_arith_op_aux v aexp Hrepr_binop Hreduce HloadArgsStep HwasmArithEq :=
  (inv Hrepr_binop; simpl;
   destruct (Hreduce aexp) as [s' [s_final [fr [m' [wal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]];
   exists s_final, fr;
   replace v with (Vprim ( primInt aexp)) in * by congruence;
   split; auto;
   dostep_nary 0; [apply r_global_get; eassumption|];
   eapply rt_trans; [apply app_trans_const; [auto|apply HloadArgsStep]|];
   dostep_nary_eliml 2 1;[constructor; apply rs_binop_success; reflexivity|];
   (try (dostep_nary_eliml 2 1;[constructor; apply rs_binop_success; reflexivity|]));
   dostep_nary 2; [eapply r_store_success; rewrite HwasmArithEq; eassumption|];
   eassumption).


Local Ltac reduce_under_label:=
  eapply rt_trans;
  [try apply app_trans|];
  [try apply app_trans_const; auto|];
  [try eapply reduce_trans_label1|].

(* TODO: Remove or refactor for better re-use *)
Lemma increment_global_mem_ptr_reduce (sr : store_record) (fr : frame) (n : N): 
  forall (state : host_state) (gmp_v : N),
    INV_global_mem_ptr_writable sr fr ->
    sglob_val sr (f_inst fr) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
    (Z.of_N (gmp_v + n) < Wasm_int.Int32.modulus)%Z ->
    exists (sr' : store_record),
      (forall instrs,
          reduce_trans
            (state, sr, fr, map AI_basic (increment_global_mem_ptr global_mem_ptr n) ++ instrs)
            (state, sr', fr, instrs))
      /\ supdate_glob sr (f_inst fr) global_mem_ptr (VAL_num (VAL_int32 (N_to_i32 (gmp_v + n)))) = Some sr'.
Proof.
  intros ?? Hgmp HgmpValue HgmpNewValueInBound.
  destruct (Hgmp (VAL_int32 (Wasm_int.Int32.repr (Z.of_N (gmp_v + n)%N)))) as [sr' Hsr'].
  exists sr'; split; auto.
  intros.
  separate_instr; do 3 rewrite catA.
  apply app_trans with (es':=[]).
  separate_instr.
  dostep_nary 0. apply r_global_get; eassumption.
  dostep_nary 2. constructor; apply rs_binop_success; reflexivity.
  cbn; unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add; cbn.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; [|lia]; rewrite Wasm_int.Int32.Z_mod_modulus_id; [|lia]; rewrite -N2Z.inj_add.
  replace ($VN N_to_VAL_i32 (gmp_v + n)) with ($V (VAL_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_N (gmp_v + n)))))) by now cbn.
  apply rt_step; apply r_global_set; eassumption.
Qed.

Lemma store_preserves_INV (sr : store_record) :
  forall fr m addr off v,
    INV sr fr ->
    smem sr (f_inst fr) = Some m ->
    (off + 8 <= page_size)%N ->
    (Z.of_N addr + Z.of_N page_size <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
    exists sr' m',
      smem sr' (f_inst fr) = Some m'
      /\ mem_length m = mem_length m'
      /\ store m addr off (bits v) (length (bits v)) = Some m'
      /\ smem_store sr (f_inst fr) addr off v (typeof_num v) = Some sr'
      /\ INV sr' fr
      /\ (forall a, (a + 4 <= (addr + off))%N -> load_i32 m a = load_i32 m' a)
      /\ (forall a, (a + 8 <= (addr + off))%N -> load_i64 m a = load_i64 m' a)
      /\ s_funcs sr = s_funcs sr'
      /\ (forall g gv, sglob_val sr (f_inst fr) g = gv -> sglob_val sr' (f_inst fr) g = gv).
Proof.
  intros fr m addr off v HINV Hm Hoff Haddr.
  unfold page_size in *. simpl_modulus_in Haddr.
  have I := HINV. destruct I as (_&_&_&_&_&_& (Hmeminst & (m0 & (Hmem0 & size & Hm0size))) &_).
  replace m0 with m in * by congruence. clear Hmem0.
  destruct Hm0size as (Hmemsize & Hmemmaxsize & Hsizebound).
  assert (Hsrmem: lookup_N (s_mems sr) 0 = Some m)
    by now unfold smem in Hm; rewrite Hmeminst in Hm; cbn in Hm; destruct (s_mems sr).  
  assert (Hstore: exists m', store m addr off (bits v) (length (bits v)) = Some m') by now destruct v; apply enough_space_to_store; unfold_bits; cbn in *; try lia.
  destruct Hstore as [m' Hstore].
  remember (upd_s_mem sr (set_nth m' sr.(s_mems) (N.to_nat 0) m')) as sr'.
  assert (Hsmem_store : smem_store sr (f_inst fr) addr off v (typeof_num v) = Some sr'). {
    unfold smem_store; rewrite Hmeminst; cbn.
    destruct (s_mems sr). now cbn in Hsrmem.
    replace m1 with m in * by now cbn in *.
    replace (ssrnat.nat_of_bin (tnum_length (typeof_num v))) with (Datatypes.length (bits v)) 
      by now destruct v; unfold_bits; cbn in *. 
    rewrite Hstore; rewrite Heqsr'; now cbn. }
  assert (Hmemlength': mem_length m = mem_length m') by now unfold store in Hstore;
    destruct (addr + off + N.of_nat (Datatypes.length (bits v)) <=? mem_length m)%N; [now destruct (write_bytes_preserve_type Hstore)|inv Hstore].
  exists sr', m'; auto.
  split; auto.
  unfold smem_store in Hsmem_store; rewrite Hmeminst in Hsmem_store; cbn in *.
  rewrite Hsrmem in Hsmem_store; rewrite Heqsr'; unfold smem.
  rewrite Hmeminst; cbn.
  destruct (s_mems sr); [now cbn|now inv Hsrmem].
  do 3 (try split; auto).
  split. { (* INV *)
    apply update_mem_preserves_INV with (vd:=m') (s:=sr) (m:=m) (m':=m'); auto.
    - lia.
    - replace (mem_max_opt m') with (mem_max_opt m);[assumption|rewrite store_offset_eq in Hstore; eapply mem_store_preserves_max_pages; eauto].
    - exists size; split; auto. unfold mem_size in Hmemsize; now rewrite Hmemlength' in Hmemsize.
  } split. { (* all i32 values in mem are preserved *)
    intros.
    assert (exists v', load_i32 m a = Some v') as Hex by now apply enough_space_to_load; lia.
    destruct Hex as [v' Hv']; rewrite Hv'; symmetry; destruct v; rewrite store_offset_eq in Hstore.
    - apply load_store_load_i32 with (m:=m) (a2:=(addr+off)%N) (w:=(bits (VAL_int32 s))); auto.
    - apply load_store_load_i32' with (m:=m) (a2:=(addr+off)%N) (w:=(bits (VAL_int64 s))); auto.
    - apply load_store_load_i32 with (m:=m) (a2:=(addr+off)%N) (w:=(bits (VAL_float32 s))); auto.
    - apply load_store_load_i32' with (m:=m) (a2:=(addr+off)%N) (w:=(bits (VAL_float64 s))); auto.
  } split. { (* all i64 values in mem are preserved *)
    intros.
    assert (exists v', load_i64 m a = Some v') as Hex by now apply enough_space_to_load_i64; lia.
    destruct Hex as [v' Hv']; rewrite Hv'; symmetry; destruct v; rewrite store_offset_eq in Hstore.
    - apply load_store_load_i64 with (m:=m) (a2:=(addr+off)%N) (w:=(bits (VAL_int32 s))); auto.
    - apply load_store_load_i64' with (m:=m) (a2:=(addr+off)%N) (w:=(bits (VAL_int64 s))); auto.
    - apply load_store_load_i64 with (m:=m) (a2:=(addr+off)%N) (w:=(bits (VAL_float32 s))); auto.
    - apply load_store_load_i64' with (m:=m) (a2:=(addr+off)%N) (w:=(bits (VAL_float64 s))); auto.
  }
  unfold smem_store in Hsmem_store.
  destruct (lookup_N (inst_mems (f_inst fr)) 0). 2: discriminate.
  destruct (lookup_N (s_mems sr) m1). 2: discriminate.
  destruct (store m2 addr off (bits v) (ssrnat.nat_of_bin (tnum_length (typeof_num v)))). 2: discriminate.
  split; intros; now inv Hsmem_store.
Qed.

Lemma make_carry_reduce (ord : N) :
  forall state sr fr m gmp res,
    INV sr fr ->
    smem sr (f_inst fr) = Some m ->
    sglob_val sr (f_inst fr) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp))) ->
    (Z.of_N gmp + Z.of_N page_size <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
    sglob_val sr (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr res))) ->
    exists (sr': store_record) m',
      (forall instrs,
          reduce_trans
            (state, sr, fr, map AI_basic (make_carry global_mem_ptr ord glob_tmp1) ++ instrs)
            (state, sr', fr, ($VN (VAL_int32 (N_to_i32 (gmp + 8)%N))) :: instrs))
      /\ INV sr' fr
      /\ smem sr' (f_inst fr) = Some m'
      /\ sglob_val sr' (f_inst fr) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp + 16))))
      /\ load_i64 m' gmp = Some (VAL_int64 (Int64.repr res))
      /\ load_i32 m' (gmp + 8)%N = Some (VAL_int32 (N_to_i32 ord))
      /\ load_i32 m' (gmp + 12)%N = Some (VAL_int32 (N_to_i32 gmp))
      /\ (forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m' a)
      /\ (forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m' a)
      /\ s_funcs sr = s_funcs sr'
      /\ mem_length m = mem_length m'.
Proof.
  intros state sr fr m gmp res HINV Hmem Hgmp HenoughMem Hres.
  assert (0 + 8 <= page_size)%N as Hoff1 by now unfold page_size.
  assert (8 + 8 <= page_size)%N as Hoff2 by now unfold page_size.
  assert (12 + 8 <= page_size)%N as Hoff3 by now unfold page_size.
  remember (VAL_int64 (Int64.repr res)) as res_val.
  assert (HdesRes: wasm_deserialise (bits res_val) T_i64 = res_val) by now apply deserialise_bits; subst res_val.
  remember (VAL_int32 (Int32.repr (Z.of_N gmp))) as res_addr.
  assert (HdesResAddr: wasm_deserialise (bits res_addr) T_i32 = res_addr) by now apply deserialise_bits; subst res_addr.
  remember (VAL_int32 (Int32.repr (Z.of_N ord))) as ord_val.
  assert (HdesOrd: wasm_deserialise (bits ord_val) T_i32 = ord_val) by now apply deserialise_bits; subst ord_val.
  remember (VAL_int32 (Int32.repr (Z.of_N (gmp + 8)))) as ord_addr.
  remember (VAL_int32 (Int32.repr (Z.of_N (gmp + 12)))) as arg_addr.
  remember (VAL_num (VAL_int32 (N_to_i32 (gmp + 16)))) as newgmp.
  (* Store the 63-bit result at gmp *)
  destruct (store_preserves_INV sr fr m gmp 0%N res_val HINV Hmem Hoff1 HenoughMem) as (sr1 & m1 & Hmem1 & Hmemlength1 & Hstore1 & Hsmem_store1 & HINV1 & Hpres32_1 & Hpres64_1 & Hsfs1 & HglobPres1).
  assert (HenoughMem1 : (Z.of_N gmp + Z.of_N page_size <= Z.of_N (mem_length m1) < Int32.modulus)%Z) by now rewrite Hmemlength1 in HenoughMem.

  (* Store the ordinal (e.g. C0 or C1) at gmp + 8 *)
  destruct (store_preserves_INV sr1 fr m1 gmp 8%N ord_val HINV1 Hmem1 Hoff2 HenoughMem1) as (sr2 & m2 & Hmem2 & Hmemlength2 & Hstore2 & Hsmem_store2 & HINV2 & Hpres32_2 & Hpres64_2 & Hsfs2 & HglobPres2). 
  assert (HenoughMem2 : (Z.of_N gmp + Z.of_N page_size <= Z.of_N (mem_length m2) < Int32.modulus)%Z) by now rewrite Hmemlength2 in HenoughMem1.

  (* Store the _address_ of the result (gmp) at gmp + 12 *)
  destruct (store_preserves_INV sr2 fr m2 gmp 12%N res_addr HINV2 Hmem2 Hoff2 HenoughMem2) as (sr3 & m3 & Hmem3 & Hmemlength3 & Hstore3 & Hsmem_store3 & HINV3 & Hpres32_3 & Hpres64_3 & Hsfs_3 & HglobPres3).
  
  have I := HINV3. destruct I as (_&_&_& HgmpWritable &_).
  have I := HINV. destruct I as (_&_&_&_&_&_&_&_&_&_&_&_&_& Hmult2 &_).

  (* Increment gmp by 16 to point to next free address *)
  destruct (HgmpWritable (VAL_int32 (N_to_i32 (gmp + 16)))) as [sr'  Hupdgmp].
  assert (HINV' : INV sr' fr). {
    apply update_global_preserves_INV with (sr:=sr3) (i:=global_mem_ptr) (m:=m3) (num:=(VAL_int32 (N_to_i32 (gmp+16)))); auto.
    left; split; [right; right; now constructor|now cbn].
    discriminate.
    move => _. intros n [Heqn Hrangen]. 
    replace n with (gmp + 16)%N.
    unfold page_size in *. lia.
    inv Heqn.
    repeat rewrite Int32.Z_mod_modulus_id in H0; try lia.
    move => _. intros n [Heqn Hrangen]. 
    replace n with (gmp + 16)%N.
    assert (-1 < Z.of_N gmp < Wasm_int.Int32.modulus)%Z by now unfold page_size in *; simpl_modulus_in HenoughMem; simpl_modulus; cbn in HenoughMem |- *; lia. 
    destruct (Hmult2 _ _ Hmem Hgmp H) as (n0 & Hn0).
    now exists (n0 + 8)%N.
    inv Heqn.
    repeat rewrite Int32.Z_mod_modulus_id in H0; try lia. }
  assert (Hgmp' : sglob_val sr' (f_inst fr) global_mem_ptr = Some newgmp) by now
    apply HglobPres1, HglobPres2, HglobPres3 in Hgmp; subst newgmp; apply update_global_get_same with (sr:=sr3).
  (* All i32 values below gmp are preserved *)
  assert (Hpres32: forall a, (a + 4 <= gmp)%N -> load_i32 m a = load_i32 m3 a) by now 
    intros; rewrite ->Hpres32_1, ->Hpres32_2, ->Hpres32_3; try lia; auto.
  (* All i64 values below gmp are preserved *)
  assert (Hpres64: forall a, (a + 8 <= gmp)%N -> load_i64 m a = load_i64 m3 a) by now
    intros; rewrite ->Hpres64_1, ->Hpres64_2, -> Hpres64_3; try lia; auto.
  exists sr', m3.
  split. { (* make_carry instructions reduce *)
    intros.
    assert (HrewriteGmp : N_of_uint i32m (N_to_i32 gmp) = gmp) by now cbn; rewrite Int32.Z_mod_modulus_id;[now rewrite N2Z.id|lia].  
    unfold make_carry.
    separate_instr.
    dostep_nary 0. apply r_global_get; eassumption.
    dostep_nary_eliml 0 1. apply r_global_get; eassumption.
    dostep_nary 2.
    apply r_store_success; rewrite HrewriteGmp; subst res_val; cbn; eassumption.
    dostep_nary 0. apply r_global_get; apply HglobPres1 in Hgmp; eassumption.
    dostep_nary 2. apply r_store_success; rewrite HrewriteGmp; subst ord_val; cbn; eassumption.
    dostep_nary 0. apply r_global_get; apply HglobPres1, HglobPres2 in Hgmp; eassumption.
    dostep_nary_eliml 0 1. apply r_global_get; apply HglobPres1, HglobPres2 in Hgmp; eassumption.
    dostep_nary 2. apply r_store_success; rewrite HrewriteGmp; subst res_addr; cbn; eassumption.
    dostep_nary 0. apply r_global_get; apply HglobPres1, HglobPres2, HglobPres3 in Hgmp; eassumption.
    dostep_nary 2. constructor. apply rs_binop_success. cbn. unfold Int32.iadd, Int32.add, Int32.unsigned; cbn.
    rewrite Int32.Z_mod_modulus_id. replace 8%Z with (Z.of_N 8) by now cbn. rewrite <-N2Z.inj_add. reflexivity.
    simpl_modulus; simpl_modulus_in HenoughMem; unfold page_size in *; cbn in *; lia.
    dostep_nary_eliml 0 1. apply r_global_get; apply HglobPres1, HglobPres2, HglobPres3 in Hgmp; eassumption.
    dostep_nary_eliml 2 1. constructor. apply rs_binop_success. cbn. unfold Int32.iadd, Int32.add, Int32.unsigned; cbn.
    rewrite Int32.Z_mod_modulus_id. replace 16%Z with (Z.of_N 16) by now cbn. rewrite <-N2Z.inj_add. reflexivity.
    simpl_modulus; simpl_modulus_in HenoughMem; unfold page_size in *; cbn in *; lia.
    dostep_nary_eliml 1 1. replace ($VN N_to_VAL_i32 (gmp + 16)) with ($V (VAL_num (N_to_VAL_i32 (gmp + 16)))) by now cbn.
    apply r_global_set. eassumption.
    now apply rt_refl. }  
  replace (smem sr' (f_inst fr)) with (smem sr3 (f_inst fr)) by now eapply update_global_preserves_memory; eassumption.
  repeat (split; auto).
  - (* Result can be loaded as an i64 from address gmp *)
    rewrite <-Hpres64_3, <-Hpres64_2, <-HdesRes; try lia.
    eapply store_load_i64 with (m:=m); subst res_val; erewrite i64_val_8_bytes in *; eauto.
  - (* The ordinal can be loaded as an i32 from address gmp + 8 *)
    replace (VAL_int32 (N_to_i32 ord)) with ord_val by now cbn.
    rewrite <-Hpres32_3, <-HdesOrd; try lia.
    eapply store_load_i32 with (m:=m1); subst ord_val; erewrite i32_val_4_bytes in *; rewrite store_offset_eq in Hstore2; eauto.
  - (* The address of the result (gmp) can be loaded from address gmp + 12 *)
    replace (VAL_int32 (N_to_i32 gmp)) with res_addr by now cbn.
    rewrite <-HdesResAddr; try lia.
    apply store_load_i32 with (m:=m2); subst res_addr; erewrite i32_val_4_bytes in *; rewrite store_offset_eq in Hstore3; eauto.
  - (* Functions in the store are preserved*)
    rewrite Hsfs1 Hsfs2 Hsfs_3; eapply update_global_preserves_funcs; eassumption.
  - (* Length of memory is preserved *)
    now rewrite Hmemlength1 Hmemlength2 Hmemlength3.
Qed.

(* 2 tactics for reducing instructions for exact arithmetic operations (addc, addcarryc) 
   TODO: Consider merging/ refactoring (split in 2 in anticipation of supporting both addc and addcarryc) *)
Ltac apply_exact_reduce_aux1 Hdes1 Hdes2 :=
      intros; unfold apply_exact_add_operation;
      (* remember to avoid unfolding *)
      remember ((make_carry global_mem_ptr C1_ord glob_tmp1)) as carryInstrsC1;
      remember ((make_carry global_mem_ptr C0_ord glob_tmp1)) as carryInstrsC0;
      separate_instr;
      (* Load and deserialise 1st argument *)
      dostep_nary 0; [eapply r_local_get; eauto|];
      dostep_nary 1; [eapply r_load_success; eauto|];
      rewrite Hdes1;
      (* Load and deserialise 1st argument *)
      dostep_nary_eliml 0 1; [eapply r_local_get; eauto|];
      dostep_nary_eliml 1 1; [eapply r_load_success; eauto|];
      rewrite Hdes2;
      (* Apply addition binary operation *)
      dostep_nary 2; [constructor;apply rs_binop_success; now cbn|].

Ltac apply_exact_reduce_aux2 v Hdes if_constr Hrewrite carry_instrs Hreduce :=
      (* Apply bitmask *)
      dostep_nary 2; [constructor; apply rs_binop_success; now cbn|];
      rewrite uint63_add_i64_add;
      (* Temporarily store the result in a global *)
      dostep_nary 1; [rewrite unfold_val_notation; eapply r_global_set; eauto|];
      (* Put the result on the stack again *)
      dostep_nary 0; [eapply r_global_get; eauto|];
      (* Load and deserialise the argument *)
      dostep_nary_eliml 0 1; [eapply r_local_get; eauto|];
      dostep_nary_eliml 1 1; [eapply r_load_success; eauto|];
      rewrite Hdes;
      (* Check if the addition overflowed is overflow *)
      dostep_nary 2; [constructor; apply rs_relop|];
      (* Step into the right branch and reduce make_carry *)
      dostep_nary 1; [constructor; apply if_constr; rewrite Hrewrite; auto; try discriminate|];
      dostep_nary 0; [eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); auto|];
      reduce_under_label; [cbn; subst carry_instrs; apply Hreduce|];
      dostep_nary 0; [constructor; apply rs_label_const; auto|];
      now apply rt_refl.

Definition local_holds_address_to_i64 (sr : store_record) (fr : frame) (l : localidx) (addr: i32) (val : i64) (m : meminst) bs : Prop :=
    lookup_N fr.(f_locs) l = Some (VAL_num (VAL_int32 addr))
    /\ load m (Wasm_int.N_of_uint i32m addr) 0%N (N.to_nat (tnum_length T_i64)) = Some bs
    /\ wasm_deserialise bs T_i64 = (VAL_int64 val).

Lemma apply_exact_add_operation_reduce (x y : localidx) (addone : bool) :
  forall state sr fr m gmp_v addrx addry bsx bsy n1 n2 c0_tag c1_tag it_carry v,
    INV sr fr ->
    M.get c0_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C0") (Common.BasicAst.nNamed "carry") it_carry 1%N C0_ord) ->
    M.get c1_tag cenv = Some (Build_ctor_ty_info (Common.BasicAst.nNamed "C1") (Common.BasicAst.nNamed "carry") it_carry 1%N C1_ord) ->
    ((~ (to_Z (n1 + n2) < to_Z n1)%Z /\ v = Vconstr c0_tag [Vprim (AstCommon.primInt ; (n1 + n2)%uint63)]) \/ ((to_Z (n1 + n2) < to_Z n1)%Z /\ v = Vconstr c1_tag [Vprim (AstCommon.primInt ; (n1 + n2)%uint63)])) ->
    smem sr (f_inst fr) = Some m ->
    (* Local x holds address to 1st i64 *)
    local_holds_address_to_i64 sr fr x addrx (Int64.repr (to_Z n1)) m bsx ->
    (* Local y holds address to 2nd i64 *)
    local_holds_address_to_i64 sr fr y addry (Int64.repr (to_Z n2)) m bsy ->
    (* There is enough free memory available *)
    (Z.of_N gmp_v + Z.of_N page_size <= Z.of_N (mem_length m) < Int32.modulus)%Z ->
    sglob_val sr (f_inst fr) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
    exists (sr': store_record) m',
      (forall instrs,
          reduce_trans
            (state, sr, fr, map AI_basic (apply_exact_add_operation global_mem_ptr glob_tmp1 x y addone) ++ instrs)
            (state, sr', fr, ($VN (VAL_int32 (N_to_i32 (gmp_v + 8)%N))) :: instrs))
      /\ INV sr' fr
      /\ smem sr' (f_inst fr) = Some m'
      (* gmp points to next free segment of memory *)
      /\ sglob_val sr' (f_inst fr) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp_v + 16))))
      (* address gmp points to i64 result *)
      /\ load_i64 m' gmp_v = Some (VAL_int64 (Int64.repr (to_Z (n1 + n2)%uint63)))
      (* address gmp + 8 points to either ordinal of C0 or C1, depending on if there is a carry *)
      /\ (~ (to_Z (n1 + n2) < to_Z n1)%Z -> load_i32 m' (gmp_v + 8)%N = Some (VAL_int32 (N_to_i32 C0_ord)))
      /\ ((to_Z (n1 + n2) < to_Z n1)%Z -> load_i32 m' (gmp_v + 8)%N = Some (VAL_int32 (N_to_i32 C1_ord)))
      (* address gmp + 12 points to the address of the result (gmp) *)
      /\ load_i32 m' (gmp_v + 12)%N = Some (VAL_int32 (N_to_i32 gmp_v))
      /\ s_funcs sr = s_funcs sr'
      /\ mem_length m = mem_length m'
      /\ repr_val_LambdaANF_Wasm v sr' (f_inst fr) (Val_ptr (gmp_v + 8)%N)
      (* Values are preserved *)
      /\ (forall (wal : wasm_value) (val : cps.val),
             repr_val_LambdaANF_Wasm val sr (f_inst fr) wal ->
             repr_val_LambdaANF_Wasm val sr' (f_inst fr) wal).
Proof.
  intros state sr fr m gmp addrx addry bsx bsy n1 n2 c0_tag c1_tag it_carry v HINV Hc0 Hc1 Hv Hmem (Hxinframe & Hloadx & Hdesx) (Hyinframe & Hloady & Hdesy) HgmpBounds Hgmp.
  have I := HINV. destruct I as (_&_&_& _ &_&_&_&_&_&_& HnoGlobDups &_&_& Hmult2 &_&_& Hi64tempsW).
  assert (Hglob_tmp1: i64_glob glob_tmp1) by now constructor.
  destruct (Hi64tempsW _ Hglob_tmp1 (VAL_int64 (Int64.repr (to_Z (n1 + n2)%uint63)))) as [sr1 Hsr1].
  assert (HINV1 : INV sr1 fr). {
    apply update_global_preserves_INV with (sr:=sr) (i:=glob_tmp1) (m:=m) (num:=(VAL_int64 (Int64.repr (to_Z (n1 + n2)%uint63)))); auto.
    discriminate.
    intro; discriminate.
    intro; discriminate. }
  assert (Hsfs1 : s_funcs sr = s_funcs sr1) by now eapply update_global_preserves_funcs; eauto.
  assert (Hmem1 : smem sr1 (f_inst fr) = Some m) by now apply update_global_preserves_memory in Hsr1.
  assert (Hgmp1 : sglob_val sr1 (f_inst fr) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp)))). {
    apply update_global_get_other with (j:=glob_tmp1) (sr:=sr) (num:=(VAL_int64 (Int64.repr (to_Z (n1 + n2)%uint63)))); auto. discriminate. }
  assert (HresVal : sglob_val sr1 (f_inst fr) glob_tmp1 = Some (VAL_num (VAL_int64 (Int64.repr (to_Z (n1 + n2)%uint63))))) by now apply update_global_get_same with (sr:=sr); auto.

  assert (-1 < Z.of_N gmp < Int32.modulus)%Z by now simpl_modulus; simpl_modulus_in HgmpBounds; cbn in HgmpBounds |- *.

  destruct (Hmult2 _ _ Hmem Hgmp H) as (n & Hgmpmult2); clear H.

  have HcarryRedC0 := make_carry_reduce C0_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC0 as (sr_C0 & m_C0 & Hmake_carry_red_C0 & HINV_C0 & Hmem_C0 & Hgmp_C0 & HloadRes_C0 & HloadOrd_C0 & HloadArg_C0 & Hpres64_C0 & Hpres32_C0 & Hsfs_C0 & Hmemlength_C0).

  assert (HnewgmpBoundsC0: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C0) < Int32.modulus)%Z) by now simpl_modulus; simpl_modulus_in HgmpBounds; cbn in HgmpBounds |- *.

  assert (HconstrArgsC0: @repr_val_constr_args_LambdaANF_Wasm [:: Vprim (AstCommon.primInt; (n1 + n2)%uint63)] sr_C0 (f_inst fr) (4 + (gmp+8))%N). {
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); try lia; eauto.
    unfold wasm_value_to_i32, wasm_value_to_u32; replace (4 + (gmp + 8))%N with (gmp +12)%N;[auto|lia].
    eapply Rprim_v with (gmp:=(gmp + 16)%N); try lia; eauto.
    now constructor. }

  assert (HvalC0: repr_val_LambdaANF_Wasm (Vconstr c0_tag [Vprim (AstCommon.primInt ; (n1 + n2)%uint63)]) sr_C0 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
      eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C0_ord)) (t:=c0_tag) (sr:=sr_C0) (m:=m_C0) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C0_ord); auto; try lia.
      - unfold get_ctor_ord; now rewrite Hc0.
      - unfold get_ctor_arity; now rewrite Hc0.
      - now exists (n+4)%N.  }

  have HcarryRedC1 := make_carry_reduce C1_ord state sr1 fr m _ _ HINV1 Hmem1 Hgmp1 HgmpBounds HresVal.
  destruct HcarryRedC1 as (sr_C1 & m_C1 & Hmake_carry_red_C1 & HINV_C1 & Hmem_C1 & Hgmp_C1 & HloadRes_C1 & HloadOrd_C1 & HloadArg_C1 & Hpres64_C1 & Hpres32_C1 & Hsfs_C1 & Hmemlength_C1).

  assert (HnewgmpBoundsC1: (Z.of_N (gmp + 16) + 8 <= Z.of_N (mem_length m_C1) < Int32.modulus)%Z) by now simpl_modulus; simpl_modulus_in HgmpBounds; cbn in HgmpBounds |- *.
    
  assert (HconstrArgsC1: repr_val_constr_args_LambdaANF_Wasm [:: Vprim (AstCommon.primInt; (n1 + n2)%uint63)] sr_C1  (f_inst fr) (4 + (gmp+8))%N). { 
    eapply Rcons_l with (wal:=(Val_ptr gmp)) (gmp:=(gmp+16)%N); try lia; eauto.
    unfold wasm_value_to_i32, wasm_value_to_u32; replace (4 + (gmp + 8))%N with (gmp +12)%N;[auto|lia].
    eapply Rprim_v with (gmp:=(gmp + 16)%N); try lia; eauto.
    now constructor. }

  assert (HvalC1: repr_val_LambdaANF_Wasm (Vconstr c1_tag [Vprim (AstCommon.primInt ; (n1 + n2)%uint63)]) sr_C1 (f_inst fr) (Val_ptr (gmp + 8)%N)). {
      eapply Rconstr_boxed_v with (v:=Int32.repr (Z.of_N C1_ord)) (t:=c1_tag) (sr:=sr_C1) (m:=m_C1) (gmp:=(gmp+16)%N) (addr:=(gmp + 8)%N) (arity:=1) (ord:=C1_ord); auto; try lia.
      - unfold get_ctor_ord; now rewrite Hc1.
      - unfold get_ctor_arity; now rewrite Hc1.
      - now exists (n+4)%N.  }

  destruct addone eqn:Haddone.
  { (* addcarryc: Compute x + y + 1 and check if there is overflow *)
    admit. (* TODO: addcarryc *)
  } { (* addc: Compute x + y and check if there is overflow *)
    destruct Hv as [[Heq Hv]|[Heq Hv]]; subst v;
(* destruct (Z_lt_dec (to_Z (n1 + n2)) (to_Z n1)); *)
    [exists sr_C0, m_C0|exists sr_C1, m_C1];
    (* First reduce instructions *)
    split. 1, 3: apply_exact_reduce_aux1 Hdesx Hdesy.
    (* Reduce remaining instructions:  *)
(*        - 1st case: There is a carry *)
(*        - 2nd case: There is no carry *)
    apply_exact_reduce_aux2 (VAL_int64 (Int64.repr (to_Z (n1 + n2)))) Hdesx rs_if_false uint63_nlt_int64_nlt carryInstrsC0 Hmake_carry_red_C0.
    apply_exact_reduce_aux2 (VAL_int64 (Int64.repr (to_Z (n1 + n2)))) Hdesx rs_if_true uint63_lt_int64_lt carryInstrsC1 Hmake_carry_red_C1.
    (* The assumption for the remaining goals for both cases are already in the context *)
    all: repeat (split; auto); try now intros.
    all: intros; eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr) (m:=m) (gmp:=gmp) (gmp':=(gmp + 16)%N); eauto; try lia; now erewrite ->Hsfs1; eauto.
Admitted.

Ltac dep_destruct_primint v p x :=
  try dependent destruction v; try discriminate; dependent destruction p; dependent destruction x; try discriminate.
(* Application of primitive operators can never evaluate to a function value *)
Lemma primop_value_not_funval :
  forall p pfs f' vs v op op_name str b op_arr,
    prim_funs_env_wellformed cenv penv pfs ->
    M.get p pfs = Some f' ->
    M.get p penv = Some (op_name, str, b, op_arr) ->
    KernameMap.find op_name primop_map = Some op ->
    f' vs = Some v ->
    forall rho fds f0, ~ subval_or_eq (Vfun rho fds f0) v.
Proof.
  intros.
  destruct (H p op_name str b op_arr op f' vs v H1 H2 H0 H3) as
    [true_tag [false_tag [it_bool [eq_tag [lt_tag [gt_tag [it_comparison [c0_tag [c1_tag [it_carry [pair_tag [it_prod (Happ & _)]]]]]]]]]]]].
  clear H2.
  assert (H' : forall p', (Vfun rho fds f0) <> Vprim p') by now intros.
  assert (HunaryConstr : forall tag p', ~ subval_or_eq (Vfun rho fds f0) (Vconstr tag [Vprim p'])). {
    intros. intro Hcontra.
    destruct (rt_then_t_or_eq _ _ _ _ Hcontra); try discriminate.        
    destruct (subval_v_constr _ _ _ H2) as (? & Hsubconst & Hin).
    destruct Hin;[subst x; now destruct (subval_or_eq_fun_not_prim _ p' H')|destruct H4]. }
  assert (HbinaryConstr : forall tag p1 p2, ~ subval_or_eq (Vfun rho fds f0) (Vconstr tag [Vprim p1 ; Vprim p2])). {
    intros. intro Hcontra.
    destruct (rt_then_t_or_eq _ _ _ _ Hcontra); try discriminate.        
    destruct (subval_v_constr _ _ _ H2) as (? & Hsubconst & Hin).
    destruct Hin as [Hx|Hin];[|destruct Hin as [Hx'|Hempty];[|now inv Hempty]];subst x;[now destruct (subval_or_eq_fun_not_prim _ p1 H')|now destruct (subval_or_eq_fun_not_prim _ p2 H')]. }
  destruct vs eqn:Hvs1. now unfold apply_LambdaANF_primInt_operator in Happ.
  destruct l. { (* Unary operators *)
    destruct op; unfold apply_LambdaANF_primInt_operator in Happ; dep_destruct_primint v0 p0 x; 
      unfold LambdaANF_primInt_unop_fun in Happ;
      inversion Happ;
      now apply subval_or_eq_fun_not_prim. }
  destruct l. { (* Binary operators *)
    destruct op; unfold apply_LambdaANF_primInt_operator in Happ; 
    dep_destruct_primint v0 p0 x; dep_destruct_primint v1 p1 x; 
    unfold LambdaANF_primInt_arith_fun, LambdaANF_primInt_bool_fun, LambdaANF_primInt_compare_fun, LambdaANF_primInt_carry_fun, LambdaANF_primInt_prod_fun in Happ;
    inversion Happ;
    try now apply subval_or_eq_fun_not_prim.
    - destruct (p0 =? p1)%uint63; intro Hcontra;
      (destruct (rt_then_t_or_eq _ _ _ _ Hcontra);[auto; discriminate|now destruct (subval_v_constr _ _ _ H2)]).
    - destruct (p0 <? p1)%uint63; intro Hcontra;
      (destruct (rt_then_t_or_eq _ _ _ _ Hcontra);[auto; discriminate|now destruct (subval_v_constr _ _ _ H2)]).
    - destruct (p0 <=? p1)%uint63; intro Hcontra;
      (destruct (rt_then_t_or_eq _ _ _ _ Hcontra);[auto; discriminate|now destruct (subval_v_constr _ _ _ H2)]).
    - destruct (p0 ?= p1)%uint63; intro Hcontra;
      (destruct (rt_then_t_or_eq _ _ _ _ Hcontra);[auto; discriminate|now destruct (subval_v_constr _ _ _ H2)]).
    - destruct (p0 +c p1)%uint63; eapply HunaryConstr.
    - destruct (addcarryc p0 p1)%uint63; eapply HunaryConstr.
    - destruct (p0 -c p1)%uint63; eapply HunaryConstr.
    - destruct (subcarryc p0 p1)%uint63; eapply HunaryConstr.
    - eapply HbinaryConstr.
    - eapply HbinaryConstr. }
  destruct l. { (* Ternary operators *)
    destruct op; unfold apply_LambdaANF_primInt_operator in Happ; 
    dep_destruct_primint v0 p0 x;
    dep_destruct_primint v1 p1 x;
    dep_destruct_primint v2 p2 x;
    unfold LambdaANF_primInt_diveucl_21, LambdaANF_primInt_addmuldiv in Happ;
    inversion Happ.
    - destruct (diveucl_21 p0 p1 p2); eapply HbinaryConstr.
    - try now apply subval_or_eq_fun_not_prim. }
  (* There are no operators with arity > 3 *)
  destruct op; unfold apply_LambdaANF_primInt_operator in Happ; 
    dep_destruct_primint v0 p0 x;
    dep_destruct_primint v1 p1 x;
    dep_destruct_primint v2 p2 x.
Qed.

Lemma primitive_operation_reduces : forall lenv pfs state s f m fds f' (x : var) (x' : localidx) (p : prim) op_name str b op_arr op
                                           (ys : list var) (e : exp) (vs : list val) (rho : env) (v : val) (gmp_v : u32) instrs,
    prim_funs_env_wellformed cenv penv pfs ->
    M.get p pfs = Some f' ->
    M.get p penv = Some (op_name, str, b, op_arr) ->
    KernameMap.find op_name primop_map = Some op ->
    map_injective lenv ->
    domains_disjoint lenv fenv ->
    (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
    (forall var varIdx, @repr_var nenv lenv var varIdx -> N.to_nat varIdx < length (f_locs f)) ->
    @repr_var nenv lenv x x' ->
    @rel_env_LambdaANF_Wasm lenv (Eprim x p ys e) rho s f fds ->
    @repr_primitive_operation nenv lenv op ys instrs ->
    INV s f ->
    smem s (f_inst f) = Some m ->
    sglob_val s (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v))) ->
    (Z.of_N gmp_v + Z.of_N page_size < Z.of_N (mem_length m))%Z ->
    get_list ys rho = Some vs ->
    f' vs = Some v ->
    exists s' f', reduce_trans
                    (state, s, f, map AI_basic (instrs ++ [ BI_local_set x' ])) (state, s', f', []) /\
                    INV s' f' /\
                    f_inst f = f_inst f' /\
                    s_funcs s = s_funcs s' /\
                    @rel_env_LambdaANF_Wasm lenv e (M.set x v rho) s' f' fds /\
                    (forall (wal : wasm_value) (val : cps.val),
                        repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
                        repr_val_LambdaANF_Wasm val s' (f_inst f') wal) /\
                    (exists wal,
                        f' = {|f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                             ; f_inst := f_inst f|} /\
                          repr_val_LambdaANF_Wasm v s' (f_inst f') wal).
Proof.
  intros ??????????????????????? Hpfs Hf' Hpenv Hop HlenvInjective Hdisjoint HfenvWf HlocsInBounds Hrepr_x
    HrelE HprimRepr Hinv Hmem Hgmp HenoughM Hys_vs HprimResSome.
  remember {| f_locs := set_nth (VAL_num (N_to_value gmp_v)) (f_locs f) (N.to_nat x') (VAL_num (N_to_value gmp_v))
           ; f_inst := f_inst f
           |} as fr'.
  have Hnofunval := primop_value_not_funval _ _ _ _ _ _ _ _ _ _ Hpfs Hf' Hpenv Hop HprimResSome.
  have Hpfs' := Hpfs _ _ _ _ _ _ _ vs v Hpenv Hop Hf' HprimResSome.
  clear Hop.
  have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
  destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [<- [Hmem4 Hmem5]]]]]].
  assert (m' = m) by congruence. subst m'.
  assert ((Z.of_N gmp_v < Wasm_int.Int32.modulus)%Z). {
    apply mem_length_upper_bound in Hmem5. cbn in Hmem5. simpl_modulus. cbn. lia. }
  rename x into x0, x' into x0'.
  inv HprimRepr.
  { (* Unary operations *) admit. }
  { (* Binary operations *)
    assert (forall w,
             exists mem, store m (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                           (bits (VAL_int64 w))
                           8 = Some mem) as Htest. {
      intros.
      apply enough_space_to_store. cbn.
      assert ((Datatypes.length (serialise_i64 w)) = 8) as Hl.
      { unfold serialise_i64, encode_int, bytes_of_int, rev_if_be.
        destruct (Archi.big_endian); reflexivity. } rewrite Hl. clear Hl. cbn.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
      unfold page_size in HenoughM. lia. }

    assert (forall n,
               exists s' s_final fr m' wal,
                 s' = upd_s_mem s (set_nth m' s.(s_mems) 0 m')
                 /\ smem_store s (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                      (VAL_int64 (Z_to_i64 (to_Z n))) T_i64 = Some s'
                 /\ fr ={| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                        ; f_inst := f_inst f
                        |}
                 /\ smem s' (f_inst fr) = Some m'
                 /\ reduce_trans (state, s', f, map AI_basic [ BI_global_get global_mem_ptr
                                                               ; BI_global_get global_mem_ptr
                                                               ; BI_const_num (nat_to_value 8)
                                                               ; BI_binop T_i32 (Binop_i BOI_add)
                                                               ; BI_global_set global_mem_ptr
                                                               ; BI_local_set x0'
                      ])
                      (state, s_final, fr, [::])

                 /\ INV s' fr
                 /\ supdate_glob s' (f_inst f) global_mem_ptr
                      (VAL_num (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 8)))) = Some s_final
                 /\ INV s_final fr
                 /\ f_inst f = f_inst fr
                 /\ s_funcs s = s_funcs s_final
                 /\ rel_env_LambdaANF_Wasm (lenv:=lenv) e (M.set x0 (Vprim (primInt n)) rho) s_final fr fds
                 /\ (forall (wal : wasm_value) (v : val),
                        repr_val_LambdaANF_Wasm v s (f_inst f) wal -> repr_val_LambdaANF_Wasm v s_final (f_inst fr) wal)
                 /\ (exists wal,
                        fr ={| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                            ; f_inst := f_inst f |}
                        /\ repr_val_LambdaANF_Wasm (Vprim (primInt n)) s_final (f_inst fr) wal)). {
      intros.
      destruct (Htest (Z_to_i64 (to_Z n))) as [m' Hm'].
      remember (upd_s_mem s (set_nth m' s.(s_mems) 0 m')) as s'.
      exists s'.
      assert (Hm'': smem_store s (f_inst f) (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) 0%N
                      (VAL_int64 (Z_to_i64 (to_Z n))) T_i64 = Some s'). {
        unfold smem_store. rewrite Hmem1. cbn. subst s'.
        unfold smem in Hmem2. rewrite Hmem1 in Hmem2. destruct (s_mems s)=>//.
        injection Hmem2 as ->. now rewrite Hm'. }
      assert (Hinv' : INV s' f). {
        subst.
        assert (mem_length m = mem_length m'). {
          apply mem_store_preserves_length in Hm'. congruence. }
        assert (mem_max_opt m = mem_max_opt m'). {
          apply mem_store_preserves_max_pages in Hm'. congruence. }
        eapply update_mem_preserves_INV. apply Hinv. eassumption. erewrite <- H3. lia.
        congruence. exists (mem_size m); split; auto. unfold mem_size. congruence. reflexivity. }
      have I := Hinv'. destruct I as [_ [_ [_ [Hgmp_w [_ [Hglob_mut [Hlinmem' [Hgmp' [_ [_ [_ [_ [_ [Hgmp_mult_two]]]]]]]]]]]]]].
      destruct Hlinmem' as [Hmem1' [m'' [Hmem2' [size' [Hmem3' [Hmem4' Hmem5']]]]]].
      destruct (Hgmp_w (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp_v) (nat_to_i32 8)))) as [s_final Hupd_glob].
      assert (smem s' (f_inst f) = Some m'). {
        subst s'. unfold smem, lookup_N. cbn.
        rewrite Hmem1'. apply set_nth_nth_error_same with (e:=m).
        unfold smem in Hmem. rewrite Hmem1 in Hmem.
        destruct (s_mems s)=>//. }
      assert (m' = m'') by congruence. subst m''.
      assert (HgmpBound': (gmp_v + 8 + 8 < mem_length m')%N). {
        assert (mem_length m = mem_length m') by
          now apply mem_store_preserves_length in Hm'.
        replace (mem_length m') with (mem_length m).
        now unfold page_size in *. }
      remember {| f_locs := set_nth (VAL_num (N_to_value gmp_v)) (f_locs f) (N.to_nat x0') (VAL_num (N_to_value gmp_v))
               ; f_inst := f_inst f
               |} as fr.
      assert (Hinv'': INV s' fr). {
        apply update_local_preserves_INV with (f:=f) (x':=N.to_nat x0') (v:=N_to_i32 gmp_v).
        assumption. apply HlocsInBounds with (var:=x0). assumption. assumption.
      }
      assert (Hsglobval_s':sglob_val s' (f_inst f) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by
        now apply (memory_store_preserves_globals s f) with m'.
      assert (Hgmp_w' : INV_global_mem_ptr_writable s' f) by now destruct Hinv'.
      assert (Z.of_N (gmp_v + 8)%N < Wasm_int.Int32.modulus)%Z as HgmpModulus by now
          apply mem_length_upper_bound in Hmem5; simpl_modulus; cbn in Hmem5 |- *.
      have HincGmp := increment_global_mem_ptr_reduce s' f 8%N state gmp_v Hgmp_w' Hsglobval_s' HgmpModulus.
      assert (HfsEq: s_funcs s = s_funcs s') by now subst.
      assert (HfsEq': s_funcs s' = s_funcs s_final) by now apply update_global_preserves_funcs in Hupd_glob.
      assert (HfsEq'': s_funcs s = s_funcs s_final) by now subst.
      assert (HgmpBound: (-1 < Z.of_N (gmp_v + 8) < Wasm_int.Int32.modulus)%Z). {
        apply mem_length_upper_bound in Hmem5. simpl_modulus_in Hmem5. cbn in Hmem5.
        simpl_modulus. cbn. lia.
      }

      assert (HenoughM': (gmp_v + page_size < mem_length m')%N). {
        assert (mem_length m = mem_length m') by
          now apply mem_store_preserves_length in Hm'.
        replace (mem_length m') with (mem_length m). lia. }

      assert True by auto.

      assert (Hinv_final : INV s_final fr). {
        eapply update_global_preserves_INV with (i:=global_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp_v + 8)))); eauto.
        left. split. apply gmp_i32_glob. now cbn. discriminate.
        now subst fr.
        move => _. intros. 
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]. assumption.
        now subst s'.
        lia.
        destruct H6 as [Heqn0 Hboundn0]. 
        replace n0 with (gmp_v + 8)%N. lia.
        inv Heqn0. 
        repeat rewrite Int32.Z_mod_modulus_id in H7. lia. lia. lia.
        move => _. intros. 
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]. assumption.
        now subst s'.
        lia.
        destruct H6 as [Heqn0 Hboundn0]. 
        replace n0 with (gmp_v + 8)%N. 
        exists (n0' + 4)%N; lia.
        inv Heqn0. 
        repeat rewrite Int32.Z_mod_modulus_id in H7. lia. lia. lia.
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in Hupd_glob.
        rewrite Heqfr. cbn in Hupd_glob |- *.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in Hupd_glob.        
        unfold N_to_i32. 
        now replace (Z.of_N gmp_v + 8)%Z with (Z.of_N (gmp_v + 8))%Z in * by lia.
        lia.
      }

      destruct HincGmp as [sr' (HincReduce & Hglob_sr')].

      assert (Hinv_sr' : INV sr' fr). {
        eapply update_global_preserves_INV with (sr:=s') (i:=global_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp_v+8)))); eauto.
        left. split. apply gmp_i32_glob. now cbn. discriminate.
        now subst fr.
        move => _. 
        intros n0 [Heqn0 Hboundn0]. 
        replace n0 with (gmp_v + 8)%N. lia.
        inversion Heqn0.
        repeat rewrite Int32.Z_mod_modulus_id in H7. lia. lia. lia.
        move => _. 
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0' Hn0]; auto. lia.
        intros n0 [Heqn0 Hboundn0].
        replace n0 with (gmp_v + 8)%N. 
        exists (n0' + 4)%N. lia.
        inversion Heqn0.
        repeat rewrite Int32.Z_mod_modulus_id in H7. lia. lia. lia.
        now subst fr.
      }
        
      assert (Hrepr_val : repr_val_LambdaANF_Wasm (Vprim (primInt n)) sr' (f_inst fr) (Val_ptr gmp_v)). {
        apply Rprim_v with (gmp:=(gmp_v+8)%N) (m:=m'); auto.
        subst fr. eapply update_global_get_same. eassumption.
        lia.
        destruct Hgmp_mult_two with (gmp_v:=gmp_v) (m:=m') as [n0 Hn0].
        assumption. assumption. lia. exists n0. lia.
        replace (smem sr' (f_inst fr)) with (smem s' (f_inst fr)) by now subst fr; eapply update_global_preserves_memory.
        now subst fr.
        assert ((wasm_deserialise (bits (VAL_int64 (Z_to_i64 (to_Z n)))) T_i64) = (VAL_int64 (Z_to_i64 (to_Z n)))) by now apply deserialise_bits.
        rewrite -H6.
        apply (store_load_i64 m m' gmp_v (bits (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
        assert (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v) = gmp_v). {
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        rewrite -H7.
        apply Hm'. }
      assert (HvalsPreserved : forall (wal : wasm_value) (v : val),
                 repr_val_LambdaANF_Wasm v s (f_inst f) wal -> repr_val_LambdaANF_Wasm v sr' (f_inst fr) wal). {
        intros.
        apply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s) (m:=m) (m':=m') (gmp:=gmp_v) (gmp':=(gmp_v + 8)%N); auto.
        replace (s_funcs s) with (s_funcs s') by auto.
        now apply update_global_preserves_funcs in Hglob_sr'.
        now subst fr.
        replace (smem sr' (f_inst fr)) with (smem s' (f_inst fr)) by now subst fr; eapply update_global_preserves_memory.
        now subst fr.
        now subst fr.
        { simpl_modulus. cbn. simpl_modulus_in H1. cbn in H1. simpl_modulus_in HgmpBound.
          apply mem_length_upper_bound in Hmem5.
          unfold page_size, max_mem_pages in *. lia. }
        apply update_global_get_same with (sr:=s').
        now subst fr.
        { simpl_modulus. cbn.
          subst size'.
          apply mem_length_upper_bound in Hmem5'.
          unfold page_size, max_mem_pages in *.
          lia. }
        lia.
        { intros.
          assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. subst.
            simpl_modulus_in HenoughM'.
            apply mem_store_preserves_length in Hm'. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'.
          symmetry.
          apply (load_store_load_i32' m m' a (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) v' (bits (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        { intros a Ha.
          assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i64' m m' a (Wasm_int.N_of_uint i32m (N_to_i32 gmp_v)) v' (bits (VAL_int64 (Z_to_i64 (to_Z n))))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }
        now subst fr. }
      assert (HrelE' : rel_env_LambdaANF_Wasm (lenv:=lenv) e (M.set x0 (Vprim (primInt n)) rho) sr' fr fds). {
        have Hl := HlocsInBounds _ _ Hrepr_x.
        apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl as [? Hlx].
        unfold rel_env_LambdaANF_Wasm.
        destruct HrelE as [Hfun1 [Hfun2 Hvar]].
        split.
        { (* funs1 *)
          intros ????? Hrho Hv'.
          destruct (var_dec x0 x2).
          { (* x = x1 *)
            subst x2. rewrite M.gss in Hrho. inv Hrho.
            assert (~ subval_or_eq (Vfun rho' fds' f0) (Vprim (primInt n))). { apply subval_or_eq_fun_not_prim. intros. congruence. }
            contradiction.
          }
          { (* x <> x1 *) rewrite M.gso in Hrho; eauto. }
        } split.
        { intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
          destruct Hnfd as [i' [Htrans Hval]].
          exists i'. split. assumption.
          apply val_relation_func_depends_on_funcs with (s:=s); auto.
          replace (s_funcs s) with (s_funcs s') by auto.
          now apply update_global_preserves_funcs in Hglob_sr'.        
          now subst fr.
        }
        {
          intros. destruct (var_dec x0 x2).
          { (* x = x1 *)
            subst x2. exists (Vprim (primInt n)), (Val_ptr gmp_v).
            rewrite M.gss. split; auto.
            split.
            exists x0'. cbn. split. intros.
            inv Hrepr_x.  unfold translate_var. unfold translate_var in H8.
            destruct (lenv ! x0) eqn:Hx; rewrite Hx in H8=>//. injection H8 as ->.
            now rewrite Hx.
            unfold lookup_N; cbn; auto.
            subst fr. cbn. erewrite set_nth_nth_error_same; eauto.
            now subst fr.
          }
          { (* x <> x1 *)
            assert (Hocc : occurs_free (Eprim x0 p [:: x ; y] e) x2) by now apply Free_Eprim2.
            have H' := Hvar _ Hocc H7.
            destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
            exists val', wal'. split.
            rewrite M.gso; auto. split.
            destruct Hloc as [i' [Hl1 Hl2]].
            unfold stored_in_locals. exists i'. split; auto.
            subst fr. unfold lookup_N.
            rewrite set_nth_nth_error_other; auto.
            inv Hrepr_x.
            specialize Hl1 with err_str.
            intro. assert (x0' = i') by lia. subst x0'.
            unfold translate_var in Hl1, H8.
            destruct (lenv ! x2) eqn:Hlx1; rewrite Hlx1 in Hl1=>//.
            destruct (lenv ! x0) eqn:Hlx2; rewrite Hlx2 in H8=>//.
            have H'' := HlenvInjective _ _ _ _ n0 Hlx2 Hlx1. congruence.
            apply nth_error_Some. congruence.
            now apply HvalsPreserved.
          }
        }
      }
      exists sr', fr, m', (Val_ptr gmp_v).
      try repeat (split; auto). all: subst fr; auto.
      assert (sglob_val s' (f_inst f) global_mem_ptr =
                Some (VAL_num (VAL_int32 (N_to_i32 gmp_v)))) by now subst s'.
      separate_instr.
      dostep_nary 0. eapply r_global_get.
      eassumption.
      eapply rt_trans.
      eapply app_trans_const; auto.
      apply HincReduce.
      apply rt_step.
      eapply r_local_set. reflexivity.
      apply /ssrnat.leP.
      apply HlocsInBounds in Hrepr_x. lia.
      reflexivity.
      cbn; unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add; cbn.
      
      rewrite Wasm_int.Int32.Z_mod_modulus_id; [|lia].      
      unfold N_to_i32 in Hglob_sr'.
      replace 8%Z with (Z.of_N 8) by now cbn.
      rewrite -N2Z.inj_add.
      assumption.
      replace (s_funcs s) with (s_funcs s') by auto.
      now apply update_global_preserves_funcs in Hglob_sr'.        
      exists (Val_ptr gmp_v).
      split; auto. }

    assert (HunaryConstrValRelEnv: forall sr fr t ord p addr,
               v = Vconstr t [Vprim (AstCommon.primInt ; p)] ->
               get_ctor_arity cenv t = Ret 1 ->
               get_ctor_ord cenv t = Ret ord ->
               fr = {|f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 8)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 8)%N))));
                   f_inst := f_inst f|} ->
               repr_val_LambdaANF_Wasm v sr (f_inst fr) (Val_ptr addr) ->
               s_funcs s = s_funcs sr ->
               nth_error (f_locs fr) (N.to_nat x0') = Some (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr addr)))) ->
               (Z.of_N ord < Wasm_int.Int32.half_modulus)%Z ->
               (forall (wal0 : wasm_value) (v0 : val),
                   repr_val_LambdaANF_Wasm v0 s (f_inst f) wal0 -> repr_val_LambdaANF_Wasm v0 sr (f_inst fr) wal0) -> rel_env_LambdaANF_Wasm (lenv:=lenv) e (M.set x0 v rho) sr fr fds). {
      intros.
      subst fr.
      have Hl := HlocsInBounds _ _ Hrepr_x.
      apply nth_error_Some in Hl.
      apply notNone_Some in Hl. destruct Hl as [? Hlx].
      destruct HrelE as [Hfun1 [Hfun2 Hvar]].
      split. {
        intros ????? Hrho Hv'.
        destruct (var_dec x0 x2).
        - (* x0 = x1 *) (* v0 can never be a function value, by assumption on primops *)
          subst x2. rewrite M.gss in Hrho; eauto.
          inversion Hrho. subst v0.
          have H'' := Hnofunval rho' fds' f0.
          contradiction.
        - (* x0 <> x1 *) rewrite M.gso in Hrho; eauto.
      } split. {
        intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
        destruct Hnfd as [i' [Htrans HvalFun]].
        exists i'. split. assumption.
        apply val_relation_func_depends_on_funcs with (s:=s); auto.
      } {
        intros x2 Hx2free Hx2notfun. 
        destruct (var_dec x0 x2).
        { (* x = x1 *)
          subst x2.
          exists v, (Val_ptr addr).
          rewrite M.gss. split; auto.
          split.
          exists x0'. cbn. split. intros.
          inv Hrepr_x.  unfold translate_var. unfold translate_var in H7.
          destruct (lenv ! x0) eqn:Hx; rewrite Hx in H7=>//. injection H7 as ->.
          now rewrite Hx.
          unfold lookup_N; cbn; auto.
          assumption. 
        }
        { (* x <> x1 *)
          assert (Hocc : occurs_free (Eprim x0 p [:: x ; y] e) x2) by now apply Free_Eprim2.              
          have H' := Hvar _ Hocc Hx2notfun.
          destruct H' as [val' [wal' [Hrho [Hloc Hval']]]].
          exists val', wal'. split.
          rewrite M.gso; auto. split.
          destruct Hloc as [i' [Hl1 Hl2]].
          unfold stored_in_locals. exists i'. split; auto.
          unfold lookup_N.
          rewrite set_nth_nth_error_other; auto.
          inv Hrepr_x.
          specialize Hl1 with err_str.
          intro. assert (x0' = i') by lia. subst x0'.
          unfold translate_var in Hl1, H7.
          destruct (lenv ! x2) eqn:Hlx1; rewrite Hlx1 in Hl1=>//.
          destruct (lenv ! x0) eqn:Hlx2; rewrite Hlx2 in H7=>//.
          have H'' := HlenvInjective _ _ _ _ n Hlx2 Hlx1. congruence.
          eapply HlocsInBounds; eauto.
          now apply H12.
        } } }

    assert (forall t ord,
               v = Vconstr t [] ->
               get_ctor_arity cenv t = Ret 0 ->
               get_ctor_ord cenv t = Ret ord ->
               (Z.of_N ord < Wasm_int.Int32.half_modulus)%Z ->
               exists fr wal,
                 INV s fr
                 /\ fr = {| f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)))
                         ; f_inst := f_inst f
                         |}
                 /\ repr_val_LambdaANF_Wasm v s (f_inst fr) wal
                 /\ rel_env_LambdaANF_Wasm (lenv:=lenv) e (M.set x0 v rho) s fr fds
                 /\ (forall (wal0 : wasm_value) (v : val),
                        repr_val_LambdaANF_Wasm v s (f_inst f) wal0 -> repr_val_LambdaANF_Wasm v s (f_inst fr) wal0)
                 /\ reduce_trans (state, s, f,
                        [ (v_to_e (VAL_num (VAL_int32 (wasm_value_to_i32 wal))))
                          ; AI_basic (BI_local_set x0') ]) (state, s, fr, [::])). {
      intros.
      remember {| f_locs := set_nth (VAL_num (N_to_value (2 * ord + 1))) (f_locs f) (N.to_nat x0') (VAL_num (N_to_value (2 * ord + 1)))
               ; f_inst := f_inst f
               |} as fr.
      assert (Hinv' : INV s fr). {
        apply update_local_preserves_INV with (f:=f) (x':=N.to_nat x0') (v:=(N_to_i32 (2 * ord + 1))).
        assumption.
        apply HlocsInBounds with (var:=x0). assumption.
        now subst fr. }

      assert (HvalsPreserved:
               (forall (wal0 : wasm_value) (v0 : val),
                   repr_val_LambdaANF_Wasm v0 s (f_inst f) wal0 -> repr_val_LambdaANF_Wasm v0 s (f_inst fr) wal0)) by now subst fr.

      assert (HreprVal: repr_val_LambdaANF_Wasm v s (f_inst fr) (Val_unboxed (2 * ord + 1)%N)). {
        rewrite H4.
        apply Rconstr_unboxed_v with (ord:=ord); auto.
        now rewrite N.mul_comm.
        simpl_modulus. simpl_modulus_in H7.
        cbn.
        destruct ord; lia.
      }

      assert (HrelE' : @rel_env_LambdaANF_Wasm lenv e (map_util.M.set x0 v rho) s fr fds). {
        have Hl := HlocsInBounds _ _ Hrepr_x.
        apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl as [? Hlx].

        destruct HrelE as [Hfun1 [Hfun2 Hvar]]. unfold rel_env_LambdaANF_Wasm. split.
        { intros. destruct (var_dec x0 x2).
          { subst x2. rewrite M.gss in H8. inv H8.
            apply subval_or_eq_fun in H9.
            destruct H9 as [v1 [Hr1 Hr2]]. inv Hr2.
          }
          { by rewrite M.gso in H8; eauto. }
        } split.
        { intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          exists i. split. assumption. now subst fr.
        }
        { intros. destruct (var_dec x0 x2).
          { subst x2.
            assert ( (Wasm_int.Int32.half_modulus < Wasm_int.Int32.modulus)%Z ) by now rewrite Wasm_int.Int32.half_modulus_modulus.
            exists (Vconstr t []), (Val_unboxed (2 * ord + 1)%N).
            rewrite M.gss. split. congruence.
            split.
            {
              unfold stored_in_locals. exists x0'. split.
              - unfold translate_var. inv Hrepr_x. unfold translate_var in H11.
                destruct (lenv ! x0) eqn:Hx; rewrite Hx in H11 =>//. injection H11 as ->. now rewrite Hx.
              - subst fr. unfold lookup_N, nat_to_value, nat_to_i32, wasm_value_to_i32. simpl.
                erewrite set_nth_nth_error_same; eauto.
            }
            {
              econstructor ; eauto.
              now rewrite N.mul_comm.
              {
                now inv HreprVal. }
            }
          }
          {
            assert (Hocc: occurs_free (Eprim x0 p [:: x; y] e) x2). { now apply Free_Eprim2. }
            have H' := Hvar _ Hocc H9.
            destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
            exists val', wal'.
            split. rewrite M.gso; auto.
            split. 2: now subst fr.
            destruct Hloc as [i [Hl1 Hl2]].
            unfold stored_in_locals. exists i. split; auto.
            subst fr.
            unfold lookup_N.
            rewrite set_nth_nth_error_other; auto.
            intro. assert (x0' = i) by lia. subst x0'. inv Hrepr_x.
            specialize Hl1 with err_str.
            unfold translate_var in Hl1, H11.
            destruct (lenv ! x2) eqn:Hlx1; rewrite Hlx1 in Hl1=>//. injection Hl1 as ->.
            destruct (lenv ! x0) eqn:Hlx2; rewrite Hlx2 in H11=>//. injection H11 as ->.
            have H'' := HlenvInjective _ _ _ _ n Hlx2 Hlx1. contradiction.
            apply nth_error_Some. congruence.
          }
        }
      }
      exists fr, (Val_unboxed (2 * ord + 1)%N).
      try repeat (split; auto).
      subst fr.
      apply rt_step. eapply r_local_set. reflexivity.
      apply /ssrnat.leP.
      apply HlocsInBounds in Hrepr_x. lia.
      reflexivity. }

    assert (exists n1 n2,
               rho ! x = Some (Vprim (primInt n1))
               /\ rho ! y = Some (Vprim (primInt n2))
               /\ vs = [ Vprim (primInt n1) ; Vprim (primInt n2) ]
           ). {
      clear H3 H4.
      destruct Hpfs' as  [? [? [? [? [? [? [? [? [? [? [? [? [Hres _]]]]]]]]]]]]].
      unfold get_list in *.
      destruct (rho ! x) eqn:Hrho_x. 2: discriminate.
      destruct (rho ! y) eqn:Hrho_y. 2: discriminate.
      assert (List.In v0 vs) by (inv Hys_vs; now constructor).
      assert (List.In v1 vs) by (inv Hys_vs; right; now constructor).
      destruct (apply_primop_only_defined_on_primInts _ vs v _ _ _ _ _ _ _ _ Hres v0 H3) as [n1 Hn1].
      destruct (apply_primop_only_defined_on_primInts _ vs v _ _ _ _ _ _ _ _ Hres v1 H4) as [n2 Hn2].
      exists n1, n2.
      split; subst; auto.
      split; subst; auto.
      congruence. }
    destruct H5 as [n1 [n2 [Hrho_x [Hrho_y Hvs]]]].
    assert (exists wal1,
               stored_in_locals (lenv:=lenv) x wal1 f /\ repr_val_LambdaANF_Wasm (Vprim ( primInt n1)) s (f_inst f) wal1). {
      destruct HrelE as [_ [_ Hvars]].
      assert (occurs_free (Eprim x0 p [:: x ; y ] e) x) by now (constructor; constructor).
      assert (HfdsNone_x: find_def x fds = None). {
        inv H0.
        unfold translate_var in H6.
        destruct (lenv ! x) eqn:Hx. 2: now rewrite Hx in H6.
        unfold domains_disjoint in Hdisjoint.
        apply Hdisjoint in Hx.
        apply HfenvWf_None with (f:=x) in HfenvWf. now rewrite HfenvWf.
      }
      have Hx := Hvars _ H5 HfdsNone_x. destruct Hx as [v1' [w1 [Hrho_x' [Hloc_x Hval_x]]]].
      exists w1; split; auto.
      now replace v1' with (Vprim (primInt n1)) in Hval_x by now rewrite Hrho_x in Hrho_x'; inv Hrho_x'.
    }
    destruct H5 as [wal1 [Hloc_x Hval_x]].
    assert (exists wal2,
               stored_in_locals (lenv:=lenv) y wal2 f /\ repr_val_LambdaANF_Wasm (Vprim (primInt n2)) s (f_inst f) wal2). {
      destruct HrelE as [_ [_ Hvars]].
      assert (occurs_free (Eprim x0 p [:: x ; y ] e) y) by now (constructor; right; constructor).
      assert (HfdsNone_y: find_def y fds = None). {
        inv H1.
        unfold translate_var in H6.
        destruct (lenv ! y) eqn:Hy. 2: now rewrite Hy in H6.
        unfold domains_disjoint in Hdisjoint.
        apply Hdisjoint in Hy.
        apply HfenvWf_None with (f:=y) in HfenvWf. now rewrite HfenvWf.
      }
      have Hy := Hvars _ H5 HfdsNone_y. destruct Hy as [v2' [w2 [Hrho_y' [Hloc_y Hval_y]]]].
      exists w2; split; auto.
      now replace v2' with (Vprim (primInt n2)) in Hval_y by now rewrite Hrho_y in Hrho_y'; inv Hrho_y'.
    }
    destruct H5 as [wal2 [Hloc_y Hval_y]].
    destruct Hloc_x as [? [Htrans Hx']].
    assert (x1 = x'). {
      inv H0.
      have H' := Htrans err_str.
      unfold translate_var in *.
      destruct (lenv ! x) eqn:Hx.
      congruence.
      now rewrite Hx in H5.
    }
    subst x1. clear Htrans.
    destruct Hloc_y as [? [Htrans Hy']].
    assert (x1 = y'). {
      inv H1.
      have H' := Htrans err_str.
      unfold translate_var in *.
      destruct (lenv ! y) eqn:Hy.
      congruence.
      now rewrite Hy in H5.
    }
    subst x1. clear Htrans.
    assert (Hrv1: exists addr1, wal1 = Val_ptr addr1
               /\ load_i64 m addr1 = Some (VAL_int64 (Z_to_i64 (to_Z n1)))). {
      inv Hval_x. replace m with m0 by congruence. exists addr. split; auto.
      remember (primInt n) as p1; remember (primInt n1) as p2.
      inversion H11; subst p1 p2.
      now replace n1 with n by now apply inj_pair2 in H13.
    }
    destruct Hrv1 as [addr1 Hload1].
    destruct Hload1 as [? Hload1]. subst wal1.
    unfold load_i64 in Hload1. destruct (load m addr1 0%N 8) eqn:Hload1'. 2: discriminate.
    assert (Haddr1: addr1 = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr1)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. now rewrite N2Z.id.
      inv Hval_x. lia. }
    assert (Hrv2: exists addr2, wal2 = Val_ptr addr2
               /\ load_i64 m addr2 = Some (VAL_int64 (Z_to_i64 (to_Z n2)))). {
      inv Hval_y. replace m with m0 by congruence. exists addr. split; auto.
      remember (primInt n) as p1; remember (primInt n2) as p2.
      inversion H11; subst p1 p2.
      now replace n2 with n by now apply inj_pair2 in H13.
    }
    destruct Hrv2 as [addr2 Hload2].
    destruct Hload2 as [? Hload2]. subst wal2.
    unfold load_i64 in Hload2. destruct (load m addr2 0%N 8) eqn:Hload2'. 2: discriminate.
    assert (addr2 = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr2)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. now rewrite N2Z.id.
      inv Hval_y. lia. }
    assert (HloadStep1: forall es,
               reduce_trans
                 (state, s, f, ([:: AI_basic (BI_local_get x')] ++
                                  [:: AI_basic (BI_load T_i64 None 2%N 0%N)] ++
                                  es))
                 (state, s, f, ([:: $V VAL_num (VAL_int64 (Z_to_i64 (to_Z n1))) ] ++ es))). {
      intros.
      dostep_nary 0. apply r_local_get. eassumption.
      dostep_nary 1. eapply r_load_success; try eassumption.
      rewrite -Haddr1. apply Hload1'.
      replace (wasm_deserialise b0 T_i64) with (VAL_int64 (Z_to_i64 (to_Z n1))) by congruence.
      now apply rt_refl. }
    assert (HloadStep2: forall es,
               reduce_trans
                 (state, s, f, ([:: AI_basic (BI_local_get y')] ++
                                  [:: AI_basic (BI_load T_i64 None 2%N 0%N)] ++
                                  es))
                 (state, s, f, ([:: $V VAL_num (VAL_int64 (Z_to_i64 (to_Z n2))) ] ++ es))). {
      intros.
      dostep_nary 0. apply r_local_get. eassumption.
      dostep_nary 1. eapply r_load_success; try eassumption. rewrite -H5. apply Hload2'.
      replace (wasm_deserialise b1 T_i64) with (VAL_int64 (Z_to_i64 (to_Z n2))) by congruence.
      now apply rt_refl. }
    assert (HloadStep': forall es,
               reduce_trans
                 (state, s, f, ([:: AI_basic (BI_local_get x')] ++
                                  [:: AI_basic (BI_load T_i64 None 2%N 0%N)] ++
                                  [:: AI_basic (BI_local_get y')] ++
                                  [:: AI_basic (BI_load T_i64 None 2%N 0%N)] ++
                                  es))
                 (state, s, f, ([:: $V VAL_num (VAL_int64 (Z_to_i64 (to_Z n1))) ; $V VAL_num (VAL_int64 (Z_to_i64 (to_Z n2))) ] ++ es))). {
      intros.
      eapply rt_trans.
      apply HloadStep1.
      eapply rt_trans.
      apply app_trans_const; auto.
      now apply rt_refl.
    }
    destruct Hpfs' as
      [true_tag [false_tag [bool_tag [eq_tag [lt_tag [gt_tag [comp_tag [c0_tag [c1_tag [carry_tag [pair_tag [prod_tag [Hres [Htrue [Hfalse [Heq [Hlt [Hgt [Hc0 [Hc1 Hpair]]]]]]]]]]]]]]]]]]]].
    assert (Htrue_arr: get_ctor_arity cenv true_tag = Ret 0) by now unfold get_ctor_arity; rewrite Htrue.
    assert (Htrue_ord: get_ctor_ord cenv true_tag = Ret 0%N) by now unfold get_ctor_ord; rewrite Htrue.
    assert (Hfalse_arr: get_ctor_arity cenv false_tag = Ret 0) by now unfold get_ctor_arity; rewrite Hfalse.
    assert (Hfalse_ord: get_ctor_ord cenv false_tag = Ret 1%N) by now unfold get_ctor_ord; rewrite Hfalse.
    rewrite Hvs in Hres.
    unfold apply_LambdaANF_primInt_operator in Hres.
    destruct op;
    ltac:(match goal with | [ H : None = Some _  |- _ ] => discriminate | _ => idtac end);
    unfold LambdaANF_primInt_arith_fun in Hres.
    - (* add *) solve_arith_op_aux v (n1 + n2)%uint63 H2 H3 HloadStep' uint63_add_i64_add.
    - (* sub *) solve_arith_op_aux v (n1 - n2)%uint63 H2 H3 HloadStep' uint63_sub_i64_sub.
    - (* mul *) solve_arith_op_aux v (n1 * n2)%uint63 H2 H3 HloadStep' uint63_mul_i64_mul.
    - { (* div *)
      inv H2; simpl.
      destruct (H3 (n1 / n2)%uint63) as [s' [s_final [fr [m' [wal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]].
      replace v with (Vprim (primInt (n1 / n2)%uint63)) in * by congruence.
      exists s_final, fr.
      split; auto.
      dostep_nary 0. eapply r_global_get; eassumption.
      eapply rt_trans.
      apply app_trans_const; auto.
      destruct (Z.eq_dec (to_Z n2) (to_Z 0)).
      { (* n2 = 0 *)
        dostep_nary_eliml 1 1. constructor; apply rs_testop_i64.
        dostep_nary_eliml 1 1. constructor; apply rs_if_true; unfold wasm_bool.
        replace Wasm_int.Int64.zero with (Z_to_i64 (to_Z 0)) by now rewrite to_Z_0.
        rewrite uint63_eq_int64_eq. discriminate. now rewrite e0.
        dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
        dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
        dostep_nary 2. eapply r_store_success.
        rewrite uint63_div0 in Hstore; auto.
        eassumption.
        now apply Hstep. }
      { (* n2 <> 0 *)
        dostep_nary_eliml 1 1. constructor; apply rs_testop_i64.
        dostep_nary_eliml 1 1. constructor; apply rs_if_false; unfold wasm_bool; auto.
        replace Wasm_int.Int64.zero with (Z_to_i64 (to_Z 0)) by now rewrite to_Z_0.
        rewrite uint63_neq_int64_neq; auto.
        dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
        rewrite catA.
        reduce_under_label.
        apply HloadStep'.
        reduce_under_label.
        apply rt_step. constructor; apply rs_binop_success. simpl.
        rewrite uint63_div_i64_div; simpl; auto.
        dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
        dostep_nary 2. eapply r_store_success.
        eassumption.
        eassumption. } }
    - { (* mod *)
      inv H2; simpl.
      destruct (H3 (n1 mod n2)%uint63) as [s' [s_final [fr [m' [wal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]].
      replace v with (Vprim (primInt (n1 mod n2)%uint63)) in * by congruence.
      exists s_final, fr.
      split; auto.
      dostep_nary 0. eapply r_global_get; eassumption.
      eapply rt_trans.
      apply app_trans_const; auto.
      destruct (Z.eq_dec (to_Z n2) (to_Z 0)).
      { (* n2 = 0 *)
        dostep_nary_eliml 1 1. constructor; apply rs_testop_i64.
        dostep_nary_eliml 1 1. constructor; apply rs_if_true; unfold wasm_bool.
        replace Wasm_int.Int64.zero with (Z_to_i64 (to_Z 0)) by now rewrite to_Z_0.
        rewrite uint63_eq_int64_eq. discriminate. now rewrite e0.
        dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
        rewrite catA.
        reduce_under_label.
        apply HloadStep1.
        dostep_nary_eliml 0 1. constructor. apply rs_label_const; auto.
        dostep_nary 2. eapply r_store_success.
        rewrite uint63_mod0 in Hstore; eauto.
        eassumption. }
      { (* n2 <> 0 *)
        dostep_nary_eliml 1 1. constructor; apply rs_testop_i64.
        dostep_nary_eliml 1 1. constructor; apply rs_if_false; unfold wasm_bool; auto.
        replace Wasm_int.Int64.zero with (Z_to_i64 (to_Z 0)) by now rewrite to_Z_0.
        rewrite uint63_neq_int64_neq; auto.
        dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
        rewrite catA.
        reduce_under_label.
        apply HloadStep'.
        reduce_under_label.
        apply rt_step. constructor; apply rs_binop_success; simpl; rewrite uint63_mod_i64_mod; simpl; auto.
        dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
        dostep_nary 2. eapply r_store_success.
        eassumption.
        eassumption. } }
    (* TODO: Factor out helper lemma for shifts *)
    - { (* lsl *)
        inv H2; simpl.
        destruct (H3 (n1 << n2)%uint63) as [s' [s_final [fr [m' [wal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]].
        replace v with (Vprim (primInt (n1 << n2)%uint63)) in * by congruence.
        exists s_final, fr.
        split; auto.
        dostep_nary 0. eapply r_global_get; eassumption.
        eapply rt_trans.
        apply app_trans_const; auto.
        destruct (Z_lt_dec (to_Z n2) (to_Z 63)).
        { (* n2 < 63 *)
          dostep_nary_eliml 2 1. constructor; apply rs_relop.
          dostep_nary_eliml 1 1. constructor; apply rs_if_true; unfold wasm_bool.
          replace (Z_to_i64 63) with (Z_to_i64 (to_Z 63)) by now cbn.
          rewrite uint63_lt_int64_lt; auto. discriminate.
          dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
          rewrite catA.
          reduce_under_label.
          apply HloadStep'.
          reduce_under_label.
          dostep_nary 2; constructor; apply rs_binop_success; reflexivity.
          reduce_under_label.
          apply rt_step. constructor; apply rs_binop_success; reflexivity. cbn.
          rewrite uint63_lsl_i64_shl; simpl; auto.
          dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
          dostep_nary 2. eapply r_store_success.
          eassumption.
          eassumption. }
        { (* n2 <= 63 *)
          dostep_nary_eliml 2 1. constructor; apply rs_relop.
          dostep_nary_eliml 1 1. constructor; apply rs_if_false; unfold wasm_bool.
          replace (Z_to_i64 63) with (Z_to_i64 (to_Z 63)) by now cbn.
          rewrite uint63_nlt_int64_nlt; auto.
          dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
          dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
          dostep_nary 2. eapply r_store_success.
          assert (to_Z 63 <= to_Z n2)%Z as Hle by now destruct (Z.lt_ge_cases (to_Z n2) (to_Z 63)).
          rewrite (uint63_lsl63 _ _ Hle) in Hstore; eauto.
          eassumption. } }
    - { (* lsr *)
        inv H2; simpl.
        destruct (H3 (n1 >> n2)%uint63) as [s' [s_final [fr [m' [wal [Hs' [Hstore [Hfr [Hsmem [Hstep [Hinv1 [Hupd_glob Hr]]]]]]]]]]]].
        replace v with (Vprim (primInt (n1 >> n2)%uint63)) in * by congruence.
        exists s_final, fr.
        split; auto.
        dostep_nary 0. eapply r_global_get; eassumption.
        eapply rt_trans.
        apply app_trans_const; auto.
        destruct (Z_lt_dec (to_Z n2) (to_Z 63)).
        { (* n2 < 63 *)
          dostep_nary_eliml 2 1. constructor; apply rs_relop.
          dostep_nary_eliml 1 1. constructor; apply rs_if_true; unfold wasm_bool.
          replace (Z_to_i64 63) with (Z_to_i64 (to_Z 63)) by now cbn.
          rewrite uint63_lt_int64_lt; auto. discriminate.
          dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
          rewrite catA.
          reduce_under_label.
          apply HloadStep'.
          reduce_under_label.
          apply rt_step. constructor; apply rs_binop_success. simpl.
          rewrite uint63_lsr_i64_shr; simpl; auto.
          dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
          dostep_nary 2. eapply r_store_success.
          eassumption.
          eassumption. }
        { (* n2 <= 63 *)
          dostep_nary_eliml 2 1. constructor; apply rs_relop.
          dostep_nary_eliml 1 1. constructor; apply rs_if_false; unfold wasm_bool.
          replace (Z_to_i64 63) with (Z_to_i64 (to_Z 63)) by now cbn.
          rewrite uint63_nlt_int64_nlt; auto.
          dostep_nary_eliml 0 1. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i64])(vs:=[::]); auto.
          dostep_nary_eliml 0 1. constructor; apply rs_label_const; auto.
          dostep_nary 2. eapply r_store_success.
          assert (to_Z 63 <= to_Z n2)%Z as Hle by now destruct (Z.lt_ge_cases (to_Z n2) (to_Z 63)).
          rewrite (uint63_lsr63 _ _ Hle) in Hstore; eauto.
          eassumption. } }
    - (* land *) solve_arith_op_aux v (n1 land n2)%uint63 H2 H3 HloadStep' uint63_land_i64_and.
    - (* lor *) solve_arith_op_aux v (n1 lor n2)%uint63 H2 H3 HloadStep' uint63_lor_i64_or.
    - (* lxor *) solve_arith_op_aux v (n1 lxor n2)%uint63 H2 H3 HloadStep' uint63_lxor_i64_xor.
    (* TODO: Factor out helper lemma for booleans *)
    - { (* eqb *)
        inv H2; simpl.
        destruct (Z.eq_dec (to_Z n1) (to_Z n2)).
        { (* n1 = n2 *)
          assert (Hv_true: v = Vconstr true_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (reflect_iff _ _ (Uint63.eqbP n1 n2)) in e0; rewrite e0 in Hres.
          destruct (H4 _ _ Hv_true Htrue_arr Htrue_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor; apply rs_relop.
            dostep_nary 1. constructor; apply rs_if_true; unfold wasm_bool.
            rewrite uint63_eq_int64_eq; [discriminate|now rewrite e0].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 1)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 0%N by congruence.
            - replace t with true_tag in * by congruence. rewrite Htrue_arr in H8; inv H8; lia.
          }
          try repeat (split; auto). all: subst fr; auto.
          exists wal; auto. }
        { (* n1 <> n2 *)
          assert (Hv_false: v = Vconstr false_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (to_Z_neq_uint63_eqb_false _ _ n) in Hres.
          destruct (H4 _ _ Hv_false Hfalse_arr Hfalse_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor; apply rs_relop.
            dostep_nary 1. constructor; apply rs_if_false; unfold wasm_bool.
            rewrite uint63_neq_int64_neq; [reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 3)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 1%N by congruence.
            - replace t with false_tag in * by congruence. rewrite Hfalse_arr in H8; inv H8; lia.
          }
          try repeat (split; auto). all: subst fr; auto.
          exists wal; auto. } }
    - { (* ltb *)
        inv H2; simpl.
        destruct (Z_lt_dec (to_Z n1) (to_Z n2)).
        { (* n1 < n2 *)
          assert (Hv_true: v = Vconstr true_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (reflect_iff _ _ (Uint63.ltbP n1 n2)) in l; rewrite l in Hres.
          destruct (H4 _ _ Hv_true Htrue_arr Htrue_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor; apply rs_relop.
            dostep_nary 1. constructor; apply rs_if_true; unfold wasm_bool.
            rewrite uint63_lt_int64_lt; [discriminate|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 1)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 0%N by congruence.
            - replace t with true_tag in * by congruence. rewrite Htrue_arr in H8; inv H8; lia.
          }
          try repeat (split; auto). all: subst fr; auto.
          exists wal; auto. }
        { (* ~ (n1 < n2) *)
          assert (Hv_false: v = Vconstr false_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (to_Z_nlt_uint63_ltb_false _ _ n) in Hres.
          destruct (H4 _ _ Hv_false Hfalse_arr Hfalse_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor; apply rs_relop.
            dostep_nary 1. constructor; apply rs_if_false; unfold wasm_bool.
            rewrite uint63_nlt_int64_nlt; [reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 3)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 1%N by congruence.
            - replace t with false_tag in * by congruence. rewrite Hfalse_arr in H8; inv H8; lia.
          }
          try repeat (split; auto). all: subst fr; auto.
          exists wal; auto. } }
    - { (* leb *)
        inv H2; simpl.
        destruct (Z_le_dec (to_Z n1) (to_Z n2)).
        { (* n1 < n2 *)
          assert (Hv_true: v = Vconstr true_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (reflect_iff _ _ (Uint63.lebP n1 n2)) in l; rewrite l in Hres.
          destruct (H4 _ _ Hv_true Htrue_arr Htrue_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor; apply rs_relop.
            dostep_nary 1. constructor; apply rs_if_true; unfold wasm_bool.
            rewrite uint63_le_int64_le; [discriminate|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 1)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 0%N by congruence.
            - replace t with true_tag in * by congruence. rewrite Htrue_arr in H8; inv H8; lia.
          }
          try repeat (split; auto). all: subst fr; auto.
          exists wal; auto. }
        { (* ~ (n1 < n2) *)
          assert (Hv_false: v = Vconstr false_tag []) by now unfold LambdaANF_primInt_bool_fun in Hres; rewrite (to_Z_nle_uint63_leb_false _ _ n) in Hres.
          destruct (H4 _ _ Hv_false Hfalse_arr Hfalse_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor; apply rs_relop.
            dostep_nary 1. constructor; apply rs_if_false; unfold wasm_bool.
            rewrite uint63_nle_int64_nle; [reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 3)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 1%N by congruence.
            - replace t with false_tag in * by congruence. rewrite Hfalse_arr in H8; inv H8; lia.
          }
          try repeat (split; auto). all: subst fr; auto.
          exists wal; auto. } }
    - { (* compare *)
        inv H2; simpl.
        destruct (Z_lt_dec (to_Z n1) (to_Z n2)).
        { (* n1 < n2 *)
          assert (Hv_lt: v = Vconstr lt_tag [])
            by now unfold LambdaANF_primInt_compare_fun in Hres;
            inversion Hres as [Hcomp]; rewrite compare_def_spec; unfold compare_def;
            rewrite (reflect_iff _ _ (Uint63.ltbP n1 n2)) in l; rewrite l.
          assert (Hlt_arr: get_ctor_arity cenv lt_tag = Ret 0) by now unfold get_ctor_arity; rewrite Hlt.
          assert (Hlt_ord: get_ctor_ord cenv lt_tag = Ret 1%N) by now unfold get_ctor_ord; rewrite Hlt.
          destruct (H4 _ _ Hv_lt Hlt_arr Hlt_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor; apply rs_relop.
            dostep_nary 1. constructor; apply rs_if_true; unfold wasm_bool.
            rewrite uint63_lt_int64_lt;[discriminate|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 3)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try discriminate.
            - now replace ord with 1%N by congruence.
            - replace t with lt_tag in * by congruence; rewrite Hlt_arr in H8;inv H8; lia.
          }
          try repeat (split; auto). subst fr; auto.
          exists wal; auto. }
        { (* ~ (n1 < n2) *)
          destruct (Z.eq_dec (to_Z n1) (to_Z n2)).
          { (* n1 = n2 *)
            assert (Hv_eq: v = Vconstr eq_tag [])
              by now  unfold LambdaANF_primInt_compare_fun in Hres;
              inversion Hres as [Hcomp];
              rewrite compare_def_spec; unfold compare_def;
              rewrite (to_Z_nlt_uint63_ltb_false _ _ n);
              rewrite (reflect_iff _ _ (Uint63.eqbP n1 n2)) in e0; rewrite e0.
            assert (Heq_arr: get_ctor_arity cenv eq_tag = Ret 0) by now unfold get_ctor_arity; rewrite Heq.
            assert (Heq_ord: get_ctor_ord cenv eq_tag = Ret 0%N) by now unfold get_ctor_ord; rewrite Heq.
            destruct (H4 _ _ Hv_eq Heq_arr Heq_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor; apply rs_relop.
            dostep_nary 1. constructor; apply rs_if_false; unfold wasm_bool.
            rewrite uint63_nlt_int64_nlt;[reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            rewrite catA.
            reduce_under_label.
            apply HloadStep'.
            reduce_under_label.
            dostep_nary 2. constructor; apply rs_relop.
            apply rt_step. constructor; apply rs_if_true; unfold wasm_bool.
            cbn; rewrite uint63_eq_int64_eq;[discriminate|assumption].
            reduce_under_label.
            apply rt_step. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            reduce_under_label.
            apply rt_step. constructor. apply rs_label_const; auto.
            dostep_nary 0. constructor. apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 1)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try (replace t with eq_tag in *; [rewrite Heq_arr in H8; inv H8; lia|congruence]); try discriminate.
            now replace ord with 0%N by congruence.
          }
          try repeat (split; auto). subst fr; auto.
          exists wal; auto. }
          { (* n1 <> n2 *)
            assert (Hv_gt: v = Vconstr gt_tag [])
              by now unfold LambdaANF_primInt_compare_fun in Hres; inversion Hres as [Hcomp];
              rewrite compare_def_spec; unfold compare_def;
              rewrite (to_Z_nlt_uint63_ltb_false _ _ n);
              now rewrite (to_Z_neq_uint63_eqb_false _ _ n0).
            assert (Hgt_arr: get_ctor_arity cenv gt_tag = Ret 0) by now unfold get_ctor_arity; rewrite Hgt.
            assert (Hgt_ord: get_ctor_ord cenv gt_tag = Ret 2%N) by now unfold get_ctor_ord; rewrite Hgt.
            destruct (H4 _ _ Hv_gt Hgt_arr Hgt_ord) as [fr [wal [Hinv' [Hfr [HreprVal [HrelE' [HvalsPreserved Hstep]]]]]]].
          simpl_modulus; simpl_modulus; cbn; lia.
          exists s, fr.
          split. {
            separate_instr.
            eapply rt_trans.
            apply HloadStep'.
            dostep_nary 2. constructor; apply rs_relop.
            dostep_nary 1. constructor; apply rs_if_false; unfold wasm_bool.
            rewrite uint63_nlt_int64_nlt;[reflexivity|assumption].
            dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            separate_instr.
            rewrite catA.
            reduce_under_label.
            apply HloadStep'.
            reduce_under_label.
            dostep_nary 2. constructor; apply rs_relop.
            apply rt_step. constructor; apply rs_if_false; unfold wasm_bool.
            cbn. rewrite uint63_neq_int64_neq;[reflexivity|assumption].
            reduce_under_label.
            apply rt_step. eapply r_block with (t1s:=[::]) (t2s:=[:: T_num T_i32])(vs:=[::]); eauto.
            reduce_under_label.
            apply rt_step; constructor; apply rs_label_const; auto.
            dostep_nary 0. constructor; apply rs_label_const; auto.
            replace [:: $VN VAL_int32 (Wasm_int.Int32.repr 5)] with [:: $V VAL_num (VAL_int32 (wasm_value_to_i32 wal))]; auto.
            inv HreprVal; try (replace t with gt_tag in *; [rewrite Hgt_arr in H8; inv H8; lia|congruence]); try discriminate.
            now replace ord with 2%N by congruence.
          }
          try repeat (split; auto). subst fr; auto.
          exists wal; auto. } } }
    - { (* addc *)
        inversion H2.
        subst x1 y0.
        assert (HaddcApp: LambdaANF_primInt_carry_fun c0_tag c1_tag addc n1 n2 = v) by congruence.
        assert (N.to_nat x0' < Datatypes.length (f_locs f)) by now eapply HlocsInBounds; eauto.
        rewrite Haddr1 in Hload1'. replace 8 with (N.to_nat (tnum_length T_i64)) in Hload1' by now cbn. 
        assert (Hbsx : wasm_deserialise b0 T_i64 = Z_to_VAL_i64 φ (n1)%uint63) by congruence.
        rewrite H5 in Hload2'. replace 8 with (N.to_nat (tnum_length T_i64)) in Hload2' by now cbn. 
        assert (Hbsy : wasm_deserialise b1 T_i64 = Z_to_VAL_i64 φ (n2)%uint63) by congruence.
        assert (Z.of_N gmp_v + Z.of_N page_size <= Z.of_N (mem_length m) < Int32.modulus)%Z. {
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
          simpl_modulus. cbn. cbn in HenoughM. lia. }
        unfold LambdaANF_primInt_carry_fun in HaddcApp.
        remember {|f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 8)%N)))) (f_locs f) (N.to_nat x0') (VAL_num (VAL_int32 (wasm_value_to_i32 (Val_ptr (gmp_v + 8)%N))));
                   f_inst := f_inst f|} as fr'.
        destruct (n1 +c n2)%uint63 eqn:Haddc;
          replace i with (n1 + n2)%uint63 in * by now (rewrite addc_def_spec in Haddc; unfold addc_def in Haddc; destruct (n1 + n2 <? n1)%uint63; inversion Haddc).
        { (* No carry *)
          assert (~ (to_Z (n1 + n2) < to_Z n1)%Z). {
            rewrite addc_def_spec in Haddc. unfold addc_def in Haddc. 
            intro Hcontra.
            destruct ((n1 + n2) <? n1)%uint63 eqn:Hltb. inv Haddc.
            now rewrite (reflect_iff _ _ (ltbP (n1 + n2) n1)) in Hcontra. }                
          symmetry in HaddcApp.
          have H''' := conj H8 HaddcApp. 
          have HaddcRed :=  apply_exact_add_operation_reduce x' y' false state s f m gmp_v (wasm_value_to_i32 (Val_ptr addr1)) (wasm_value_to_i32 (Val_ptr addr2)) b0 b1 n1 n2 c0_tag c1_tag carry_tag v Hinv Hc0 Hc1 (or_introl H''') Hmem2 (conj Hx' (conj Hload1' Hbsx)) (conj Hy' (conj Hload2' Hbsy)) H7 Hgmp.        
          destruct HaddcRed as [sr' [m' (HinstrsRed & HINV_sr' & Hmem_sr' & Hgmp_sr' & _ & _ & _ & _ & Hsfuncs_sr' & Hmemlen_m' & Hval_sr' & HvalsPreserved)]].
        exists sr', fr'.
        split. 
        eapply rt_trans;[apply HinstrsRed|].
        dostep_nary' 1. rewrite unfold_val_notation; eapply r_local_set with (f':=fr'). now subst fr'.
        apply /ssrnat.leP.
        apply HlocsInBounds in Hrepr_x. lia.
        now subst fr'.
        now apply rt_refl.
        split; auto.
        eapply update_local_preserves_INV with (f':=fr'); eauto.
        split. now subst fr'.
        split; auto.
        split; auto.
        eapply HunaryConstrValRelEnv; eauto. 
        unfold get_ctor_arity. now rewrite Hc0.
        unfold get_ctor_ord. now rewrite Hc0.
        now subst fr'.
        subst fr'.
        cbn.
        now rewrite nth_error_set_eq.
        now cbn.
        now subst fr'.
        split; subst fr'; auto; cbn.
        now exists (Val_ptr (gmp_v + 8)%N). }
        { (* Carry *)
          assert (to_Z (n1 + n2) < to_Z n1)%Z. { 
            rewrite addc_def_spec in Haddc. unfold addc_def in Haddc. 
            destruct ((n1 + n2) <? n1)%uint63 eqn:Hltb. 
            now rewrite (reflect_iff _ _ (ltbP (n1 + n2) n1)) Hltb.
            inv Haddc. }
          symmetry in HaddcApp.
          have H''' := conj H8 HaddcApp. 
          have HaddcRed :=  apply_exact_add_operation_reduce x' y' false state s f m gmp_v (wasm_value_to_i32 (Val_ptr addr1)) (wasm_value_to_i32 (Val_ptr addr2)) b0 b1 n1 n2 c0_tag c1_tag carry_tag v Hinv Hc0 Hc1 (or_intror H''') Hmem2 (conj Hx' (conj Hload1' Hbsx)) (conj Hy' (conj Hload2' Hbsy)) H7 Hgmp.
        destruct HaddcRed as [sr' [m' (HinstrsRed & HINV_sr' & Hmem_sr' & Hgmp_sr' & _ & _ & _ & _ & Hsfuncs_sr' & Hmemlen_m' & Hval_sr' & HvalsPreserved)]].
        exists sr', fr'.
        split. 
        eapply rt_trans;[apply HinstrsRed|].
        dostep_nary' 1. rewrite unfold_val_notation; eapply r_local_set with (f':=fr'). now subst fr'.
        apply /ssrnat.leP.
        apply HlocsInBounds in Hrepr_x. lia.
        now subst fr'.
        now apply rt_refl.
        split; auto.
        eapply update_local_preserves_INV with (f':=fr'); eauto.
        split. now subst fr'.
        split; auto.
        split; auto.
        eapply HunaryConstrValRelEnv; eauto. 
        unfold get_ctor_arity. now rewrite Hc1.
        unfold get_ctor_ord. now rewrite Hc1.
        now subst fr'.
        subst fr'.
        cbn.
        now rewrite nth_error_set_eq.
        now cbn.
        now subst fr'.
        split; subst fr'; auto; cbn.
        now exists (Val_ptr (gmp_v + 8)%N). } } 
    - { (* addcarryc *) admit. }
    - { (* subc *) admit. }
    - { (* subcarryc *)  admit. }
    - { (* mulc *)  admit. }
    - { (* diveucl *) admit. }
  }
  { (* Ternary operations *) admit. }
Admitted. (* Qed. *)

(* MAIN THEOREM, corresponds to 4.3.2 in Olivier's thesis *)
Theorem repr_bs_LambdaANF_Wasm_related :
  (* rho is environment containing outer fundefs. e is body of LambdaANF program *)
  forall lenv pfs (rho : eval.env) (v : cps.val) (e : exp) (n : nat) (vars : list cps.var) (fds : fundefs)
                               fAny k (lh : lholed k),
    cenv_restricted cenv ->
    (* restrictions on prim_funs env *)
    prim_funs_env_returns_no_funvalues pfs ->
    prim_funs_env_wellformed cenv penv pfs ->
    (* restrictions on lenv, fenv *)
    map_injective lenv ->
    domains_disjoint lenv fenv ->
    (* bound vars globally unique *)
    vars = (collect_local_variables e) ++ (collect_function_vars (Efun fds e))%list ->
    NoDup vars ->
    (* fenv maps f vars to the index of the corresponding wasm function *)
    (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
    (* find_def a fds <> None, rho ! a imply fn value *)
    (forall (a : positive) (v : cps.val), rho ! a = Some v -> find_def a fds <> None ->
             v = Vfun (M.empty cps.val) fds a) ->

    (* restricts e w.r.t. to size s.t. all vars fit in i32s *)
    expression_restricted cenv e ->
    (* SSA form, let-bound vars not assigned yet *)
    (forall x, In x (collect_local_variables e) -> rho ! x = None) ->
    bstep_e pfs cenv rho e v n ->  (* e n-steps to v *)
    forall (hs : host_state) (sr : store_record) (f : frame) (e' : list basic_instruction),

      (* translated fds in sr, TODO consider including in INV *)
      (forall a t ys e errMsg, find_def a fds = Some (t, ys, e) ->
          expression_restricted cenv e /\ (forall x, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
          NoDup (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)) /\
          (exists fidx : funcidx, translate_var nenv fenv a errMsg = Ret fidx /\
                repr_val_LambdaANF_Wasm (Vfun (M.empty cps.val) fds a) sr (f_inst f) (Val_funidx fidx))) ->

      (* local vars from lenv in bound *)
      (forall var varIdx, @repr_var nenv lenv var varIdx -> N.to_nat varIdx < length (f_locs f)) ->

      (* invariants *)
      INV sr f ->

      (* translate_body e returns instructions *)
      @repr_expr_LambdaANF_Wasm penv lenv e e' ->

      (* relates a LambdaANF evaluation environment [rho] to a Wasm environment [store/frame] (free variables in e) *)
      @rel_env_LambdaANF_Wasm lenv e rho sr f fds ->
      exists (sr' : store_record) (f' : frame) k' (lh' : lholed k'),
        reduce_trans (hs, sr,  fAny, [AI_frame 0 f (lfill lh (map AI_basic e'))])
                     (hs, sr', fAny, [AI_frame 0 f' (lfill lh' [::AI_basic BI_return])]) /\
        (* value sr'.res points to value related to v *)
        result_val_LambdaANF_Wasm v sr' (f_inst f) /\
        f_inst f = f_inst f' /\ s_funcs sr = s_funcs sr' /\
        (* previous values are preserved *)
        (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst f) wal ->
                         repr_val_LambdaANF_Wasm val sr' (f_inst f') wal) /\
        (* INV holds if program will continue to run *)
        (INV_result_var_out_of_mem_is_zero sr' f' -> INV sr' f').
Proof with eauto.
  intros lenv pfs rho v e n vars fds fAny k lh HcenvRestr HprimFunsRet HprimFunsRelated HlenvInjective HenvsDisjoint Hvars Hnodup
     HfenvWf HfenvRho HeRestr Hunbound Hev. subst vars.
  generalize dependent lenv. generalize dependent lh. revert k fAny.
  induction Hev; intros k fAny lh lenv HlenvInjective HenvsDisjoint state sr fr instructions
                        Hfds HlocInBound Hinv Hrepr_e HrelE.
  - (* Econstr *)
    inversion Hrepr_e.
    inversion H8.
    { (* boxed constructor *)
    assert (Hmaxargs: (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z). { now inv HeRestr. }
    subst t0 x0 vs0 e0. rename H7 into Hx'. rename H6 into Hexp.
    { cbn. repeat rewrite map_cat. cbn.

      (* prepare calling memory_grow_reduce *)
      have I := Hinv. destruct I as [_[_[_[_[_[_[_[_[_[HfnsBound[_[_[_[_ [HfuncGrow HfuncsId]]]]]]]]]]]]]]].
      remember (Build_frame [VAL_num (N_to_value page_size)] (f_inst fr)) as fM.
      assert (HinvM: INV sr fM). {
        subst fM. eapply change_locals_preserves_INV. eassumption.
        intros i ? Hl. destruct i; last by destruct i.
        inv Hl. now eexists. reflexivity.
      }
      assert (Hloc0: nth_error (f_locs fM) 0 = Some (VAL_num (N_to_value page_size))) by (subst fM; reflexivity).
      have Hgrowmem := memory_grow_reduce state sr _ Hloc0 HinvM.
      destruct Hgrowmem as [gmp' [s' [Hred [Hsfuncs [HvalPreserved [[HinvFm' Henoughmem] | HoutofM]]]]]].

      (* invariants after reducing grow *)
      have I := HinvFm'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
      destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
      have HenoughM := Henoughmem _ Hmem2. destruct HenoughM as [Hgmp HenoughM]. clear Henoughmem.
      assert (Hinv': INV s' fr). {
        destruct fr.
        eapply change_locals_preserves_INV with (f:=fM). eassumption. apply Hinv.
        subst fM. reflexivity.
      } clear HinvFm'.

      { assert (HrelE' : (forall y : var,
           In y ys ->
           find_def y fds = None ->
           exists (v6 : cps.val) (val : wasm_value),
             rho ! y = Some v6 /\
             @stored_in_locals lenv y val fr /\
             repr_val_LambdaANF_Wasm v6 s' (f_inst fr) val)). {
              destruct HrelE as [_ Hvar]. intros.
        assert (Hocc: occurs_free (Econstr x t ys e) y) by (constructor; auto).
        apply Hvar in Hocc; auto. destruct Hocc as [val [wal [Hrho [Hloc Hval]]]].
        exists val, wal. subst fM. by repeat split; auto.
      }

     assert (HfVal' : (forall (y : positive) (y' : funcidx) (v : cps.val),
           rho ! y = Some v ->
           repr_funvar y y' ->
           repr_val_LambdaANF_Wasm v s' (f_inst fr) (Val_funidx y'))).
     { intros. destruct HrelE as [Hfun1 [Hfun2 _]].
      assert (Hfd: (exists i : N, fenv ! y = Some i)). {
        inv H2. unfold translate_var in H3. destruct (fenv ! y) eqn:Hy; rewrite Hy in H3=>//.
        now exists f. }
      apply HfenvWf in Hfd. apply notNone_Some in Hfd.

       have H' := HfenvRho _ _ H1 Hfd. subst v0.
       apply notNone_Some in Hfd. destruct Hfd as [[[f' ys''] e''] ?H].

       assert (Hsubval: subval_or_eq (Vfun (M.empty _) fds y)
        (Vfun (M.empty cps.val) fds y)) by constructor.

       inv H2.
       have H' := Hfun1 _ _ _ _ _ H1 Hsubval. destruct H' as [_ [_ H']].
       apply Hfun2 with (errMsg:=errMsg) in H'.
       destruct H' as [i [HvarI Hval]].
       assert (i = y') by congruence. subst i.
       eapply val_relation_func_depends_on_funcs; try apply Hval. auto.
     }
     rewrite HeqfM in Hgmp. subst fM.
      have Hconstr := store_constr_reduce state _ _ _ _ _ _ t _ _ _ _ _ H9 H10 H11 HenvsDisjoint HfenvWf Hinv'
      Hmem2 Hgmp HenoughM HrelE' Hmaxargs H12 H HfVal'.
      destruct Hconstr as [s_v [Hred_v [Hinv_v [Hfuncs' [HvalPreserved' [cap_v [wal [? [<- Hvalue]]]]]]]]].
      have I := Hinv'. destruct I as [_ [_ [HoutM0 _]]].
    {
      have Hl := HlocInBound _ _ Hx'. apply nth_error_Some in Hl.
      apply notNone_Some in Hl. destruct Hl as [? Hlx].

      remember ({|f_locs := set_nth (VAL_num (VAL_int32 (wasm_value_to_i32 wal))) (f_locs fr) (N.to_nat x') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)));
      f_inst := f_inst fr|}) as f_before_IH.

      assert (Hfds': forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) (errMsg : bytestring.String.t),
        find_def a fds = Some (t, ys, e) ->
          expression_restricted cenv e /\
          (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
          NoDup
            (ys ++
             collect_local_variables e ++
             collect_function_vars (Efun fds e)) /\
          (exists fidx : funcidx,
             translate_var nenv fenv a errMsg = Ret fidx /\
             repr_val_LambdaANF_Wasm (Vfun (M.empty cps.val) fds a) s_v (f_inst f_before_IH) (Val_funidx fidx))). {
        intros ? ? ? ? ? Hfd. apply Hfds with (errMsg:=errMsg) in Hfd.
        destruct Hfd as [? [? [? [idx [HtransF Hval]]]]].
        repeat (split; try assumption).
        exists idx. split. assumption.
        eapply val_relation_func_depends_on_funcs.
        2:{ subst f_before_IH. apply Hval. }
        congruence.
      }

      assert (HlocInBound': (forall (var : positive) (varIdx : localidx),
          @repr_var nenv lenv var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs f_before_IH))). {
          intros ?? Hvar. subst f_before_IH. cbn.
          rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
          apply HlocInBound in Hvar. lia. }

      assert (Hinv_before_IH: INV s_v f_before_IH). {
        eapply update_local_preserves_INV; try eassumption.
        apply nth_error_Some. congruence. }
      (* prepare IH *)

      (* evironment relation *)
      assert (HrelE_v : @rel_env_LambdaANF_Wasm lenv e rho' s_v f_before_IH fds).
      { clear IHHev Hinv Hmem1 Hmem2 Hmem3 Hmem4 Hinv' Hred_v.
        destruct HrelE as [Hfun1 [Hfun2 Hvar]]. unfold rel_env_LambdaANF_Wasm. split.
        { (* fns1 *) intros ????? Hrho Hv. subst rho'.
           destruct (var_dec x x1).
           { (* x=x1 *) subst x1. rewrite M.gss in Hrho. inv Hrho.
             apply subval_or_eq_fun in Hv. destruct Hv as [v1 [Hr1 Hr2]].
             have H'' := get_list_In_val _ _ _ _ H Hr2.
             destruct H'' as [x2 [Hin Hrho]].
             have H' := Hfun1 _ _ _ _ _ Hrho Hr1. assumption.
           }
           { (* x<>x1 *) rewrite M.gso in Hrho; eauto. }
        } split.
        { (* fns2 *)
          intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          assert (Hfs: s_funcs sr = s_funcs s_v) by congruence.
          exists i. split. assumption.
          eapply val_relation_func_depends_on_funcs. eassumption.
          subst f_before_IH. assumption.
        }
        { (* local vars *)
          intros ? Hocc Hfd. destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1. exists (Vconstr t vs), wal.
            subst rho'. rewrite M.gss. split; auto. split.
            subst f_before_IH. exists x'. cbn. split.
            inv Hx'. intro. unfold translate_var. unfold translate_var in H0.
            destruct (lenv ! x) eqn:Hx; rewrite Hx in H0=>//. injection H0 as ->.
            rewrite Hx. reflexivity.
            unfold lookup_N.
            erewrite set_nth_nth_error_same; eauto.
            subst f_before_IH. assumption.
          }
          { (* x <> x1 *)
            assert (Hocc': occurs_free (Econstr x t ys e) x1). { now apply Free_Econstr2. }
            have H' := Hvar _ Hocc' Hfd.
            destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
            exists val', wal'. split.
            subst rho'. rewrite M.gso; auto. split.
            destruct Hloc as [i [Hl1 Hl2]].
            unfold stored_in_locals. exists i. split; auto.
            subst f_before_IH. cbn.
            unfold lookup_N.
            rewrite set_nth_nth_error_other; auto.
            intro. subst x'.
            inv Hx'.
            specialize Hl1 with err_str.
            unfold translate_var in Hl1, H3.
            destruct (lenv ! x1) eqn:Hlx1; rewrite Hlx1 in Hl1=>//. injection Hl1 as ->.
            destruct (lenv ! x) eqn:Hlx2; rewrite Hlx2 in H3=>//. injection H3 as ->.
            have H'' := HlenvInjective _ _ _ _ n Hlx2 Hlx1.
            assert (i = x'0) by lia; subst i=>//.
            apply nth_error_Some. congruence. subst f_before_IH.
            apply HvalPreserved'. apply HvalPreserved. assumption.
          }
        }
      }

      assert (HeRestr' : expression_restricted cenv e). { now inv HeRestr. }

      assert (Hunbound' : (forall x : var, In x (collect_local_variables e) ->
                                                           rho' ! x = None)). {
        subst rho'. intros.
        assert (~ In x (collect_local_variables e)). {
          apply NoDup_app_remove_r in Hnodup. cbn in Hnodup.
          now apply NoDup_cons_iff in Hnodup. }
        assert (x <> x1) by congruence. rewrite M.gso; auto.
        apply Hunbound. now right.
      }

      assert (Hnodup': NoDup (collect_local_variables e ++
                              collect_function_vars (Efun fds e))). {
       cbn in Hnodup. apply NoDup_cons_iff in Hnodup.
       now destruct Hnodup. }

       assert (HfenvRho' : forall (a : positive) (v : cps.val),
          rho' ! a = Some v -> find_def a fds <> None -> v = Vfun (M.empty cps.val) fds a). {
          intros ?? Hrho Hfd. apply HfenvRho; auto. subst rho'.
          rewrite M.gso in Hrho; auto. intro Hcontra. subst a.
          apply notNone_Some in Hfd. apply HfenvWf in Hfd. destruct Hfd.
          inv Hx'. destruct HenvsDisjoint as [Hd1 Hd2].
          apply Hd2 in H0. unfold translate_var in H2. now rewrite H0 in H2. }

      have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny lh _ HlenvInjective HenvsDisjoint
                 state s_v f_before_IH _ Hfds' HlocInBound' Hinv_before_IH Hexp HrelE_v.
      destruct IH as [s_final [f_final [k' [lh' [Hred_IH [Hval [Hfinst [Hsfuncs' [HvalPres H_INV]]]]]]]]].
      clear IHHev HfenvRho' Hunbound' Hnodup' HlocInBound' Hinv_before_IH Hfds Hfds'.
      cbn in Hfinst.

      exists s_final, f_final, k', lh'. split.
      (* steps *)

      subst instrs instructions.

      eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
      eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
      apply r_eliml=>//. elimr_nary_instr 0. apply r_call.
      apply HfuncsId. unfold grow_mem_function_idx.
      unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
      dostep_nary 1.
      eapply r_invoke_native with (ves:= [AI_basic (BI_const_num (N_to_value page_size))])
        (vs:= [VAL_num (N_to_value page_size)]); try eassumption; eauto. reflexivity.

      eapply rt_trans. apply app_trans.
      eapply reduce_trans_frame. apply reduce_trans_label. apply Hred.
      dostep_nary 0. apply r_global_get. eassumption.
      dostep_nary 2. constructor. apply rs_relop. cbn.
      dostep_nary 1. constructor. apply rs_if_false. reflexivity.
      dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
      dostep_nary 0. constructor. apply rs_label_const; auto.

      cbn.
      repeat rewrite map_cat. cbn. repeat rewrite map_cat.

      (* take the first 10 instr lists *)
      separate_instr. do 9! rewrite catA.
      eapply rt_trans. apply app_trans. apply Hred_v.

      clear Hred_v. cbn. separate_instr. rewrite catA.
      eapply rt_trans. apply app_trans.
      dostep_nary 0. apply r_global_get. eassumption.

      assert (f_inst f_before_IH = f_inst fr) as Hfinst'. { subst. reflexivity. }
      dostep'. eapply r_local_set with (v:=VAL_num (VAL_int32 (wasm_value_to_i32 wal))). eassumption.
      apply /ssrnat.leP. apply nth_error_Some. congruence. subst. reflexivity. apply rt_refl. cbn.
      apply rt_refl.
      eapply rt_trans. apply Hred_IH. cbn. apply rt_refl.

      subst f_before_IH.
      repeat (split; auto). congruence.
    }}
    { (* grow mem failed *)
    subst instructions instrs.

    (* split of dead instructions after
       (BI_if (BT_valtype None) [:: BI_return] [::]) *)
    separate_instr. do 4 rewrite catA.
     match goal with
     |- context C [reduce_trans (_, _, _, [:: AI_frame _ _ (lfill _
        (_ ++ [:: AI_basic (BI_if _ [:: BI_return] [::])] ++ ?es))])] =>
         let es_tail := fresh "es_tail" in
         remember es as es_tail
     end. do 4 rewrite <- catA.

    have Hlh := lholed_nested_label _ lh [AI_basic BI_return] es_tail. subst es_tail.
    destruct Hlh as [k' [lh' Heq']].

    do 3! eexists. exists lh'. split.

    eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
    eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
    apply r_eliml=>//. elimr_nary_instr 0. apply r_call.
    apply HfuncsId. unfold grow_mem_function_idx.
    unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
    dostep_nary 1.
    eapply r_invoke_native with (ves:= [AI_basic (BI_const_num (N_to_value page_size))])
      (vs:= [VAL_num (N_to_value page_size)]); try eassumption; eauto; try by (rewrite HeqfM; auto). reflexivity.
    eapply rt_trans. apply app_trans. eapply rt_trans.
    eapply reduce_trans_frame'. eapply reduce_trans_label. subst fM. apply Hred.
    dostep_nary' 0. constructor. apply rs_local_const=>//. apply rt_refl. cbn.
    dostep_nary 0. apply r_global_get. subst fM. eassumption.
    dostep_nary 2. constructor. apply rs_relop.
    dostep_nary 1. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
    dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
    apply rt_refl. cbn.

    rewrite Heq'. apply rt_refl.
    split. right. subst fM. assumption.
    split=>//. split=>//.
    split. { intros. subst fM. apply HvalPreserved. assumption. }

    intro Hcontra. subst fM. rewrite Hcontra in HoutofM. inv HoutofM. }}}
    { (* Nullary constructor case *)

      subst. injection H as <-.
      remember ({|f_locs := set_nth (VAL_num (nat_to_value (N.to_nat (2 * ord + 1)))) (f_locs fr) (N.to_nat x') (VAL_num (nat_to_value (N.to_nat (2 * ord + 1)))) ; f_inst := f_inst fr|}) as f_before_IH.
      assert (HNoDup' : NoDup (collect_local_variables e ++ collect_function_vars (Efun fds e))). {
        cbn in Hnodup. apply NoDup_cons_iff in Hnodup.
        destruct Hnodup. assumption.
      }
      assert (HfenvRho' : (forall (a : positive) (v : val),
        (map_util.M.set x (Vconstr t []) rho) ! a = Some v ->
        find_def a fds <> None -> v = Vfun (M.empty val) fds a)). {
        intros. apply HfenvRho. rewrite M.gso in H. assumption.
        intro. subst a. apply notNone_Some in H0. apply HfenvWf in H0. destruct H0. inv H7. destruct HenvsDisjoint as [Hd1 Hd2]. apply Hd2 in H. unfold translate_var in H0. rewrite H in H0. inv H0. assumption.
      }
      assert (Herestr' :  expression_restricted cenv e). {
        inv HeRestr. assumption.
      }

      assert (Hunbound' : (forall x0 : var,
        In x0 (collect_local_variables e) ->
        (map_util.M.set x (Vconstr t []) rho) ! x0 = None)). {
        intros. apply NoDup_app_remove_r in Hnodup. cbn in Hnodup. apply NoDup_cons_iff in Hnodup. rewrite M.gso. apply Hunbound. unfold collect_local_variables. cbn. fold collect_local_variables. right. assumption. destruct Hnodup as [Hx _ ]. unfold not. unfold not in Hx. intros Heq. subst x. apply Hx in H. contradiction.
      }

      assert (Hfds' :  (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) (errMsg : string),
        find_def a fds = Some (t, ys, e) ->
        expression_restricted cenv e /\
        (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)) /\
        (exists fidx : funcidx,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Wasm (Vfun (M.empty val) fds a) sr (f_inst f_before_IH) (Val_funidx fidx)))). {
        intros ? ? ? ? ? Hfd.
        apply Hfds with (errMsg:=errMsg) in Hfd.
        destruct Hfd as [? [? [? [idx [Htransf Hval]]]]]; repeat (split; try assumption).
        exists idx. split.
        assumption. subst f_before_IH.
        by eapply val_relation_func_depends_on_funcs; auto.
      }

      assert (HlocInBound': (forall (var : positive) (varIdx : u32),
        @repr_var nenv lenv var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs f_before_IH))). {
        intros ?? Hvar. subst f_before_IH. cbn.
          rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
          apply HlocInBound in Hvar, H7. lia. }

      assert (Hinv' : INV sr f_before_IH). {
        eapply update_local_preserves_INV; try eassumption.
        now destruct (HlocInBound x x').
      }

      assert (HrelE' : @rel_env_LambdaANF_Wasm lenv e (map_util.M.set x (Vconstr t []) rho) sr f_before_IH fds). {
        have Hl := HlocInBound _ _ H7.
        apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl as [? Hlx].

        destruct HrelE as [Hfun1 [Hfun2 Hvar]]. unfold rel_env_LambdaANF_Wasm. split.
        { intros. destruct (var_dec x x1).
          { subst x1. rewrite M.gss in H. inv H.
            apply subval_or_eq_fun in H0.
            destruct H0 as [v1 [Hr1 Hr2]]. inv Hr2.
          }
          { by rewrite M.gso in H; eauto. }
        } split.
        { intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          exists i. split. assumption. subst f_before_IH. assumption.
        }
        { intros. destruct (var_dec x x1).
          { subst x1.

            assert ( (Wasm_int.Int32.half_modulus < Wasm_int.Int32.modulus)%Z ). {
              now rewrite Wasm_int.Int32.half_modulus_modulus.
            }

            exists (Vconstr t []), (Val_unboxed (2 * ord + 1)%N).
            rewrite M.gss. split. reflexivity.
            split.
            {
              unfold stored_in_locals. exists x'. split.
              - unfold translate_var. inv H7. unfold translate_var in H2.
                destruct (lenv ! x) eqn:Hx; rewrite Hx in H2=>//. injection H2 as ->. now rewrite Hx.
              - subst f_before_IH. cbn. unfold lookup_N, nat_to_value, nat_to_i32, wasm_value_to_i32. repeat f_equal.
                erewrite set_nth_nth_error_same; eauto. by rewrite N_nat_Z.
            }
            {
              econstructor ; eauto.
              now rewrite N.mul_comm.
              { inv HeRestr.
                unfold ctor_ordinal_restricted in H11.
                apply H11 in H9.
                simpl_modulus. (* cbn. *)
                simpl_modulus_in H9.
                (* cbn. *)
                cbn in H9.
                cbn.
                destruct ord ; lia.
              }
              (* assumption. *)
            }
          }
          {
            assert (Hocc: occurs_free (Econstr x t [] e) x1). { now apply Free_Econstr2. }
            have H' := Hvar _ Hocc H0.
            destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
            exists val', wal'.
            split. rewrite M.gso; auto.
            split. 2: now subst f_before_IH.
            destruct Hloc as [i [Hl1 Hl2]].
            unfold stored_in_locals. exists i. split; auto.
            subst f_before_IH.
            unfold lookup_N.
            rewrite set_nth_nth_error_other; auto.
            intro. assert (x' = i) by lia. subst x'. inv H7.
            specialize Hl1 with err_str.
            unfold translate_var in Hl1, H2.
            destruct (lenv ! x1) eqn:Hlx1; rewrite Hlx1 in Hl1=>//. injection Hl1 as ->.
            destruct (lenv ! x) eqn:Hlx2; rewrite Hlx2 in H2=>//. injection H2 as ->.
            have H'' := HlenvInjective _ _ _ _ n Hlx2 Hlx1. contradiction.
            apply nth_error_Some. congruence.
          }
        }
      }

      have IH := IHHev HNoDup' HfenvRho' Herestr' Hunbound' _ fAny lh _ HlenvInjective HenvsDisjoint
                 state sr f_before_IH _ Hfds' HlocInBound' Hinv' H6 HrelE'.
      destruct IH as [sr' [f' [k' [lh' [Hred [Hval [Hfinst [Hsfuncs [HvalPres H_INV]]]]]]]]].

      exists sr', f', k', lh'.
      split. eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
      dostep_nary 1. eapply r_local_set with (f':=f_before_IH)
         (v:=VAL_num (nat_to_value (N.to_nat
           (match ord with
            | 0 => 0
            | N.pos q => N.pos q~0
            end + 1)))%N).
        subst f_before_IH. reflexivity.
        have I := Hinv.
        apply /ssrnat.leP.
        apply HlocInBound in H7. assumption.
        subst f_before_IH. reflexivity.
        apply rt_refl.

      (* IH *)
      apply Hred.

      subst f_before_IH.
      by repeat (split; auto).
    }
  - (* Eproj: let x := proj_n y in e *)
    { inv Hrepr_e.
      rename H8 into Hx', H9 into Hy'.

      (* y is constr value with correct tag, arity *)
      assert (Hy : occurs_free (Eproj x t n y e) y) by constructor.
      have HrelE' := HrelE.
      destruct HrelE' as [Hfun1 [Hfun2 Hvar]].
      assert (HfdNone: find_def y fds = None). {
        apply HfenvWf_None with (f:=y) in HfenvWf. rewrite HfenvWf.
        inv Hy'. unfold translate_var in H1.
        destruct (lenv ! y) eqn:Hy'; rewrite Hy' in H1=>//. injection H1 as ->. now apply HenvsDisjoint in Hy'. }
      apply Hvar in Hy; auto. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
      rewrite Hrho in H. inv H.
      have Hrepr' := Hrepr. inv Hrepr'.
      (* unboxed absurd *) inv H0.
      (* boxed *)
      inv Hlocal. destruct H.

      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [HfnsUpperBound [_ [_ _]]]]]]]]]]]].
      have Hextr := extract_constr_arg n vs v _ _ _ _ HfnsUpperBound H0 H10 H16.
      destruct Hextr as [bs [wal [Hload [Heq Hbsval]]]].

      remember {| f_locs := set_nth (VAL_num (wasm_deserialise bs T_i32)) (f_locs fr) (N.to_nat x') (VAL_num (wasm_deserialise bs T_i32))
                ; f_inst := f_inst fr
                |} as f_before_IH.

      assert (Hrm: @rel_env_LambdaANF_Wasm lenv e (map_util.M.set x v rho) sr f_before_IH fds). {
        split; intros.
        { (* funs1 *)
          destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1.
            rewrite M.gss in H11. inv H11. rename v0 into v.
            apply nthN_In in H0.
            have H' := subval_or_eq_constr _ _ _ t H13 H0.
            have HF := Hfun1 _ _ _ _ _ Hrho H'. destruct HF as [? [? HF]]. subst.
            apply Hfun2 with (errMsg:=""%bs) in HF.
            destruct HF as [i [Htrans Hval]].
            inv Hval. do 2 split => //.
            eapply find_def_name_in_fundefs. eassumption.
          }
          { (* x <> x1*)
            rewrite M.gso in H11; auto.
            have H' := Hfun1 _ _ _ _ _ H11 H13. destruct H' as [? [? H']]. subst.
            apply Hfun2 with (errMsg:=""%bs) in H'.
            destruct H' as [i [Htf Hval]].
            inv Hval. do 2 split => //.
            eapply find_def_name_in_fundefs. eassumption.
           }
        } split.
        { (* funs2 *)
          intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          exists i. split. assumption. subst f_before_IH. assumption.
        }
        { (* local vars *)
          intros. destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1.
            exists v. exists wal. split.
            rewrite map_util.M.gsspec.
            apply peq_true.
            split. exists x'. split. inv Hx'. intro.
            unfold translate_var in H14. unfold translate_var.
            destruct (lenv ! x) eqn:Hx; rewrite Hx in H14=>//.
            injection H14 as ->.  by rewrite Hx.
            unfold wasm_deserialise in Heq. rewrite Heq.
            have Hl := HlocInBound _ _ Hx'. apply nth_error_Some in Hl.
            apply notNone_Some in Hl. destruct Hl.
            subst f_before_IH. eapply set_nth_nth_error_same. eassumption.
            subst f_before_IH. assumption. }
          { (* x <> x1 *)
            assert (Hocc: occurs_free (Eproj x t n y e) x1). { constructor; assumption. }
            apply Hvar in Hocc; auto. destruct Hocc as [v6 [wal' [Henv [Hloc Hval]]]].
            exists v6. exists wal'.
            subst f_before_IH.
            repeat split; auto.
            rewrite map_util.M.gsspec.
            rewrite peq_false. assumption. congruence.
            destruct Hloc as [x1' [? ?]].
            unfold stored_in_locals. cbn.

            assert (x1' <> x'). { intro. subst x1'.
              inv Hx'. unfold translate_var in H17.
              destruct (lenv ! x) eqn:Heqn; rewrite Heqn in H17=>//.
              injection H17 as ->.
              specialize H14 with err_str. unfold translate_var in H14.
              destruct (lenv ! x1) eqn:Heqn'; rewrite Heqn' in H14=>//.
              injection H14 as ->.
              have Hcontra := HlenvInjective _ _ _ _ n0 Heqn Heqn'.
              now apply Hcontra. }
          exists x1'.
          split; auto.
          unfold lookup_N.
          rewrite set_nth_nth_error_other; auto; try lia.
          eapply HlocInBound. eassumption.
        }
     }}

     assert (Hfds': (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) errMsg,
      find_def a fds = Some (t, ys, e) ->
        expression_restricted cenv e /\
        (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++
           collect_local_variables e ++
           collect_function_vars (Efun fds e)) /\
        (exists fidx : funcidx,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Wasm (Vfun (M.empty cps.val) fds a) sr (f_inst f_before_IH) (Val_funidx fidx)))). {
         intros ? ? ? ? ? Hfd. apply Hfds with (errMsg:=errMsg) in Hfd.
         destruct Hfd as [? [? [? [idx [HtransF Hval]]]]].
         repeat (split; try assumption).
         exists idx. split. assumption. subst f_before_IH.
         eapply val_relation_func_depends_on_funcs.
         2: eassumption.
         congruence.
      }

     assert (HlocInBound': (forall (var : positive) (varIdx : localidx),
        @repr_var nenv lenv var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs f_before_IH))). {
      intros ?? Hvar'. cbn. subst f_before_IH.
      rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
      apply HlocInBound in Hvar'. lia. }

     assert (Hinv': INV sr f_before_IH). {
       subst f_before_IH. cbn.
       eapply update_local_preserves_INV. 3: reflexivity.
       assumption. apply nth_error_Some. intros. apply nth_error_Some.
       eapply HlocInBound. eassumption. }

     assert (HeRestr' : expression_restricted cenv e). { now inv HeRestr. }
     assert (Hunbound': (forall x0 : var, In x0 (collect_local_variables e) ->
                                          (map_util.M.set x v rho) ! x0 = None)). {
       intros.
       assert (~ In x (collect_local_variables e)). {
         apply NoDup_app_remove_r in Hnodup. cbn in Hnodup.
         now apply NoDup_cons_iff in Hnodup. }
       assert (x <> x1) by congruence. rewrite M.gso; auto.
       apply Hunbound. now right.
     }

     assert (Hnodup' : NoDup (collect_local_variables e ++
                              collect_function_vars (Efun fds e))). {
       cbn in Hnodup. apply NoDup_cons_iff in Hnodup.
       now destruct Hnodup. }

     assert (HfenvRho' : forall (a : positive) (v0 : cps.val),
              (map_util.M.set x v rho) ! a = Some v0 ->
              find_def a fds <> None ->
              v0 = Vfun (M.empty cps.val) fds a). {
       intros. apply HfenvRho; auto.
       rewrite M.gso in H11; auto. intro Hcontra. subst a.
       apply notNone_Some in H13. apply HfenvWf in H13. destruct H13.
       inv Hx'. destruct HenvsDisjoint as [Hd1 Hd2].
       apply Hd2 in H11. unfold translate_var in H13. now rewrite H11 in H13. }

     have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny lh _ HlenvInjective HenvsDisjoint
                      state _ _ _ Hfds' HlocInBound' Hinv' H7 Hrm.
     destruct IH as [sr' [f' [k' [lh' [Hred [Hval [Hfinst [Hsfuncs [HvalPres H_INV]]]]]]]]]. cbn in Hfinst.

     exists sr', f', k', lh'. cbn. split.
     { (* take steps *)
       have Htmp := Hy'. inversion Htmp. subst i s.

       have I := Hinv'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
       have Hly := HlocInBound _ _ Hy'.
       have Hlx := HlocInBound _ _ Hx'.
       rewrite H in H11. injection H11 as ->.

       eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
       (* get_local y' *)
       dostep_nary 0. apply r_local_get. apply H1.
       (* add offset n *)
       dostep_nary 2. constructor. apply rs_binop_success. cbn. reflexivity.
       assert (Har: Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (wasm_value_to_i32 (Val_ptr addr))
            (nat_to_i32 ((N.to_nat n + 1) * 4))) = ((4 + addr) + 4 * n)%N). {
          replace (4 + addr)%N with (addr + 4)%N by lia. replace (4*n)%N with (n*4)%N by lia. cbn.
       unfold load in Hload.
       destruct (((4 + addr) + 4 * n + (0 + N.of_nat 4) <=? mem_length m)%N) eqn:Heqn. 2: inv Hload.
       apply N.leb_le in Heqn.
       destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
       assert (m' = m). { unfold smem in H10, Hmem2. subst f_before_IH. rewrite Hmem1 in H10, Hmem2.
        congruence. } subst.
       apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
       repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia).  }

       dostep_nary 1. eapply r_load_success. eassumption. rewrite Har. apply Hload.
       (* save result in x' *)
       dostep_nary 1. eapply r_local_set with (v := VAL_num (VAL_int32 (Wasm_int.Int32.repr (decode_int bs)))) (f':=f_before_IH); subst f_before_IH=>//.
       apply /ssrnat.leP. now apply HlocInBound in Hx'. apply rt_refl.
       apply Hred. }
     subst f_before_IH. by repeat (split; auto).
    }
  - (* Ecase *)
    {
      intros.
      assert (caseConsistent cenv cl t). { assumption. }
      inv Hrepr_e.
      rename H5 into Hy'.
      assert (Hy : occurs_free (Ecase y cl) y) by constructor.
      have HrelE' := HrelE.
      destruct HrelE' as [Hfun1 [Hfun2 Hvar]].
      assert (HfdNone: find_def y fds = None). {
        apply HfenvWf_None with (f:=y) in HfenvWf. rewrite HfenvWf.
        inv Hy'. unfold translate_var in H3. destruct (lenv ! y) eqn:Hy'; rewrite Hy' in H3=>//.
        injection H3 as ->.
        now apply HenvsDisjoint in Hy'.
      }
      have Hy0 := Hy.
      apply Hvar in Hy0; auto.
      destruct Hy0 as [v0 [wal [Hrho [Hlocals Hval]]]].
      assert (v0 = (Vconstr t vl)) by congruence. subst v0.
      (* Assert that we can step into either
         the unboxed or boxed cases,
         and from there into the correct branch *)
      assert (Hstep_case:
               exists e' k0 (lh0 : lholed k0),
                 reduce_trans
                     (state, sr, fAny,
                       [AI_frame 0 fr (lfill lh ([seq AI_basic i | i <-
                                           [:: BI_local_get y'
                                            ; BI_const_num (nat_to_value 1)
                                            ; BI_binop T_i32 (Binop_i BOI_and)
                                            ; BI_testop T_i32 TO_eqz
                                            ; BI_if (BT_valtype None)
                                                e1'
                                                e2']]))])
                     (state, sr, fAny, [AI_frame 0 fr (lfill lh0 (map AI_basic e'))])
                 /\ @repr_expr_LambdaANF_Wasm penv lenv e e'). {
        have Hval' := Hval.
        inv Hval.
        { (* Unboxed cases (nullary) *)
          assert (exists e' e'',
                     select_nested_if false y' ord brs2 =
                       [ BI_local_get y'
                         ; BI_const_num (nat_to_value (N.to_nat (2 * ord + 1)))
                         ; BI_relop T_i32 (Relop_i ROI_eq)
                         ; BI_if (BT_valtype None)
                             e'
                             e'' ]
                     /\ (forall k0 (lh0 : lholed k0),
                           exists k0' (lh0' : lholed k0'),
                           reduce_trans
                             (state, sr, fAny, [AI_frame 0 fr (lfill lh0 (map AI_basic e2'))])
                             (state, sr, fAny, [AI_frame 0 fr (lfill lh0' (map AI_basic e'))]))
                     /\ @repr_expr_LambdaANF_Wasm penv lenv e e').
          {
            destruct Hlocals as [i [Htrans_y Hlocs]].
            assert (i = y'). { inv Hy'. specialize (Htrans_y err_str). rewrite H3 in Htrans_y. inv Htrans_y. reflexivity. } subst i.
            have Hif_red := unboxed_nested_if_chain_reduces cl fAny y t e y' lenv brs1 brs2 e2' fr state sr ord Hlocs HcenvRestr HeRestr H2 H1 H5 H14 H6 H9.
            destruct Hif_red as [e' [e'' [Hsel [Hred Hrep]]]].
            by exists e', e''.
          }
          destruct H3 as [e' [e'' [_ [Hred Hrep]]]].
          have Hholednested := lholed_nested_label k lh (map AI_basic e2') [].
          destruct Hholednested as [k0' [lh0' He2']].
          have Hred' := Hred k0' lh0'.
          destruct Hred' as [k0 [lh0 Hred']].
          exists e', k0, lh0. split; auto.
          have Hlocals' := Hlocals.
          destruct Hlocals' as [i [Htrans_y Hntherror]].
          assert (i = y'). { inv Hy'. specialize (Htrans_y err_str). rewrite H3 in Htrans_y. inv Htrans_y. reflexivity. } subst i.
          eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
          dostep_nary 0. apply r_local_get. eauto.
          dostep_nary 2. constructor. apply rs_binop_success.
          cbn.
          assert (Heq: Wasm_int.Int32.iand (wasm_value_to_i32 (Val_unboxed (ord * 2 + 1)%N)) (nat_to_i32 1) = Wasm_int.Int32.one).
          {
            rewrite N.mul_comm.
            unfold wasm_value_to_i32; unfold wasm_value_to_u32; unfold N_to_i32.
            cbn.
            eapply and_of_odd_and_1_1. rewrite N.mul_comm in H10. lia.
          }
          rewrite Heq. reflexivity.
          dostep_nary 1. constructor. eapply rs_testop_i32.
          dostep'. constructor. apply rs_if_false. reflexivity.
          dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
          apply rt_refl.
          rewrite -He2' in Hred'. apply Hred'.
        }
        { (* Boxed cases (non-nullary) *)
          assert (exists e' e'',
                     select_nested_if true y' ord brs1 =
                       [ BI_local_get y'
                       ; BI_load T_i32 None 2%N 0%N
                       ; BI_const_num (nat_to_value (N.to_nat ord))
                       ; BI_relop T_i32 (Relop_i ROI_eq)
                       ; BI_if (BT_valtype None)
                           e'
                           e'' ]
                     /\ (forall k0 (lh0 : lholed k0),
                           exists k0' (lh0' : lholed k0'),
                           reduce_trans
                             (state, sr, fAny, [AI_frame 0 fr (lfill lh0 (map AI_basic e1'))])
                             (state, sr, fAny, [AI_frame 0 fr (lfill lh0' (map AI_basic e'))]))
                     /\ @repr_expr_LambdaANF_Wasm penv lenv e e').
          {
            destruct Hlocals as [i [Htrans_y Hlocs]].
            assert (i = y'). { inv Hy'. specialize (Htrans_y err_str). rewrite H3 in Htrans_y. inv Htrans_y. reflexivity. } subst i.
            destruct Hinv as [_ [_ [_ [_ [_ [_ [Hmem _]]]]]]].
            have Hif_red := boxed_nested_if_chain_reduces cl fAny y t vl e addr y' lenv brs1 brs2 e1' state sr fr ord Hmem Hval' Hlocs HcenvRestr HeRestr H0 H10 H1 H6 H7.
            destruct Hif_red as [e' [e'' [Hsel [Hred Hrep]]]].
            have Hred' := Hred k lh.
            by exists e', e''.
          }
          destruct H3 as [e' [e'' [_ [Hred Hrep]]]].
          have Hholednested := lholed_nested_label k lh (map AI_basic e1') [].
          destruct Hholednested as [k0' [lh0' He1']].
          destruct (Hred k0' lh0') as [k0 [lh0 Hred']].
          exists e', k0, lh0. split; auto.
          destruct Hlocals as [i [Htrans_y Hntherror]].
          assert (i = y'). { inv Hy'. specialize (Htrans_y err_str). rewrite H3 in Htrans_y. inv Htrans_y. reflexivity. }
          eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
          dostep_nary 0. apply r_local_get. rewrite H3 in Hntherror. eauto.
          assert (Hand : Wasm_int.Int32.iand (wasm_value_to_i32 (Val_ptr addr)) (nat_to_i32 1) = Wasm_int.Int32.zero). {
            destruct H14 as [n0 Hn0].
            rewrite Hn0.
            unfold wasm_value_to_u32; unfold wasm_value_to_i32; unfold N_to_i32.
            cbn.
            apply and_of_even_and_1_0.
            lia.
          }
          dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
          dostep_nary 1. constructor. apply rs_testop_i32. cbn.
          dostep'. constructor. apply rs_if_true. by rewrite Hand.
          dostep'. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
          apply rt_refl.
          rewrite -He1' in Hred'. apply Hred'.
        }
      }
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem [_ [_ [_ [_ [_  _]]]]]]]]]]]].

      assert (Hrel: @rel_env_LambdaANF_Wasm lenv e rho sr fr fds).
      { unfold rel_env_LambdaANF_Wasm.
        split. intros. eauto.
        split. eauto. intros.
        assert (occurs_free (Ecase y cl) x).
        eapply occurs_free_Ecase_Included.
        apply findtag_In. eauto. eauto.
        apply Hvar; auto.
      }

      assert (HeRestr': expression_restricted cenv e). {
        inv HeRestr.
        rewrite Forall_forall in H5.
        apply H5 with (x:=(t,e)).
        by apply findtag_In.
      }

      assert (Hunbound': (forall x : var, In x (collect_local_variables e) ->
                                     rho ! x = None)). {
        intros. apply Hunbound. cbn.
        apply in_flat_map.
        exists (t,e). split; auto.
        by apply findtag_In.
      }

      destruct Hstep_case as [e' [k0 [lh0 [Hred Hrepre]]]].

      assert (Hnodup': NoDup (collect_local_variables e ++
                                collect_function_vars (Efun fds e))). {
        apply NoDup_incl_NoDup' with (l1:=collect_local_variables (Ecase y cl)) =>//.
        apply NoDup_case with (cl:=cl) (t:=t) (y:=y)=>//.
        apply NoDup_app_remove_r in Hnodup. assumption.
        assert (In (t, e) cl). { by apply findtag_In. }
        intros ??. apply in_flat_map. by exists (t, e).
      }

      have IH := IHHev Hnodup' HfenvRho HeRestr' Hunbound' k0 fAny lh0 _ HlenvInjective HenvsDisjoint
                       state _ _ _ Hfds HlocInBound Hinv Hrepre Hrel.
      destruct IH as [sr' [fr' [k1 [lh1 [Hstep [Hval_e [Hfinst [HvalPres H_INV]]]]]]]].

      exists  sr', fr', k1, lh1. split.
      { (* steps *)
        eapply rt_trans. apply Hred.
        apply Hstep.
      }
      split. apply Hval_e.
      split. apply Hfinst.
      split. apply HvalPres.
      apply H_INV.
    }
  - (* Eapp *)
    { inv Hrepr_e. rename args' into args_instr.
      assert (HfdsRhoEq: fl = fds /\ rho' = M.empty _). { destruct HrelE as [Hfun1 _]. eapply Hfun1 in H. now destruct H. apply rt_refl. } destruct HfdsRhoEq. subst fl rho'.
      (* treat direct + indirect calls in one *)
      assert (Hval: exists fidx,
        reduce_trans (state, sr, fr, [AI_basic instr])
                     (state, sr, fr, [AI_basic (BI_const_num (N_to_value fidx))]) /\
        repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f') sr (f_inst fr) (Val_funidx fidx)). {

      inv H8.
      { (* indirect call *)
        assert (Hocc: occurs_free (Eapp f t ys) f) by constructor.
        have Hrel := HrelE. destruct Hrel as [Hfun1 [_ Hvar]].
        assert (HfNone: find_def f fds = None). {
          apply HfenvWf_None with (f:=f) in HfenvWf. rewrite HfenvWf.
          inv H3. unfold translate_var in H4. destruct (lenv ! f) eqn:Hf'; rewrite Hf' in H4=>//.
          injection H4 as ->. now apply HenvsDisjoint in Hf'. }
        apply Hvar in Hocc; auto. destruct Hocc as [val [wal [Hrho [[j [Htrans Hwal]] Hval]]]].
        inv H3. rewrite Htrans in H4. inv H4.
        rewrite H in Hrho. inv Hrho. inv Hval.
        rewrite H1 in H6. symmetry in H6. inv H6.
        rename i into locIdx.
        exists idx. split.
        dostep'. apply r_local_get. eassumption. apply rt_refl.
        econstructor; eauto. }
      { (* direct call *)
        inv H3. unfold translate_var in H4. destruct (fenv ! f) eqn:Hf; rewrite Hf in H4=>//.
        injection H4 as ->.
        assert (Hf': exists i, fenv ! f = Some i) by eauto.
        apply HfenvWf in Hf'.
        assert (Htemp: f' = f). { apply HfenvRho in H. now inv H. now destruct Hf'. }
        inv Htemp.
        destruct HrelE as [Hfun1 [Hfun2 _]].
        assert (Hsubval: subval_or_eq (Vfun (M.empty cps.val) fds f)
                                      (Vfun (M.empty cps.val) fds f)) by constructor.
        have H' := Hfun1 _ _ _ _ _ H Hsubval. destruct H' as [_ [_ H']].
        apply Hfun2 with (errMsg:=errMsg) in H'.
        destruct H' as [idx [HtransF Hval]].
        assert (idx = i). { unfold translate_var in HtransF. now rewrite Hf in HtransF. }
        subst idx. exists i. split. apply rt_refl.
        assumption.
      }
    }

    destruct Hval as [fidx [HredF Hval]]. inv Hval.
    rewrite H9 in H1. inv H1. rename H14 into Hexpr.

    repeat rewrite map_cat. cbn.
    have Hfargs := fun_args_reduce state _ _ _ _ _ _ _ _ _ Hinv H0 HenvsDisjoint HfenvWf HfenvRho HrelE H7.
    destruct Hfargs as [args [HfargsRed HfargsRes]].

    remember {| f_locs := [seq (VAL_num (N_to_value a)) | a <- args] ++
                   (repeat (VAL_num (N_to_value 0)) (Datatypes.length (collect_local_variables e)));
               f_inst := f_inst fr |} as f_before_IH.

    (* prepare IH *)
    remember (create_local_variable_mapping (xs ++(collect_local_variables e))) as lenv_before_IH.

    assert (Hfds_before_IH: (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) errMsg,
      find_def a fds = Some (t, ys, e) ->
        expression_restricted cenv e /\
        (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++
           collect_local_variables e ++
           collect_function_vars (Efun fds e)) /\
        (exists fidx : funcidx,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Wasm (Vfun (M.empty cps.val) fds a) sr (f_inst f_before_IH) (Val_funidx fidx)))). {
         intros ? ? ? ? ? Hfd. eapply Hfds with (errMsg:=errMsg) in Hfd.
         destruct Hfd as [? [? [? [idx [HtransF Hval]]]]].
         repeat (split; try assumption).
         exists idx. split. assumption.
         eapply val_relation_func_depends_on_funcs.
         2: subst f_before_IH; eassumption.
         congruence.
    }

    assert (HlocInBound_before_IH: (forall (var : positive) (varIdx : localidx),
          @repr_var nenv (create_local_variable_mapping (xs ++ collect_local_variables e)) var varIdx ->
           N.to_nat varIdx < Datatypes.length (f_locs f_before_IH))). {
      intros ?? Hvar. subst f_before_IH. cbn. inv Hvar. apply var_mapping_list_lt_length in H1.
      rewrite app_length in H1. apply const_val_list_length_eq in HfargsRes.
      rewrite app_length. rewrite map_length -HfargsRes.
      rewrite map_repeat_eq. rewrite map_length. apply set_lists_length_eq in H2.
      now rewrite -H2.
    }

    assert (Hinv_before_IH : INV sr f_before_IH). {
       subst. now eapply init_locals_preserves_INV. }

    assert (HrelE': @rel_env_LambdaANF_Wasm lenv_before_IH e rho'' sr f_before_IH fds). {
      unfold rel_env_LambdaANF_Wasm. split.
      { (* funs1 *)
        intros.
        assert (Hdec: decidable_eq var). {
          intros n m. unfold Decidable.decidable. now destruct (var_dec n m). }
       have H' := In_decidable Hdec x xs. clear Hdec. destruct H'.
       { (* In x xs *)
         have H' := set_lists_In _ _ _ _ _ _ H4 H1 H2.
         destruct (get_list_In_val _ _ _ _ H0 H') as [y [Hiny HyRho]].
         destruct HrelE as [Hfun1 [Hfun2 _]]. eauto.
       }
       { (* ~In x xs *)
         have H' := set_lists_not_In _ _ _ _ _ H2 H4. rewrite H1 in H'.
         erewrite def_funs_find_def in H'.
         2:{ intro Hcontra. apply def_funs_not_find_def with (fds':=fds) (rho:=M.empty _) in Hcontra.
             rewrite Hcontra in H'. inv H'. } inv H'.
         have H' := set_lists_not_In _ _ _ _ _ H2 H4.
         rewrite H1 in H'.
         apply def_funs_spec in H'. destruct H' as [[? ?] | [? Hcontra]]. 2: inv Hcontra.
         apply subval_fun in H3. 2: assumption.
         destruct H3 as [f1 [?H ?H]]. inv H3. now inv H10.
      }} split.
      { (* fun2 *)
        destruct HrelE as [_ [Hfun2 _]].
        intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
        destruct Hnfd as [i [Htrans Hval]].
        exists i. split. assumption. subst f_before_IH. assumption. }
      { (* vars *)
        intros. destruct HrelE as [_ HrelVars].
        assert (In x xs). {
          apply Hfds with (errMsg:=""%bs) in H9; auto.
          destruct H9 as [? [Hxxs ?]].
          have H' := Hxxs _ H1. now destruct H'. }
        destruct (get_set_lists_In_xs _ _ _ _ _ H4 H2) as [v' Hv'].
        have H' := set_lists_nth_error _ _ _ _ _ _ H2 H4 Hv'.
        destruct H' as [k' [Hvk Hxk]].
        have H'' := const_val_list_nth_error _ _ _ _ _ _ HfargsRes Hvk.
        destruct H'' as [w [Hw Hnth]].
        exists v', w. split; auto. split; auto.

        unfold stored_in_locals. subst lenv_before_IH f_before_IH. exists (N.of_nat k').
        split. {
          intros. unfold create_local_variable_mapping.
          rewrite (var_mapping_list_lt_length_nth_error_idx _ (N.of_nat k')); auto.
          apply Hfds with (errMsg:=""%bs) in H9. destruct H9 as [_ [_ [HnodupE _]]].
          rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE. assumption.
          unfold lookup_N.
          rewrite Nat2N.id.
          rewrite nth_error_app1; auto. apply nth_error_Some. intro.
          rewrite H5 in Hxk. inv Hxk. }
        cbn. unfold lookup_N.
        rewrite nth_error_app1. 2: {
          rewrite length_is_size size_map -length_is_size.
          apply const_val_list_length_eq in HfargsRes.
          rewrite -HfargsRes.
          apply nth_error_Some. rewrite Nat2N.id. congruence. }
        rewrite Nat2N.id. assumption.
        subst f_before_IH. assumption. }
    }

    assert (HeRestr' : expression_restricted cenv e). {
        apply Hfds with (errMsg:=""%bs) in H9. now destruct H9. }

    assert (Hunbound': (forall x : var, In x (collect_local_variables e) -> rho'' ! x = None)). {
      intros.
      assert (~ exists v, find_def x fds = Some v). {
        intro Hcontra. destruct Hcontra as [? Hfd].
        assert (Hfd': find_def x fds <> None) by congruence.
        clear Hfd. rename Hfd' into Hfd.
        eapply find_def_in_collect_function_vars in Hfd.
        apply Hfds with (errMsg:=""%bs) in H9. destruct H9 as [_ [_ [HnodupE _]]].
        apply NoDup_app_remove_l in HnodupE.
        eapply NoDup_app_In in HnodupE; eauto. }
      assert (Hfd: find_def x fds = None). { destruct (find_def x fds); eauto. exfalso. eauto. }
      apply def_funs_not_find_def with (fds':=fds) (rho:=M.empty _) in Hfd.
      assert (HxIn: ~ In x xs). {
        intro Hcontra. apply Hfds with (errMsg:=""%bs) in H9. destruct H9 as [_ [_ [HnodupE _]]].
        rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE.
        eapply NoDup_app_In in HnodupE; eauto. }
      have H'' := set_lists_not_In _ _ _ _ _ H2 HxIn. rewrite <- H''.
      now rewrite Hfd.
    }

    assert (HlenvInjective': map_injective lenv_before_IH). {
      subst lenv_before_IH.
      apply create_local_variable_mapping_injective. {
      apply Hfds with (errMsg:=""%bs) in H9. destruct H9 as [_ [_ [HnodupE _]]].
      rewrite catA in HnodupE. now apply NoDup_app_remove_r in HnodupE.
    }}

    assert (HenvsDisjoint': domains_disjoint lenv_before_IH fenv). {
      apply Hfds with (errMsg:=""%bs) in H9. destruct H9 as [_ [_ [HnodupE _]]].
      subst lenv_before_IH. unfold domains_disjoint. split; intros.
      { (* -> *)
        apply variable_mapping_Some_In in H1; auto.
        assert (~ exists v, fenv ! x = Some v). {
          intro Hcontra. apply HfenvWf in Hcontra.
          apply notNone_Some in Hcontra.
          eapply find_def_in_collect_function_vars in Hcontra.
          rewrite catA in HnodupE. eapply NoDup_app_In in HnodupE; eauto. }
          destruct (fenv ! x) eqn:Hx; auto. exfalso. eauto. }
      { (* <- *)
         assert (exists res : fun_tag * seq var * exp, find_def x fds = Some res).
           apply HfenvWf; eauto.
         apply notNone_Some in H3.
         eapply find_def_in_collect_function_vars in H3.
         apply variable_mapping_NotIn_None; auto.
         rewrite catA in HnodupE. intro Hcontra.
         eapply NoDup_app_In in HnodupE; eauto. }
    }

    assert (Hnodup': NoDup (collect_local_variables e ++
                            collect_function_vars (Efun fds e))). {
      apply Hfds with (errMsg:=""%bs) in H9. destruct H9 as [_ [_ [HnodupE _]]].
      apply NoDup_app_remove_l in HnodupE.
      assumption. }

    assert (HfenvRho': forall (a : positive) (v : cps.val),
      rho'' ! a = Some v ->
      find_def a fds <> None -> v = Vfun (M.empty _) fds a). {
      intros.
      assert (HaXs: ~ In a xs). {
        eapply Hfds in H9. destruct H9 as [_ [_ [HnodupE _]]].
        apply NoDup_app_remove_middle in HnodupE.
        intro Hcontra. eapply find_def_in_collect_function_vars in H3.
        eapply NoDup_app_In in HnodupE; eauto. }

    have H' := set_lists_not_In _ _ _ _ _ H2 HaXs.
    rewrite <- H' in H1.
    eapply def_funs_find_def in H3. now erewrite H' in H3. }

    remember (LH_rec [] 0 [] (LH_base [] []) []) as lh_IH.

    subst lenv_before_IH.
    have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny lh_IH _ HlenvInjective' HenvsDisjoint'
                   state _ _ _ Hfds_before_IH HlocInBound_before_IH Hinv_before_IH Hexpr HrelE'.

    destruct IH as [sr_final [fr_final [k' [lh' [Hred [Hval [Hfinst [Hfuncs [HvalPres H_INV]]]]]]]]].
    clear IHHev.
    subst lh_IH. cbn in Hred. rewrite cats0 in Hred.

    (* start execution *)
    do 4! eexists. split.
    eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.

    eapply rt_trans. apply app_trans. apply HfargsRed.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    separate_instr. apply app_trans. apply HredF.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    dostep'. apply r_return_call_indirect_success. eapply r_call_indirect_success; eauto.
    { (* table identity map *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htableid _]]]]]]]]]]]].
      inv H6. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id.
      - rewrite N2Z.id. eapply Htableid. eassumption.
      - unfold lookup_N in H13. apply Some_notNone in H13. apply nth_error_Some in H13.
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [[HfnsBound _] _]]]]]]]]]].
        unfold max_num_functions, num_custom_funs in HfnsBound. simpl_modulus. cbn. lia. }
    { (* type *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htype _]]]]]]]]]]]]].
      assert (Hlen: length xs = length ys). {
        apply set_lists_length_eq in H2.
        apply get_list_length_eq in H0. rewrite H2 H0. reflexivity. }
      rewrite Htype. 2: { inv HeRestr. lia. } rewrite -Hlen. cbn. now rewrite Nat2N.id. } apply rt_refl. apply rt_refl.

    dostep'. eapply r_return_invoke with (a:=fidx); try eassumption; try reflexivity.
    apply map_const_const_list.
    rewrite map_length repeat_length.
    apply const_val_list_length_eq in HfargsRes.
    apply set_lists_length_eq in H2. rewrite H2. symmetry. assumption.

    dostep'.
    eapply r_invoke_native with (vs:= map (fun a => VAL_num (N_to_value a)) args); try eassumption; try reflexivity.
    - unfold v_to_e_list. by rewrite -map_map_seq.
    - rewrite repeat_length map_length. apply const_val_list_length_eq in HfargsRes.
      apply set_lists_length_eq in H2. rewrite H2. assumption.
    - by apply default_vals_i32_Some.
    (* apply IH *)
    subst f_before_IH. apply Hred.

    subst f_before_IH. cbn in Hfinst.
    repeat (split; auto).
    }
  - (* Eletapp *)
    (* needs 2 IH, first one for the function body (mostly copy paste from Eapp, could be refactored),
                   second one for the continuation, similar to the other cases *)
    { inv Hrepr_e. rename args' into args_instr. rename e into e_cont, x into x_res.
      assert (Htemp: fl = fds /\ rho' = M.empty _). { destruct HrelE as [Hfun1 _]. eapply Hfun1 in H. now destruct H. apply rt_refl. } destruct Htemp. subst fl rho'.
      (* treat direct + indirect calls in one *)
      assert (Hval: exists fidx,
        reduce_trans (state, sr, fr, [AI_basic instr])
                     (state, sr, fr, [AI_basic (BI_const_num (N_to_value fidx))])
     /\ @repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f') sr (f_inst fr) (Val_funidx fidx)
     /\ exists e_body', @repr_expr_LambdaANF_Wasm penv (create_local_variable_mapping (xs ++ collect_local_variables e_body)%list) e_body e_body'). {
      inv H12.
      { (* indirect call *)
        assert (Hocc: occurs_free (Eletapp x_res f t ys e_cont) f). { constructor. by left. }
        have Hrel := HrelE. destruct Hrel as [_ Hlocals].
        assert (HfNone: find_def f fds = None). {
          apply HfenvWf_None with (f:=f) in HfenvWf. rewrite HfenvWf.
          inv H3. unfold translate_var in H4. destruct (lenv ! f) eqn:Hf';rewrite Hf' in H4=>//.
          injection H4 as ->.
          now apply HenvsDisjoint in Hf'. }
        apply Hlocals in Hocc; auto. destruct Hocc as [val [wal [Hrho [[j [Htrans Hwal]] Hval]]]].
        inv H3. rewrite Htrans in H4. inv H4.
        rewrite H in Hrho. inv Hrho. inv Hval.
        rewrite H1 in H6. symmetry in H6. inv H6.
        rename i into locIdx.
        exists idx. split.
        dostep'. apply r_local_get. eassumption. apply rt_refl. split.
        econstructor; eauto. eauto. }
      { (* direct call *)
        inv H3. unfold translate_var in H4. destruct (fenv ! f) eqn:Hf; rewrite Hf in H4=>//.
        injection H4 as ->.
        assert (Hf': exists i, fenv ! f = Some i) by eauto.
        apply HfenvWf in Hf'.
        assert (Htemp: f' = f). { apply HfenvRho in H. now inv H. now destruct Hf'. } inv Htemp.
        destruct HrelE as [Hfun1 [Hfun2 _]].
        assert (Hsubval: subval_or_eq (Vfun (M.empty cps.val) fds f)
                                      (Vfun (M.empty cps.val) fds f)) by constructor.
        have H' := Hfun1 _ _ _ _ _ H Hsubval. destruct H' as [_ [_ H']].
        apply Hfun2 with (errMsg:=errMsg) in H'.
        destruct H' as [idx [HtransF Hval]].
        assert (idx = i). { unfold translate_var in HtransF. now rewrite Hf in HtransF. }
        subst idx. exists i. split. apply rt_refl.
        split. assumption. inv Hval. rewrite H7 in H1. inv H1. eauto.
      }
    }

    destruct Hval as [fidx [HredF [Hval [e_body' HexprBody]]]]. inv Hval.
    rewrite H7 in H1. inv H1. rename H16 into Hexpr.

    repeat rewrite map_cat. cbn.
    have HrelE' := rel_env_app_letapp _ _ _ _ _ _ _ _ _ HrelE.
    have Hfargs := fun_args_reduce state _ _ _ _ _ _ _ _ _ Hinv H0 HenvsDisjoint HfenvWf HfenvRho HrelE' H11.
    destruct Hfargs as [args [HfargsRed HfargsRes]].

    remember {| f_locs := [seq (VAL_num (N_to_value a)) | a <- args] ++
                     (repeat (VAL_num (N_to_value 0)) (Datatypes.length (collect_local_variables e_body)));
               f_inst := f_inst fr |} as f_before_IH.

    (* prepare IH1 for e_body *)
    remember (create_local_variable_mapping (xs ++ collect_local_variables e_body)) as lenv_before_IH.

    assert (Hfds_before_IH: (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) errMsg,
      find_def a fds = Some (t, ys, e) ->
        expression_restricted cenv e /\
        (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++
           collect_local_variables e ++
           collect_function_vars (Efun fds e)) /\
        (exists fidx : funcidx,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Wasm (Vfun (M.empty cps.val) fds a) sr (f_inst f_before_IH) (Val_funidx fidx)))). {
         intros ? ? ? ? ? Hfd. eapply Hfds with (errMsg:=errMsg) in Hfd.
         destruct Hfd as [? [? [? [idx [HtransF Hval]]]]].
         repeat (split; try assumption).
         exists idx. split. assumption.
         eapply val_relation_func_depends_on_funcs.
         2: subst f_before_IH; apply Hval.
         congruence.
    }

    assert (HlocInBound_before_IH: (forall (var : positive) (varIdx : localidx),
          @repr_var nenv (create_local_variable_mapping (xs ++ collect_local_variables e_body)) var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs f_before_IH))). {
      intros ?? Hvar. subst f_before_IH. cbn. inv Hvar. apply var_mapping_list_lt_length in H1.
      rewrite app_length in H1. apply const_val_list_length_eq in HfargsRes.
      rewrite app_length. rewrite map_length -HfargsRes.
      rewrite map_repeat_eq. rewrite map_length. apply set_lists_length_eq in H2.
      now rewrite -H2.
    }

    assert (Hinv_before_IH : INV sr f_before_IH). {
       subst. now eapply init_locals_preserves_INV. }

    assert (HrelE_before_IH: @rel_env_LambdaANF_Wasm lenv_before_IH e_body rho'' sr f_before_IH fds). {
      unfold rel_env_LambdaANF_Wasm. split.
      { (* funs1 *) intros.
        assert (Hdec: decidable_eq var). {
          intros n m. unfold Decidable.decidable. now destruct (var_dec n m). }
       have H' := In_decidable Hdec x xs. clear Hdec. destruct H'.
       { (* In x xs *)
         have H' := set_lists_In _ _ _ _ _ _ H4 H1 H2.
         destruct (get_list_In_val _ _ _ _ H0 H') as [y [Hiny HyRho]].
         destruct HrelE as [Hfun1 [Hfun2 _]]. eauto. }
       { (* ~In x xs *)
         have H' := set_lists_not_In _ _ _ _ _ H2 H4. rewrite H1 in H'.
         erewrite def_funs_find_def in H'.
         2:{ intro Hcontra. apply def_funs_not_find_def with (fds':=fds) (rho:=M.empty _) in Hcontra.
             rewrite Hcontra in H'. inv H'. } inv H'.
         have H' := set_lists_not_In _ _ _ _ _ H2 H4.
         rewrite H1 in H'.
         apply def_funs_spec in H'. destruct H' as [[? ?] | [? Hcontra]]. 2: inv Hcontra.
         apply subval_fun in H3. 2: assumption.
         destruct H3 as [f1 [?H ?H]]. inv H3. inv H8 => //. }
      } split.
      { (* funs2 *)
        intros ? ? Hnfd. destruct HrelE as [_ [Hfun2 _]].
        apply Hfun2 with (errMsg:=errMsg) in Hnfd.
        destruct Hnfd as [i [Htrans Hval]].
        exists i. split. assumption. subst f_before_IH. assumption. }
      { (* vars *)
        intros. destruct HrelE as [_ HrelVars].
        assert (In x xs). {
          apply Hfds with (errMsg:=""%bs) in H7; auto. destruct H7 as [? [Hxxs ?]].
          have H' := Hxxs _ H1. now destruct H'. }
        have H' := get_set_lists_In_xs _ _ _ _ _ H4 H2. destruct H' as [v'' Hv'].
        have H' := set_lists_nth_error _ _ _ _ _ _ H2 H4 Hv'.
        destruct H' as [k' [Hvk' Hxk']].
        have H'' := const_val_list_nth_error _ _ _ _ _ _ HfargsRes Hvk'.
        destruct H'' as [w [Hw Hnth]].
        exists v'', w. split; auto. split; auto.

        unfold stored_in_locals. subst lenv_before_IH f_before_IH. exists (N.of_nat k').
        split. {
          intros. unfold create_local_variable_mapping.
          rewrite (var_mapping_list_lt_length_nth_error_idx _ (N.of_nat k')); auto.
          apply Hfds with (errMsg:=""%bs) in H7. destruct H7 as [_ [_ [HnodupE _]]].
          rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE. assumption.
          unfold lookup_N. rewrite Nat2N.id.
          rewrite nth_error_app1; auto. apply nth_error_Some. intro.
          rewrite H5 in Hxk'. inv Hxk'. }
        cbn.
        unfold lookup_N. rewrite Nat2N.id.
        rewrite nth_error_app1. 2: {
          rewrite length_is_size size_map -length_is_size.
          apply const_val_list_length_eq in HfargsRes.
          rewrite -HfargsRes.
          apply nth_error_Some. congruence. } assumption.
        subst f_before_IH. assumption. }
    }

    assert (HeRestr' : expression_restricted cenv e_body). {
        apply Hfds with (errMsg:=""%bs) in H7. now destruct H7. }

    assert (Hunbound': (forall x : var, In x (collect_local_variables e_body) -> rho'' ! x = None)). {
      intros.
      assert (~ exists v, find_def x fds = Some v). {
        intro Hcontra. destruct Hcontra as [? Hfd].
        assert (Hfd': find_def x fds <> None) by congruence.
        clear Hfd. rename Hfd' into Hfd.
        eapply find_def_in_collect_function_vars in Hfd.
        apply Hfds with (errMsg:=""%bs) in H7. destruct H7 as [_ [_ [HnodupE _]]].
        apply NoDup_app_remove_l in HnodupE.
        eapply NoDup_app_In in HnodupE; eauto. }
      assert (Hfd: find_def x fds = None). { destruct (find_def x fds); eauto. exfalso. eauto. }
      apply def_funs_not_find_def with (fds':=fds) (rho:=M.empty _) in Hfd.
      assert (HxIn: ~ In x xs). {
        intro Hcontra. apply Hfds with (errMsg:=""%bs) in H7. destruct H7 as [_ [_ [HnodupE _]]].
        rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE.
        eapply NoDup_app_In in HnodupE; eauto. }
      have H'' := set_lists_not_In _ _ _ _ _ H2 HxIn. rewrite <- H''.
      now rewrite Hfd.
    }

    assert (HlenvInjective': map_injective lenv_before_IH). {
      subst lenv_before_IH.
      apply create_local_variable_mapping_injective. {
      apply Hfds with (errMsg:=""%bs) in H7. destruct H7 as [_ [_ [HnodupE _]]].
      rewrite catA in HnodupE. now apply NoDup_app_remove_r in HnodupE.
    }}

    assert (HenvsDisjoint': domains_disjoint lenv_before_IH fenv). {
      apply Hfds with (errMsg:=""%bs) in H7. destruct H7 as [_ [_ [HnodupE _]]].
      subst lenv_before_IH. unfold domains_disjoint. split; intros.
      { (* -> *)
        apply variable_mapping_Some_In in H1; auto.
        assert (~ exists v, fenv ! x = Some v). {
          intro Hcontra. apply HfenvWf in Hcontra.
          apply notNone_Some in Hcontra.
          eapply find_def_in_collect_function_vars in Hcontra.
          rewrite catA in HnodupE. eapply NoDup_app_In in HnodupE; eauto. }
          destruct (fenv ! x) eqn:Hx; auto. exfalso. eauto. }
      { (* <- *)
         assert (exists res : fun_tag * seq var * exp, find_def x fds = Some res).
           apply HfenvWf; eauto.
         apply notNone_Some in H3.
         eapply find_def_in_collect_function_vars in H3.
         apply variable_mapping_NotIn_None; auto.
         rewrite catA in HnodupE. intro Hcontra.
         eapply NoDup_app_In in HnodupE; eauto. }
    }

    assert (Hnodup': NoDup (collect_local_variables e_body ++
                            collect_function_vars (Efun fds e_body))). {
      apply Hfds with (errMsg:=""%bs) in H7. destruct H7 as [_ [_ [HnodupE _]]].
      apply NoDup_app_remove_l in HnodupE.
      assumption. }

    assert (HfenvRho': forall (a : positive) (v : cps.val),
      rho'' ! a = Some v ->
      find_def a fds <> None -> v = Vfun (M.empty _) fds a). {
      intros.
      assert (HaXs: ~ In a xs). {
        eapply Hfds in H7. destruct H7 as [_ [_ [HnodupE _]]].
        apply NoDup_app_remove_middle in HnodupE.
        intro Hcontra. eapply find_def_in_collect_function_vars in H3.
        eapply NoDup_app_In in HnodupE; eauto. }

    have H' := set_lists_not_In _ _ _ _ _ H2 HaXs.
    rewrite <- H' in H1.
    eapply def_funs_find_def in H3. now erewrite H' in H3. }

    remember (LH_rec [] 0 [] (LH_base [] []) []) as lh_before_IH.

    subst lenv_before_IH.
    have IH_body := IHHev1 Hnodup' HfenvRho' HeRestr' Hunbound' _ fr lh_before_IH _ HlenvInjective' HenvsDisjoint'
                   state _ _ _ Hfds_before_IH HlocInBound_before_IH Hinv_before_IH Hexpr HrelE_before_IH.

    destruct IH_body as [sr_after_call [fr_after_call [k0 [lh0 [Hred [Hval [Hfinst [Hfuncs [HvalPres H_INV]]]]]]]]].
    clear HfenvRho' Hnodup' Hunbound' HeRestr' IHHev1.
    subst lh_before_IH. cbn in Hred. rewrite cats0 in Hred.

    assert (Hcont: exists (sr_final : store_record) (fr_final : frame) k' (lh' : lholed k'),
      reduce_trans (state, sr_after_call, fAny, [AI_frame 0 fr (lfill lh ([ AI_basic (BI_global_get result_out_of_mem)
                                                                         ; AI_basic (BI_if (BT_valtype None) [:: BI_return ] [::])
                                                                         ; AI_basic (BI_global_get result_var)
                                                                         ; AI_basic (BI_local_set x') ] ++ (map AI_basic e')))])
                   (state, sr_final, fAny, [AI_frame 0 fr_final (lfill lh' [:: AI_basic BI_return])])
         /\ result_val_LambdaANF_Wasm v' sr_final (f_inst fr_final)
         /\ f_inst fr_final = f_inst fr
         /\ s_funcs sr_final = s_funcs sr
            (* previous values are preserved *)
         /\ (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst fr) wal ->
                             repr_val_LambdaANF_Wasm val sr_final (f_inst fr) wal)
         /\ (INV_result_var_out_of_mem_is_zero sr_final fr_final -> INV sr_final fr_final)). {
      destruct Hval as [Hsuccess | HOutOfMem].
      { (* success *)
        clear Hexpr. rename H10 into Hexpr.
        destruct Hsuccess as [w [wal [Hres [Heq [Hval HresM]]]]].
        remember ({|f_locs := set_nth (VAL_num (VAL_int32 w)) (f_locs fr) (N.to_nat x') (VAL_num (VAL_int32 (wasm_value_to_i32 wal)));
                    f_inst := f_inst fr|}) as f_before_cont.

        (* prepare IH for continuation *)
        assert (Hnodup': NoDup (collect_local_variables e_cont ++
                                collect_function_vars (Efun fds e_cont))). {
          cbn in Hnodup. now inv Hnodup.
        }

        assert (HfenvRho': forall (a : positive) (v0 : val),
          (map_util.M.set x_res v rho) ! a = Some v0 ->
          find_def a fds <> None -> v0 = Vfun (M.empty val) fds a). {
          intros. apply HfenvRho; auto.
          rewrite M.gso in H1; auto. intro Hcontra. subst a.
          apply notNone_Some in H3. apply HfenvWf in H3. destruct H3.
          destruct HenvsDisjoint as [Hd1 Hd2].
          apply Hd2 in H1. inv H9. unfold translate_var in H3. now rewrite H1 in H3.
        }

        assert (HeRestr': expression_restricted cenv e_cont). { now inv HeRestr. }

        assert (Hunbound': (forall x : var, In x (collect_local_variables e_cont) ->
                               (map_util.M.set x_res v rho) ! x = None)). {
          intros.
          assert (~ In x_res (collect_local_variables e_cont)). {
            apply NoDup_app_remove_r in Hnodup. cbn in Hnodup.
            now apply NoDup_cons_iff in Hnodup. }
          rewrite M.gso; auto.
          apply Hunbound. now right. now intro.
        }

        assert (HlocInBound_before_cont_IH: (forall (var : positive) (varIdx : localidx),
          @repr_var nenv lenv var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs f_before_cont))). {
           intros ?? Hvar. subst f_before_cont. cbn.
          rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
          apply HlocInBound in Hvar. lia. }

        assert (Hinv_before_cont_IH: INV sr_after_call f_before_cont). {
          subst f_before_cont f_before_IH; cbn in Hfinst.
          eapply update_local_preserves_INV. 3: subst w; reflexivity.
          eapply change_locals_preserves_INV with (l := f_locs fr).
          apply H_INV. rewrite Hfinst in HresM. apply HresM.
          have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [Hlocs32 _]]]]]]]]]. assumption.
          rewrite -Hfinst. now destruct fr.
          eapply HlocInBound. eassumption. }

        assert (Hfds_before_cont_IH: (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) errMsg,
          find_def a fds = Some (t, ys, e) ->
            expression_restricted cenv e /\
            (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
            NoDup
              (ys ++
               collect_local_variables e ++
               collect_function_vars (Efun fds e)) /\
            (exists fidx : funcidx,
               translate_var nenv fenv a errMsg = Ret fidx /\
               repr_val_LambdaANF_Wasm (Vfun (M.empty cps.val) fds a)
                 sr_after_call (f_inst f_before_cont) (Val_funidx fidx)))). {
          intros ? ? ? ? ? Hfd. eapply Hfds with (errMsg:=errMsg) in Hfd.
          destruct Hfd as [? [? [? [idx [HtransF' Hval']]]]].
          repeat (split; try assumption).
          exists idx. split. assumption.
          eapply val_relation_func_depends_on_funcs.
          2: subst f_before_cont; apply Hval'. now subst. }

        assert (HrelE_before_cont_IH: @rel_env_LambdaANF_Wasm lenv e_cont (map_util.M.set x_res v rho) sr_after_call f_before_cont fds). {
          unfold rel_env_LambdaANF_Wasm. split; intros.
          { (* funs1 *)
            destruct (var_dec x x_res).
            { (* x = x_res *)
              subst x_res. rewrite M.gss in H1. inv H1. rename v0 into v.
              destruct HrelE as [Hfun1 [Hfun2 _]].
              assert (Hsubval: subval_or_eq (Vfun (M.empty val) fds f0)
                                            (Vfun (M.empty val) fds f0)).
              { apply rt_refl. }
              have H''1 := Hfun1 _ _ _ _ _ _ Hsubval.
              have H' := step_preserves_empty_env_fds _ _ _ _ _ _ fds' _ _ _ _ HprimFunsRet Hev1 H3.
              edestruct H'.
              { intros ? ? ? ? ? Hrho Hsubval'.
                assert (Hdec: decidable_eq var). { intros n m.
                unfold Decidable.decidable. now destruct (var_dec n m). }
                have H'' := In_decidable Hdec x0 xs. destruct H''.
                { (* In x0 xs *)
                  have H'' := set_lists_In _ _ _ _ _ _ H1 Hrho H2.
                  destruct (get_list_In_val _ _ _ _ H0 H'') as [y [HyIn HyRho]].
                  have H12' := Hfun1 _ _ _ _ _ HyRho Hsubval'.
                  now destruct H12' as [?[??]].
                }
                { (* ~In x0 xs *)
                  have H'' := set_lists_not_In _ _ _ _ _ H2 H1.
                  rewrite Hrho in H''.
                  erewrite def_funs_find_def in H''. 2: {
                    intro Hcontra. eapply def_funs_not_find_def  in Hcontra.
                    erewrite Hcontra in H''. inv H''. }
                  inv H''.
                  have H'' := set_lists_not_In _ _ _ _ _ H2 H1.
                  rewrite Hrho in H''.
                  apply subval_fun in Hsubval'.
                  destruct Hsubval' as [ff [Heq Hfundef]]. now inv Heq.
                  apply def_funs_spec in H''. destruct H'' as [[tuple Hfd] | Hcontra].
                  assumption. now destruct Hcontra.
                }
              }
              {
                intros ? ? ? ? [HbodyNofun | HfdsNofun].
              - eapply repr_expr_LambdaANF_Wasm_no_Efun_subterm; eauto.
              - destruct HfdsNofun as [Hsub HsubFds].
                eapply dsubterm_fds_e_find_def in HsubFds.
                2:{ now apply NoDup_app_remove_l in Hnodup. }
                destruct HsubFds as [? [? [? Hfd]]].
                have Hfd' := Hfd.
                eapply Hfds in Hfd. destruct Hfd as [_ [_ [_ [? [? HvalFun]]]]]. inv HvalFun.
                assert (e = e'') by congruence. subst e''.
                eapply repr_expr_LambdaANF_Wasm_no_Efun_subterm; eauto. }
              { now destruct H4. }
           }
           { (* x <> x_res*)
             rewrite M.gso in H1; auto.
             destruct HrelE' as [Hfun1 [Hfun2 Hvar]].
             have H' := Hfun1 _ _ _ _ _ H1 H3. assumption.
           }
         } split.
         { (* funs2 *)
            intros ? ? Hnfd. destruct HrelE as [_ [Hfun2 _]].
            apply Hfun2 with (errMsg:=errMsg) in Hnfd.
            destruct Hnfd as [i [Htrans' Hval']].
            exists i. split. assumption.
            eapply val_relation_func_depends_on_funcs with (s:=sr). congruence.
            subst f_before_cont. assumption.
          }
          { (* local vars *)
            intros. destruct (var_dec x x_res).
            { (* x = x_res *)
              subst x_res.
              exists v. exists wal. split.
              now rewrite M.gss.
              split. exists x'. split. inv H9. intro.
              unfold translate_var in H4. unfold translate_var.
              destruct (lenv ! x) eqn:Hx; rewrite Hx in H4=>//. injection H4 as ->.
              by rewrite Hx=>//.
              have Hl := HlocInBound _ _ H9. apply nth_error_Some in Hl.
              apply notNone_Some in Hl. destruct Hl. subst f_before_cont.
              eapply set_nth_nth_error_same. eassumption.
              subst f_before_cont f_before_IH. assumption. }
            { (* x <> x_res *)
              assert (Hocc: occurs_free (Eletapp x_res f t ys e_cont) x).
              { now apply Free_Eletapp2. }
              destruct HrelE as [_ [_ Hvar]].

              apply Hvar in Hocc; auto. destruct Hocc as [v6 [wal' [Henv' [Hloc' Hval']]]].
              exists v6. exists wal'. repeat split; auto.
              rewrite M.gso. assumption. auto.
              destruct Hloc' as [x1' [? ?]].
              unfold stored_in_locals. cbn.

              assert (x1' <> x'). {
                intro. subst x1'. inv H9.
                unfold translate_var in H8.
                destruct (lenv ! x_res) eqn:Heqn; rewrite Heqn in H8=>//. injection H8 as ->.
                specialize H4 with err_str. unfold translate_var in H4.
                destruct (lenv ! x) eqn:Heqn'; rewrite Heqn' in H4=>//. injection H4 as ->.
                have Hcontra := HlenvInjective _ _ _ _ _ Heqn Heqn'.
                now apply Hcontra. }
              exists x1'. split; auto. subst f_before_cont. cbn.
              unfold lookup_N.
              rewrite set_nth_nth_error_other; eauto.
              have Hl := HlocInBound _ _ H9. now intro.
              subst f_before_cont f_before_IH. rewrite -Hfinst in HvalPres.
              apply HvalPres. assumption.
            }
          }
        }

        have IH_cont := IHHev2 Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny lh lenv HlenvInjective HenvsDisjoint
                   state _ _ _ Hfds_before_cont_IH HlocInBound_before_cont_IH Hinv_before_cont_IH Hexpr HrelE_before_cont_IH.
        destruct IH_cont as [sr_final [fr_final [k_final [lh_final [Hred' [Hval' [Hfinst' [Hfuncs' [HvalPres' H_INV']]]]]]]]]. clear IHHev2.

        exists sr_final, fr_final, k_final, lh_final. split.

        eapply rt_trans. apply reduce_trans_frame'.
        apply reduce_trans_label'. apply app_trans.
        dostep_nary 0. apply r_global_get. subst f_before_IH. eassumption.
        dostep_nary 1. constructor. apply rs_if_false. reflexivity.
        dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto. cbn.
        dostep_nary 0. constructor. apply rs_label_const =>//.
        dostep_nary 0. apply r_global_get. subst f_before_IH. eassumption.
        dostep_nary' 1. eapply r_local_set with (v:= VAL_num (VAL_int32 w)) (f' := f_before_cont).
        subst f_before_cont. reflexivity.
        apply /ssrnat.leP. eapply HlocInBound. eassumption.
        subst f_before_cont w. reflexivity. apply rt_refl.
        (* IH *)
        cbn. apply Hred'.

        subst f_before_cont f_before_IH. rewrite -Hfinst'.
        repeat (split; auto).
        congruence.
        intros. { rewrite -Hfinst' in HvalPres'. apply HvalPres'.
                  cbn. rewrite -Hfinst in HvalPres. apply HvalPres. assumption. }
      }
      { (* out of mem *)

       (* split of dead instructions after
         (BI_if (BT_valtype None) [:: BI_return] [::]) *)
        separate_instr.
        match goal with
        |- context C [reduce_trans (_, _, _, [:: AI_frame _ _ (lfill _
           (_ ++ [:: AI_basic (BI_if (BT_valtype None) [:: BI_return] [::])] ++ ?es))])] =>
            let es_tail := fresh "es_tail" in
            remember es as es_tail
        end.

        have Hlh := lholed_nested_label _ lh [AI_basic BI_return] es_tail. subst es_tail.
        destruct Hlh as [k' [lh' Heq']]. cbn in Heq'.

        exists sr_after_call, fr. eexists. exists lh'. split.

        eapply rt_trans.
        apply reduce_trans_frame'. apply reduce_trans_label'.
        dostep_nary 0. apply r_global_get. subst f_before_IH. eassumption.
        dostep_nary 1. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
        dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
        apply rt_refl. rewrite Heq'. apply rt_refl.

        split. right. subst f_before_IH. assumption.
        split. reflexivity. split. congruence. split.
        { intros. subst f_before_IH. cbn in Hfinst.
          rewrite -Hfinst in HvalPres. apply HvalPres.
          assumption. }
        intro Hcontra. unfold INV_result_var_out_of_mem_is_zero in Hcontra.
        subst f_before_IH. cbn in Hfinst.
        rewrite HOutOfMem in Hcontra. inv Hcontra.
      }
    }
    destruct Hcont as [sr_final [fr_final [k_final [lh_final [Hred_final [Hval_final [Hfinst' [Hfuncs' [HvalPres' H_INV']]]]]]]]].

    (* start execution *)
    do 4! eexists. split.
    eapply rt_trans. eapply reduce_trans_frame'. apply reduce_trans_label'.
    eapply rt_trans. apply app_trans. apply HfargsRed.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    separate_instr. apply app_trans. apply HredF.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    apply app_trans with (es :=
             [:: AI_basic (BI_const_num (N_to_value fidx));
                 AI_basic (BI_call_indirect 0%N (N.of_nat (Datatypes.length ys)))]).
    dostep'. eapply r_call_indirect_success; eauto.
    { (* table identity map *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htableid _]]]]]]]]]]]].
      inv H6. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id.
      - rewrite N2Z.id. eapply Htableid. eassumption.
      - unfold lookup_N in H15. apply Some_notNone in H15. apply nth_error_Some in H15.
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [[HfnsBound _] _]]]]]]]]]].
        unfold max_num_functions, num_custom_funs in HfnsBound. simpl_modulus. cbn. lia. }
    { (* type *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htype _]]]]]]]]]]]]].
      assert (Hlen: length xs = length ys). {
        apply set_lists_length_eq in H2.
        apply get_list_length_eq in H0. rewrite H2 H0. reflexivity. }
      rewrite Htype. 2: { inv HeRestr. lia. } rewrite -Hlen. cbn. now rewrite Nat2N.id. } apply rt_refl.
    rewrite catA. cbn. eapply rt_trans.
    eapply app_trans with (es := ([seq AI_basic (BI_const_num (N_to_value a)) | a <- args] ++ [:: AI_invoke fidx])).
    (* enter function *)
    dostep'. eapply r_invoke_native with (vs:= map (fun a => (VAL_num (N_to_value a))) args); try eassumption.
    reflexivity. reflexivity.
    unfold v_to_e_list. now rewrite -map_map_seq.
    reflexivity. reflexivity.
    { rewrite repeat_length map_length.
    apply const_val_list_length_eq in HfargsRes.
    apply set_lists_length_eq in H2. rewrite H2. assumption. }
    reflexivity. cbn. apply default_vals_i32_Some.
    (* apply IH1: function body *)
    subst f_before_IH. apply Hred. apply rt_refl.
    eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
    dostep_nary 0. constructor. apply rs_return with (lh:=lh0) (vs:=[::]) => //.
    cbn. apply rt_refl.
    (* apply IH2: continuation *)
    eapply rt_trans. apply Hred_final. apply rt_refl.
    rewrite Hfinst' in Hval_final.
    rewrite Hfinst'.
    by repeat (split; auto).
    }
  - (* Efun *)
    inv Hrepr_e. (* absurd, fn defs only on topmost level *)
  - (* Eprim_val *)
    { inv Hrepr_e.
      (* TODO cleanup copy paste *)
      (* prepare calling memory_grow_reduce *)
      have I := Hinv. destruct I as [_[_[_[_[_[_[_[_[_[HfnsBound[_[_[_[_ [HfuncGrow HfuncsId]]]]]]]]]]]]]]].
      remember (Build_frame [VAL_num (N_to_value page_size)] (f_inst fr)) as fM.
      assert (HinvM: INV sr fM). {
        subst fM. eapply change_locals_preserves_INV. eassumption.
        intros i ? Hl. destruct i; last by destruct i.
        inv Hl. now eexists. reflexivity.
      }
      assert (Hloc0: nth_error (f_locs fM) 0 = Some (VAL_num (N_to_value page_size))) by (subst fM; reflexivity).
      have Hgrowmem := memory_grow_reduce state sr _ Hloc0 HinvM.
      destruct Hgrowmem as [gmp' [s' [Hred [Hsfuncs [HvalPreserved [[HinvFm' Henoughmem] | HoutofM]]]]]].

      { (* Successfully grow memory if necessary *)
        (* invariants after reducing grow *)
        have I := HinvFm'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
        destruct Hlinmem as [Hmem1 [m [Hmem2 [size [<- [Hmem4 Hmem5]]]]]].
        have HenoughM := Henoughmem _ Hmem2. destruct HenoughM as [Hgmp HenoughM]. clear Henoughmem.
        assert (Hinv': INV s' fr). {
          destruct fr.
          eapply change_locals_preserves_INV with (f:=fM). eassumption. apply Hinv.
          subst fM. reflexivity.
        } clear HinvFm'.
        assert ((Z.of_N gmp' < Wasm_int.Int32.modulus)%Z). {
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5. simpl_modulus. cbn. lia. }

        (* There exists memory containing the new value *)
        assert (exists mem, store m (Wasm_int.N_of_uint i32m (N_to_i32 gmp')) 0%N
                              (bits (VAL_int64 v0))
                              8 = Some mem) as Htest.
        { apply enough_space_to_store. cbn.
          assert ((Datatypes.length (serialise_i64 v0)) = 8) as Hl.
          { unfold serialise_i64, encode_int, bytes_of_int, rev_if_be.
            destruct (Archi.big_endian); reflexivity. } rewrite Hl. clear Hl. cbn.
          rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
          unfold page_size in HenoughM. lia. }
        destruct Htest as [m_after_store Hm_after_store].

        remember (upd_s_mem s' (set_nth m_after_store s'.(s_mems) 0 m_after_store)) as s_prim.
        assert (HmStore: smem_store s' (f_inst fr) (Wasm_int.N_of_uint i32m (N_to_i32 gmp'))
                         0%N (VAL_int64 v0) T_i64 = Some s_prim).
        { subst s_prim.
          unfold smem_store. subst fM. rewrite Hmem1. cbn.
          unfold smem in Hmem2. rewrite Hmem1 in Hmem2. destruct (s_mems s')=>//.
          injection Hmem2 as ->. now rewrite Hm_after_store. }

        assert (HgmpPreserved: sglob_val s_prim (f_inst fr) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 gmp')))). {
          subst s_prim.
          unfold upd_s_mem, sglob_val, sglob. cbn.
          unfold sglob_val, sglob in Hgmp. subst fM. cbn in Hgmp.
          destruct (inst_globals (f_inst fr)); first by inv Hgmp.
          assumption.
        }

        assert (Hgmp_v_mult_two: exists n, (gmp' = 2 * n)%N). {
          destruct Hinv' as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hgmp_mult_two]]]]]]]]]]]]].
          eapply Hgmp_mult_two; subst fM; try eassumption; try lia.
        }

        assert (HmemLengthPreserved: mem_length m = mem_length m_after_store). {
          apply mem_store_preserves_length in Hm_after_store. congruence. }

        assert (HmemPreserved: smem s_prim (f_inst fr) = Some m_after_store). {
          subst s_prim. cbn.
          unfold smem. subst fM. rewrite Hmem1. cbn. by destruct (s_mems s').
        }

        assert (Hinv_prim : INV s_prim fr). {
          subst.
          assert (mem_length m = mem_length m_after_store). {
            apply mem_store_preserves_length in Hm_after_store. congruence. }
          assert (mem_max_opt m = mem_max_opt m_after_store). {
            apply mem_store_preserves_max_pages in Hm_after_store. congruence. }
          eapply update_mem_preserves_INV. apply Hinv'. eassumption. erewrite <- H0. lia.
          congruence. exists (mem_size m); split; auto. unfold mem_size. congruence.  reflexivity. }

        remember ({|f_locs := set_nth (VAL_num (VAL_int32 (N_to_i32 gmp'))) (f_locs fr) (N.to_nat x') (VAL_num (VAL_int32 (N_to_i32 gmp')));
                    f_inst := f_inst fr|}) as f_before_IH.


        have I := Hinv_prim. destruct I as [_ [_ [_ [Hgmp_w _]]]].

        (* New store with gmp incremented by 8 *)
        destruct (Hgmp_w (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp') (N_to_i32 8)))) as [s_before_IH Hs_before_IH].
        edestruct i32_exists_N as [gmp [HgmpEq HgmpBound]].
        erewrite HgmpEq in Hs_before_IH.
        assert (gmp = gmp' + 8)%N. {
          inversion HgmpEq.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H1; try lia.
          unfold store in Hm_after_store.
          destruct ((Wasm_int.N_of_uint i32m (N_to_i32 gmp') + 0 + N.of_nat 8
                     <=? mem_length m)%N) eqn:Har. 2: by now inv Har.
          apply N.leb_le in Har. cbn in Har.
          rewrite Wasm_int.Int32.Z_mod_modulus_id in Har; try lia.
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
          simpl_modulus. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        subst gmp.

        assert (Hinv_before_IH : INV s_before_IH f_before_IH). {
          assert (INV s_prim f_before_IH). { eapply update_local_preserves_INV; eauto. }
          eapply update_global_preserves_INV with (i:=global_mem_ptr) (num:=(VAL_int32 (N_to_i32 (gmp' + 8)))); eauto.
          left. split. apply gmp_i32_glob. now cbn. 
          discriminate.
          now subst f_before_IH.
          { move => _.
            intros n [Heqn Hboundn].
            assert ((8 + 8 < Z.of_N page_size)%Z). { unfold page_size. lia. }
            replace n with (gmp' + 8)%N.
            lia.
            inv Heqn.
            repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H4; auto. lia. }          
          { move => _.
            intros n [Heqn Hboundn].
            destruct Hgmp_v_mult_two as [n' Hn'].
            replace n with (gmp' + 8)%N.
            exists (n' + 4)%N. lia.
            inv Heqn.
            repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H2; auto. lia. }          
          now subst f_before_IH.
        }

        assert (HmemPreserved': smem s_before_IH (f_inst fr) = Some m_after_store). {
          subst s_prim. cbn.
          apply update_global_preserves_memory in Hs_before_IH. rewrite -Hs_before_IH. cbn.
          by destruct (s_mems s'). }

        assert (HlocInBound' : forall (var : positive) (varIdx : localidx),
                   @repr_var nenv lenv var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs f_before_IH)). {
          intros ?? Hvar. subst f_before_IH. cbn.
          rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
          apply HlocInBound in Hvar, H3. lia.
        }

        assert (Hnodup' : NoDup (collect_local_variables e ++ collect_function_vars (Efun fds e)) ). {
          cbn in Hnodup. apply NoDup_cons_iff in Hnodup. now destruct Hnodup.
        }

        assert (HfenvRho' :  forall (a : positive) (v : val),
                   (map_util.M.set x (Vprim p) rho) ! a = Some v -> find_def a fds <> None -> v = Vfun (M.empty val) fds a). {
          intros. apply HfenvRho; auto. rewrite M.gso in H0. assumption.
          intro. subst a. apply notNone_Some in H1. apply HfenvWf in H1. destruct H1. inv H0.
          destruct HenvsDisjoint as [Hd1 Hd2]. apply Hd2 in H2. unfold translate_var in H2.
          inv H3. unfold translate_var in H0. rewrite H2 in H0. inv H0.
        }

        assert (HeRestr' : expression_restricted cenv e) by now inv HeRestr.

        assert (Hunbound' : forall x0 : var, In x0 (collect_local_variables e) -> (map_util.M.set x (Vprim p) rho) ! x0 = None). {
          intros.
          apply NoDup_app_remove_r in Hnodup.
          cbn in Hnodup.
          apply NoDup_cons_iff in Hnodup.
          rewrite M.gso.
          apply Hunbound.
          unfold collect_local_variables.
          cbn.
          fold collect_local_variables.
          right. assumption.
          destruct Hnodup as [Hx _ ].
          unfold not. unfold not in Hx. intros Heq. subst x.
          apply Hx in H0. contradiction.
        }

        (* Equivalence of store functions *)
        assert (HfsEq1: s_funcs s' = s_funcs s_prim) by now subst.
        assert (HfsEq2: s_funcs s_prim = s_funcs s_before_IH) by now apply update_global_preserves_funcs in Hs_before_IH.
        assert (HfsEq3: s_funcs s' = s_funcs s_before_IH) by now subst.
        assert (HfsEq4: s_funcs sr = s_funcs s_before_IH) by now subst.
        assert (Hfds' : forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) (errMsg : string),
                   find_def a fds = Some (t, ys, e) ->
                   expression_restricted cenv e /\
                     (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
                     NoDup (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)) /\
                     (exists fidx : funcidx,
                         translate_var nenv fenv a errMsg = Ret fidx /\
                           repr_val_LambdaANF_Wasm (Vfun (M.empty val) fds a)
                            s_before_IH (f_inst f_before_IH) (Val_funidx fidx))). {
          intros ? ? ? ? ? Hfd.
          apply Hfds with (errMsg:=errMsg) in Hfd.
          destruct Hfd as [? [? [? [idx [Htransf Hval]]]]]; repeat (split; try assumption).
          exists idx.
          split =>//.
          eapply val_relation_func_depends_on_funcs. 2: subst f_before_IH; eassumption.
          congruence.
        }
        assert (Hv_int: exists n, p = primInt n) by now destruct p; destruct x0.
        destruct Hv_int as [n Hn].
        assert (Hv0: v0 = Z_to_i64 (to_Z n)) by now rewrite Hn in H6; unfold translate_primitive_value in *; simpl in H6.
        assert (Hvalue : repr_val_LambdaANF_Wasm (Vprim (primInt n)) s_before_IH (f_inst f_before_IH) (Val_ptr gmp')). {
          apply Rprim_v with (gmp := (gmp' + 8)%N) (m := m_after_store) (addr := gmp'); auto; try lia.
          { apply update_global_get_same with (sr:=s_prim). subst f_before_IH. assumption. }
          { subst f_before_IH. assumption. }
          { apply store_load_i64 in Hm_after_store; auto.
            assert (wasm_deserialise (bits (VAL_int64 v0)) T_i64 = VAL_int64 v0) by now apply deserialise_bits.

            rewrite H0 in Hm_after_store.
            replace (Wasm_int.N_of_uint i32m (N_to_i32 gmp')) with gmp' in Hm_after_store. rewrite <-Hv0. assumption.
            cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
          }
        }

        assert (HmemLengthBound: (Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z). {
          apply mem_length_upper_bound in Hmem5. simpl_modulus_in Hmem5. cbn in Hmem5.
          simpl_modulus. cbn. lia.
        }

        assert (HmemLengthBound': (Z.of_N (mem_length m_after_store) < Wasm_int.Int32.modulus)%Z). {
          apply mem_length_upper_bound in Hmem5.
          simpl_modulus_in Hmem5. cbn in Hmem5. simpl_modulus. cbn. lia.
        }

        assert (HenoughMem': (Z.of_N gmp' + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z). {
          unfold page_size in HenoughM. lia.
        }

        assert (HenoughMem'': (Z.of_N gmp' + 8 + 8 <= Z.of_N (mem_length m_after_store) < Wasm_int.Int32.modulus)%Z). {
          unfold page_size in HenoughM. lia.
        }

        (* Before the continuation, the gmp global contains the old gmp value incremented by 8 *)
        assert (HglobalUpdatedGmp: sglob_val s_before_IH (f_inst fr) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 (gmp' + 8)))))
            by now apply update_global_get_same with (sr:=s_prim) (sr':=s_before_IH).

        (* All values in memory below the gmp are preserved *)
        assert (HvalsInMemPreserved: forall a, (a + 4 <= gmp')%N -> load_i32 m a = load_i32 m_after_store a). {
          intros a Ha.
          assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i32' m m_after_store a (Wasm_int.N_of_uint i32m (N_to_i32 gmp')) v' (bits (VAL_int64 v0))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }

        assert (HvalsInMemPreserved': forall a, (a + 8 <= gmp')%N -> load_i64 m a = load_i64 m_after_store a). {
          intros a Ha.
          assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i64' m m_after_store a (Wasm_int.N_of_uint i32m (N_to_i32 gmp')) v' (bits (VAL_int64 v0))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }

        assert (HrelE' : @rel_env_LambdaANF_Wasm lenv e (map_util.M.set x (Vprim p) rho) s_before_IH f_before_IH fds). {
          have Hl := HlocInBound _ _ H3.
          apply nth_error_Some in Hl.
          apply notNone_Some in Hl. destruct Hl as [? Hlx].
          unfold rel_env_LambdaANF_Wasm.
          destruct HrelE as [Hfun1 [Hfun2 Hvar]].
          split.
          { (* funs1 *)
            intros. destruct (var_dec x x1).
            { (* x = x1 *)
              subst x1. rewrite M.gss in H0. inv H0.
              assert (~ subval_or_eq (Vfun rho' fds' f) (Vprim (primInt n))). { apply subval_or_eq_fun_not_prim. intros. congruence. }
              contradiction.
            }
            { (* x <> x1 *) rewrite M.gso in H0; eauto. }
          } split.
          { intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
            destruct Hnfd as [i [Htrans Hval]].
            exists i. split. assumption.
            eapply val_relation_func_depends_on_funcs. eassumption.
            subst f_before_IH. assumption.
          }
          {
            intros. destruct (var_dec x x1).
            { (* x = x1 *)
              subst x1. exists (Vprim (primInt n)), (Val_ptr gmp').
              rewrite M.gss. split; auto. rewrite Hn; auto. split.
              subst f_before_IH. exists x'. cbn. split.
              inv H3.  unfold translate_var. unfold translate_var in H2.
              destruct (lenv ! x) eqn:Hx; rewrite Hx in H2=>//. injection H2 as ->.
              intros. now rewrite Hx.
              unfold lookup_N.
              erewrite set_nth_nth_error_same; eauto.
              subst f_before_IH. assumption.
            }
            { (* x <> x1 *)
              assert (Hocc : occurs_free (Eprim_val x p e) x1) by now apply Free_Eprim_val.
              have H' := Hvar _ Hocc H1.
              destruct H' as [val' [wal' [Hrho [Hloc Hval]]]].
              exists val', wal'. split.
              rewrite M.gso; auto. split.
              destruct Hloc as [i [Hl1 Hl2]].
              unfold stored_in_locals. exists i. split; auto.
              subst f_before_IH.
              unfold lookup_N.
              rewrite set_nth_nth_error_other; auto.
              intro. assert (i = x') by lia. subst x'. inv H3.
              specialize Hl1 with err_str.
              unfold translate_var in Hl1, H4.
              destruct (lenv ! x1) eqn:Hlx1; rewrite Hlx1 in Hl1=>//. injection Hl1 as ->.
              destruct (lenv ! x) eqn:Hlx2; rewrite Hlx2 in H4=>//. injection H4 as ->.
              have H'' := HlenvInjective _ _ _ _ n0 Hlx2 Hlx1. contradiction.
              apply nth_error_Some. congruence.
              subst f_before_IH fM.
              by eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s')
                  (sr':=s_before_IH) (gmp' := (gmp' + 8)%N); eauto; try lia.
            }
          }
        }

        have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny lh lenv HlenvInjective HenvsDisjoint state _ _ _ Hfds' HlocInBound' Hinv_before_IH H5 HrelE'.
        destruct IH as [s_final [f_final [k'' [lh'' [Hred_IH [Hval [Hfinst [Hsfuncs' [HvalPres H_INV]]]]]]]]].

        assert (Hfinst': f_inst f_before_IH = f_inst fr) by now subst.

        exists s_final, f_final, k'', lh''.

        split.
        eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
        eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
        apply r_eliml=>//. elimr_nary_instr 0. apply r_call.
        apply HfuncsId. unfold grow_mem_function_idx.
        unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
        dostep_nary 1.
        eapply r_invoke_native with (ves:= [AI_basic (BI_const_num (N_to_value page_size))])
          (vs:= [VAL_num (N_to_value page_size)]); try eassumption; eauto; try by (rewrite HeqfM; auto).
        reflexivity.

        eapply rt_trans. apply app_trans.
        eapply reduce_trans_frame.
        apply reduce_trans_label. subst fM. apply Hred. cbn.

        dostep_nary 0. apply r_global_get. apply Hinv'.
        dostep_nary 2. constructor. apply rs_relop. cbn.
        dostep_nary 1. constructor. apply rs_if_false. reflexivity.
        dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
        dostep_nary 0. constructor. apply rs_label_const=>//.

        cbn.
        dostep_nary 0. apply r_global_get. subst fM. eassumption.
        dostep_nary 2. eapply r_store_success; subst fM; eauto.
        dostep_nary 0. apply r_global_get. apply HgmpPreserved.
        cbn. dostep_nary 1. eapply r_local_set with (f':=f_before_IH) (v:= VAL_num (VAL_int32 (N_to_i32 gmp'))). subst f_before_IH. reflexivity.
        apply /ssrnat.leP.
        apply HlocInBound in H3. lia. subst. reflexivity.
        cbn.
        dostep_nary 0. apply r_global_get. now rewrite Hfinst'.
        dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
        dostep_nary 1. apply r_global_set with (v:= (VAL_num (VAL_int32 (Wasm_int.Int32.iadd (N_to_i32 gmp') (nat_to_i32 8))))). rewrite HgmpEq. subst f_before_IH. eassumption.
        apply rt_refl.
        (* apply IH *)
        apply Hred_IH.

        repeat split=>//; try congruence.
        intros wal val Hval'. subst f_before_IH fM.
        apply HvalPres.
        by eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with
           (sr:=s') (gmp := gmp') (gmp' := (gmp' + 8)%N); eauto; try lia.
      } { (* Growing the memory failed *)

       (* split of dead instructions after
         (BI_if (BT_valtype None) [:: BI_return] [::]) *)
        separate_instr. do 4 rewrite catA.
        match goal with
        |- context C [reduce_trans (_, _, _, [:: AI_frame _ _ (lfill _
           (_ ++ [:: AI_basic (BI_if (BT_valtype None) [:: BI_return] [::])] ++ ?es))])] =>
            let es_tail := fresh "es_tail" in
            remember es as es_tail
        end. do 4 rewrite <- catA.

        have Hlh := lholed_nested_label _ lh [AI_basic BI_return] es_tail. subst es_tail.
        destruct Hlh as [k' [lh' Heq']]. cbn in Heq'.

        do 3! eexists. exists lh'. split.
        eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
        eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
        apply r_eliml=>//. elimr_nary_instr 0. apply r_call.
        apply HfuncsId. unfold grow_mem_function_idx.
        unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
        dostep_nary 1.
        eapply r_invoke_native with (ves:= [AI_basic (BI_const_num (N_to_value page_size))])
          (vs:= [VAL_num (N_to_value page_size)]); try eassumption; eauto; try by (rewrite HeqfM; auto).
        reflexivity.

        eapply rt_trans. apply app_trans.
        eapply reduce_trans_frame.
        apply reduce_trans_label. subst fM. apply Hred. cbn.

        dostep_nary 0. apply r_global_get. subst fM. eassumption.
        dostep_nary 2. constructor. apply rs_relop.
        dostep_nary 1. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
        dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
        apply rt_refl. cbn.
        rewrite Heq'. apply rt_refl.
        split. right. subst fM. assumption. split. reflexivity. split. congruence.
        split.
        { intros. subst fM. apply HvalPreserved. assumption. }
        intro Hcontra. subst fM. rewrite Hcontra in HoutofM. inv HoutofM. }
    }
  - (* Eprim *)
    { cbn. inv Hrepr_e.
      have I := Hinv. destruct I as [_[_[_[_[_[_[Horglinmem [_[_[HfnsBound[_[_[_[_ [HfuncGrow HfuncsId]]]]]]]]]]]]]]].
      destruct Horglinmem as [Horgmem1 [orgm [Horgmem2 [orgsize [<- [Horgmem4 Horgmem5]]]]]].
      remember (Build_frame [VAL_num (N_to_value page_size)] (f_inst fr)) as fM.
      assert (HinvM: INV sr fM). {
        subst fM. eapply change_locals_preserves_INV. eassumption.
        intros i ? Hl. destruct i; last by destruct i.
        inv Hl. now eexists. reflexivity.
      }
      assert (Hloc0: lookup_N (f_locs fM) 0 = Some (VAL_num (N_to_value page_size))) by (subst fM; reflexivity).
      have Hgrowmem := memory_grow_reduce state sr _ Hloc0 HinvM.
      destruct Hgrowmem as [gmp' [s' [Hred [Hsfuncs [HvalPreserved [[HinvFm' Henoughmem] | HoutofM]]]]]].
      { (* Successfully grow memory if necessary *)
        (* invariants after reducing grow *)
        have I := HinvFm'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
        destruct Hlinmem as [Hmem1 [m [Hmem2 [size [<- [Hmem4 Hmem5]]]]]].
        have HenoughM := Henoughmem _ Hmem2. destruct HenoughM as [Hgmp HenoughM]. clear Henoughmem.
        assert (Hinv': INV s' fr). {
          destruct fr.
          eapply change_locals_preserves_INV with (f:=fM). eassumption. apply Hinv.
          subst fM. reflexivity.
        } clear HinvFm'.
        assert ((Z.of_N gmp' < Wasm_int.Int32.modulus)%Z). {
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5. simpl_modulus. cbn. lia. }

        assert (Hlocals : (forall y : var,
                              In y ys ->
                              find_def y fds = None ->
                              exists (v6 : cps.val) (val : wasm_value),
                                rho ! y = Some v6 /\
                                  @stored_in_locals lenv y val fr /\
                                  repr_val_LambdaANF_Wasm v6 s' (f_inst fr) val)). {
          destruct HrelE as [_ Hvar]. intros.
          assert (Hocc: occurs_free (Eprim x f ys e) y) by (constructor; auto).
          apply Hvar in Hocc; auto. destruct Hocc as [val [wal [Hrho [Hloc Hval]]]].
          exists val, wal. subst fM. by repeat split; auto.
        }

        assert (HrelE': @rel_env_LambdaANF_Wasm lenv (Eprim x f ys e) rho s' fr fds). {
          destruct HrelE as [Hfun1 [Hfun2 Hvar]]. split. assumption.
          split.
          intros.
          destruct (Hfun2 _ errMsg H3) as [idx [Htrans_idx Hrepr_idx]].
          exists idx. split. assumption.
          eapply val_relation_func_depends_on_funcs. eassumption. eassumption.
          intros.
          destruct (Hvar _ H3) as [val [wal [Hrho' [Hlocs Hval]]]]; auto.
          exists val. exists wal.
          split. assumption.
          split. assumption.
          subst fM. cbn in HvalPreserved.
          now apply HvalPreserved.
        }

        assert (f_inst fM = f_inst fr) by now subst fM.
        rewrite H3 in Hgmp.

        subst fM.

        have Hprim_red := primitive_operation_reduces lenv pfs state s' fr m fds f' x x' f
                            op_name s b n op ys e vs rho v gmp' prim_instrs HprimFunsRelated H0 H10 H11 HlenvInjective HenvsDisjoint HfenvWf HlocInBound H7 HrelE' H12 Hinv' Hmem2 Hgmp HenoughM H H1.

        clear HrelE'.

        destruct Hprim_red as [sr_before_IH [fr_before_IH [Hred' [Hinv_before_IH [Hfinst [Hsfs [HrelE' [HvalsPreserved [wal [Hfr_eq Hrepr_val]]]]]]]]]].

        have Hrepr_e' := H8.

        assert (Hnodup' : NoDup (collect_local_variables e ++ collect_function_vars (Efun fds e))). {
          cbn in Hnodup. apply NoDup_cons_iff in Hnodup. now destruct Hnodup.
        }

        assert (HfenvRho' :
                 (forall (a : positive) (v0 : val),
                     (map_util.M.set x v rho) ! a = Some v0 ->
                     find_def a fds <> None -> v0 = Vfun (M.empty val) fds a)). {
          intros. apply HfenvRho; auto. rewrite M.gso in H4. assumption.
          intro. subst a. apply notNone_Some in H5. apply HfenvWf in H5. destruct H5. inv H4.
          destruct HenvsDisjoint as [Hd1 Hd2]. apply Hd2 in H6.
          inv H7. unfold translate_var in H4. rewrite H6 in H4. inv H4.
        }
        assert (HeRestr' : expression_restricted cenv e) by now inv HeRestr.

        assert (Hunbound' : (forall x0 : var,
                                In x0 (collect_local_variables e) -> (map_util.M.set x v rho) ! x0 = None)). {
                    intros.
          apply NoDup_app_remove_r in Hnodup.
          cbn in Hnodup.
          apply NoDup_cons_iff in Hnodup.
          rewrite M.gso.
          apply Hunbound.
          unfold collect_local_variables.
          cbn.
          fold collect_local_variables.
          right. assumption.
          destruct Hnodup as [Hx _ ].
          unfold not. unfold not in Hx. intros Heq. subst x.
          apply Hx in H4. contradiction. }

        assert (HfVal' : (forall (y : positive) (y' : funcidx) (v : cps.val),
                             rho ! y = Some v ->
                             repr_funvar y y' ->
                             repr_val_LambdaANF_Wasm v sr_before_IH (f_inst fr_before_IH) (Val_funidx y'))).
        { intros. destruct HrelE as [Hfun1 [Hfun2 _]].
          assert (Hfd: (exists i : funcidx, fenv ! y = Some i)). {
            inv H5. unfold translate_var in H6. destruct (fenv ! y) eqn:Hy; rewrite Hy in H6. eauto. discriminate. }
          apply HfenvWf in Hfd. apply notNone_Some in Hfd.

          have H' := HfenvRho _ _ H4 Hfd. subst v0.
          apply notNone_Some in Hfd. destruct Hfd as [[[f'' ys''] e''] ?H].

          assert (Hsubval: subval_or_eq (Vfun (M.empty _) fds y)
                             (Vfun (M.empty cps.val) fds y)) by constructor.

          inv H5.
          have H' := Hfun1 _ _ _ _ _ H4 Hsubval. destruct H' as [_ [_ H']].
          apply Hfun2 with (errMsg:=errMsg) in H'.
          destruct H' as [i [HvarI Hval]].
          assert (i = y') by congruence. subst i.
          apply val_relation_func_depends_on_funcs with (s:=sr). rewrite -Hsfs. auto. rewrite -Hfinst.
          apply Hval.
        }

        assert (Hfds' :
                 (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) (errMsg : string),
           find_def a fds = Some (t, ys, e) ->
           expression_restricted cenv e /\
           (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
           NoDup (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)) /\
           (exists fidx : funcidx,
              translate_var nenv fenv a errMsg = Ret fidx /\
                repr_val_LambdaANF_Wasm (Vfun (M.empty val) fds a) sr_before_IH (f_inst fr_before_IH) (Val_funidx fidx)))). {
          intros ? ? ? ? ? Hfd.
          subst.
          apply Hfds with (errMsg:=errMsg) in Hfd.
          destruct Hfd as [? [? [? [idx [Htransf Hval]]]]]; repeat (split; try assumption).
          exists idx.
          split; auto. }

        assert (HlocInBound' : (forall (var : positive) (varIdx : localidx),
                                   repr_var (lenv:=lenv) nenv var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs fr_before_IH))).
        {
          intros ?? Hvar. subst fr_before_IH.
          rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
          apply HlocInBound in Hvar, H7. lia.
        }


        have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny lh lenv HlenvInjective HenvsDisjoint state _ _ _ Hfds' HlocInBound' Hinv_before_IH Hrepr_e' HrelE'.

        destruct IH as [s_final [f_final [k'' [lh'' [Hred_IH [Hval [Hfinst' [Hsfuncs' [HvalPres H_INV]]]]]]]]].

        exists s_final, f_final, k'', lh''.

        split.

        eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
        eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
        apply r_eliml. constructor.
        elimr_nary_instr 0.
        apply r_call.
        apply HfuncsId. unfold grow_mem_function_idx.
        unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
        dostep_nary 1.
        eapply r_invoke_native with (ves:= [AI_basic (BI_const_num (N_to_value page_size))])
                                    (vs:= [VAL_num (N_to_value page_size)]); try eassumption; eauto; try by (rewrite HeqfM; auto).
        reflexivity.

        eapply rt_trans. apply app_trans.
        eapply reduce_trans_frame.
        apply reduce_trans_label. subst. apply Hred. cbn.
        dostep_nary 0. apply r_global_get. subst. apply Hinv'.
        dostep_nary 2. constructor. apply rs_relop. cbn.
        dostep_nary 1. constructor. apply rs_if_false. reflexivity.
        dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
        dostep_nary 0. constructor. apply rs_label_const; auto.

        cbn.
        rewrite map_cat.
        eapply rt_trans with (y := (state, sr_before_IH, fr_before_IH, [] ++ ?[t'])).
        apply app_trans.
        apply Hred'.
        apply rt_refl.
        apply Hred_IH.
        subst fr_before_IH.
        replace (s_funcs s_final) with (s_funcs s') by now rewrite -Hsfuncs';rewrite -Hsfs.
        do 4 (split; auto).
        }
      { (* Growing the memory failed *)

        (* split of dead instructions after
         (BI_if (BT_valtype None) [:: BI_return] [::]) *)
        separate_instr. do 4 rewrite catA.
        match goal with
          |- context C [reduce_trans (_, _, _, [:: AI_frame _ _ (lfill _
                                                                   (_ ++ [:: AI_basic (BI_if (BT_valtype None) [:: BI_return] [::])] ++ ?es))])] =>
            let es_tail := fresh "es_tail" in
            remember es as es_tail
        end. do 4 rewrite <- catA.

        have Hlh := lholed_nested_label _ lh [AI_basic BI_return] es_tail. subst es_tail.
        destruct Hlh as [k' [lh' Heq']]. cbn in Heq'.

        do 3! eexists. exists lh'. split.
        eapply rt_trans. apply reduce_trans_frame'. apply reduce_trans_label'.
        eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
        apply r_eliml. constructor.
        elimr_nary_instr 0.
        apply r_call.
        apply HfuncsId. unfold grow_mem_function_idx.
        unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
        dostep_nary 1.
        eapply r_invoke_native with (ves:= [AI_basic (BI_const_num (N_to_value page_size))])
                                    (vs:= [VAL_num (N_to_value page_size)]); try eassumption; eauto; try by (rewrite HeqfM; auto).
        reflexivity.

        eapply rt_trans. apply app_trans.
        eapply reduce_trans_frame.
        apply reduce_trans_label. subst fM. apply Hred. cbn.

        dostep_nary 0. apply r_global_get. subst fM. eassumption.
        dostep_nary 2. constructor. apply rs_relop.
        dostep_nary 1. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
        dostep_nary 0. eapply r_block with (t1s:=[::]) (t2s:=[::])(vs:=[::]); auto.
        apply rt_refl. cbn.
        rewrite Heq'. apply rt_refl.
        split. right. subst fM. assumption. split. reflexivity. split. congruence.
        split.
        { intros. subst fM. apply HvalPreserved. assumption. }
        intro Hcontra. subst fM. rewrite Hcontra in HoutofM. inv HoutofM. }
    }
  - (* Ehalt *)
    cbn. inv Hrepr_e. destruct HrelE as [_ [_ Hvar]].
    assert (HfNone: find_def x fds = None). {
      apply HfenvWf_None with (f:=x) in HfenvWf. rewrite HfenvWf.
      inv H1. unfold translate_var in H0. destruct (lenv ! x) eqn:Hx; rewrite Hx in H0=>//. injection H0 as ->.
      now apply HenvsDisjoint in Hx. }
     destruct (Hvar x) as [v6 [wal [Henv [Hloc Hrepr]]]]; auto.
    rewrite Henv in H. inv H.

    have I := Hinv. destruct I as [INVres [_ [HMzero [Hgmp_r [_ [Hmuti32 [Hlinmem [HgmpInMem [_ [Hfuncs [Hinstglobs [_ [_ Hgmp_mult_two]]]]]]]]]]]]].
    destruct (i32_glob_implies_i32_val _ _ _ gmp_i32_glob Hgmp_r Hmuti32) as [gmp Hgmp].
   
    edestruct i32_exists_N as [x'' [Hx'' ?]]. erewrite Hx'' in Hgmp. subst.

    destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst.
    assert (Hmemlengthbound: (Z.of_N (mem_length m) < Int32.modulus)%Z). {
      apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
      simpl_modulus. simpl_modulus_in H. cbn. lia. }
    apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
    have HinM := HgmpInMem _ _ Hmem2 Hgmp.
    
    unfold INV_result_var_writable, global_var_w in INVres.
    destruct (INVres (VAL_int32 (wasm_value_to_i32 wal))) as [s' Hs].
    (* specialize INVres with (VAL_int32 (wasm_value_to_i32 wal)). *)
    (* destruct INVres as [s' Hs]. *)

    destruct Hloc as [ilocal [H4 Hilocal]]. inv H1. erewrite H4 in H0. injection H0 => H'. subst.

    exists s', fr, k, lh.  cbn. split.

    (* execute wasm instructions *)
    apply reduce_trans_frame'. apply reduce_trans_label'.
    dostep_nary 0. eapply r_local_get. eassumption.
    dostep_nary' 1. apply r_global_set with (v:= VAL_num (VAL_int32 (wasm_value_to_i32 wal))). eassumption. apply rt_refl.

    split.
    left. exists (wasm_value_to_i32 wal). exists wal.
    repeat split. eapply update_global_get_same. eassumption.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply Hrepr; eauto.
    eapply update_global_preserves_funcs; try eassumption.
    erewrite <- update_global_preserves_memory; try eassumption.
    simpl_modulus. cbn. lia.
    eapply update_global_get_other; try eassumption.
    unfold global_mem_ptr, result_var. lia.
    simpl_modulus. cbn. lia. lia.
    eapply update_global_get_other; try eassumption. now intro. split; first auto.
    split. eapply update_global_preserves_funcs; eassumption.
    split. { intros.
      assert (smem s' (f_inst fr) = Some m). {
        now rewrite -(update_global_preserves_memory _ _ _ _ _ Hs). }
      assert (sglob_val s' (f_inst fr) global_mem_ptr = Some (VAL_num (VAL_int32 (N_to_i32 x'')))). {
      erewrite update_global_get_other; try eassumption. reflexivity. now intro.
    }
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=sr); eauto.
      eapply update_global_preserves_funcs. eassumption.
      simpl_modulus. cbn. lia.
      simpl_modulus. cbn. lia.
      lia.
    }
    intro H_INV. eapply update_global_preserves_INV with (i:=result_var) (num:=(VAL_int32 (wasm_value_to_i32 wal))).
    left. split. apply result_var_i32_glob. now cbn. 
    eassumption.
    discriminate.
    eassumption.
    now intro.
    now intro.
    eassumption.
    Unshelve. all: try assumption; try apply ""%bs; try apply [].
Qed.

End MAIN.
