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
               Coq.Relations.Relations Relations.Relation_Operators Lia.

Require Import compcert.lib.Integers compcert.common.Memory.

From CertiCoq.CodegenWasm Require Import LambdaANF_to_Wasm LambdaANF_to_Wasm_utils.

From Wasm Require Import datatypes operations host memory_list opsem
                         type_preservation instantiation_spec
                         instantiation_properties properties common.

Require Import Libraries.maps_util.
From Coq Require Import List.

Import ssreflect eqtype ssrbool eqtype.
Import LambdaANF.toplevel LambdaANF.cps compM.
Import bytestring.
Import ExtLib.Structures.Monad MonadNotation.
Import bytestring.
Import ListNotations.
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
                                  | Some (Build_ctor_ty_info _ _ _ a _) =>
                                    N.of_nat (length ys) = a
                                  | None => False
                                  end) e.


Inductive expression_restricted : cps.exp -> Prop :=
| ER_constr : forall x t ys e,
    (Z.of_nat (Pos.to_nat t) < Wasm_int.Int32.half_modulus)%Z ->
      (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z ->
      expression_restricted e ->
      expression_restricted (Econstr x t ys e)
  | ER_case : forall x ms,
      Forall (fun p => (Z.of_nat (Pos.to_nat (fst p)) < Wasm_int.Int32.half_modulus)%Z /\
                        expression_restricted (snd p)) ms ->
      expression_restricted (Ecase x ms)
  | ER_proj : forall x t n y e,
      expression_restricted e ->
      expression_restricted (Eproj x t n y e)
  | ER_letapp : forall f x ft ys e,
      expression_restricted e ->
      (Z.of_nat (Datatypes.length ys) <= max_function_args)%Z ->
      expression_restricted (Eletapp x f ft ys e)
  | ER_fun : forall e fds,
      expression_restricted e ->
      (forall f t ys e', find_def f fds = Some (t, ys, e') ->
                   Z.of_nat (length ys) <= max_function_args /\
                   expression_restricted e')%Z ->
      (Z.of_nat (numOf_fundefs fds) < max_num_functions)%Z ->
      expression_restricted (Efun fds e)
  | ER_app : forall f ft ys,
      (Z.of_nat (Datatypes.length ys) <= max_function_args)%Z ->
      expression_restricted (Eapp f ft ys)
  | ER_prim_val : forall x p e,
      expression_restricted e ->
      expression_restricted (Eprim_val x p e)
  | ER_prim : forall x p ys e,
      expression_restricted e ->
      expression_restricted (Eprim x p ys e)
  | ER_halt : forall x,
      expression_restricted (Ehalt x).

Local Hint Constructors expression_restricted : core.

Theorem check_restrictions_expression_restricted : forall e e',
  check_restrictions e = Ret () ->
  subterm_or_eq e' e -> expression_restricted e'.
Proof.
  have IH := exp_mut
    (fun e => check_restrictions e = Ret () -> forall e',
                subterm_or_eq e' e -> expression_restricted e')
    (fun fds => ((fix iter (fds : fundefs) : error Datatypes.unit :=
                   match fds with
                   | Fnil => Ret ()
                   | Fcons _ _ ys e' fds' =>
                       _ <- assert (Z.of_nat (length ys) <=? max_function_args)%Z
                            "found fundef with too many function args, check max_function_args";;
                       _ <- (iter fds');;
                       check_restrictions e'
                   end) fds) = Ret () -> forall e' e'',
               dsubterm_fds_e e' fds -> subterm_or_eq e'' e' -> expression_restricted e'').
  intros. eapply IH; eauto; clear IH; try intros.
  { (* Econstr *)
    rename H3 into Hsub, H1 into IHe. inv H2.
    destruct (Z.of_nat (Pos.to_nat t) <? Wasm_int.Int32.half_modulus)%Z eqn:Htupper. 2: inv H3.
    destruct (Z.of_nat (Datatypes.length l) <=? max_constr_args)%Z eqn:Hlen. 2: inv H3.
    cbn in H3. clear H.
    apply Z.ltb_lt in Htupper.
    apply Z.leb_le in Hlen. apply clos_rt_rtn1 in Hsub. inv Hsub. constructor; auto.
    apply IHe; auto. apply rt_refl. inv H. apply IHe; auto. now apply clos_rtn1_rt. }
  { (* Ecase nil *)
    rename H2 into Hsub.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor. apply Forall_nil.
    now inv H2. }
  { (* Ecase cons *)
    rename H4 into Hsub, H1 into IHe, H2 into IHe0. inv H3.
    clear H0 H e. rename e0 into e.
    destruct ((Z.of_nat (Pos.to_nat c) <? Wasm_int.Int32.half_modulus)%Z) eqn:Hupper. 2: inv H2.
    (* cbn in H2. *) destruct (check_restrictions e) eqn:Hrestr. inv H2.
    destruct (sequence _ ) eqn:Hseq; inv H2. destruct u.
    assert (check_restrictions (Ecase v l) = Ret ()). {
      unfold check_restrictions. simpl. now rewrite Hseq. }
    assert (expression_restricted (Ecase v l)). {
       apply IHe0; auto. apply rt_refl. }

    apply clos_rt_rtn1 in Hsub. inv Hsub.
    { constructor. apply Forall_cons. simpl. split. now apply Z.ltb_lt.
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
    destruct (Z.of_nat (numOf_fundefs f2) <? max_num_functions)%Z eqn:HmaxFns. 2: inv H2.
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
      - now apply Z.ltb_lt in HmaxFns.
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

Inductive repr_var {lenv} : positive -> immediate -> Prop :=
| repr_var_V : forall s err_str i,
    translate_var nenv lenv s err_str = Ret i ->
    repr_var s i.

Inductive repr_funvar : positive -> immediate -> Prop :=
| repr_funvar_FV : forall s i errMsg,
    translate_var nenv fenv s errMsg = Ret i ->
    repr_funvar s i.

Inductive repr_read_var_or_funvar {lenv} : positive -> basic_instruction -> Prop :=
| repr_var_or_funvar_V : forall p i,
    repr_var (lenv:=lenv) p i -> repr_read_var_or_funvar p (BI_get_local i)
| repr_var_or_funvar_FV : forall p i,
    repr_funvar p i -> repr_read_var_or_funvar p (BI_const (nat_to_value i)).

(* constr_alloc_ptr: pointer to linear_memory[p + 4 + 4*n] = value v *)
Inductive set_nth_constr_arg {lenv} : nat -> var -> list basic_instruction -> Prop :=
  Make_nth_proj: forall (v : var) n instr,
    repr_read_var_or_funvar (lenv:=lenv) v instr ->
    set_nth_constr_arg n v
      [ BI_get_global constr_alloc_ptr
      ; BI_const (nat_to_value ((1 + n) * 4))
      ; BI_binop T_i32 (Binop_i BOI_add)
      ; instr
      ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0)
      ; BI_get_global global_mem_ptr
      ; BI_const (nat_to_value 4)
      ; BI_binop T_i32 (Binop_i BOI_add)
      ; BI_set_global global_mem_ptr
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
    repr_fun_args_Wasm (a :: args) ([BI_get_local a'] ++ instr)
(* arg is function -> lookup id for handling indirect calls later *)
| FA_cons_fun : forall a a' args instr,
    repr_funvar a a' ->
    repr_fun_args_Wasm args instr ->
    repr_fun_args_Wasm (a :: args) ([BI_const (nat_to_value a')] ++ instr).

Inductive repr_asgn_constr_Wasm {lenv} : immediate -> ctor_tag -> list var -> list basic_instruction -> list basic_instruction ->  Prop :=
| Rconstr_asgn_boxed :
  forall x' t vs sargs scont arity,
    get_ctor_arity cenv t = Ret arity ->
    arity > 0 ->
    (* store args *)
    Forall_statements_in_seq (set_nth_constr_arg (lenv:=lenv)) vs sargs ->

    repr_asgn_constr_Wasm x' t vs scont
      ([ BI_const (N_to_value page_size)
       ; BI_call grow_mem_function_idx
       ; BI_get_global result_out_of_mem
       ; BI_const (nat_to_value 1)
       ; BI_relop T_i32 (Relop_i ROI_eq)
       ; BI_if (Tf nil nil)
           (* grow mem failed *)
           [ BI_return ]
           []
       ; BI_get_global global_mem_ptr
       ; BI_set_global constr_alloc_ptr
       ; BI_get_global constr_alloc_ptr
       ; BI_const (nat_to_value (Pos.to_nat t))
       ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0)
       ; BI_get_global global_mem_ptr
       ; BI_const (nat_to_value 4)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_set_global global_mem_ptr
       ] ++ sargs ++ [BI_get_global constr_alloc_ptr; BI_set_local x'] ++ scont)

| Rconstr_asgn_unboxed :
  forall x' t scont,
    get_ctor_arity cenv t = Ret 0 ->
    repr_asgn_constr_Wasm x' t [] scont
      ([ BI_const (nat_to_value (Pos.to_nat t))
       ; BI_const (nat_to_value 1)
       ; BI_binop T_i32 (Binop_i BOI_shl)
       ; BI_const (nat_to_value 1)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_set_local x' ] ++ scont ).


Inductive repr_case_boxed: immediate -> list (ctor_tag * list basic_instruction) -> list basic_instruction -> Prop :=
| Rcase_boxed_nil: forall v, repr_case_boxed v [] [ BI_unreachable ]
| Rcase_boxed_cons: forall v t instrs brs instrs_more,
    repr_case_boxed v brs instrs_more ->
    repr_case_boxed v ((t, instrs) :: brs)
      [ BI_get_local v
      ; BI_load T_i32 None 2%N 0%N
      ; BI_const (nat_to_value (Pos.to_nat t))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (Tf nil nil)
          instrs
          instrs_more ].

Inductive repr_case_unboxed: immediate -> list (ctor_tag * list basic_instruction) -> list basic_instruction -> Prop :=
| Rcase_unboxed_nil: forall v, repr_case_unboxed v [] [ BI_unreachable ]
| Rcase_unboxed_cons: forall v t instrs brs instrs_more,
    repr_case_unboxed v brs instrs_more ->
    repr_case_unboxed v ((t, instrs) :: brs)
      [ BI_get_local v
      ; BI_const (nat_to_value (Pos.to_nat (2 * t + 1)))
      ; BI_relop T_i32 (Relop_i ROI_eq)
      ; BI_if (Tf nil nil)
          instrs
          instrs_more
      ].

(* CODEGEN RELATION: relatates LambdaANF expression and result of translate_exp *)
Inductive repr_expr_LambdaANF_Wasm {lenv} : LambdaANF.cps.exp -> list basic_instruction -> Prop :=
| R_halt_e: forall x x',
    repr_var (lenv:=lenv) x x' ->
    repr_expr_LambdaANF_Wasm (Ehalt x)
      [ BI_get_local x'
      ; BI_set_global result_var
      ; BI_return
      ]
| Rproj_e: forall x x' t n y y' e e',
    repr_expr_LambdaANF_Wasm e e' ->
    repr_var (lenv:=lenv) x x' ->
    repr_var (lenv:=lenv) y y' ->
    repr_expr_LambdaANF_Wasm (Eproj x t n y e)
      ([ BI_get_local y'
       ; BI_const (nat_to_value (((N.to_nat n) + 1) * 4))
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_load T_i32 None (N_of_nat 2) (N_of_nat 0)
       ; BI_set_local x'
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
      [ BI_get_local y'
      ; BI_const (nat_to_value 1)
      ; BI_binop T_i32 (Binop_i BOI_and)
      ; BI_testop T_i32 TO_eqz
      ; BI_if (Tf [] [])
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
                                                [BI_return_call_indirect (length args)])

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
       ; BI_call_indirect (length args)
       ; BI_get_global result_out_of_mem
       ; BI_if (Tf nil nil)
           (* grow mem failed *)
           [ BI_return ]
           []
       ; BI_get_global result_var
       ; BI_set_local x'
       ] ++ e')

| R_prim_val : forall x x' p v e e',
    repr_var (lenv:=lenv) x x' ->
    repr_expr_LambdaANF_Wasm e e' ->
    translate_primitive p = Ret v ->
    repr_expr_LambdaANF_Wasm (Eprim_val x p e)
      ([ BI_const (N_to_value page_size)
       ; BI_call grow_mem_function_idx
       ; BI_get_global result_out_of_mem
       ; BI_const (nat_to_value 1)
       ; BI_relop T_i32 (Relop_i ROI_eq)
       ; BI_if (Tf [] [])
           (* grow mem failed *)
           [ BI_return ]
           []
       ; BI_get_global global_mem_ptr
       ; BI_const (VAL_int64 v)
       ; BI_store T_i64 None 2%N 0%N
       ; BI_get_global global_mem_ptr
       ; BI_set_local x'
       ; BI_get_global global_mem_ptr
       ; BI_const (nat_to_value 8)
       ; BI_binop T_i32 (Binop_i BOI_add)
       ; BI_set_global global_mem_ptr
       ] ++ e')

with repr_branches {lenv}: immediate -> list (ctor_tag * exp) -> list (ctor_tag * list basic_instruction) -> list (ctor_tag * list basic_instruction) -> Prop :=
| Rbranch_nil : forall x, repr_branches x [] [ ] [ ]

| Rbranch_cons_boxed : forall x cl t e n e' brs1 brs2,
    repr_branches x cl brs1 brs2 ->
    get_ctor_arity cenv t = Ret n ->
    0 < n ->
    repr_expr_LambdaANF_Wasm e e' ->
    repr_branches x ((t, e) :: cl) ((t,e') :: brs1) brs2

| Rbranch_cons_unboxed : forall x cl t e n e' brs1 brs2,
    repr_branches x cl brs1 brs2 ->
    get_ctor_arity cenv t = Ret n ->
    n = 0 ->
    repr_expr_LambdaANF_Wasm e e' ->
    repr_branches x ((t, e) :: cl) brs1 ((t,e') :: brs2).

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

Theorem translate_exp_correct {lenv} :
    forall e instructions,
      correct_cenv_of_exp cenv e ->
    translate_exp nenv cenv lenv fenv e = Ret instructions ->
    @repr_expr_LambdaANF_Wasm lenv e instructions.
Proof.
  induction e using exp_ind'; intros instr Hcenv; intros.
  - (* Econstr *)
    simpl in H.
    destruct (translate_exp nenv cenv lenv fenv e) eqn:H_eqTranslate; inv H.
    destruct (translate_var nenv lenv v _) eqn:H_translate_var. inv H1.
    destruct l as [|v0 l'].
    + (* Nullary constructor *)
      inv H1.
      eapply Rconstr_e with (e':=l0) (x':=i); eauto.
      apply IHe; auto.
      assert (subterm_e e (Econstr v t [] e) ). { constructor; constructor. }
      eapply Forall_constructors_subterm. eassumption. assumption.
      econstructor; eauto.
      eapply Rconstr_asgn_unboxed.
      apply Forall_constructors_in_constr in Hcenv.
      destruct (cenv ! t) eqn:Hc; auto. destruct c. inv Hcenv.
      unfold get_ctor_arity. now rewrite Hc.
    + (* Non-nullary constructor *)
      remember (v0 :: l') as l.
      destruct (store_constructor nenv cenv lenv fenv t l) eqn:store_constr.
      inv H1. inv H1. cbn.
      rename i into v'.
      unfold store_constructor in store_constr.
      destruct (set_constructor_args nenv lenv fenv (v0 :: l') 0) eqn:Hconstrargs. inv store_constr.
      inversion store_constr.
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
    destruct (translate_exp nenv cenv lenv fenv e) eqn:He. inv H.
    destruct (translate_exp nenv cenv lenv fenv (Ecase v l)) eqn:Hl.
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
    destruct (get_ctor_arity cenv c) eqn:Har. inv H.
    destruct n eqn:Hn.
    + (* Unboxed branch *)
      inv H. destruct l3. econstructor; eauto. econstructor; eauto. econstructor; eauto. cbn in H7.
      by repeat (econstructor; eauto).
    + (* Boxed branch *)
        inv H. by destruct l2; econstructor; eauto; econstructor; eauto; try lia.
  - (* Eproj *)
    simpl in H.
    destruct (translate_exp nenv cenv lenv fenv e) eqn:He. inv H.
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
    destruct (translate_exp nenv cenv lenv fenv e) eqn:H_eqTranslate. inv H.
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
    destruct (translate_exp nenv cenv lenv fenv e) eqn:H_eqTranslate. inv H1.
    destruct (translate_var nenv lenv v _) eqn:Hvar. inv H1.
    destruct (translate_primitive p) eqn:Hprim. inv H1.
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
    by inv H.
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
Let repr_expr_LambdaANF_Wasm := @repr_expr_LambdaANF_Wasm cenv fenv nenv.
Let repr_funvar := @repr_funvar fenv nenv.

Variable host_function : eqType.
Let host := host host_function.
Let store_record := store_record host_function.
Variable host_instance : host.
Let host_state := host_state host_instance.
Let reduce_trans := @reduce_trans host_function host_instance.


(* VALUE RELATION *)
(* immediate is pointer to linear memory or function id *)
Inductive repr_val_LambdaANF_Wasm:
  LambdaANF.cps.val -> store_record -> instance -> wasm_value -> Prop :=
| Rconstr_unboxed_v : forall v (t : ctor_tag) (sr : store_record) fi,
    Pos.to_nat (t * 2 + 1) = v ->
    (-1 < Z.of_nat v < Wasm_int.Int32.modulus)%Z ->
    get_ctor_arity cenv t = Ret 0 ->
    repr_val_LambdaANF_Wasm (Vconstr t []) sr fi (Val_unboxed v)

| Rconstr_boxed_v : forall v t vs (sr : store_record) fi gmp m (addr : nat) arity,
    (* simple memory model: gmp is increased whenever new mem is needed,
       gmp only increases *)
    sglob_val sr fi global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
    (-1 < Z.of_nat gmp < Wasm_int.Int32.modulus)%Z ->
    (* constr arity > 0 *)
    get_ctor_arity cenv t = Ret arity ->
    arity > 0 ->
    (* addr in bounds of linear memory (later INV: gmp + 4 < length of memory) *)
    (addr + 4 <= gmp) ->
    (exists n, addr = 2 * n) ->
    (* store_record contains memory *)
    List.nth_error sr.(s_mems) 0 = Some m ->
    (* constructor tag is set, see LambdaANF_to_W, constr alloc structure*)
    v = tag_to_i32 t ->
    load_i32 m (N.of_nat addr) = Some (VAL_int32 v) ->
    (* arguments are set properly *)
    repr_val_constr_args_LambdaANF_Wasm vs sr fi (4 + addr) ->
    repr_val_LambdaANF_Wasm (Vconstr t vs) sr fi (Val_ptr addr)

| Rfunction_v : forall fds f sr fi tag xs e e' idx ftype ts body,
      repr_funvar f idx ->
      find_def f fds = Some (tag, xs, e) ->
      (* types of local vars: all i32 *)
      ts = repeat T_i32 (length (collect_local_variables e)) ->
      (* find runtime representation of function *)
      nth_error sr.(s_funcs) idx = Some (FC_func_native fi ftype ts body) ->
      ftype = Tf (List.map (fun _ => T_i32) xs) [] ->
      body = e' ->
      repr_expr_LambdaANF_Wasm (create_local_variable_mapping (xs ++ collect_local_variables e)) e e'
         ->
           repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f) sr fi (Val_funidx idx)

|  Rprim_v : forall p v sr fi gmp m addr,
    sglob_val sr fi global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
    (-1 < Z.of_nat gmp < Wasm_int.Int32.modulus)%Z ->
    (addr+8 <= gmp) ->
    (exists n, addr = 2 * n) ->
    List.nth_error sr.(s_mems) 0 = Some m ->
    translate_primitive p = Ret v ->
    load_i64 m (N.of_nat addr) = Some (VAL_int64 v) ->
    repr_val_LambdaANF_Wasm (Vprim p) sr fi (Val_ptr addr)

with repr_val_constr_args_LambdaANF_Wasm : list LambdaANF.cps.val ->
                                              store_record ->
                                              instance ->
                                              immediate ->
                                              Prop :=
     | Rnil_l: forall sr fr addr,
        repr_val_constr_args_LambdaANF_Wasm nil sr fr addr

     | Rcons_l: forall v wal vs sr fi m addr gmp,
        (* store_record contains memory *)
        List.nth_error sr.(s_mems) 0 = Some m ->

        sglob_val (host_function:=host_function) sr fi global_mem_ptr =
          Some (VAL_int32 (nat_to_i32 gmp)) ->
        (-1 < Z.of_nat gmp < Wasm_int.Int32.modulus)%Z ->
        (addr + 4 <= gmp) ->

        (* constr arg is ptr related to value v *)
        load_i32 m (N.of_nat addr) = Some (VAL_int32 (wasm_value_to_i32 wal)) ->
        repr_val_LambdaANF_Wasm v sr fi wal ->

        (* following constr args are also related *)
        repr_val_constr_args_LambdaANF_Wasm vs sr fi (4 + addr) ->
        repr_val_constr_args_LambdaANF_Wasm (v::vs) sr fi addr.

Scheme repr_val_LambdaANF_Wasm_mut := Induction for repr_val_LambdaANF_Wasm Sort Prop
  with repr_val_constr_args_LambdaANF_Wasm_mut :=
    Induction for repr_val_constr_args_LambdaANF_Wasm Sort Prop.

Lemma val_relation_func_depends_on_funcs : forall val s s' fi i,
  s_funcs s = s_funcs s' ->
  repr_val_LambdaANF_Wasm val s  fi (Val_funidx i) ->
  repr_val_LambdaANF_Wasm val s' fi (Val_funidx i).
Proof.
  intros ? ? ? ? ? Hfuncs Hval.
  inv Hval. now econstructor; eauto.
Qed.


(* TODO move somewhere else *)
Ltac simpl_eq :=
  repeat lazymatch goal with
  | H: nat_to_i32 _ = nat_to_i32 _ |- _ =>
        injection H as H
  | H: _ = Wasm_int.Int32.Z_mod_modulus _ |- _ =>
         rewrite Wasm_int.Int32.Z_mod_modulus_id in H; last lia
  | H: Wasm_int.Int32.Z_mod_modulus _ = _ |- _ =>
          rewrite Wasm_int.Int32.Z_mod_modulus_id in H; last lia
  | H: Z.of_nat _ = Z.of_nat _ |- _ =>
         apply Nat2Z.inj in H
  end.

Ltac solve_eq_global x y :=
  assert (x = y); first
    (try assert (nat_to_i32 x = nat_to_i32 y) by congruence; simpl_eq; done); subst y.

(* TODO add case when global was updated etc. *)
Ltac solve_eq_mem m1 m2 :=
  assert (m1 = m2) by congruence; subst m2.

(* proves and substitutes equality on given vars, the first one is kept *)
Ltac solve_eq x y :=
  lazymatch goal with
  (* equality on global mems *)
  | H: nth_error (s_mems ?s) 0 = Some x |- _ => solve_eq_mem x y
  (* equality on globals *)
  | H: _ |- _ => solve_eq_global x y
  end.

Lemma val_relation_depends_on_mem_smaller_than_gmp_and_funcs :
  forall v sr sr' m m' fi gmp gmp' value,
    sr.(s_funcs) = sr'.(s_funcs) ->
    nth_error sr.(s_mems)  0 = Some m ->
    nth_error sr'.(s_mems) 0 = Some m' ->
    (* memories agree on values < gmp *)
    sglob_val sr fi global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
    (Z.of_nat gmp + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
    sglob_val sr' fi global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp')) ->
    (Z.of_nat gmp' + 8 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
    gmp' >= gmp ->
    (forall a, (a + 4 <= N.of_nat gmp)%N -> load_i32 m a = load_i32 m' a) ->
    (forall a, (a + 8 <= N.of_nat gmp)%N -> load_i64 m a = load_i64 m' a) ->

    repr_val_LambdaANF_Wasm v sr fi value ->
    repr_val_LambdaANF_Wasm v sr' fi value.
Proof.
  intros. inv H9.
  (* Nullary constructor value *)
  { now constructor.  }
  (* Non-nullary constructor value *)
  {
  have indPrinciple := repr_val_constr_args_LambdaANF_Wasm_mut
  (fun (v : cps.val) (s : datatypes.store_record host_function) (fi : instance) (w : wasm_value)
       (H: repr_val_LambdaANF_Wasm v s fi w) =>
       (forall a s' m m',
          s_funcs s = s_funcs s' ->
          nth_error s.(s_mems) 0 = Some m ->
          nth_error s'.(s_mems) 0 = Some m' ->
          (* memories agree on values < gmp *)
          sglob_val s fi global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
          (Z.of_nat gmp + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
          sglob_val s' fi global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp')) ->
          (Z.of_nat gmp' + 8 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
          gmp' >= gmp ->
          (forall a, (a + 4<= N.of_nat gmp)%N -> load_i32 m a = load_i32 m' a) ->
          (forall a, (a + 8<= N.of_nat gmp)%N -> load_i64 m a = load_i64 m' a) ->
              repr_val_LambdaANF_Wasm v s' fi w)
    )
  (fun (l : seq cps.val) (s : datatypes.store_record host_function) (fi : instance) (i : immediate)
       (H: repr_val_constr_args_LambdaANF_Wasm l s fi i) =>
       (forall a s' m m',
          s_funcs s = s_funcs s' ->
          nth_error s.(s_mems) 0 = Some m ->
          nth_error s'.(s_mems) 0 = Some m' ->
          (* memories agree on values < gmp *)
          sglob_val s fi global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
          (Z.of_nat gmp + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
          sglob_val s' fi global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp')) ->
          (Z.of_nat gmp' + 8 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
          gmp' >= gmp ->
          (forall a, (a + 4 <= N.of_nat gmp)%N -> load_i32 m a = load_i32 m' a) ->
          (forall a, (a + 8 <= N.of_nat gmp)%N -> load_i64 m a = load_i64 m' a) ->
             repr_val_constr_args_LambdaANF_Wasm l s' fi i)
  ). have H19' := H19.
    eapply indPrinciple in H19; intros; clear indPrinciple; try eassumption; try lia.
    { solve_eq gmp0 gmp.
      solve_eq m m0.
      econstructor; try eassumption. lia. lia. reflexivity.
      rewrite <- H7. assumption. lia. }
    { now constructor. }
    { solve_eq gmp gmp0. solve_eq gmp gmp1.
      solve_eq m m0. solve_eq m1 m2.
      econstructor; eauto. lia. rewrite <- H27; auto; try lia. }
    { econstructor; eauto. congruence. }
    { econstructor; eauto.
      solve_eq gmp gmp1. lia.
      solve_eq m1 m2. rewrite <- H27. assumption. solve_eq gmp gmp1. lia. }
    { econstructor. }
    { solve_eq gmp gmp0. solve_eq gmp gmp1.
      econstructor; eauto; try lia.
      rewrite <- H28. assert (m1 = m2) by congruence. subst m2. eassumption.
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
Definition result_val_LambdaANF_Wasm (val : LambdaANF.cps.val)
                                        (sr : store_record) (fi : instance) : Prop :=

     (exists res_i32 wasmval,
       (* global var *result_var* contains correct return value *)
       sglob_val sr fi result_var = Some (VAL_int32 res_i32)
         /\ wasm_value_to_i32 wasmval = res_i32
         /\ repr_val_LambdaANF_Wasm val sr fi wasmval
         /\ (sglob_val sr fi result_out_of_mem = Some (nat_to_value 0)))
  \/ (sglob_val sr fi result_out_of_mem = Some (nat_to_value 1)).


(* ENVIRONMENT RELATION (also named memory relation in C-backend) *)

Definition stored_in_locals {lenv} (x : cps.var) (v : wasm_value) (f : frame ) :=
  exists i,
  (forall err, translate_var nenv lenv x err = Ret i) /\
  List.nth_error f.(f_locs) i = Some (VAL_int32 (wasm_value_to_i32 v)).

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

Definition globals_all_mut_i32 s := forall g g0,
  nth_error (@s_globals host_function s) g = Some g0 ->
  exists i, g0 = {| g_mut := MUT_mut; g_val := VAL_int32 i |}.

Definition global_var_w var (s : store_record) (f : frame) := forall val,
  exists s', @supdate_glob host_function s (f_inst f) var (VAL_int32 val) = Some s'.

Definition global_var_r var (s : store_record) (f : frame) :=
   exists v, @sglob_val host_function s (f_inst f) var = Some (VAL_int32 v).

Definition INV_result_var_writable := global_var_w result_var.
Definition INV_result_var_out_of_mem_writable := global_var_w result_out_of_mem.
Definition INV_global_mem_ptr_writable := global_var_w global_mem_ptr.
Definition INV_constr_alloc_ptr_writable := global_var_w constr_alloc_ptr.
Definition INV_globals_all_mut_i32 := globals_all_mut_i32.

(* indicates all good *)
Definition INV_result_var_out_of_mem_is_zero s f :=
  @sglob_val host_function s (f_inst f) result_out_of_mem = Some (VAL_int32 (nat_to_i32 0)).

Definition INV_linear_memory sr fr :=
      smem_ind (host_function:=host_function) sr (f_inst fr) = Some 0
   /\ exists m, nth_error (s_mems sr) 0 = Some m
   /\ exists size, mem_size m = size
   /\ mem_max_opt m = Some max_mem_pages
   /\ (size <= max_mem_pages)%N.

Definition INV_global_mem_ptr_in_linear_memory s f := forall gmp_v m,
  nth_error (s_mems s) 0 = Some m ->
  @sglob_val host_function s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp_v)) ->
  (-1 < Z.of_nat gmp_v < Wasm_int.Int32.modulus)%Z ->
  (* enough space to store an i32 *)
  (N.of_nat gmp_v + 8 <= mem_length m)%N.

Definition INV_constr_alloc_ptr_in_linear_memory s f := forall addr t m,
  @sglob_val host_function s (f_inst f) constr_alloc_ptr = Some (VAL_int32 addr) ->
  exists m', store m (Wasm_int.N_of_uint i32m addr) 0%N
                     (bits (nat_to_value (Pos.to_nat t))) (t_length T_i32) = Some m'.

Definition INV_locals_all_i32 f := forall i v,
  nth_error (f_locs f) i = Some v -> exists v', v = (VAL_int32 v').

Definition INV_num_functions_bounds sr :=
  (Z.of_nat num_custom_funs <= Z.of_nat (length (@s_funcs host_function sr)) < Wasm_int.Int32.modulus)%Z.

Definition INV_inst_globs_nodup f :=
  NoDup (inst_globs (f_inst f)).

Definition INV_table_id sr fr :=
  forall f i errMsg,
    translate_var nenv fenv f errMsg = Ret i ->
    stab_addr (host_function:=host_function) sr fr
      (Wasm_int.nat_of_uint i32m (nat_to_i32 i)) = Some i.

Definition INV_fvar_idx_inbounds sr :=
  forall fvar fIdx, repr_funvar fvar fIdx ->
                    fIdx < length (s_funcs (host_function:=host_function) sr).

Definition INV_types sr fr :=
  forall i, (Z.of_nat i <= max_function_args)%Z ->
            stypes (host_function:=host_function) sr (f_inst fr) i =
              Some (Tf (List.repeat T_i32 i) [::]).

Definition INV_global_mem_ptr_multiple_of_two s f := forall gmp_v m,
  nth_error (s_mems s) 0 = Some m ->
  @sglob_val host_function s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp_v)) ->
  (-1 < Z.of_nat gmp_v < Wasm_int.Int32.modulus)%Z ->
  exists n, gmp_v = 2 * n.

Definition INV_exists_func_grow_mem sr fr :=
  nth_error sr.(s_funcs) grow_mem_function_idx =
    Some (@FC_func_native host_function (f_inst fr) (Tf [T_i32] []) [] grow_memory_if_necessary).

Definition INV_inst_funcs_id sr f := forall i,
   i < length (@s_funcs host_function sr) ->
  nth_error (inst_funcs (f_inst f)) i = Some i.

(* invariants that need to hold throughout the execution of the Wasm program,
   doesn't hold anymore when memory runs out -> just abort

   also depends on fenv, shouldn't depend on lenv *)
Definition INV (s : store_record) (f : frame) :=
    INV_result_var_writable s f
 /\ INV_result_var_out_of_mem_writable s f
 /\ INV_result_var_out_of_mem_is_zero s f
 /\ INV_global_mem_ptr_writable s f
 /\ INV_constr_alloc_ptr_writable s f
 /\ INV_globals_all_mut_i32 s
 /\ INV_linear_memory s f
 /\ INV_global_mem_ptr_in_linear_memory s f
 /\ INV_locals_all_i32 f
 /\ INV_num_functions_bounds s
 /\ INV_inst_globs_nodup f
 /\ INV_table_id s f
 /\ INV_types s f
 /\ INV_global_mem_ptr_multiple_of_two s f
 /\ INV_exists_func_grow_mem s f
 /\ INV_inst_funcs_id s f.

Lemma update_global_preserves_globals_all_mut_i32 : forall sr sr' i f num,
  globals_all_mut_i32 sr ->
  supdate_glob sr (f_inst f) i (VAL_int32 num) = Some sr' ->
  globals_all_mut_i32 sr'.
Proof.
  intros. unfold globals_all_mut_i32 in *. intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H0.
  destruct (nth_error (inst_globs (f_inst f)) i) eqn:Heqn. 2: inv H0. cbn in H0.
  destruct (nth_error (s_globals sr) g1) eqn:Heqn'. 2: inv H0. inv H0. cbn in H1.
  destruct (Nat.lt_total g g1) as [Heq | [Heq | Heq]].
  - (* g < g1 *)
    erewrite set_nth_nth_error_other in H1; eauto. lia. apply nth_error_Some. congruence.
  - (* g = g1 *)
    subst. erewrite set_nth_nth_error_same in H1; eauto. inv H1.
    assert (g_mut g2 = MUT_mut). { apply H in Heqn'. destruct Heqn'. subst. reflexivity. }
    rewrite H0. eauto.
  - (* g1 < g *)
    rewrite set_nth_nth_error_other in H1. eauto. lia.
    apply nth_error_Some. intro. congruence.
Qed.

Lemma update_global_preserves_global_var_w : forall i j sr sr' f num,
  global_var_w i sr f ->
  supdate_glob sr (f_inst f) j (VAL_int32 num) = Some sr' ->
  global_var_w i sr' f.
Proof.
  intros ? ? ? ? ? ? HG. unfold global_var_w. intro. unfold global_var_w in HG.
    unfold supdate_glob, sglob_ind, supdate_glob_s in *.
    destruct (nth_error (inst_globs (f_inst f)) i) eqn:Heqn. cbn in HG. 2: cbn in HG; eauto.
    cbn in HG. destruct (nth_error (s_globals sr) g) eqn:Heqn'.
    { cbn in H. edestruct HG as [? H1]. clear H1.
      destruct (nth_error (inst_globs (f_inst f)) j) eqn:Heqn''. 2: inv H. cbn in H.
      destruct (nth_error (s_globals sr) g1) eqn:Heqn'''. 2: inv H. cbn in H. inv H. cbn.
      destruct (nth_error
       (set_nth _ (s_globals sr) g1 {| g_mut := g_mut g2; g_val := VAL_int32 num |}) g) eqn:Heqn''''. cbn. intro. eauto.
       exfalso. cbn in HG.
     assert (g1 < length (s_globals sr)) as Hl. { apply nth_error_Some. intro. congruence. }
     apply nth_error_Some in Heqn''''. congruence.
     erewrite nth_error_set_nth_length. apply nth_error_Some. congruence.
     eassumption. }
     cbn in HG. edestruct HG. eauto. inv H0.
     Unshelve. auto.
Qed.

Lemma update_global_preserves_result_var_out_of_mem_is_zero : forall i sr sr' f num,
  INV_result_var_out_of_mem_is_zero sr f ->
  INV_inst_globs_nodup f ->
  result_out_of_mem <> i ->
  supdate_glob sr (f_inst f) i (VAL_int32 num) = Some sr' ->
  INV_result_var_out_of_mem_is_zero sr' f.
Proof.
  unfold INV_result_var_out_of_mem_is_zero. intros.
  eapply update_global_get_other; eauto.
Qed.

Lemma update_global_preserves_linear_memory : forall j sr sr' f  num,
  INV_linear_memory sr f ->
  supdate_glob sr (f_inst f) j (VAL_int32 num) = Some sr' ->
  INV_linear_memory sr' f.
Proof.
  intros.
  unfold supdate_glob, sglob_ind, supdate_glob_s in H0.
  destruct (nth_error (inst_globs (f_inst f))) eqn:Heqn. 2: inv H0. cbn in H0.
  destruct (nth_error (s_globals sr) g). 2: inv H0. cbn in H0. inv H0.
  assumption.
Qed.

Lemma update_global_preserves_num_functions_bounds : forall j sr sr' f  num,
  INV_num_functions_bounds sr ->
  supdate_glob sr (f_inst f) j (VAL_int32 num) = Some sr' ->
  INV_num_functions_bounds sr'.
Proof.
  unfold INV_num_functions_bounds. intros.
  assert (s_funcs sr = s_funcs sr') as Hfuncs. {
   unfold supdate_glob, supdate_glob_s in H0.
   destruct (sglob_ind sr (f_inst f) j). 2:inv H0. cbn in H0.
   destruct (nth_error (s_globals sr) n). 2: inv H0. inv H0. reflexivity. }
   rewrite Hfuncs in H. apply H.
Qed.

Lemma update_global_preserves_global_mem_ptr_in_linear_memory : forall j sr sr' f m num,
  INV_global_mem_ptr_in_linear_memory sr f ->
  INV_inst_globs_nodup f ->
  nth_error (s_mems sr) 0 = Some m ->
  (-1 < Z.of_nat num < Wasm_int.Int32.modulus)%Z ->
  (j = global_mem_ptr -> num + 8 < N.to_nat (mem_length m)) ->
  @supdate_glob host_function sr (f_inst f) j (VAL_int32 (nat_to_i32 num)) = Some sr' ->
  INV_global_mem_ptr_in_linear_memory sr' f.
Proof.
  unfold INV_global_mem_ptr_in_linear_memory.
  intros ? ? ? ? ? ? Hinv Hnodup Hmem Hnum Hcond Hupd ? ? Hm Hglob Hunbound.
  assert (m = m0). { apply update_global_preserves_memory in Hupd. congruence. }
  subst m0. destruct (Nat.eq_dec j global_mem_ptr).
  { (* g = global_mem_ptr *)
     subst. have H' := update_global_get_same _ _ _ _ _ _ Hupd.
     rewrite H' in Hglob. inv Hglob.
     repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H0; lia. }
  { (* g <> global_mem_ptr *)
    assert (Hgmp_r : @sglob_val host_function sr (f_inst f)
                     global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp_v))). {
    unfold sglob_val, sglob, sglob_ind in Hglob.
    unfold sglob_val, sglob, sglob_ind.
    destruct (nth_error (inst_globs (f_inst f)) global_mem_ptr) eqn:Heqn.
      2: inv Hglob. cbn in Hglob.
    destruct (nth_error (s_globals sr') g) eqn:Heqn'; inv Hglob. cbn.
    unfold supdate_glob, supdate_glob_s, sglob_ind in Hupd.
    destruct (nth_error (inst_globs (f_inst f)) j) eqn:Heqn''. 2: inv Hupd.
    cbn in Hupd. destruct (nth_error (s_globals sr) g1) eqn:Heqn'''; inv Hupd.
    cbn in Heqn'. erewrite set_nth_nth_error_other in Heqn'; eauto.
    rewrite Heqn'. reflexivity. intro. subst. apply n.
    eapply NoDup_nth_error; eauto; try congruence.
    now apply nth_error_Some. now apply nth_error_Some. } auto. }
Qed.

Lemma update_global_preserves_table_id : forall j sr sr' f m num,
  INV_table_id sr f ->
  INV_inst_globs_nodup f ->
  nth_error (s_mems sr) 0 = Some m ->
  (-1 < Z.of_nat num < Wasm_int.Int32.modulus)%Z ->
  (j = global_mem_ptr -> num + 8 < N.to_nat (mem_length m)) ->
  supdate_glob sr (f_inst f) j (VAL_int32 (nat_to_i32 num)) = Some sr' ->
  INV_table_id sr' f.
Proof.
  unfold INV_table_id, stab_addr. intros.
  apply H in H5.
  destruct (inst_tab (f_inst f)). inv H5. rewrite -H5.
  unfold supdate_glob, supdate_glob_s in H4.
  destruct (sglob_ind (host_function:=host_function) sr (f_inst f) j). 2: inv H4.
  cbn in H4. destruct (nth_error (s_globals sr) n); inv H4. reflexivity.
Qed.

Lemma update_global_preserves_types : forall j sr sr' f m num,
  INV_types sr f ->
  INV_inst_globs_nodup f ->
  nth_error (s_mems sr) 0 = Some m ->
  (-1 < Z.of_nat num < Wasm_int.Int32.modulus)%Z ->
  (j = global_mem_ptr -> num + 8 < N.to_nat (mem_length m)) ->
  supdate_glob (host_function:=host_function) sr (f_inst f) j
             (VAL_int32 (nat_to_i32 num)) = Some sr' ->
  INV_types sr' f.
Proof.
  unfold INV_types, stab_addr. intros.
  apply H in H5. rewrite -H5.
  unfold supdate_glob, supdate_glob_s in H4.
  destruct (sglob_ind (host_function:=host_function) sr (f_inst f) j). 2: inv H4.
  cbn in H4. destruct (nth_error (s_globals sr) n); inv H4. reflexivity.
Qed.

Lemma update_global_preserves_global_mem_ptr_multiple_of_two : forall j sr sr' f m num,
    INV_global_mem_ptr_multiple_of_two sr f ->
    INV_inst_globs_nodup f ->
    nth_error (s_mems sr) 0 = Some m ->
    (-1 < Z.of_nat num < Wasm_int.Int32.modulus)%Z ->
    (j = global_mem_ptr -> num + 8 < N.to_nat (mem_length m) /\ exists n, num = 2  * n) ->
    @supdate_glob host_function sr (f_inst f) j (VAL_int32 (nat_to_i32 num)) = Some sr' ->
    INV_global_mem_ptr_multiple_of_two sr' f.
Proof.
  unfold INV_global_mem_ptr_multiple_of_two.
  intros j sr sr' f m num. intros Hinv Hnodups Hnth Hrange Hj Hupd.
  intros gmp_v m0 ? Hglob Hrange'.
  assert (m = m0). { apply update_global_preserves_memory in Hupd. congruence. }
  subst m0. destruct (Nat.eq_dec j global_mem_ptr).
  { (* g = global_mem_ptr *)
     subst. have H' := update_global_get_same _ _ _ _ _ _ Hupd.
     rewrite H' in Hglob. injection Hglob as Hglob. solve_eq num gmp_v.
     assert (num + 8 < N.to_nat (mem_length m) /\ (exists n : nat, num = 2 * n)) by now apply Hj.
     destruct H0 as [_ [n Hn]]. by exists n.
  }
  { (* g <> global_mem_ptr *)
    assert (Hgmp_r : @sglob_val host_function sr (f_inst f)
                     global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp_v))). {
    unfold sglob_val, sglob, sglob_ind in Hglob.
    unfold sglob_val, sglob, sglob_ind.
    destruct (nth_error (inst_globs (f_inst f)) global_mem_ptr) eqn:Heqn.
      2: inv Hglob. cbn in Hglob.
    destruct (nth_error (s_globals sr') g) eqn:Heqn'; inv Hglob. cbn.
    unfold supdate_glob, supdate_glob_s, sglob_ind in Hupd.
    destruct (nth_error (inst_globs (f_inst f)) j) eqn:Heqn''. 2: inv Hupd.
    cbn in Hupd. destruct (nth_error (s_globals sr) g1) eqn:Heqn'''; inv Hupd.
    cbn in Heqn'. erewrite set_nth_nth_error_other in Heqn'; eauto.
    rewrite Heqn'. reflexivity. intro. subst. apply n.
    eapply NoDup_nth_error; eauto; try congruence.
    now apply nth_error_Some. now apply nth_error_Some. }
    eapply Hinv; eauto.
  }
Qed.

Lemma update_global_preserves_exists_func_grow_mem : forall j sr sr' fr f  num,
  INV_exists_func_grow_mem sr fr ->
  supdate_glob sr (f_inst f) j (VAL_int32 num) = Some sr' ->
  INV_exists_func_grow_mem sr' fr.
Proof.
  unfold INV_exists_func_grow_mem. intros.
  assert (s_funcs sr = s_funcs sr') as Hfuncs. {
   unfold supdate_glob, supdate_glob_s in H0.
   destruct (sglob_ind sr (f_inst f) j). 2:inv H0. cbn in H0.
   destruct (nth_error (s_globals sr) n). 2: inv H0. inv H0. reflexivity. }
   rewrite Hfuncs in H. apply H.
Qed.

Lemma update_global_preserves_inst_funcs_id : forall j sr sr' fr f  num,
  INV_inst_funcs_id sr fr ->
  supdate_glob sr (f_inst f) j (VAL_int32 num) = Some sr' ->
  INV_inst_funcs_id sr' fr.
Proof.
  unfold INV_inst_funcs_id. intros.
  assert (s_funcs sr = s_funcs sr') as Hfuncs. {
   unfold supdate_glob, supdate_glob_s in H0.
   destruct (sglob_ind sr (f_inst f) j). 2:inv H0. cbn in H0.
   destruct (nth_error (s_globals sr) n). 2: inv H0. inv H0. reflexivity. }
   rewrite Hfuncs in H. by apply H.
Qed.

Corollary update_global_preserves_INV : forall sr sr' i f m num,
  INV sr f ->
  (* if result_out_of_mem is set, INV doesn't need to hold anymore *)
  result_out_of_mem <> i ->
  (* if updated gmp, new value in mem *)
  nth_error (s_mems sr) 0 = Some m ->
  (-1 < Z.of_nat num < Wasm_int.Int32.modulus)%Z ->
  (i = global_mem_ptr -> num + 8 < N.to_nat (mem_length m)) ->
  (i = global_mem_ptr -> exists n, num = 2 * n) ->
  (* upd. global var *)
  supdate_glob (host_function:=host_function) sr (f_inst f) i
             (VAL_int32 (nat_to_i32 num)) = Some sr' ->
  INV sr' f.
Proof with eassumption.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]].
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_result_var_out_of_mem_is_zero...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_globals_all_mut_i32...
  split. eapply update_global_preserves_linear_memory...
  split. eapply update_global_preserves_global_mem_ptr_in_linear_memory...
  split. assumption.
  split. eapply update_global_preserves_num_functions_bounds...
  split. assumption.
  split. eapply update_global_preserves_table_id...
  split. eapply update_global_preserves_types...
  split. now eapply update_global_preserves_global_mem_ptr_multiple_of_two.
  split. eapply update_global_preserves_exists_func_grow_mem...
  eapply update_global_preserves_inst_funcs_id...
Qed.

Corollary update_local_preserves_INV : forall sr f f' x' v,
  INV sr f ->
  x' < length (f_locs f) ->
  f' = {| f_locs := set_nth (VAL_int32 v) (f_locs f) x' (VAL_int32 v)
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
  f' = {| f_locs := [seq nat_to_value i | i <- args] ++
                      repeat (nat_to_value 0) n
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
      assert (Hlen: i < Datatypes.length ([seq nat_to_value i | i <- args]
                                          ++ repeat (nat_to_value 0) n)). {
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
Lemma global_var_w_implies_global_var_r : forall (s : store_record) inst var,
  globals_all_mut_i32 s -> global_var_w var s inst -> global_var_r var s inst.
Proof.
  intros s inst i Hmut32 GVW.
  destruct exists_i32 as [x _].
  unfold global_var_w in GVW. edestruct GVW. unfold supdate_glob, sglob_ind in H.
  unfold global_var_r, sglob_val, sglob, sglob_ind.
  destruct ((nth_error (inst_globs (f_inst inst)) i)) eqn:Hv. 2: inv H.
  cbn in H. cbn. unfold supdate_glob_s in H.
  destruct (nth_error (s_globals s) g) eqn:Hg. 2: inv H. cbn.
  apply Hmut32 in Hg. destruct Hg. inv H0. eexists. reflexivity. Unshelve. assumption.
Qed.

Lemma update_mem_preserves_global_var_w : forall i s f s' m vd,
   global_var_w i s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   global_var_w i s' f.
Proof.
  destruct exists_i32 as [x _].
  intros. unfold upd_s_mem in H0. subst. edestruct H. unfold global_var_w. intro.
  unfold supdate_glob, sglob_ind, supdate_glob_s in *. cbn in *.
  destruct (nth_error (inst_globs (f_inst f)) i). 2: inv H0. cbn in *.
  destruct (nth_error (s_globals s) g). 2: inv H0. cbn in *. eexists. reflexivity.
  Unshelve. assumption.
Qed.

Lemma update_mem_preserves_result_var_out_of_mem_is_zero : forall s f s' m vd,
   INV_result_var_out_of_mem_is_zero s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_result_var_out_of_mem_is_zero s' f.
Proof.
  unfold INV_result_var_out_of_mem_is_zero, sglob_val, sglob, sglob_ind, nat_to_i32.
  intros. subst. cbn in *.
  destruct (inst_globs (f_inst f)). inv H.
  destruct l. inv H. destruct l. inv H. destruct l. inv H. assumption.
Qed.

Lemma update_mem_preserves_all_mut_i32 : forall s s' m vd,
   globals_all_mut_i32 s  ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   globals_all_mut_i32 s'.
Proof.
  unfold globals_all_mut_i32. intros.
  unfold upd_s_mem in H0. assert (s_globals s = s_globals s') as Hglob. {
   subst. destruct s. reflexivity. }
  rewrite Hglob in H. apply H in H1. destruct H1 as [i Hi]. eauto.
Qed.

Lemma update_mem_preserves_linear_memory : forall s s' f m vd,
   INV_linear_memory s f  ->
   mem_max_opt m = Some max_mem_pages ->
   (exists size, mem_size m = size /\ size <= max_mem_pages)%N ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_linear_memory s' f.
Proof.
  unfold INV_linear_memory.
  intros s s' f m vd [H [m' [H1 [size [H2 [H3 H4]]]]]] H' [size' [H6 H7]].
  split. assumption. exists m. split. subst.
  cbn. destruct (s_mems s); inv H1. reflexivity.
   exists size'. repeat split; auto.
Qed.

Lemma update_mem_preserves_global_mem_ptr_in_linear_memory : forall s s' f m m',
   INV_global_mem_ptr_in_linear_memory s f ->
   INV_global_mem_ptr_writable s f ->
   INV_globals_all_mut_i32 s ->
   nth_error (s_mems s) 0  = Some m ->
   (mem_length m' >= mem_length m)%N ->
   upd_s_mem s (set_nth m' (s_mems s) 0 m') = s' ->
   INV_global_mem_ptr_in_linear_memory s' f.
Proof.
  unfold INV_global_mem_ptr_in_linear_memory.
  intros ? ? ? ? ? H Hinv Hinv' ? ? ? ? ? ? ? ?. subst.
  cbn in H3. destruct (s_mems s); inv H0. inv H3.
  eapply update_mem_preserves_global_var_w in Hinv; eauto.
  apply global_var_w_implies_global_var_r in Hinv.
    2: now eapply update_mem_preserves_all_mut_i32.
  assert (N.of_nat gmp_v + 8 <= mem_length m)%N. { apply H; auto. } lia.
  Unshelve. assumption. assumption.
Qed.

Lemma update_mem_preserves_global_constr_alloc_ptr_in_linear_memory : forall s s' f m m' vd,
   INV_constr_alloc_ptr_in_linear_memory s f  ->
   INV_constr_alloc_ptr_writable s f ->
   INV_globals_all_mut_i32 s ->
   nth_error (s_mems s) 0  = Some m ->
   (mem_length m' >= mem_length m)%N ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m') = s' ->
   INV_constr_alloc_ptr_in_linear_memory s' f.
Proof.
  unfold INV_constr_alloc_ptr_in_linear_memory.
  intros ? ? ? ? ? ? H Hinv Hinv' ? ? ? ? ? ? ?.
  eapply update_mem_preserves_global_var_w in Hinv; eauto.
  apply global_var_w_implies_global_var_r in Hinv.
  unfold global_var_r in Hinv. destruct Hinv as [v Hv]. rewrite H3 in Hv. inv Hv.
  eapply H in H3; eauto. now eapply update_mem_preserves_all_mut_i32.
Qed.

Lemma update_mem_preserves_num_functions_bounds : forall s s' m vd,
   INV_num_functions_bounds s  ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_num_functions_bounds s'.
Proof.
  unfold INV_num_functions_bounds. intros. subst. cbn. assumption.
Qed.

Lemma update_mem_preserves_table_id : forall s s' f m vd,
   INV_table_id s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_table_id s' f.
Proof.
  unfold INV_table_id. intros. subst. apply H in H1. rewrite -H1. reflexivity.
Qed.

Lemma update_mem_preserves_types : forall s s' f m vd,
   INV_types s f ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_types s' f.
Proof.
  unfold INV_types. intros. subst. apply H in H1. rewrite -H1. reflexivity.
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
   nth_error (s_mems s) 0  = Some m ->
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
  nth_error (s_mems s) 0  = Some m ->
  (mem_length m' >= mem_length m)%N ->
  mem_max_opt m' = Some max_mem_pages ->
  (exists size, mem_size m' = size /\ size <= max_mem_pages)%N ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m') = s' ->
  INV s' f.
Proof with eassumption.
  intros. unfold INV.
  destruct H as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]].
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_result_var_out_of_mem_is_zero...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_all_mut_i32...
  split. eapply update_mem_preserves_linear_memory...
  split. eapply update_mem_preserves_global_mem_ptr_in_linear_memory...
  split. assumption.
  split. eapply update_mem_preserves_num_functions_bounds...
  split. assumption.
  split. eapply update_mem_preserves_table_id...
  split. eapply update_mem_preserves_types...
  split. eapply update_mem_preserves_global_mem_ptr_multiple_of_two...
  split. eapply update_mem_preserves_exists_func_grow_mem...
  eapply update_mem_preserves_inst_funcs_id...
Qed.


(** The lemmas [r_eliml] and [r_elimr] are relicts,
    kept for compatability for now, TODO rework (use new context representation) **)
Lemma r_eliml : forall hs s f es hs' s' f' es' lconst,
  const_list lconst ->
  reduce (host_instance := host_instance) hs s f es hs' s' f' es' ->
  reduce hs s f (lconst ++ es) hs' s' f' (lconst ++ es').
Proof.
  move => hs s f es hs' s' f' es' lconst HConst H.
  apply const_es_exists in HConst. destruct HConst as [vs ?].
  eapply r_label with (lh:=LH_base vs []). eassumption.
  - cbn. rewrite cats0. congruence.
  - cbn. rewrite cats0. congruence.
Qed.

Lemma r_elimr: forall hs s f es hs' s' f' es' les,
    reduce (host_instance := host_instance) hs s f es hs' s' f' es' ->
    reduce hs s f (es ++ les) hs' s' f' (es' ++ les).
Proof.
  move => hs s f es hs' s' f' es' les H.
  eapply r_label with (lh:=LH_base [] les); eauto.
Qed.

Lemma reduce_trans_label' : forall instr instr' hs hs' sr sr' fr fr' i (lh : lholed i),
 clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction)
 (reduce_tuple (host_instance:=host_instance))
 (hs,  sr, fr, instr)
 (hs', sr', fr', instr') ->

  clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction) (reduce_tuple (host_instance:=host_instance))
  (hs,  sr,  fr,  lfill lh instr)
  (hs', sr', fr', lfill lh instr').
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
 clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction)
 (reduce_tuple (host_instance:=host_instance))
 (hs,  sr, fr, instr)
 (hs', sr', fr', []) ->

  clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction) (reduce_tuple (host_instance:=host_instance))
  (hs,  sr, fr, [:: AI_label 0 [::] instr])
  (hs', sr', fr', [::]).
Proof.
  intros.
  remember (LH_rec [] 0 [] (LH_base [] []) []) as lh.
  have H' := reduce_trans_label' instr [] _ _ _ _ _ _ _ lh. subst lh. cbn in H'.
  rewrite cats0 in H'. eapply rt_trans. eapply H'; auto. eassumption.
  eapply rt_step. constructor. now apply rs_label_const.
Qed.

Lemma reduce_trans_label0 : forall instr instr' hs hs' sr sr' fr fr',
 clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction)
 (reduce_tuple (host_instance:=host_instance))
 (hs,  sr, fr, instr)
 (hs', sr', fr', instr') ->

  clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction) (reduce_tuple (host_instance:=host_instance))
  (hs,  sr, fr, [:: AI_label 0 [::] instr])
  (hs', sr', fr', [:: AI_label 0 [::] instr']).
Proof.
  intros.
  remember (LH_rec [] 0 [] (LH_base [] []) []) as lh.
  have H' := reduce_trans_label' instr instr' _ _ _ _ _ _ _ lh. subst lh. cbn in H'.
  do 2! rewrite cats0 in H'. eapply rt_trans. eapply H'; auto. eassumption.
  apply rt_refl.
Qed.

Lemma reduce_trans_local : forall instructions hs hs' sr sr' fr fr' f0,
 clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction)
 (reduce_tuple (host_instance:=host_instance))
 (hs,  sr, fr, instructions)
 (hs', sr', fr', []) ->

  clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction) (reduce_tuple (host_instance:=host_instance))
  (hs,  sr, f0, [:: AI_local 0 fr instructions])
  (hs', sr', f0, [::]).
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
    eapply rt_step. eapply r_local. apply H.
    now eapply IHclos_refl_trans_1n.
Qed.

(* TODO rename and consolidate lemmas above *)
Lemma reduce_trans_local' : forall instr instr' hs hs' sr sr' fr fr' f0,
 clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction)
 (reduce_tuple (host_instance:=host_instance))
 (hs,  sr, fr, instr)
 (hs', sr', fr', instr') ->

  clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction) (reduce_tuple (host_instance:=host_instance))
  (hs,  sr, f0, [:: AI_local 0 fr instr])
  (hs', sr', f0, [:: AI_local 0 fr' instr']).
Proof.
  intros.
  apply clos_rt_rt1n in H.
  remember (hs, sr, fr, instr) as x. remember (hs', sr', fr', instr') as x'.
  generalize dependent hs. generalize dependent hs'. revert instr instr' fr fr' f0 sr sr'.
  induction H; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[? ?] ?] ?].
    have IH := IHclos_refl_trans_1n _ _ _ _ _ _ _ _ Logic.eq_refl _ Logic.eq_refl.
    eapply rt_trans with (y := (?[hs], ?[sr], f0, [:: AI_local 0 ?[f'] ?[instr]])).
    2: by apply IH.
    eapply rt_step. now eapply r_local.
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
         | |- reduce _ _ _ ([::AI_basic (BI_const ?c1)] ++ [:: ?instr])        _ _ _ _ => idtac
         | |- reduce _ _ _ ([::AI_basic (BI_const ?c1)] ++ [:: ?instr] ++ ?l3) _ _ _ _ =>
            assert ([:: AI_basic (BI_const c1)] ++ [:: instr] ++ l3 =
                    [:: AI_basic (BI_const c1); instr] ++ l3) as H by reflexivity; rewrite H;
                                                       apply r_elimr; clear H
         end
  | 2 => lazymatch goal with
         | |- reduce _ _ _ ([::AI_basic (BI_const ?c1)] ++ [::AI_basic (BI_const ?c2)] ++ [:: ?instr])        _ _ _ _ => idtac
         | |- reduce _ _ _ ([::AI_basic (BI_const ?c1)] ++ [::AI_basic (BI_const ?c2)] ++ [:: ?instr] ++ ?l3) _ _ _ _ =>
            assert ([:: AI_basic (BI_const c1)] ++ [:: AI_basic (BI_const c2)] ++ [:: instr] ++ l3 =
                    [:: AI_basic (BI_const c1); AI_basic (BI_const c2); instr] ++ l3) as H by reflexivity; rewrite H;
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

Ltac dostep_nary' n :=
  dostep'; first elimr_nary_instr n.

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
  load m (N.of_nat addr) 0%N 4 = Some b ->
  (-1 < decode_int b < Wasm_int.Int32.modulus)%Z.
Proof.
  intros.
  (* length b = 4 bytes *)
  unfold load, those in H.
  destruct (N.of_nat addr + (0 + N.of_nat 4) <=? mem_length m)%N. 2: inv H.
  unfold read_bytes in H. cbn in H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 0)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 1)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 2)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 3)%N (mem_data m)). 2: inv H.
  inv H.
  unfold decode_int, int_of_bytes, rev_if_be, Wasm_int.Int32.modulus, two_power_nat.
  destruct Archi.big_endian;
    destruct b0, b1, b2, b3; cbn;
      unfold Byte.modulus, Byte.wordsize, two_power_nat, Wordsize_8.wordsize in *;
        cbn in *; lia.
Qed.

Lemma decode_int64_bounds : forall b m addr,
  load m (N.of_nat addr) 0%N 8 = Some b ->
  (-1 < decode_int b < Wasm_int.Int64.modulus)%Z.
Proof.
  intros.
  (* length b = 8 bytes *)
  unfold load, those in H.
  destruct (N.of_nat addr + (0 + N.of_nat 8) <=? mem_length m)%N. 2: inv H.
  unfold read_bytes in H. cbn in H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 0)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 1)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 2)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 3)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 4)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 5)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 6)%N (mem_data m)). 2: inv H.
  destruct (memory_list.mem_lookup (N.of_nat addr + 0 + 7)%N (mem_data m)). 2: inv H.
  inv H.
  unfold decode_int, int_of_bytes, rev_if_be, Wasm_int.Int64.modulus, two_power_nat.
  destruct Archi.big_endian;
    destruct b0, b1, b2, b3, b4, b5, b6, b7; cbn;
      unfold Byte.modulus, Byte.wordsize, two_power_nat, Wordsize_8.wordsize in *;
        cbn in *; lia.
Qed.

Lemma value_bounds : forall wal v sr fr,
  INV_num_functions_bounds sr ->
  repr_val_LambdaANF_Wasm v sr fr wal ->
 (-1 < Z.of_nat (wasm_value_to_immediate wal) < Wasm_int.Int32.modulus)%Z.
Proof.
  intros ? ? ? ? Hinv H.
  inv H.
  - (* constr. value unboxed *) cbn. lia.
  - (* constr. value boxed *) cbn. lia.
  - (* function value *)
    cbn.
    assert (idx < length (s_funcs sr)). { apply nth_error_Some. congruence. }
    unfold INV_num_functions_bounds in Hinv. lia.
  - (* prim. value boxed *) cbn. lia.
Qed.

Lemma extract_constr_arg : forall n vs v sr fr addr m,
  INV_num_functions_bounds sr ->
  nthN vs n = Some v ->
  nth_error (s_mems sr) 0 = Some m ->
  (* addr points to the first arg after the constructor tag *)
  repr_val_constr_args_LambdaANF_Wasm vs sr fr addr ->
  exists bs wal, load m (N.of_nat addr + 4 * n) 0%N 4 = Some bs /\
             VAL_int32 (wasm_value_to_i32 wal) = wasm_deserialise bs T_i32 /\
             repr_val_LambdaANF_Wasm v sr fr wal.
Proof.
  intros n vs v sr fr addr m Hinv H H1 H2. generalize dependent v.
  generalize dependent n. generalize dependent m.
  induction H2; intros. 1: inv H.
  assert (n = N.of_nat (N.to_nat n)) as Heq by lia. rewrite Heq in H7. generalize dependent v0. revert Heq.
  induction (N.to_nat n); intros; rewrite ->Heq in *; clear Heq.
  - (* n = 0 *)
    inv H7. assert (m = m0) by congruence. subst m0. rewrite N.add_comm. unfold load_i32 in H3.
    destruct (load m (N.of_nat addr) 0%N 4) eqn:Hl; inv H3. exists b. exists wal.
    repeat split. rewrite <- Hl. now rewrite N.add_comm. unfold wasm_value_to_i32.
    have H'' := value_bounds wal.
    unfold wasm_deserialise. f_equal. f_equal.
    have H' := decode_int32_bounds _ _ _ Hl. simpl_eq.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H8; auto.
    eapply value_bounds; eauto. assumption.
  - (* n = S n0 *)
    cbn in H7.
    replace (match
         match Pos.of_succ_nat n0 with
         | (p~1)%positive => Pos.IsPos p~0
         | (p~0)%positive => Pos.IsPos (Pos.pred_double p)
         | 1%positive => Pos.IsNul
         end
       with
       | Pos.IsPos p => N.pos p
       | _ => 0
       end)%N with (N.of_nat n0)%N in H7.
    2: { destruct (N.succ (N.of_nat n0)) eqn:Heqn. lia.
         destruct (Pos.of_succ_nat n0) eqn:Har; lia. }
    edestruct IHrepr_val_constr_args_LambdaANF_Wasm; try eassumption.
    destruct H8 as [wal' [Hl [Heq Hval]]].
    exists x. exists wal'. split. rewrite -Hl. f_equal. lia. split; eauto.
Qed.

Lemma memory_grow_success : forall m sr fr,
  INV_linear_memory sr fr ->
  nth_error (s_mems sr) 0 = Some m ->
  (mem_size m + 1 <=? max_mem_pages)%N ->
  exists m', mem_grow m 1 = Some m'.
Proof.
  intros m sr fr Hinv H Hsize. eexists. unfold mem_grow.
  assert ((mem_size m + 1 <=? page_limit)%N) as H'. {
    unfold max_mem_pages in H. unfold page_limit. apply N.leb_le.
    apply N.leb_le in Hsize. unfold max_mem_pages in Hsize. lia.
  } rewrite H'. clear H'.
  unfold INV_linear_memory in Hinv. destruct Hinv as [H1 [m' [H2 [H3 [H4 [H5 H6]]]]]].
  rewrite H2 in H. inv H. rewrite H5. cbn. rewrite Hsize. reflexivity.
Qed.

Ltac simpl_modulus_in H :=
  unfold Wasm_int.Int32.modulus, Wasm_int.Int32.half_modulus, two_power_nat in H; cbn in H.
Ltac simpl_modulus :=
  unfold Wasm_int.Int32.modulus, Wasm_int.Int32.half_modulus, two_power_nat.

Lemma memory_grow_reduce_need_grow_mem : forall state s f gmp m,
  nth_error (f_locs f) 0 = Some (N_to_value page_size) ->
  (* INV only for the properties on s,
     the one on f won't hold anymore when we switch to reference types (WasmGC), TODO consider
     having INV only depend on s
  *)
  INV s f ->
  (* need more memory *)
  sglob_val s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
  nth_error (s_mems s) 0 = Some m ->
  (-1 < Z.of_nat gmp < Wasm_int.Int32.modulus)%Z ->
  ~~ Wasm_int.Int32.lt
       (Wasm_int.Int32.repr
          (Wasm_int.Int32.signed
             (Wasm_int.Int32.iadd (nat_to_i32 gmp)
                (nat_to_i32 (N.to_nat page_size))) ÷ 65536))
       (Wasm_int.Int32.repr (Z.of_nat (ssrnat.nat_of_bin (mem_size m)))) = true ->
  exists s', reduce_trans
   (state, s, f, [seq AI_basic i | i <- grow_memory_if_necessary])
   (state, s', f, [])
   /\ s_funcs s = s_funcs s'
   /\ (forall wal val, repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
                       repr_val_LambdaANF_Wasm val s' (f_inst f) wal)
   (* enough memory to alloc. constructor *)
   /\ ((INV s' f /\
       (forall m, nth_error (s_mems s') 0 = Some m ->
          @sglob_val host_function s' (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) /\
          (Z.of_nat gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z))
       \/ (@sglob_val host_function s' (f_inst f) result_out_of_mem = Some (VAL_int32 (nat_to_i32 1)))).
Proof with eauto.
  (* grow memory if necessary *)
  intros state sr fr gmp m Hloc Hinv Hgmp Hm HgmpBound HneedMoreMem.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM [? [? [HglobNodup HinvRest]]]]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m' [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
  assert (m = m') by congruence. subst m'.

  assert (global_var_r global_mem_ptr sr fr) as H2.
  { apply global_var_w_implies_global_var_r; auto. }
  have H' := HgmpInM _ _ Hm2 Hgmp HgmpBound.
  (* need to grow memory *)
  destruct (N.leb_spec (size + 1) max_mem_pages); unfold max_mem_pages in *.
  (* grow memory success *)
  assert (mem_size m + 1 <= page_limit)%N. { unfold page_limit. lia. }
  assert (Hsize: (mem_size m + 1 <=? max_mem_pages)%N).
  { subst. apply N.leb_le. now unfold max_mem_pages. }

  have Hgrow := memory_grow_success _ _ _ INVlinmem Hm2 Hsize.
  destruct Hgrow.
  { eexists. split.
    (* load global_mem_ptr *)
    dostep_nary 0. apply r_get_global. eassumption.
    eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
    apply r_eliml=>//. elimr_nary_instr 0. apply r_get_local. eassumption.
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
           (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z).
      apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
      have H'' := signed_upper_bound (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size).
      simpl_modulus_in H''. cbn. lia. cbn in H5. lia. }
    dostep. apply r_eliml; auto.
    elimr_nary_instr 0. eapply r_current_memory...

    dostep_nary 2. constructor. apply rs_relop.

    dostep'. constructor. subst.
    rewrite HneedMoreMem. apply rs_if_true. intro H3'. inv H3'.

    dostep'. constructor. apply rs_block with (vs:=[])(n:= 0); auto.
    cbn. apply reduce_trans_label.
    dostep_nary 1. eapply r_grow_memory_success; eauto.
    dostep_nary 2. constructor. apply rs_relop. cbn.
    dostep'. constructor. apply rs_if_false.

    assert (size >= 0)%N. { subst. cbn. auto. lia. }
    { unfold Wasm_int.Int32.eq. cbn. rewrite zeq_false. reflexivity. intro.
      subst. cbn in *. unfold page_limit in *.
      rewrite Z_nat_bin in H6.
      rewrite Wasm_int.Int32.Z_mod_modulus_id in H6. lia. simpl_modulus. cbn. lia. }
    dostep'. constructor. apply rs_block with (vs:= [])(n:=0); eauto.
    apply reduce_trans_label. cbn. apply rt_refl.
    intros. split. reflexivity. split.
    { (* value relation preserved *)
      intros.
      eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H5.
      reflexivity. eassumption.
      cbn. destruct (s_mems sr). inv Hm2. reflexivity. eassumption.
      subst. apply mem_length_upper_bound in Hm5; cbn in Hm5. simpl_modulus; cbn; lia.
      rewrite <- Hgmp. reflexivity. subst.
      apply mem_length_upper_bound in Hm5; cbn in Hm5.
      apply mem_grow_increases_length in H4. simpl_modulus; cbn; lia. lia.
      intros. eapply mem_grow_preserves_original_values; eauto; unfold page_limit; lia.
      intros. eapply mem_grow_preserves_original_values; eauto; unfold page_limit; lia.
    } left. split.
    { (* invariant *) eapply update_mem_preserves_INV. 6: reflexivity. assumption.
      eassumption. erewrite mem_grow_increases_length; eauto. lia.
      eapply mem_grow_preserves_max_pages... exists (mem_size m + 1)%N. split.
      eapply mem_grow_increases_size in H4; auto. rewrite N.add_comm.
      apply H4. now apply N.leb_le. }
    { (* enough memory available *)
      rename x into m''.
      intros. destruct (set_nth m'' (s_mems sr) 0 m'') eqn:Hm'. inv H5.
      inv H5. assert (m0 = m''). { destruct (s_mems sr); inv Hm'; auto. } subst m0.
      rename m'' into m'.
      assert (mem_length m' = (page_size + mem_length m)%N) as Hlength'. {
                        eapply mem_grow_increases_length in H4; eauto. }
      rewrite Hlength'. apply mem_length_upper_bound in Hm5; cbn in Hm5.
      split. unfold sglob_val, sglob, upd_s_mem. assumption.
      unfold page_size. lia.
    }
  }

  { (* growing memory fails *)
    edestruct INVresM_w as [sr'' HresM].

    eexists. split.
    (* load global_mem_ptr *)
    dostep_nary 0. apply r_get_global. eassumption.
    eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
    apply r_eliml=>//. elimr_nary_instr 0. apply r_get_local. eassumption.
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
           (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z).
      apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
      have H'' := signed_upper_bound (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size).
      cbn. simpl_modulus_in H''. lia. cbn in H3. lia. }
    dostep. apply r_eliml; auto.
    elimr_nary_instr 0. eapply r_current_memory...

    dostep_nary 2. constructor. apply rs_relop.

    dostep'. constructor. subst. rewrite HneedMoreMem. apply rs_if_true. discriminate.
    dostep'. constructor. apply rs_block with (vs:=[])(n:= 0); auto.
    apply reduce_trans_label.
    dostep_nary 1. eapply r_grow_memory_failure; try eassumption.
    dostep_nary 2. constructor. apply rs_relop. cbn.
    dostep'. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
    dostep'. constructor. eapply rs_block with (vs:=[]); auto.
    apply reduce_trans_label. cbn.
    constructor. apply r_set_global. eassumption.
    (* correct resulting environment *)
    split. eapply update_global_preserves_funcs; eassumption.
    split.
    { (* val relation preserved *)
      intros. subst size.
      have Hlength := mem_length_upper_bound _ Hm5.
      unfold page_size, max_mem_pages in Hlength. cbn in Hlength.
      eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H3; eauto.
      eapply update_global_preserves_funcs. eassumption.
      erewrite <- update_global_preserves_memory; eassumption.
      simpl_modulus. cbn. lia.
      eapply update_global_get_other; try apply HresM; auto. now intro.
      simpl_modulus. cbn. lia. }
    intros. right. eapply update_global_get_same. eassumption. }
Qed.

Lemma memory_grow_reduce_already_enough_mem : forall state s f gmp m,
  nth_error (f_locs f) 0 = Some (N_to_value page_size) ->
  (* INV only for the properties on s *)
  INV s f ->
  sglob_val s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
  nth_error (s_mems s) 0 = Some m ->
  (-1 < Z.of_nat gmp < Wasm_int.Int32.modulus)%Z ->
  (* already enough memory *)
  ~~ Wasm_int.Int32.lt
       (Wasm_int.Int32.repr
          (Wasm_int.Int32.signed
             (Wasm_int.Int32.iadd (nat_to_i32 gmp)
                (N_to_i32 page_size)) ÷ 65536))
       (Wasm_int.Int32.repr (Z.of_nat (ssrnat.nat_of_bin (mem_size m)))) = false ->
  exists s', reduce_trans
   (state, s, f, [seq AI_basic i | i <- grow_memory_if_necessary])
   (state, s', f, [])
   /\ s_funcs s = s_funcs s'
   /\ (forall wal val, repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
                       repr_val_LambdaANF_Wasm val s' (f_inst f) wal)
   (* enough memory to alloc. constructor *)
   /\ ((INV s' f /\
       (forall m, nth_error (s_mems s') 0 = Some m ->
          @sglob_val host_function s' (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) /\
          (Z.of_nat gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z))
       \/ (@sglob_val host_function s' (f_inst f) result_out_of_mem = Some (VAL_int32 (nat_to_i32 1)))).
Proof with eauto.
  destruct exists_i32 as [my_i32 _].
  (* grow memory if necessary *)
  intros state sr fr gmp m Hlocs Hinv Hgmp Hm HgmpBound HenoughMem.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM _]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m' [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
  assert (m' = m) by congruence. subst m'.

  have H' := HgmpInM _ _ Hm2 Hgmp HgmpBound.
  (* enough space already *)
  exists sr. split.
  (* load global_mem_ptr *)
  dostep_nary 0. apply r_get_global. eassumption.
  eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
  apply r_eliml=>//. elimr_nary_instr 0. apply r_get_local. eassumption.
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
           (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z).
    apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
    have H'' := signed_upper_bound (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size).
    simpl_modulus_in H''. cbn. lia. cbn in H. lia. }
  dostep. apply r_eliml; auto.
  elimr_nary_instr 0. eapply r_current_memory...

  dostep_nary 2. constructor. apply rs_relop.

  dostep'. constructor. subst.
  rewrite HenoughMem. apply rs_if_false. reflexivity.

  dostep'. constructor. apply rs_block with (vs:=[])(n:= 0); auto. cbn.
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

    remember (Wasm_int.Int32.signed (Wasm_int.Int32.repr (Z.of_nat gmp + 65536)) ÷ 65536)%Z as y.
    unfold Wasm_int.Int32.signed, Wasm_int.Int32.unsigned in Heqy.
    rewrite Z_nat_bin in Ha.
    have Hlength := mem_length_upper_bound _ Hm5.
    unfold page_size, max_mem_pages in Hlength. cbn in Hlength.

    rewrite zlt_true in Heqy. 2: {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. lia. simpl_modulus. cbn. lia. }

    unfold Wasm_int.Int32.signed in Heqy. cbn in Heqy.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in Heqy. 2: { simpl_modulus. cbn. lia. }
    cbn in Heqy. replace (Z.of_nat (Pos.to_nat 65536)) with 65536%Z in Heqy by lia.
    rewrite (Z.quot_add (Z.of_nat gmp) 1 65536) in Heqy; try lia.

    remember (Wasm_int.Int32.signed
        (Wasm_int.Int32.repr (Z.of_N (mem_size m)))) as n.
    unfold Wasm_int.Int32.signed in Ha.
    subst y. unfold Wasm_int.Int32.signed in Ha. cbn in Ha.

    rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: {
      assert ((Z.of_nat gmp ÷ 65536 < 100000)%Z) as H''. { apply Z.quot_lt_upper_bound; lia. }
      simpl_modulus. cbn.
      assert (Z.of_nat gmp ÷ 65536  >= 0)%Z. {
        rewrite Zquot.Zquot_Zdiv_pos; try lia. apply Z_div_ge0; lia.
      } lia. }

    rewrite small_signed_repr_n_n in Heqn; last by unfold max_mem_pages; lia.
    unfold Wasm_int.Int32.signed in Heqn. cbn in Heqn.

    (* 100000 arbitrary *)
    assert ((Z.of_nat gmp ÷ 65536 < 100000)%Z) as H''. { apply Z.quot_lt_upper_bound; lia. }
    assert (Z.of_nat gmp ÷ 65536  >= 0)%Z. { rewrite Zquot.Zquot_Zdiv_pos; try lia.
    apply Z_div_ge0; lia. }

    rewrite zlt_true in Ha; try lia. subst.

    rewrite N2Z.inj_div in Ha.
    cbn in Ha.
    rewrite Zquot.Zquot_Zdiv_pos in Ha; try lia.
    remember (Z.of_nat gmp) as q.
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

Lemma memory_grow_reduce : forall state s f,
  nth_error (f_locs f) 0 = Some (N_to_value page_size) ->
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
       (forall m, nth_error (s_mems s') 0 = Some m ->
          @sglob_val host_function s' (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) /\
          (Z.of_nat gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z))
       \/ (@sglob_val host_function s' (f_inst f) result_out_of_mem = Some (VAL_int32 (nat_to_i32 1)))).
Proof with eauto.
  (* grow memory if necessary *)
  intros state sr fr Hlocs Hinv.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM [? ?]]]]]]]]].
  destruct INVlinmem as [Hm1 [m [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
  assert (global_var_r global_mem_ptr sr fr) as H2.
  { apply global_var_w_implies_global_var_r; auto. } destruct H2 as [g Hgmp_r].
  destruct (i32_exists_nat g) as [gmp [HgmpEq HgmpBound]]. subst g.
  exists gmp.

  destruct ((~~ Wasm_int.Int32.lt
                 (Wasm_int.Int32.repr
                   (Wasm_int.Int32.signed
                     (Wasm_int.Int32.iadd (nat_to_i32 gmp)
                        (nat_to_i32 (N.to_nat page_size))) ÷ 65536))
                 (Wasm_int.Int32.repr (Z.of_nat (ssrnat.nat_of_bin (mem_size m)))))) eqn:HneedMoreMem.
  2: rename HneedMoreMem into HenoughMem.
  { (* need to grow memory *)
    have H' := memory_grow_reduce_need_grow_mem state _ _ _ _ Hlocs
                                  Hinv Hgmp_r Hm2 HgmpBound HneedMoreMem. apply H'. }
  { (* enough space already *)
     have H' := memory_grow_reduce_already_enough_mem state _ _ _ _ Hlocs
                                  Hinv Hgmp_r Hm2 HgmpBound HenoughMem. apply H'. }
Qed.

(* TODO use automation instead *)
Lemma nat_to_i32_eq_modulus: forall n m,
  (-1 < Z.of_nat n < Wasm_int.Int32.modulus)%Z ->
  (-1 < Z.of_nat m < Wasm_int.Int32.modulus)%Z ->
  Some (VAL_int32 (nat_to_i32 n)) = Some (VAL_int32 (nat_to_i32 m)) ->
  n = m.
Proof.
  intros. inv H1. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H3; try lia.
Qed.

Lemma nat_to_i32_plus : forall n m x,
  (-1 < Z.of_nat x < Wasm_int.Int32.modulus)%Z ->
  (-1 < Z.of_nat (n+m) < Wasm_int.Int32.modulus)%Z ->
  Wasm_int.Int32.iadd (nat_to_i32 n) (nat_to_i32 m) = nat_to_i32 x ->
  m + n = x.
Proof.
  intros. inv H1. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H3; try lia.
  repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
Qed.


Lemma store_constr_args_reduce {lenv} : forall ys offset vs sargs state rho fds s f m v_cap,
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  INV s f ->
  nth_error (s_mems s) 0 = Some m ->
  @sglob_val host_function s (f_inst f) constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap)) ->
  ((N.of_nat v_cap) + page_size < mem_length m)%N ->
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  (-1 < Z.of_nat (length ys + offset) < 2 * max_constr_args)%Z ->
  sglob_val (host_function:=host_function) s (f_inst f)
                 global_mem_ptr = Some (VAL_int32 (nat_to_i32 (4 + (4*offset) + v_cap))) ->
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
            /\ sglob_val (host_function:=host_function) s' (f_inst f)
                 constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap))
            /\ (0 <= Z.of_nat v_cap < Wasm_int.Int32.modulus)%Z
            /\ repr_val_constr_args_LambdaANF_Wasm vs s' (f_inst f) (4 + (4*offset) + v_cap)
            /\ sglob_val (host_function:=host_function) s' (f_inst f)
                 global_mem_ptr = Some (VAL_int32 (nat_to_i32 ((4 + (4*offset) + v_cap) + 4 * (length ys))))
            /\ s_funcs s = s_funcs s'
            /\ (forall (wal : wasm_value) (val : cps.val),
                    repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
                    repr_val_LambdaANF_Wasm val s' (f_inst f) wal)
            (* previous mem including tag unchanged *)
            /\ exists m', nth_error (s_mems s') 0 = Some m'
                       /\ mem_length m = mem_length m'
                       /\ forall a, N.to_nat a <= v_cap + 4 * offset -> load_i32 m a = load_i32 m' a.
Proof.
  induction ys; intros offset vs sargs state rho fds s f m v_cap HenvsDisjoint HfenvWf Hinv
                       Hm Hcap Hlen Hargs Hoffset Hgmp H Hvs HmemR HfVal.
  { inv H. inv Hvs. exists s. split. apply rt_refl. split. assumption.
    have I := Hinv. destruct I as [_ [_ [_ [Hgmp_r [Hcap_r [Hmut _]]]]]].
    apply global_var_w_implies_global_var_r in Hcap_r; auto.
    apply global_var_w_implies_global_var_r in Hgmp_r; auto.
    destruct Hcap_r as [v Hv].
    edestruct i32_exists_nat as [x [Hx ?]]. erewrite Hx in Hv. clear Hx v.
    destruct Hgmp_r as [v' Hv'].
    edestruct i32_exists_nat as [x' [Hx' ?]]. erewrite Hx' in Hv'. clear Hx' v'.

    split. eassumption.
     have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hinv_linmem _]]]]]]].
    destruct Hinv_linmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
    assert (m = m') by congruence. subst m' size.
    apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
    split. simpl_modulus. cbn. lia. split. econstructor.
    split. rewrite Hgmp. do 3! f_equal. cbn. lia.
    split. auto. split. auto.
    exists m. auto.
  }
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
                   (state, s, f, [AI_basic (BI_const (VAL_int32 (wasm_value_to_i32 wal)))]) /\
      repr_val_LambdaANF_Wasm v s (f_inst f) wal). {
        inv H. rename i into y'.
      { (* var *)
        assert (Htmp: In y (y :: ys)) by (cbn; auto).
        assert (HfdNone: find_def y fds = None). {
          inv H0. rewrite (HfenvWf_None _ HfenvWf). unfold translate_var in H.
          destruct (lenv ! y) eqn:Hy; inv H. now apply HenvsDisjoint in Hy. }
        destruct (HmemR _ Htmp HfdNone) as [val [wal [Hrho [[y0' [Htv Hly']] Hy_val]]]].
        assert (val = v) by congruence. subst v. clear Hrhoy.
        assert (y' = y0'). { inv H0. congruence. } subst y0'.
        clear Htmp. exists wal.
        split; auto.
        constructor. apply r_get_local; eassumption.
      }
      { (* fun idx *)
        eapply HfVal in Hrhoy; eauto. exists (Val_funidx i). split. apply rt_refl. eassumption.
      }
    }
    destruct Hinstr as [wal [HinstrRed HinstrVal]].
    {
      (* invariants *)
      have I := Hinv. destruct I as [_ [_ [_ [Hinv_gmp [Hinv_cap [Hinv_muti32 [Hinv_linmem
                                    [Hinv_gmpM [_ [_ [Hinv_nodup _]]]]]]]]]]].
      eapply global_var_w_implies_global_var_r in Hinv_cap; auto. destruct Hinv_cap as [cap ?].
      eapply global_var_w_implies_global_var_r in Hinv_gmp; auto. destruct Hinv_gmp as [gmp ?].

      destruct Hinv_linmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst size. cbn.

      assert (m = m') by congruence. subst m'. clear Hmem2.

      destruct (i32_exists_nat cap) as [x1 [Hx ?]]. subst cap. rename x1 into cap.
      destruct (i32_exists_nat gmp) as [x1 [Hx' ?]]. subst gmp. rename x1 into gmp.
      assert (exists m0, store m (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd
                                   (nat_to_i32 v_cap)
                                   (nat_to_i32 (S (S (S (S (offset * 4)))))))) 0%N
                        (bits (VAL_int32 (wasm_value_to_i32 wal)))
                        (t_length T_i32) = Some m0) as Hm0. {
       intros. edestruct enough_space_to_store as [m3 Hstore]. 2: { exists m3.
          replace (t_length T_i32) with (length (bits (VAL_int32 (wasm_value_to_i32 wal)))) by auto.
          apply Hstore. } rewrite N.add_0_r.
       replace (N.of_nat (length (bits (VAL_int32 (wasm_value_to_i32 wal))))) with 4%N by reflexivity.
       unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
       remember (S (S (S (S (offset * 4))))) as n. cbn.
       have H' := mem_length_upper_bound _ Hmem5. cbn in H'.

       assert (Z.of_nat offset < 2 * max_constr_args)%Z by lia.
       assert (Z.of_nat n + 4 < Z.of_N page_size)%Z. { cbn in H5.
        assert (N.of_nat n < 10000)%N.  lia. cbn. lia. }
       rewrite Wasm_int.Int32.Z_mod_modulus_id.
       rewrite Wasm_int.Int32.Z_mod_modulus_id.
       rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
       simpl_modulus. cbn. lia.
       simpl_modulus. cbn. lia.
       rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
       rewrite Wasm_int.Int32.Z_mod_modulus_id. simpl_modulus. cbn. lia.
       simpl_modulus. cbn. lia. simpl_modulus. cbn. lia.
      }

      (* prepare IH *)
      assert (Hmaxargs : (Z.of_nat (length ys) <= max_constr_args)%Z). {
      cbn in Hargs. lia. } clear Hargs.

      assert (Hoff: (length (y :: ys) + offset) = length ys + (S offset)). { cbn. lia. }
      rewrite Hoff in Hoffset. clear Hoff.

      destruct Hm0 as [m0 Hm0].
      remember (@upd_s_mem host_function s (set_nth m0 (s_mems s) 0 m0)) as s'.
      assert (Hinv' : INV s' f). {
        eapply update_mem_preserves_INV. 6: subst; reflexivity. assumption. eassumption.
        apply mem_store_preserves_length in Hm0. lia.
        apply mem_store_preserves_max_pages in Hm0. congruence.
        eexists. split. reflexivity.
        apply mem_store_preserves_length in Hm0. unfold mem_size in Hmem5.
        now rewrite Hm0 in Hmem5. }

      have I := Hinv'. destruct I as [_ [_ [_ [Hgmp_w [_ [_ [_ [? [_ [_ [_ [_ [_ [Hgmp_mult_two _]]]]]]]]]]]]]].

      destruct (Hgmp_w (Wasm_int.Int32.iadd (nat_to_i32 gmp) (nat_to_i32 4))) as [s_before_IH ?].

      assert (Hmem_before_IH : nth_error (s_mems s_before_IH) 0 = Some m0). {
        subst s'. erewrite <- update_global_preserves_memory; try eassumption.
        cbn. destruct (s_mems s). inv Hm. reflexivity. }

      assert (Hinv_before_IH : INV s_before_IH f). {
        edestruct i32_exists_nat as [? [Heq ?]]. erewrite Heq in H6.
       unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add, nat_to_i32 in Heq. inv Heq.
       repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H9; try lia.
       2: { rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
            have H' := Hinv_gmpM _ _ Hm H1 H4.
            apply mem_length_upper_bound in Hmem5; cbn in Hmem5. simpl_modulus; cbn; lia. }
       assert (x = gmp + 4) by lia. subst x.
       eapply update_global_preserves_INV; try apply H6. assumption.
       unfold result_out_of_mem, global_mem_ptr. lia. cbn.
       destruct (s_mems s). inv Hm. inv Hm. reflexivity. assumption.
       move => _. apply mem_store_preserves_length in Hm0.
       rewrite H1 in Hgmp.
       assert (-1 < Z.of_nat (4 + 4 * offset + v_cap) < Wasm_int.Int32.modulus)%Z. {
         cbn in Hoffset. unfold max_constr_args in Hmaxargs.
         unfold page_size in Hlen. cbn in Hlen.
         simpl_modulus. apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
         cbn. lia. }

       assert (gmp = (4 + 4 * offset + v_cap)). { apply nat_to_i32_eq_modulus; auto. }
       clear Hgmp.
       cbn. unfold page_size in Hlen. cbn in Hoffset. lia.
       intro.
       destruct (s_mems s). inv Hm. inv Hm.
       destruct (Hgmp_mult_two gmp m0) as [n Htwo]; eauto.
       exists (2 + n). lia.
      }

      assert (Hcap_before_IH: sglob_val (host_function:=host_function) s_before_IH
            (f_inst f) constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap))). {
        subst. eapply  update_global_get_other; try apply H6; auto. }

      assert (Hlen_m0: (N.of_nat v_cap + page_size < mem_length m0)%N). {
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

        { edestruct i32_exists_nat as [? [Hn ?]]. erewrite Hn in H6.
          rewrite H1 in Hgmp.
          assert (-1 < Z.of_nat (4 + 4 * offset + v_cap) < Wasm_int.Int32.modulus)%Z. {
             cbn in Hoffset. unfold max_constr_args in Hmaxargs.
             unfold page_size in Hlen. cbn in Hlen.
             simpl_modulus. apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
             cbn. lia. }
          assert (gmp = (4 + 4* offset + v_cap)). { apply nat_to_i32_eq_modulus; auto. }
          subst gmp. clear Hgmp.

          assert ((4 + 4 * offset + v_cap) + 4 = x). {
            assert ((-1 < Z.of_nat (4 + 4 * offset + v_cap + 4) <
                                              Wasm_int.Int32.modulus)%Z).
             { apply mem_store_preserves_length in Hm0.
               apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
               cbn in Hoffset. simpl_modulus; cbn. lia. }
             apply nat_to_i32_plus in Hn; auto. lia. } subst x. clear Hn.

          apply mem_length_upper_bound in Hmem5. cbn in Hmem5. cbn in Hoffset. clear H12.
          unfold page_size in Hlen_m0. cbn in Hlen_m0.
          assert (mem_length m0 = mem_length m). { now apply mem_store_preserves_length in Hm0. }

          eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H10; subst.
          apply update_global_preserves_funcs in H6. rewrite -H6. reflexivity.
          eassumption. eassumption. eassumption.
          have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [INVgmp_M _]]]]]]]].
          have H' := INVgmp_M _ _ Hm H1 H4. simpl_modulus. cbn. lia.
          eapply update_global_get_same in H6. eassumption.
          simpl_modulus. cbn. lia.
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
      assert (Hgmp_before_IH: sglob_val (host_function:=host_function) s_before_IH (f_inst f)
           global_mem_ptr = Some (VAL_int32 (nat_to_i32 (4 + 4 * S offset + v_cap)))). {
        subst.
        apply update_global_get_same in H6. rewrite H6. f_equal. f_equal.

        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add. cbn.
        rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. unfold nat_to_i32. f_equal.
        assert ((-1 < Z.of_nat (4 + 4 * offset + v_cap) < Wasm_int.Int32.modulus)%Z). {
          cbn in Hoffset. unfold page_size in Hlen_m0. cbn in Hlen_m0.
          unfold max_constr_args in Hmaxargs.
          apply mem_store_preserves_length in Hm0.
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5. simpl_modulus. cbn. lia. }
        rewrite Hgmp in H1. apply nat_to_i32_eq_modulus in H1; try lia.
      }

     assert (HfVal_before_IH: (forall (y : positive) (y' : immediate) (v : cps.val),
       rho ! y = Some v -> repr_funvar y y' ->
       repr_val_LambdaANF_Wasm v s_before_IH (f_inst f) (Val_funidx y'))).
     { intros. have H' := HfVal _ _ _ H7 H8.
       eapply val_relation_func_depends_on_funcs; last apply H'. subst.
       now apply update_global_preserves_funcs in H6. }

      have IH := IHys _ _ _ state _ _ _ _ _ _ HenvsDisjoint HfenvWf Hinv_before_IH Hmem_before_IH
                 Hcap_before_IH Hlen_m0 Hmaxargs Hoffset Hgmp_before_IH H3 Hvs HrelE_before_IH HfVal_before_IH.
      clear IHys Hmem_before_IH Hinv_before_IH HrelE_before_IH Hcap_before_IH.
      destruct IH as [sr [Hred [Hinv'' [Hv1 [? [Hv2 [? [? [? [m1 [Hm1 [? ?]]]]]]]]]]]].
      assert (@sglob_val host_function s (f_inst f) constr_alloc_ptr
            = @sglob_val host_function (upd_s_mem s (set_nth m0 (s_mems s) 0 m0)) (f_inst f) constr_alloc_ptr)
      as Hglob_cap by reflexivity.
      have HlenBound := mem_length_upper_bound _ Hmem5. cbn in HlenBound.

      rewrite H0 in Hcap. apply nat_to_i32_eq_modulus in Hcap; try lia. subst v_cap.

      eexists. split.
      (* reduce *)
      dostep_nary 0. apply r_get_global. rewrite Hglob_cap. eassumption.
      dostep_nary 2. constructor. constructor. reflexivity.
      eapply rt_trans. apply app_trans_const; auto. apply app_trans. eassumption.

      dostep_nary 2. eapply r_store_success; try eassumption; auto.
      dostep_nary 0. apply r_get_global. eassumption.
      dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
      dostep_nary 1. apply r_set_global. subst. eassumption.
      apply Hred.
      split. assumption. split. assumption. split. simpl_modulus. cbn. lia. split.
      econstructor. apply Hm1. eassumption. { simpl_modulus.
        apply mem_length_upper_bound in Hmem5. cbn in Hmem5, Hoffset. cbn. lia. } cbn. lia.

      { (* load val *)
        rewrite -H12; try lia.
        apply store_load_i32 in Hm0.
        assert ((N.of_nat (S (S (S (S (offset + (offset + (offset + (offset + 0))) + cap)))))) =
                (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (nat_to_i32 cap)
                            (nat_to_i32 (S (S (S (S (offset * 4))))))))) as Har. {
          remember (S (S (S (S (offset * 4))))) as o. cbn.
          assert (Z.of_nat offset < 2 * max_constr_args)%Z as HarOffset by lia. cbn in HarOffset.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
        }
        rewrite deserialise_bits in Hm0. rewrite Har. eassumption.
        auto. reflexivity. }

      { rewrite H1 in Hgmp.
        assert ((-1 < Z.of_nat (4 + 4 * offset + cap) < Wasm_int.Int32.modulus)%Z). {
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          cbn in Hoffset. simpl_modulus. cbn. lia. }
        apply nat_to_i32_eq_modulus in Hgmp; auto. subst gmp.

        apply H10.
        eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s);
          try apply Hy_val; try eassumption.
        - subst. apply update_global_preserves_funcs in H6. cbn in H6. congruence.
        - apply update_global_preserves_memory in H6. rewrite <- H6.
          cbn. destruct (s_mems s). inv Hm. subst s'. reflexivity.
        - have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [Hgmp_M _]]]]]]]].
          have H' := Hgmp_M _ _ Hm H1 H4. apply mem_length_upper_bound in Hmem5.
          cbn in Hmem5. simpl_modulus. cbn. lia.
        - simpl_modulus. cbn in Hoffset. unfold max_constr_args in Hmaxargs.
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          apply mem_store_preserves_length in Hm0. cbn. lia.
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
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
      }

      (* TODO: contains duplication: cleanup *)
      replace ((4 + S (S (S (S (offset + (offset + (offset + (offset + 0))) + cap)))))) with
      (4 + 4 * S offset + cap) by lia. apply Hv2.
      split. subst. auto. rewrite H8. f_equal. f_equal. f_equal. cbn. lia.
      split. apply update_global_preserves_funcs in H6. subst s'. cbn in H6. congruence.
      split. {
        intros. apply H10.
        assert (Heq: (nat_to_i32 gmp) = (nat_to_i32 (4 + 4 * offset + cap))) by congruence.
        assert ((-1 < Z.of_nat (4 + 4 * offset + cap) < Wasm_int.Int32.modulus)%Z).
        { cbn in Hoffset. unfold max_constr_args in Hmaxargs. simpl_modulus; cbn; lia. }
        assert (Htmp: (Some (VAL_int32 (nat_to_i32 gmp)) =
                       Some (VAL_int32 (nat_to_i32 (4 + 4 * offset + cap))))) by congruence.

        apply nat_to_i32_eq_modulus in Htmp; auto. subst gmp.

        eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H13;
          try eassumption.
        - apply update_global_preserves_funcs in H6. subst s'. cbn in H6.
          congruence.
        - apply update_global_preserves_memory in H6. rewrite <- H6.
          cbn. destruct (s_mems s). inv Hm. subst s'. reflexivity.
        - have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [Hgmp_M _]]]]]]]].
          have H' := Hgmp_M _ _ Hm H1 H4. apply mem_length_upper_bound in Hmem5.
          cbn in Hmem5. simpl_modulus. cbn. lia.
        - simpl_modulus. cbn in Hoffset. unfold max_constr_args in Hmaxargs.
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          apply mem_store_preserves_length in Hm0. cbn. lia.
        - lia.
        { intros.
          assert (Hex: exists v, load_i32 m a = Some v). {
          have Hm0' := Hm0.
          apply enough_space_to_load. unfold store in Hm0'.
          destruct ((Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (nat_to_i32 cap)
            (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 + N.of_nat (t_length T_i32) <=?
                                                             mem_length m)%N) eqn:Har. 2: inv Hm0'.
             cbn in Hoffset. apply mem_store_preserves_length in Hm0.
             unfold page_size in Hlen_m0. lia. } destruct Hex.
          assert (Har: (a + 4 <=
              Wasm_int.N_of_uint i32m
                (Wasm_int.Int32.iadd (nat_to_i32 cap)
                   (nat_to_i32 (S (S (S (S (offset * 4))))))))%N). {
            unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
            remember ((S (S (S (S (offset * 4)))))) as o. cbn.
            cbn in Hoffset.
            repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia. }

          have Ht := load_store_load_i32 _ _ _ _ _ _ _ Har H16 Hm0.
          clear Har. rewrite Ht; auto. }
        { intros.
          assert (Hex: exists v, load_i64 m a = Some v). {
            have Hm0' := Hm0.
            apply enough_space_to_load_i64. unfold store in Hm0'.
            destruct ((Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (nat_to_i32 cap)
                                                  (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 + N.of_nat (t_length T_i32) <=?
                         mem_length m)%N) eqn:Har. 2: inv Hm0'.
            cbn in Hoffset. apply mem_store_preserves_length in Hm0.
            unfold page_size in Hlen_m0. lia. } destruct Hex.
          assert (Har: (a + 8 <=
                          Wasm_int.N_of_uint i32m
                            (Wasm_int.Int32.iadd (nat_to_i32 cap)
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
          have Hm0' := Hm0.
          apply enough_space_to_load. unfold store in Hm0'.
          destruct ((Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (nat_to_i32 cap)
            (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 + N.of_nat (t_length T_i32) <=?
                                                             mem_length m)%N) eqn:Har. 2: inv Hm0'.
             cbn in Hoffset. apply mem_store_preserves_length in Hm0.
             unfold page_size in Hlen_m0. lia.
        } destruct H14. rewrite -H12; try lia.

        cbn in Hoffset. unfold max_constr_args in Hmaxargs.
        symmetry. erewrite load_store_load_i32; try apply Hm0; eauto.
        remember (S (S (S (S (offset * 4))))) as n.
        cbn. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia. }}}
Qed.

Lemma store_constr_reduce {lenv} : forall state s f rho fds ys (vs : list cps.val) t n sargs m gmp_v,
  get_ctor_arity cenv t = Ret n ->
  n > 0 ->
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  INV s f ->
  (* enough memory available *)
  nth_error (s_mems s) 0 = Some m ->
  sglob_val s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp_v)) ->
  (Z.of_nat gmp_v + Z.of_N page_size < Z.of_N (mem_length m))%Z ->
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
  (forall (y : positive) (y' : immediate) (v : cps.val),
         rho ! y = Some v ->
         repr_funvar y y' ->
         repr_val_LambdaANF_Wasm v s (f_inst f) (Val_funidx y')) ->

  exists s', reduce_trans
    (state, s, f,
      [:: AI_basic (BI_get_global global_mem_ptr)] ++
      [:: AI_basic (BI_set_global constr_alloc_ptr)] ++
      [:: AI_basic (BI_get_global constr_alloc_ptr)] ++
      [:: AI_basic (BI_const (nat_to_value (Pos.to_nat t)))] ++
      [:: AI_basic (BI_store T_i32 None 2%N 0%N)] ++
      [:: AI_basic (BI_get_global global_mem_ptr)] ++
      [:: AI_basic (BI_const (nat_to_value 4))] ++
      [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add))] ++
      [:: AI_basic (BI_set_global global_mem_ptr)] ++
      [seq AI_basic i | i <- sargs]) (state, s', f, []) /\
    INV s' f /\
    s_funcs s = s_funcs s' /\
    (forall (wal : wasm_value) (val : cps.val),
      repr_val_LambdaANF_Wasm val s (f_inst f) wal ->
      repr_val_LambdaANF_Wasm val s' (f_inst f) wal) /\
      (* cap points to value *)
    (exists cap_v wasmval, sglob_val s' (f_inst f) constr_alloc_ptr = Some (VAL_int32 cap_v)
          /\ wasm_value_to_i32 wasmval = cap_v
          /\ repr_val_LambdaANF_Wasm (Vconstr t vs) s' (f_inst f) wasmval).
Proof.
  intros ???????????? HarrSome HarrGt0 HenvsDisjoint HfenvWf Hinv HenoughM1 HenoughM2 HenoughM3
                      HmemR Hmaxargs Hsetargs Hrho HfVal.

  have I := Hinv. destruct I as [_ [_ [_ [INVgmp_w [INVcap_w [INVmuti32 [INVmem [_ [_ [_ [INV_instglobs [_ [_ [INV_gmp_mult_two _]]]]]]]]]]]]]].
  have INVgmp_r := global_var_w_implies_global_var_r _ _ _ INVmuti32 INVgmp_w.

  assert(HgmpBound: (-1 < Z.of_nat gmp_v < Wasm_int.Int32.modulus)%Z). {
    destruct INVmem as [Hmem1 [m' [Hmem2 [? [<- [Hmem4 Hmem5]]]]]]. solve_eq m m'.
    apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
    simpl_modulus. cbn. simpl_modulus_in HenoughM3. lia. }

  destruct (INV_gmp_mult_two gmp_v m) as [n0 Hgmp_mult_two]; eauto. clear INV_gmp_mult_two.
  (* invariants after set_global cap *)
  destruct (INVcap_w (nat_to_i32 gmp_v)) as [s' ?]. clear INVcap_w.
  (* INV after set_global cap *)
  assert (INV s' f) as Hinv'. {
    eapply update_global_preserves_INV; try apply H; auto.
    unfold result_out_of_mem, constr_alloc_ptr. lia.
    eassumption.
    all: intros Hcontra; inv Hcontra. }

   have I := Hinv'. destruct I as [_ [_ [_ [_ [INVcap_w'' [INVmuti32'' [INVlinmem'' _ ]]]]]]].

  (* invariants mem *)
  edestruct INVlinmem'' as [Hmem1'' [m' [Hmem2'' [size'' [Hmem3'' [Hmem4'' Hmem5'']]]]]].
  assert (m' = m). { apply update_global_preserves_memory in H. congruence. } subst m' size''.

  assert (exists mem, store m (Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v)) 0%N
                              (bits (nat_to_value (Pos.to_nat t)))
                              (t_length T_i32) = Some mem) as Htest.
  { apply enough_space_to_store. cbn.
    assert ((Datatypes.length (serialise_i32 (nat_to_i32 (Pos.to_nat t)))) = 4) as Hl.
    { unfold serialise_i32, encode_int, bytes_of_int, rev_if_be.
      destruct (Archi.big_endian); reflexivity. } rewrite Hl. clear Hl. cbn.
    rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
    destruct Hinv' as [_ [_ [_ [_ [_ [_ [Hlinmem [INVgmp_M _]]]]]]]].
    destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].

    assert (m' = m) by congruence. subst m'.
    assert (Hgmp_r : sglob_val (host_function:=host_function) s' (f_inst f) global_mem_ptr =
              Some (VAL_int32 (nat_to_i32 gmp_v))). { eapply update_global_get_other; try eassumption.
               unfold global_mem_ptr, constr_alloc_ptr. lia. }
    have Htest := INVgmp_M _ _ Hmem2 Hgmp_r. lia. }
  destruct Htest as [m' Hstore].

  remember (upd_s_mem s' (set_nth m' s'.(s_mems) 0 m')) as s_tag.
  assert (Hinv_tag : INV s_tag f). { subst.
    assert (mem_length m = mem_length m'). { apply mem_store_preserves_length in Hstore. congruence. }
    assert (mem_max_opt m = mem_max_opt m'). { apply mem_store_preserves_max_pages in Hstore. congruence. }
    eapply update_mem_preserves_INV. apply Hinv'. eassumption. erewrite <- H0. lia.
    congruence. exists (mem_size m); split; auto. unfold mem_size. congruence. reflexivity. }

  have I := Hinv_tag. destruct I as [_ [_ [_ [Hgmp_w _]]]].
  destruct (Hgmp_w (Wasm_int.Int32.iadd (nat_to_i32 gmp_v) (nat_to_i32 4))) as [s_before_args ?].
  edestruct i32_exists_nat as [gmp [HgmpEq HgmpBound']].
  erewrite HgmpEq in H0.
  assert (gmp = gmp_v + 4). {
    inversion HgmpEq. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H3; try lia.
    unfold store in Hstore.
    destruct ((Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v) + 0 + N.of_nat (t_length T_i32)
                                 <=? mem_length m)%N) eqn:Har. 2: inv Hstore.
    apply N.leb_le in Har. cbn in Har.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in Har; try lia.
    apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
    symmetry in H2. simpl_eq.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H2.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H2; lia.
    rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
    simpl_modulus. cbn. lia.
  } subst gmp.

 (* INV after set_global gmp *)
  assert (Hinv_before_args : INV s_before_args f). {
    eapply update_global_preserves_INV. 7: eassumption.
    assumption. unfold result_out_of_mem, global_mem_ptr. lia.
    subst s_tag. cbn. destruct (s_mems s'). inv Hmem2''. reflexivity. assumption.
    move => _.
    unfold page_size in HenoughM3; cbn in HenoughM3.
    apply mem_store_preserves_length in Hstore. lia.
    intro. exists (2 + n0). lia. }

  assert (Hmem: nth_error (s_mems s_before_args) 0 = Some m'). { subst s_tag. cbn.
    apply update_global_preserves_memory in H0. rewrite -H0. cbn.
    destruct (s_mems s'). inv Hmem2''. reflexivity. }
  assert (Hglob_cap: sglob_val (host_function:=host_function) s_before_args
          (f_inst f) constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 gmp_v))). {
    subst.
    replace (sglob_val (upd_s_mem s' (set_nth m' (s_mems s') 0 m')) (f_inst f) constr_alloc_ptr)
       with (sglob_val s' (f_inst f) constr_alloc_ptr) by reflexivity.
    apply update_global_get_same in H.
    eapply update_global_get_other in H0; eauto. }
  assert (HenoughM': (N.of_nat gmp_v + page_size < mem_length m')%N). {
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
      assert (s_funcs
       (upd_s_mem (host_function:=host_function) s'
          (set_nth m' (s_mems s') 0 m')) = s_funcs s') by reflexivity. congruence. }
    { erewrite update_global_preserves_memory. 2: eassumption. eassumption. }
    { apply update_global_preserves_memory in H0. subst. rewrite <- H0. cbn.
      destruct (s_mems s'). inv Hmem2''. reflexivity. }
    { eassumption. }
    { apply mem_store_preserves_length in Hstore.
      subst. apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
      simpl_modulus. simpl_modulus_in HenoughM'. cbn. lia. }
    { subst. eapply update_global_get_same. eassumption. }
    { cbn in HlenBound. rewrite Nat.add_0_r in HlenBound.
      simpl_modulus_in HenoughM'. cbn in HenoughM'.  simpl_modulus. cbn. subst.
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
        Some (VAL_int32 (nat_to_i32 (4 + gmp_v)))).
  { apply update_global_get_same in H0. rewrite H0. do 3! f_equal. lia. }

  assert (HfVal_before_args: (forall (y : positive) (y' : immediate) (v : cps.val),
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
  dostep_nary 0. apply r_get_global. eassumption.
  dostep_nary 1. apply r_set_global. eassumption. cbn.
  dostep_nary 0. apply r_get_global. eapply update_global_get_same. eassumption.
  (* write tag *)
  dostep_nary 2. eapply r_store_success. 4: eassumption.
  reflexivity. eassumption. assumption.

  dostep_nary 0. apply r_get_global.
  replace (sglob_val (upd_s_mem (host_function:=host_function) s' (set_nth m' (s_mems s') 0 m')))
     with (sglob_val s') by reflexivity.
  eapply update_global_get_other with (j:= constr_alloc_ptr). assumption.
  unfold global_mem_ptr, constr_alloc_ptr. lia.
  2: eassumption. eassumption. cbn.

  dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
  dostep_nary 1. apply r_set_global. subst. rewrite HgmpEq. eassumption.
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
    apply mem_length_upper_bound in Hmem5''; cbn in Hmem5''. simpl_modulus; cbn; lia.
    lia.

    { intros. assert (exists v, load_i32 m a = Some v). {
        apply enough_space_to_load. unfold store in Hstore.
        destruct ((Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v) + 0 +
            N.of_nat (t_length T_i32) <=?
            mem_length m)%N). 2: inv Hstore. lia. } destruct H4.
      symmetry. erewrite load_store_load_i32; try apply Hstore; eauto.
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
    { intros. assert (exists v, load_i64 m a = Some v). {
        apply enough_space_to_load_i64. unfold store in Hstore.
        destruct ((Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v) + 0 +
            N.of_nat (t_length T_i32) <=?
            mem_length m)%N). 2: inv Hstore. lia. } destruct H4.
      symmetry. erewrite load_store_load_i64; try apply Hstore; eauto.
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
  }
  (* constr value in memory *)
  eexists. eexists. split. eassumption.
  split.
  assert (wasm_value_to_i32 (Val_ptr gmp_v) = nat_to_i32 gmp_v) by reflexivity. eassumption.
  econstructor; try eassumption. { assert (Hm'': nth_error (s_mems s) 0 = Some m).
    erewrite update_global_preserves_memory; eassumption.
    apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''. unfold page_size in HenoughM3; cbn in HenoughM3.
    unfold max_constr_args in Hmaxargs. simpl_modulus. cbn. lia. }
  lia. exists n0. auto.
  reflexivity.
  apply store_load_i32 in Hstore.
  rewrite deserialise_bits in Hstore; auto.
  assert ((Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v)) = (N.of_nat gmp_v)) as Heq. {
  unfold nat_to_i32. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
  rewrite Heq in Hstore.
  rewrite -Hmemsame. eassumption. lia. reflexivity. }
Qed.


Inductive const_val_list : list cps.val -> store_record -> frame -> list nat -> Prop :=
  | CV_nil  : forall s f, const_val_list [] s f []
  | CV_cons : forall s f v vs n w ns,
       repr_val_LambdaANF_Wasm v s (f_inst f) w ->
       n = wasm_value_to_immediate w ->
       const_val_list vs s f ns ->
       const_val_list (v::vs) s f (n::ns).

Lemma map_const_const_list : forall args,
  const_list [seq AI_basic (BI_const (nat_to_value a)) | a <- args].
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
            nth_error [seq nat_to_value i | i <- ns] j =
               Some (VAL_int32 (wasm_value_to_i32 w)).
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
                 (state, sr, fr, (map (fun a => AI_basic (BI_const (nat_to_value a))) args))
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
      rewrite HfenvWf. inv H. unfold translate_var in H0. destruct (lenv ! a) eqn:Ha'; inv H0.
      now apply HenvsDisjoint in Ha'. }
    destruct (Hvar _ Hocc Hf) as [val [wal [Hrho' [Hlocs Hval]]]].
    assert (v = val) by congruence. subst val.
    destruct Hlocs as [a'' [Ha'' HlVar]]. destruct H. rewrite Ha'' in H. inv H.

    exists (wasm_value_to_immediate wal :: args'). cbn. split.
    dostep_nary 0. apply r_get_local. eassumption.
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
      apply app_trans_const with (lconst := [AI_basic (BI_const (nat_to_value a'))]); auto.
      assert (v = Vfun (M.empty _) fds a). {
        specialize HfenvWf with a. inv H. unfold translate_var in H0.
        destruct (fenv ! a); inv H0.
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
  translate_functions nenv cenv fenv fds = Ret fns ->
  numOf_fundefs fds = length fns.
Proof.
  induction fds; intros. 2: { now inv H. }
  simpl in H.
  destruct (translate_function nenv cenv fenv v l e). inv H.
  destruct (translate_functions _ _ _ fds). inv H. destruct fns; inv H. cbn. now rewrite -IHfds.
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

(* for fn values returned by the fn body of Eletapp, it holds that rho=M.empty etc. *)
Lemma step_preserves_empty_env_fds : forall rho e v c fds rho' fds' f',
  (forall (x : positive) (rho' : M.t val) (fds' : fundefs) (f' : var) (v0 : val),
	  rho ! x = Some v0 ->
	  subval_or_eq (Vfun rho' fds' f') v0 ->
	  fds' = fds /\ rho' = M.empty val /\ name_in_fundefs fds f') ->
	(forall e' e'' eAny fdsAny,
	  (subterm_or_eq e' e \/ (subterm_or_eq e' e'' /\ dsubterm_fds_e e'' fds))
	                                                -> e' <> Efun fdsAny eAny) ->
  bstep_e (M.empty (seq val -> option val)) cenv rho e v c ->
  subval_or_eq (Vfun rho' fds' f') v ->
  fds' = fds /\ rho' = M.empty val /\ name_in_fundefs fds f'.
Proof.
  intros ? ? ? ? ? ? ? ? Hrho HnoFd Hstep Hsubval.
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
  - (* Eprim *) by inv H0.
  - (* Ehalt *) by eauto.
  Unshelve. all: assumption.
Qed.


Lemma repr_expr_LambdaANF_Wasm_no_Efun_subterm {lenv} : forall e_body eAny,
  @repr_expr_LambdaANF_Wasm lenv e_body eAny ->

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
  - (* Eprim *) by inv Hexpr.
  - (* Ehalt *)
    apply rt_then_t_or_eq in H. destruct H; first congruence.
    apply clos_trans_tn1 in H. inv H. inv H0. by inv H0.
Qed.

Fixpoint select_nested_if (boxed : bool) (v : immediate) (t : ctor_tag) (es : list (ctor_tag * list basic_instruction)) : list basic_instruction :=
  match es with
  | [] => [ BI_unreachable ]
  | (t0, _) :: es' =>
      if Pos.eqb t0 t then
        create_case_nested_if_chain boxed v es
      else
        select_nested_if boxed v t es'
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
    (-1 < Z.of_nat (Pos.to_nat (2 * n + 1)) < Wasm_int.Int32.modulus)%Z ->
    Wasm_int.Int32.iand (Wasm_int.Int32.repr (Z.of_nat (Pos.to_nat (2 * n + 1)))) (Wasm_int.Int32.repr 1) = Wasm_int.Int32.one.
Proof.
  intros.
  unfold Wasm_int.Int32.iand, Wasm_int.Int32.and. cbn.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; last lia.
  by rewrite positive_nat_Z.
Qed.

Lemma exists_positive : forall n,
  exists p, Pos.to_nat (p~0) = 2 * (S n).
Proof.
  induction n.
  - exists 1%positive. reflexivity.
  - destruct IHn as [p Hp].
    exists (p+1)%positive. cbn. lia.
Qed.

Lemma and_of_even_and_1_0 : forall n,
    (-1 < Z.of_nat (2 * n) < Wasm_int.Int32.modulus)%Z ->
    Wasm_int.Int32.iand (Wasm_int.Int32.repr (Z.of_nat (2 * n))) (Wasm_int.Int32.repr 1) = Wasm_int.Int32.zero.
Proof.
  intros ? H.
  unfold Wasm_int.Int32.iand, Wasm_int.Int32.and.
  - destruct n. now cbn.
  - assert (exists p, Pos.to_nat (p~0) =  2 * (S n)) by apply exists_positive.
    destruct H0 as [p Hp].
    rewrite -Hp. rewrite -Hp in H. cbn.
    rewrite Wasm_int.Int32.Z_mod_modulus_id=>//.
    now rewrite positive_nat_Z.
Qed.

Lemma ctor_tags_restricted : forall y cl t e,
    expression_restricted (Ecase y cl) ->
    In (t, e) cl ->
    (-1 < Z.of_nat (Pos.to_nat (2 * t + 1)) < Wasm_int.Int32.modulus)%Z.
Proof.
  intros ???? Hr Hin. inv Hr.
  rewrite Forall_forall in H0. apply H0 in Hin.
  destruct Hin as [Hr' _].
  simpl_modulus. cbn. cbn in Hr'. lia.
Qed.

Lemma unboxed_nested_if_chain_reduces:
  forall cl fAny y t e v lenv brs1 brs2 e2' f hs sr,
    nth_error (f_locs f) v = Some (VAL_int32 (wasm_value_to_i32 (Val_unboxed (Pos.to_nat (t  * 2 + 1))))) ->
    expression_restricted (Ecase y cl) ->
    caseConsistent cenv cl t ->
    findtag cl t = Some e ->
    get_ctor_arity cenv t = Ret 0 ->
    @repr_branches cenv fenv nenv lenv v cl brs1 brs2 ->
    repr_case_unboxed v brs2 e2' ->
    exists e' e'',
      select_nested_if false v t brs2 =
        [ BI_get_local v
          ; BI_const (nat_to_value (Pos.to_nat (2 * t + 1)))
          ; BI_relop T_i32 (Relop_i ROI_eq)
          ; BI_if (Tf nil nil)
              e'
              e'' ]
      /\ (forall k (lh : lholed k),
          exists k0 (lh0 : lholed k0),
            reduce_trans (hs, sr, fAny, [AI_local 0 f (lfill lh (map AI_basic e2'))]) (hs, sr, fAny, [AI_local 0 f (lfill lh0 (map AI_basic e'))]))
      /\ @repr_expr_LambdaANF_Wasm lenv e e'.
Proof.
  induction cl; first by move => ??????????????? //=.
  intros fAny y t e v lenv brs1 brs2 e2' f hs sr Hval HcaseRestr HcaseConsistent Hfindtag Hunboxed Hbranches Hunboxedcase.
  destruct a as [t0 e0].
  have HcaseRestr' := HcaseRestr.
  inv HcaseRestr.
  clear H0.
  have Hfindtag' := Hfindtag.
  cbn in Hfindtag.
  destruct (M.elt_eq t0 t).
  { (* t0 = t, enter the then-branch *)
    subst t0. inv Hfindtag.
    inv Hbranches.
    { (* Impossible case: t0 cannot be the tag of a non-nullary constructor *)
      assert (n=0) by congruence. lia. }
    inv Hunboxedcase.
    exists e', instrs_more.
    split. simpl.
    assert (create_case_nested_if_chain false v brs3 = instrs_more). { now apply create_case_nested_if_chain_repr_case_unboxed. }
    rewrite Pos.eqb_refl. now rewrite H.
    split=>//.
    intros.
    have Hlh := lholed_nested_label _ lh [seq AI_basic i | i <- e'] [::].
    destruct Hlh as [k' [lh' Hlheq]].
    exists k', lh'.
    (* Step through the if-then-else into the then-branch *)
    eapply reduce_trans_local'.
    eapply rt_trans. apply reduce_trans_label'.
    dostep_nary 0. apply r_get_local. eauto.
    dostep_nary 2. constructor. apply rs_relop.
    dostep'. constructor. apply rs_if_true.
    { (* Check that (t0 << 1) + 1 = (t << 1) + 1 *)
      rewrite Pos.mul_comm.
      cbn. unfold wasm_value_to_i32.
      unfold wasm_value_to_immediate.
      unfold nat_to_i32.
      unfold Wasm_int.Int32.eq.
      rewrite zeq_true.
      intro Hcontra. inv Hcontra.
    }
    dostep'. constructor. eapply rs_block with (vs:=[]); eauto.
    apply rt_refl.
    rewrite Hlheq. apply rt_refl.
  }
  { (* t0 <> t, enter the else branch (induction hypothesis) *)
    assert (Hrestr : expression_restricted (Ecase y cl)). {
      constructor.
      inv HcaseRestr'.
      now inv H0.
    }
    inv Hbranches.
    { (* t0 is the tag of a non-nullary constructor, not even in the nested if-chain *)
      inv HcaseConsistent. eapply IHcl; eauto. }
    {
      assert (HcaseConsistent' : caseConsistent cenv cl t). { inv HcaseConsistent. assumption. }
      inv Hunboxedcase.
      have IH := IHcl fAny y t e v lenv brs1 brs3 instrs_more f hs sr  Hval Hrestr HcaseConsistent' Hfindtag Hunboxed H2 H6.
      destruct IH as [e1' [e'' [Hsel [Hred Hrep]]]].
      exists e1', e''.
      split.
      unfold select_nested_if. apply Pos.eqb_neq in n. rewrite n. fold select_nested_if. assumption.
      split=>//.
      intros.
      have Hlh := lholed_nested_label _ lh [seq AI_basic i | i <- instrs_more] [::].
      destruct Hlh as [k' [lh' Hlheq]].
      have Hred' := Hred k' lh'.
      destruct Hred' as [k0 [lh0 Hstep]].
      exists k0, lh0.
      (* Step through the if-then-else into the else-branch *)
      eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'. eapply rt_trans.
      dostep_nary 0. apply r_get_local. eauto.
      dostep_nary 2. constructor. apply rs_relop.
      dostep'. constructor. apply rs_if_false.
      (* Check that (t0 << 1) + 1 <> (t << 1);
         requires some arithmetic gymnastics  *)
      {
        rewrite Pos.mul_comm. cbn.
        unfold wasm_value_to_i32. unfold wasm_value_to_immediate. unfold nat_to_i32. unfold Wasm_int.Int32.eq.
        assert (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (Pos.to_nat t~1))) = Z.of_nat (Pos.to_nat (t~1))).
        {
          apply Wasm_int.Int32.unsigned_repr.
          unfold Wasm_int.Int32.max_unsigned.
          assert ((-1 < (Z.of_nat (Pos.to_nat t~1)) < Wasm_int.Int32.modulus)%Z). {
            apply findtag_In in Hfindtag.
            eapply ctor_tags_restricted; eauto.
          }
          lia.
        }
        assert (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (Pos.to_nat t0~1))) = Z.of_nat (Pos.to_nat (t0~1))).
        {
          apply Wasm_int.Int32.unsigned_repr.
          unfold Wasm_int.Int32.max_unsigned.
          assert ((-1 < (Z.of_nat (Pos.to_nat t0~1)) < Wasm_int.Int32.modulus)%Z). {
            eapply ctor_tags_restricted with (cl:=((t0, e0) :: cl)); eauto. now constructor.
          }
          lia.
        }
        rewrite zeq_false. reflexivity. lia.
      }
      dostep'. constructor. eapply rs_block with (vs:=[]); eauto.
      apply rt_refl. apply rt_refl.
      rewrite Hlheq.
      apply Hstep.
    }
  }
Qed.

Lemma boxed_nested_if_chain_reduces:
  forall cl fAny y t vs e addr v lenv brs1 brs2 e1' (hs : host_state) (sr : store_record) (f : frame),
    INV_linear_memory sr f ->
    repr_val_LambdaANF_Wasm (Vconstr t vs) sr (f_inst f) (Val_ptr addr) ->
    nth_error (f_locs f) v = Some (VAL_int32 (wasm_value_to_i32 (Val_ptr addr))) ->
    expression_restricted (Ecase y cl) ->
    caseConsistent cenv cl t ->
    findtag cl t = Some e ->
    @repr_branches cenv fenv nenv lenv v cl brs1 brs2 ->
    repr_case_boxed v brs1 e1' ->
    exists e' e'',
      select_nested_if true v t brs1 =
        [ BI_get_local v
        ; BI_load T_i32 None 2%N 0%N
        ; BI_const (nat_to_value (Pos.to_nat t))
        ; BI_relop T_i32 (Relop_i ROI_eq)
        ; BI_if (Tf nil nil)
            e'
            e'' ]
      /\ (forall k (lh : lholed k),
            exists k0 (lh0 : lholed k0),
            reduce_trans (hs, sr, fAny, [AI_local 0 f (lfill lh (map AI_basic e1'))]) (hs, sr, fAny, [AI_local 0 f (lfill lh0 (map AI_basic e'))]))
      /\ @repr_expr_LambdaANF_Wasm lenv e e'.
Proof.
  induction cl; first by move => ???????????????????? //=.
  intros fAny y t vs e addr v lenv brs1 brs2 e1' hs sr f Hmem Hval Hlocs HcaseRestr HcaseConsistent Hfindtag Hbranches Hboxedcase.
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
    clear Hn Hngt0.
    inv Hboxedcase.
    exists e', instrs_more.
    split. cbn.
    assert (create_case_nested_if_chain true v brs0 = instrs_more). { now apply create_case_nested_if_chain_repr_case_boxed. }
    rewrite Pos.eqb_refl. congruence.
    split=>//.
    intros.
    have Hlh := lholed_nested_label _ lh (map AI_basic e') [::].
    destruct Hlh as [k' [lh' Hlheq]].
    exists k', lh'.

    (* Step through the if-then-else into the then-branch *)
    eapply reduce_trans_local'.
    eapply rt_trans. apply reduce_trans_label'.
    dostep_nary 0. apply r_get_local. eauto.
    inv Hval.
    solve_eq m m0.
    unfold load_i32 in H18.
    destruct (load m (N.of_nat addr) (N.of_nat 0) 4) eqn:Hload. 2: { cbn in Hload. rewrite Hload in H18. inv H18. }
    dostep_nary 1. eapply r_load_success; try eassumption.
    assert (N.of_nat addr = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))). {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
    }
    rewrite <- H. apply Hload.
    dostep_nary 2. constructor. apply rs_relop.
    dostep'. constructor. apply rs_if_true. {
      (* Check that t0 = t *)
      cbn.
      unfold nat_to_i32.
      unfold Wasm_int.Int32.eq.
      cbn in Hload.
      rewrite Hload in H18.
      injection H18 => H18'.
      destruct (zeq (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (decode_int b)))
                  (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (Pos.to_nat t))))) eqn:Heq.
      discriminate. contradiction.
    }
    dostep'. constructor. eapply rs_block with (vs:=[]); eauto. apply rt_refl.
    rewrite Hlheq. apply rt_refl.
  }
  { (* t0 <> t, enter the else branch (induction hypothesis) *)
    assert (Hrestr : expression_restricted (Ecase y cl)). {
      constructor.
      inv HcaseRestr'.
      now inv H0.
    }
    inv Hbranches.
    2: { (* t0 is the tag of a nullary constructor, not even in the nested if-chain *)
      inv HcaseConsistent. eapply IHcl; eauto. }
    {
      assert (HcaseConsistent' : caseConsistent cenv cl t). { inv HcaseConsistent. assumption. }
      inv Hboxedcase.
      have IH := IHcl fAny y t vs e addr v lenv brs0 brs2 instrs_more hs sr f Hmem' Hval Hlocs Hrestr HcaseConsistent' Hfindtag H3 H7.
      destruct IH as [e0' [e'' [Hsel [Hred Hrep]]]].
      exists e0', e''.
      split.
      unfold select_nested_if. apply Pos.eqb_neq in n0. rewrite n0. fold select_nested_if. assumption.
      split=>//.
      intros.

      have Hlh := lholed_nested_label _ lh [seq AI_basic i | i <- instrs_more] [::].
      destruct Hlh as [k' [lh' Hlheq]].
      have Hred' := Hred k' lh'.
      destruct Hred' as [k0 [lh0 Hstep]].
      exists k0, lh0.

      (* Step through the if-then-else into the else-branch *)
      eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'. eapply rt_trans.
      dostep_nary 0. apply r_get_local. eauto.
      inv Hval.
      solve_eq m m0.
      unfold load_i32 in H18.
      destruct (load m (N.of_nat addr) (N.of_nat 0) 4) eqn:Hload. 2: { cbn in Hload. rewrite Hload in H18. inv H18. }
      dostep_nary 1. eapply r_load_success; try eassumption.
      assert (N.of_nat addr = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))) as H. {
        cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
      }
      rewrite <- H. apply Hload.
      dostep_nary 2. constructor. apply rs_relop.
      dostep'. constructor. apply rs_if_false.
      { (* Check that t0 <> t;
         requires some arithmetic gymnastics  *)
        assert ((-1 < Z.of_nat (Pos.to_nat t) < Wasm_int.Int32.half_modulus)%Z). {
          have Hr := Forall_forall (fun p : positive * exp =>
                                      (Z.of_nat (Pos.to_nat (fst p)) < Wasm_int.Int32.half_modulus)%Z /\
                                        expression_restricted (snd p)) ((t0, e0) :: cl).
          inv HcaseRestr'.
          destruct Hr as [Hr' _].
          apply Hr' with (x:=(t, e)) in H0. cbn. cbn in H0. lia.
          inv Hfindtag.
          destruct (M.elt_eq t0 t).
          { subst t0. inv H1. now constructor. }
          { apply findtag_In in H2. now apply List.in_cons. }
        }
        assert ((-1 < Z.of_nat (Pos.to_nat t0) < Wasm_int.Int32.half_modulus)%Z). {
          have Hr := Forall_forall (fun p : positive * exp =>
                                      (Z.of_nat (Pos.to_nat (fst p)) < Wasm_int.Int32.half_modulus)%Z /\
                                        expression_restricted (snd p)) ((t0, e0) :: cl).
          inv HcaseRestr'.
          destruct Hr as [Hr' _].
          apply Hr' with (x:=(t0, e0)) in H2. cbn. cbn in H2. lia.
          now constructor.
        }

        cbn.
        unfold nat_to_i32.
        unfold Wasm_int.Int32.eq.
        cbn in Hload.
        rewrite Hload in H18.
        injection H18 => H18'.
        destruct (zeq (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (decode_int b)))
                    (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (Pos.to_nat t0))))); auto.
        inv e1.
        rewrite H18' in H15.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in H15.
        2: { simpl_modulus. cbn. simpl_modulus_in H. lia. }
        rewrite Wasm_int.Int32.Z_mod_modulus_id in H15.
        2: { simpl_modulus. cbn. simpl_modulus_in H1. lia. }
        lia.
      }
      dostep'. constructor. eapply rs_block with (vs:=[]); eauto.
      eapply rt_refl. apply rt_refl.
      rewrite Hlheq.
      apply Hstep.
    }
  }
Qed.


(* MAIN THEOREM, corresponds to 4.3.2 in Olivier's thesis *)
Theorem repr_bs_LambdaANF_Wasm_related :
  (* rho is environment containing outer fundefs. e is body of LambdaANF program *)
  forall lenv (rho : eval.env) (v : cps.val) (e : exp) (n : nat) (vars : list cps.var) (fds : fundefs)
                               fAny k (lh : lholed k),
    map_injective lenv ->
    domains_disjoint lenv fenv ->
    vars = (collect_local_variables e) ++ (collect_function_vars (Efun fds e))%list ->
    NoDup vars ->
    (* fenv maps f vars to their indices in the wasm module *)
    (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
    (* find_def a fds <> None, rho ! a imply fn value *)
    (forall (a : positive) (v : cps.val), rho ! a = Some v -> find_def a fds <> None ->
             v = Vfun (M.empty cps.val) fds a) ->

    (* restricts e w.r.t. to size s.t. all vars fit in i32s *)
    expression_restricted e ->
    (* SSA form, let-bound vars not assigned yet *)
    (forall x, In x (collect_local_variables e) -> rho ! x = None) ->
    bstep_e (M.empty _) cenv rho e v n ->  (* e n-steps to v *)
    forall (hs : host_state) (sr : store_record) (f : frame) (e' : list basic_instruction),

      (forall a t ys e errMsg, find_def a fds = Some (t, ys, e) ->
          expression_restricted e /\ (forall x, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
          NoDup (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)) /\
          (exists fidx : immediate, translate_var nenv fenv a errMsg = Ret fidx /\
                repr_val_LambdaANF_Wasm (Vfun (M.empty cps.val) fds a) sr (f_inst f) (Val_funidx fidx))) ->

      (* local vars from lenv in bound *)
      (forall var varIdx, @repr_var nenv lenv var varIdx -> varIdx < length (f_locs f)) ->

      (* invariants *)
      INV sr f ->

      (* translate_exp e returns instructions *)
      @repr_expr_LambdaANF_Wasm lenv e e' ->

      (* relates a LambdaANF evaluation environment [rho] to a Wasm environment [store/frame] (free variables in e) *)
      @rel_env_LambdaANF_Wasm lenv e rho sr f fds ->
      exists (sr' : store_record) (f' : frame) k (lh' : lholed k),
        reduce_trans (hs, sr,  fAny, [AI_local 0 f (lfill lh (map AI_basic e'))])
                     (hs, sr', fAny, [AI_local 0 f' (lfill lh' [::AI_basic BI_return])]) /\
        (* value sr'.res points to value related to v *)
        result_val_LambdaANF_Wasm v sr' (f_inst f) /\
        f_inst f = f_inst f' /\ s_funcs sr = s_funcs sr' /\
        (* previous values are preserved *)
        (forall wal val, repr_val_LambdaANF_Wasm val sr (f_inst f) wal ->
                         repr_val_LambdaANF_Wasm val sr' (f_inst f') wal) /\
        (* INV holds if program will continue to run *)
        (INV_result_var_out_of_mem_is_zero sr' f' -> INV sr' f').
Proof with eauto.
  intros lenv rho v e n vars fds fAny k lh HlenvInjective HenvsDisjoint Hvars Hnodup
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
      remember (Build_frame [N_to_value page_size] (f_inst fr)) as fM.
      assert (HinvM: INV sr fM). {
        subst fM. eapply change_locals_preserves_INV. eassumption.
        intros i ? Hl. destruct i; last by destruct i.
        inv Hl. now eexists. reflexivity.
      }
      assert (Hloc0: nth_error (f_locs fM) 0 = Some (N_to_value page_size)) by (subst fM; reflexivity). 
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

     assert (HfVal' : (forall (y : positive) (y' : immediate) (v : cps.val),
           rho ! y = Some v ->
           repr_funvar y y' ->
           repr_val_LambdaANF_Wasm v s' (f_inst fr) (Val_funidx y'))).
     { intros. destruct HrelE as [Hfun1 [Hfun2 _]].
      assert (Hfd: (exists i : nat, fenv ! y = Some i)). {
        inv H2. unfold translate_var in H3. now destruct (fenv ! y) eqn:Hy. }
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
      rewrite HeqfM in Hgmp.
      have Hconstr := store_constr_reduce state _ _ _ _ _ _ t _ _ _ _ H9 H10 HenvsDisjoint HfenvWf Hinv'
      Hmem2 Hgmp HenoughM HrelE' Hmaxargs H11 H HfVal'.
      destruct Hconstr as [s_v [Hred_v [Hinv_v [Hfuncs' [HvalPreserved' [cap_v [wal [? [<- Hvalue]]]]]]]]].
      have I := Hinv'. destruct I as [_ [_ [HoutM0 _]]].
    {
      have Hl := HlocInBound _ _ Hx'. apply nth_error_Some in Hl.
      apply notNone_Some in Hl. destruct Hl as [? Hlx].

      remember ({|f_locs := set_nth (VAL_int32 (wasm_value_to_i32 wal)) (f_locs fr) x' (VAL_int32 (wasm_value_to_i32 wal));
      f_inst := f_inst fr|}) as f_before_IH.

      assert (Hfds': forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) (errMsg : bytestring.String.t),
        find_def a fds = Some (t, ys, e) ->
          expression_restricted e /\
          (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
          NoDup
            (ys ++
             collect_local_variables e ++
             collect_function_vars (Efun fds e)) /\
          (exists fidx : immediate,
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

      assert (HlocInBound': (forall (var : positive) (varIdx : immediate),
          @repr_var nenv lenv var varIdx -> varIdx < Datatypes.length (f_locs f_before_IH))). {
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
            destruct (lenv ! x); inv H0; reflexivity.
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
            rewrite set_nth_nth_error_other; auto.
            intro. subst x'.
            inv Hx'.
            specialize Hl1 with err_str.
            unfold translate_var in Hl1, H3.
            destruct (lenv ! x1) eqn:Hlx1; inv Hl1.
            destruct (lenv ! x) eqn:Hlx2. inv H3.
            have H'' := HlenvInjective _ _ _ _ n Hlx2 Hlx1. contradiction.
            discriminate.
            apply nth_error_Some. congruence. subst fM f_before_IH.
            apply HvalPreserved'. apply HvalPreserved. assumption.
          }
        }
      }

      assert (HeRestr' : expression_restricted e). { now inv HeRestr. }

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

      eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.
      eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
      apply r_eliml=>//. elimr_nary_instr 0. apply r_call.
      apply HfuncsId. unfold grow_mem_function_idx.
      unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
      dostep_nary 1.
      eapply r_invoke_native with (ves:= [AI_basic (BI_const (N_to_value page_size))])
        (vcs:= [N_to_value page_size]) (f':=fM); try eassumption; eauto; try by (rewrite HeqfM; auto).

      eapply rt_trans. apply app_trans.
      eapply reduce_trans_local. dostep_nary' 0. constructor. eapply rs_block with (vs:=[])=>//.
      apply reduce_trans_label. apply Hred. cbn.

      dostep_nary 0. apply r_get_global. eassumption.
      dostep_nary 2. constructor. apply rs_relop. cbn.
      dostep_nary 1. constructor. apply rs_if_false. reflexivity.
      dostep_nary 0. constructor. eapply rs_block with (vs:=[]); auto.
      dostep_nary 0. constructor. apply rs_label_const; auto.

      cbn.
      repeat rewrite map_cat. cbn. repeat rewrite map_cat.

      (* take the first 10 instr lists *)
      separate_instr. do 9! rewrite catA.
      eapply rt_trans. apply app_trans. apply Hred_v.

      clear Hred_v. cbn. separate_instr. rewrite catA.
      eapply rt_trans. apply app_trans.
      dostep_nary 0. apply r_get_global. eassumption.

      assert (f_inst f_before_IH = f_inst fr) as Hfinst'. { subst. reflexivity. }
      dostep'. eapply r_set_local. eassumption.
      apply /ssrnat.leP. apply nth_error_Some. congruence. subst. reflexivity. apply rt_refl. cbn.
      apply rt_refl.
      eapply rt_trans. apply Hred_IH. cbn. apply rt_refl.

      subst f_before_IH fM.
      repeat (split; auto). congruence.
    }}
    { (* grow mem failed *)
    subst instructions instrs.

    (* split of dead instructions after
       (BI_if (Tf [::] [::]) [:: BI_return] [::]) *)
    separate_instr. do 4 rewrite catA.
     match goal with
     |- context C [reduce_trans (_, _, _, [:: AI_local _ _ (lfill _
        (_ ++ [:: AI_basic (BI_if (Tf [::] [::]) [:: BI_return] [::])] ++ ?es))])] =>
         let es_tail := fresh "es_tail" in
         remember es as es_tail
     end. do 4 rewrite <- catA.

    have Hlh := lholed_nested_label _ lh [AI_basic BI_return] es_tail. subst es_tail.
    destruct Hlh as [k' [lh' Heq']].

    do 3! eexists. exists lh'. split.

    eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.
    eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
    apply r_eliml=>//. elimr_nary_instr 0. apply r_call.
    apply HfuncsId. unfold grow_mem_function_idx.
    unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
    dostep_nary 1.
    eapply r_invoke_native with (ves:= [AI_basic (BI_const (N_to_value page_size))])
      (vcs:= [N_to_value page_size]) (f':=fM); try eassumption; eauto; try by (rewrite HeqfM; auto).
    eapply rt_trans. apply app_trans. eapply rt_trans.
    eapply reduce_trans_local'.
    dostep_nary' 0. constructor. eapply rs_block with (vs:=[]); auto.
    eapply reduce_trans_label. apply Hred.
    dostep_nary' 0. constructor. apply rs_local_const=>//. apply rt_refl. cbn.
    dostep_nary 0. apply r_get_global. subst fM. eassumption.
    dostep_nary 2. constructor. apply rs_relop.
    dostep_nary 1. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
    dostep_nary 0. constructor. eapply rs_block with (vs:=[]); auto. apply rt_refl. cbn.

    rewrite Heq'. apply rt_refl.
    split. right. subst fM. assumption.
    split=>//. split=>//.
    split. { intros. subst fM. apply HvalPreserved. assumption. }

    intro Hcontra. subst fM. rewrite Hcontra in HoutofM. inv HoutofM. }}}
    { (* Nullary constructor case *)

      subst. injection H as <-.

      remember ({|f_locs := set_nth ((VAL_int32
                (Wasm_int.Int32.iadd
                   (Wasm_int.Int32.ishl (nat_to_i32 (Pos.to_nat t)) (nat_to_i32 1))
                   (nat_to_i32 1)))) (f_locs fr) x' ((VAL_int32
                (Wasm_int.Int32.iadd
                   (Wasm_int.Int32.ishl (nat_to_i32 (Pos.to_nat t)) (nat_to_i32 1))
                   (nat_to_i32 1)))); f_inst := f_inst fr|}) as f_before_IH.
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
      assert (Herestr' :  expression_restricted e). {
        inv HeRestr. assumption.
      }

      assert (Hunbound' : (forall x0 : var,
        In x0 (collect_local_variables e) ->
        (map_util.M.set x (Vconstr t []) rho) ! x0 = None)). {
        intros. apply NoDup_app_remove_r in Hnodup. cbn in Hnodup. apply NoDup_cons_iff in Hnodup. rewrite M.gso. apply Hunbound. unfold collect_local_variables. cbn. fold collect_local_variables. right. assumption. destruct Hnodup as [Hx _ ]. unfold not. unfold not in Hx. intros Heq. subst x. apply Hx in H. contradiction.
      }

      assert (Hfds' :  (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) (errMsg : string),
        find_def a fds = Some (t, ys, e) ->
        expression_restricted e /\
        (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)) /\
        (exists fidx : immediate,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Wasm (Vfun (M.empty val) fds a) sr (f_inst f_before_IH) (Val_funidx fidx)))). {
        intros ? ? ? ? ? Hfd.
        apply Hfds with (errMsg:=errMsg) in Hfd.
        destruct Hfd as [? [? [? [idx [Htransf Hval]]]]]; repeat (split; try assumption).
        exists idx. split.
        assumption. subst f_before_IH.
        by eapply val_relation_func_depends_on_funcs; auto.
      }

      assert (HlocInBound': (forall (var : positive) (varIdx : immediate),
        @repr_var nenv lenv var varIdx -> varIdx < Datatypes.length (f_locs f_before_IH))). {
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

            exists (Vconstr t []), (Val_unboxed (Pos.to_nat (2 * t + 1))).
            rewrite M.gss. split. reflexivity.
            split.
            {
              unfold stored_in_locals. exists x'. split.
              - unfold translate_var. inv H7. unfold translate_var in H2. destruct (lenv ! x); inv H2; reflexivity.
              - subst f_before_IH. cbn. erewrite set_nth_nth_error_same; eauto.
                unfold nat_to_i32. cbn. unfold wasm_value_to_i32. unfold wasm_value_to_immediate.
                unfold Wasm_int.Int32.iadd. unfold Wasm_int.Int32.add.
                unfold Wasm_int.Int32.ishl. unfold Wasm_int.Int32.shl. cbn.
                repeat rewrite Znat.positive_nat_Z.
                repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia); try (inv HeRestr; lia).
                simpl. congruence.
                rewrite Wasm_int.Int32.half_modulus_modulus. inv HeRestr. lia.
            }
            {
              econstructor.
              now rewrite Pos.mul_comm.
              { inv HeRestr. simpl_modulus. cbn. simpl_modulus_in H5. lia. }
              assumption.
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
            rewrite set_nth_nth_error_other; auto.
            intro. subst x'. inv H7.
            specialize Hl1 with err_str.
            unfold translate_var in Hl1, H1.
            destruct (lenv ! x1) eqn:Hlx1; inv Hl1.
            destruct (lenv ! x) eqn:Hlx2; inv H1.
            have H'' := HlenvInjective _ _ _ _ n Hlx2 Hlx1. contradiction.
            apply nth_error_Some. congruence.
          }
        }
      }

      have IH := IHHev HNoDup' HfenvRho' Herestr' Hunbound' _ fAny lh _ HlenvInjective HenvsDisjoint
                 state sr f_before_IH _ Hfds' HlocInBound' Hinv' H6 HrelE'.
      destruct IH as [sr' [f' [k' [lh' [Hred [Hval [Hfinst [Hsfuncs [HvalPres H_INV]]]]]]]]].

      exists sr', f', k', lh'.
      split. eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.
      dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
      dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
      dostep_nary 1. eapply r_set_local with (f':=f_before_IH).
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
  - (* Eproj ctor_tag t, let x := proj_n y in e *)
    { inv Hrepr_e.
      rename H8 into Hx', H9 into Hy'.

      (* y is constr value with correct tag, arity *)
      assert (Hy : occurs_free (Eproj x t n y e) y) by constructor.
      have HrelE' := HrelE.
      destruct HrelE' as [Hfun1 [Hfun2 Hvar]].
      assert (HfdNone: find_def y fds = None). {
        apply HfenvWf_None with (f:=y) in HfenvWf. rewrite HfenvWf.
        inv Hy'. unfold translate_var in H1.
        destruct (lenv ! y) eqn:Hy'; inv H1. now apply HenvsDisjoint in Hy'. }
      apply Hvar in Hy; auto. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
      rewrite Hrho in H. inv H.
      have Hrepr' := Hrepr. inv Hrepr'.
      (* unboxed absurd *) inv H0.
      (* boxed *)
      inv Hlocal. destruct H.

      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [HfnsUpperBound [_ [_ _]]]]]]]]]]]].
      have Hextr := extract_constr_arg n vs v _ _ _ _ HfnsUpperBound H0 H9 H15.
      destruct Hextr as [bs [wal [Hload [Heq Hbsval]]]].

      remember {| f_locs := set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32)
                ; f_inst := f_inst fr
                |} as f_before_IH.

      assert (Hrm: @rel_env_LambdaANF_Wasm lenv e (map_util.M.set x v rho) sr f_before_IH fds). {
        split; intros.
        { (* funs1 *)
          destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1. rewrite M.gss in H10. inv H10. rename v0 into v.
            apply nthN_In in H0.
            have H' := subval_or_eq_constr _ _ _ t H12 H0.
            have HF := Hfun1 _ _ _ _ _ Hrho H'. destruct HF as [? [? HF]]. subst.
            apply Hfun2 with (errMsg:=""%bs) in HF.
            destruct HF as [i [Htrans Hval]].
            inv Hval. do 2 split => //.
            eapply find_def_name_in_fundefs. eassumption.
          }
          { (* x <> x1*)
            rewrite M.gso in H10; auto.
            have H' := Hfun1 _ _ _ _ _ H10 H12. destruct H' as [? [? H']]. subst.
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
            unfold translate_var in H13. unfold translate_var.
            destruct (lenv ! x); auto. inv H13. cbn.
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
              inv Hx'. unfold translate_var in H16.
              destruct (lenv ! x) eqn:Heqn; inv H16.
              specialize H13 with err_str. unfold translate_var in H13.
              destruct (lenv ! x1) eqn:Heqn'; inv H13.
              have Hcontra := HlenvInjective _ _ _ _ n0 Heqn Heqn'.
              now apply Hcontra. }
          exists x1'.
          split; auto.
          rewrite set_nth_nth_error_other; auto. eapply HlocInBound. eassumption.
        }
     }}

     assert (Hfds': (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) errMsg,
      find_def a fds = Some (t, ys, e) ->
        expression_restricted e /\
        (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++
           collect_local_variables e ++
           collect_function_vars (Efun fds e)) /\
        (exists fidx : immediate,
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

     assert (HlocInBound': (forall (var : positive) (varIdx : immediate),
        @repr_var nenv lenv var varIdx -> varIdx < Datatypes.length (f_locs f_before_IH))). {
      intros ?? Hvar'. cbn. subst f_before_IH.
      rewrite length_is_size size_set_nth maxn_nat_max -length_is_size.
      apply HlocInBound in Hvar'. lia. }

     assert (Hinv': INV sr f_before_IH). {
       subst f_before_IH. cbn.
       eapply update_local_preserves_INV. 3: reflexivity.
       assumption. apply nth_error_Some. intros. apply nth_error_Some.
       eapply HlocInBound. eassumption. }

     assert (HeRestr' : expression_restricted e). { now inv HeRestr. }
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
       rewrite M.gso in H10; auto. intro Hcontra. subst a.
       apply notNone_Some in H12. apply HfenvWf in H12. destruct H12.
       inv Hx'. destruct HenvsDisjoint as [Hd1 Hd2].
       apply Hd2 in H10. unfold translate_var in H12. now rewrite H10 in H12. }

     have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny lh _ HlenvInjective HenvsDisjoint
                      state _ _ _ Hfds' HlocInBound' Hinv' H7 Hrm.
     destruct IH as [sr' [f' [k' [lh' [Hred [Hval [Hfinst [Hsfuncs [HvalPres H_INV]]]]]]]]]. cbn in Hfinst.

     exists sr', f', k', lh'. cbn. split.
     { (* take steps *)
       have Htmp := Hy'. inversion Htmp. subst i s.

       have I := Hinv'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
       have Hly := HlocInBound _ _ Hy'.
       have Hlx := HlocInBound _ _ Hx'.
       rewrite H in H10. injection H10 as ->.

       eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.
       (* get_local y' *)
       dostep_nary 0. apply r_get_local. apply H1.
       (* add offset n *)
       dostep_nary 2. constructor. apply rs_binop_success. cbn. reflexivity.

       dostep_nary 1. eapply r_load_success.

       destruct Hlinmem as [Hmem1 [m' Hmem2]]. subst f_before_IH. eassumption. apply H9.

       assert (Har: Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (wasm_value_to_i32 (Val_ptr addr))
          (nat_to_i32 ((N.to_nat n + 1) * 4))) = (N.of_nat (4 + addr) + 4 * n)%N). {
          replace (4 + addr) with (addr + 4) by lia. replace (4*n)%N with (n*4)%N by lia. cbn.
       unfold load in Hload.
       destruct ((N.of_nat (4 + addr) + 4 * n + (0 + N.of_nat 4) <=? mem_length m)%N) eqn:Heqn. 2: inv Hload.
       apply N.leb_le in Heqn.
       destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. solve_eq m m'. subst.
       apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
       repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia). }
       rewrite Har. apply Hload.

       (* save result in x' *)
       dostep_nary 1. apply r_set_local with (vd := (wasm_deserialise bs T_i32)) (f':=f_before_IH); subst f_before_IH=>//.
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
        inv Hy'. unfold translate_var in H3. destruct (lenv ! y) eqn:Hy'; inv H1.
        now apply HenvsDisjoint in Hy'. inv H3.
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
                 @reduce_trans
                     (state, sr, fAny,
                       [AI_local 0 fr (lfill lh ([seq AI_basic i | i <-
                                           [:: BI_get_local y'
                                            ; BI_const (nat_to_value 1)
                                            ; BI_binop T_i32 (Binop_i BOI_and)
                                            ; BI_testop T_i32 TO_eqz
                                            ; BI_if (Tf [::] [::])
                                                e1'
                                                e2']]))])
                     (state, sr, fAny, [AI_local 0 fr (lfill lh0 (map AI_basic e'))])
                 /\ @repr_expr_LambdaANF_Wasm lenv e e'). {
        have Hval' := Hval.
        inv Hval.
        { (* Unboxed cases (nullary) *)
          assert (exists e' e'',
                     select_nested_if false y' t brs2 =
                       [ BI_get_local y'
                         ; BI_const (nat_to_value (Pos.to_nat (2 * t + 1)))
                         ; BI_relop T_i32 (Relop_i ROI_eq)
                         ; BI_if (Tf nil nil)
                             e'
                             e'' ]
                     /\ (forall k0 (lh0 : lholed k0),
                           exists k0' (lh0' : lholed k0'),
                           reduce_trans
                             (state, sr, fAny, [AI_local 0 fr (lfill lh0 (map AI_basic e2'))])
                             (state, sr, fAny, [AI_local 0 fr (lfill lh0' (map AI_basic e'))]))
                     /\ @repr_expr_LambdaANF_Wasm lenv e e').
          {
            destruct Hlocals as [i [Htrans_y Hlocs]].
            assert (i = y'). { inv Hy'. specialize (Htrans_y err_str). rewrite H3 in Htrans_y. inv Htrans_y. reflexivity. } subst i.
            have Hif_red := unboxed_nested_if_chain_reduces cl fAny y t e y' lenv brs1 brs2 e2' fr state sr Hlocs HeRestr H2 H1 H13 H6 H9.
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
          eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.
          dostep_nary 0. apply r_get_local. eauto.
          dostep_nary 2. constructor. apply rs_binop_success.
          cbn.
          assert (Heq: Wasm_int.Int32.iand (wasm_value_to_i32 (Val_unboxed (Pos.to_nat (t * 2 + 1)))) (nat_to_i32 1) = Wasm_int.Int32.one).
          {
            rewrite Pos.mul_comm.
            unfold wasm_value_to_i32; unfold wasm_value_to_immediate; unfold nat_to_i32.
            cbn.
            eapply and_of_odd_and_1_1. by rewrite Pos.mul_comm in H8.
          }
          rewrite Heq. reflexivity.
          dostep_nary 1. constructor. eapply rs_testop_i32.
          dostep'. constructor. apply rs_if_false. reflexivity.
          dostep'. constructor. eapply rs_block with (vs := []); auto.
          apply rt_refl.
          rewrite -He2' in Hred'. apply Hred'.
        }
        { (* Boxed cases (non-nullary) *)
          assert (exists e' e'',
                     select_nested_if true y' t brs1 =
                       [ BI_get_local y'
                         ; BI_load T_i32 None 2%N 0%N
                         ; BI_const (nat_to_value (Pos.to_nat t))
                         ; BI_relop T_i32 (Relop_i ROI_eq)
                         ; BI_if (Tf nil nil)
                             e'
                             e'' ]
                     /\ (forall k0 (lh0 : lholed k0),
                           exists k0' (lh0' : lholed k0'),
                           reduce_trans
                             (state, sr, fAny, [AI_local 0 fr (lfill lh0 (map AI_basic e1'))])
                             (state, sr, fAny, [AI_local 0 fr (lfill lh0' (map AI_basic e'))]))
                     /\ @repr_expr_LambdaANF_Wasm lenv e e').
          {
            destruct Hlocals as [i [Htrans_y Hlocs]].
            assert (i = y'). { inv Hy'. specialize (Htrans_y err_str). rewrite H3 in Htrans_y. inv Htrans_y. reflexivity. } subst i.
            destruct Hinv as [_ [_ [_ [_ [_ [_ [Hmem _]]]]]]].
            have Hif_red := boxed_nested_if_chain_reduces cl fAny y t vl e addr y' lenv brs1 brs2 e1' state sr fr Hmem Hval' Hlocs HeRestr H0 H1 H6 H7.
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
          eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.
          dostep_nary 0. apply r_get_local. rewrite H3 in Hntherror. eauto.
          assert (Hand : Wasm_int.Int32.iand (wasm_value_to_i32 (Val_ptr addr)) (nat_to_i32 1) = Wasm_int.Int32.zero). {
            destruct H13 as [n0 Hn0].
            rewrite Hn0.
            unfold wasm_value_to_i32; unfold wasm_value_to_i32; unfold nat_to_i32. unfold wasm_value_to_immediate.
            apply and_of_even_and_1_0.
            lia.
          }
          dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
          dostep_nary 1. constructor. apply rs_testop_i32. cbn.
          dostep'. constructor. apply rs_if_true. by rewrite Hand.
          dostep'. constructor. eapply rs_block with (vs := []); auto.
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

      assert (HeRestr': expression_restricted e). {
        inv HeRestr.
        rewrite Forall_forall in H4.
        apply H4 with (x:=(t,e)).
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
                     (state, sr, fr, [AI_basic (BI_const (nat_to_value fidx))]) /\
        repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f') sr (f_inst fr) (Val_funidx fidx)). {

      inv H8.
      { (* indirect call *)
        assert (Hocc: occurs_free (Eapp f t ys) f) by constructor.
        have Hrel := HrelE. destruct Hrel as [Hfun1 [_ Hvar]].
        assert (HfNone: find_def f fds = None). {
          apply HfenvWf_None with (f:=f) in HfenvWf. rewrite HfenvWf.
          inv H3. unfold translate_var in H4. destruct (lenv ! f) eqn:Hf'; inv H4.
          now apply HenvsDisjoint in Hf'. }
        apply Hvar in Hocc; auto. destruct Hocc as [val [wal [Hrho [[j [Htrans Hwal]] Hval]]]].
        inv H3. rewrite Htrans in H4. inv H4.
        rewrite H in Hrho. inv Hrho. inv Hval.
        rewrite H1 in H6. symmetry in H6. inv H6.
        rename i into locIdx.
        exists idx. split.
        dostep'. apply r_get_local. eassumption. apply rt_refl.
        econstructor; eauto. }
      { (* direct call *)
        inv H3. unfold translate_var in H4. destruct (fenv ! f) eqn:Hf; inv H4.
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
    rewrite H9 in H1. inv H1. rename H16 into Hexpr.

    repeat rewrite map_cat. cbn.
    have Hfargs := fun_args_reduce state _ _ _ _ _ _ _ _ _ Hinv H0 HenvsDisjoint HfenvWf HfenvRho HrelE H7.
    destruct Hfargs as [args [HfargsRed HfargsRes]].

    remember {| f_locs := [seq nat_to_value a | a <- args] ++
                     n_zeros (repeat T_i32 (Datatypes.length (collect_local_variables e)));
               f_inst := f_inst fr |} as f_before_IH.

    (* prepare IH *)
    remember (create_local_variable_mapping (xs ++(collect_local_variables e))) as lenv_before_IH.

    assert (Hfds_before_IH: (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) errMsg,
      find_def a fds = Some (t, ys, e) ->
        expression_restricted e /\
        (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++
           collect_local_variables e ++
           collect_function_vars (Efun fds e)) /\
        (exists fidx : immediate,
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

    assert (HlocInBound_before_IH: (forall (var : positive) (varIdx : immediate),
          @repr_var nenv (create_local_variable_mapping (xs ++ collect_local_variables e)) var varIdx ->
           varIdx < Datatypes.length (f_locs f_before_IH))). {
      intros ?? Hvar. subst f_before_IH. cbn. inv Hvar. apply var_mapping_list_lt_length in H1.
      rewrite app_length in H1. apply const_val_list_length_eq in HfargsRes.
      rewrite app_length. rewrite map_length -HfargsRes.
      rewrite map_repeat_eq. do 2! rewrite map_length. apply set_lists_length_eq in H2.
      now rewrite -H2.
    }

    assert (Hinv_before_IH : INV sr f_before_IH). {
       subst. eapply init_locals_preserves_INV; try eassumption; try reflexivity.
       intros.
       repeat f_equal. unfold n_zeros. rewrite map_repeat_eq.
       rewrite <- map_map_seq. cbn. now erewrite map_repeat_eq. }

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

        unfold stored_in_locals. subst lenv_before_IH f_before_IH. exists k'.
        split. {
          intros. unfold create_local_variable_mapping.
          rewrite (var_mapping_list_lt_length_nth_error_idx _ k'); auto.
          apply Hfds with (errMsg:=""%bs) in H9. destruct H9 as [_ [_ [HnodupE _]]].
          rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE. assumption.
          rewrite nth_error_app1; auto. apply nth_error_Some. intro.
          rewrite H5 in Hxk. inv Hxk. }
        cbn.
        rewrite nth_error_app1. 2: {
          rewrite length_is_size size_map -length_is_size.
          apply const_val_list_length_eq in HfargsRes.
          rewrite -HfargsRes.
          apply nth_error_Some. congruence. } assumption.
        subst f_before_IH. assumption. }
    }

    assert (HeRestr' : expression_restricted e). {
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
          destruct (fenv ! x); auto. exfalso. eauto. }
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
    eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.

    eapply rt_trans. apply app_trans. apply HfargsRed.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    separate_instr. apply app_trans. apply HredF.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    dostep'. apply r_return_call_indirect_success. eapply r_call_indirect_success; eauto.
    { (* table identity map *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htableid _]]]]]]]]]]]].
      inv H6. eapply Htableid. eassumption. }
    { (* type *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htype _]]]]]]]]]]]]].
      assert (Hlen: length xs = length ys). {
        apply set_lists_length_eq in H2.
        apply get_list_length_eq in H0. rewrite H2 H0. reflexivity. }
      rewrite Htype. 2: { inv HeRestr. congruence. } rewrite -Hlen. cbn. inv H9.
      now rewrite map_repeat_eq. } apply rt_refl. apply rt_refl.

    (* TODO cleanup *)
    dostep'. eapply r_return_invoke with (a:=fidx); try eassumption; try reflexivity.
    apply map_const_const_list.
    do 2! rewrite map_length.
    apply const_val_list_length_eq in HfargsRes.
    apply set_lists_length_eq in H2. rewrite H2. congruence.

    dostep'.
    eapply r_invoke_native with (vcs:= map (fun a => (nat_to_value a)) args)
                                        (f':=f_before_IH); try eassumption.
    rewrite -Hfinst. subst f_before_IH.
    reflexivity. unfold v_to_e_list. now rewrite -map_map_seq.
    reflexivity. reflexivity.
    { rewrite map_length length_is_size length_is_size size_map
              -length_is_size -length_is_size.
    apply const_val_list_length_eq in HfargsRes.
    apply set_lists_length_eq in H2. rewrite H2. assumption. }
    reflexivity. reflexivity. subst; reflexivity. cbn.
    dostep'. apply r_local. constructor. eapply rs_block with (vs:=[]); auto. cbn.
    (* apply IH *)
    apply Hred.

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
                     (state, sr, fr, [AI_basic (BI_const (nat_to_value fidx))])
     /\ @repr_val_LambdaANF_Wasm (Vfun (M.empty _) fds f') sr (f_inst fr) (Val_funidx fidx)
     /\ exists e_body', @repr_expr_LambdaANF_Wasm (create_local_variable_mapping (xs ++ collect_local_variables e_body)%list) e_body e_body'). {
      inv H12.
      { (* indirect call *)
        assert (Hocc: occurs_free (Eletapp x_res f t ys e_cont) f). { constructor. by left. }
        have Hrel := HrelE. destruct Hrel as [_ Hlocals].
        assert (HfNone: find_def f fds = None). {
          apply HfenvWf_None with (f:=f) in HfenvWf. rewrite HfenvWf.
          inv H3. unfold translate_var in H4. destruct (lenv ! f) eqn:Hf'; inv H4.
          now apply HenvsDisjoint in Hf'. }
        apply Hlocals in Hocc; auto. destruct Hocc as [val [wal [Hrho [[j [Htrans Hwal]] Hval]]]].
        inv H3. rewrite Htrans in H4. inv H4.
        rewrite H in Hrho. inv Hrho. inv Hval.
        rewrite H1 in H6. symmetry in H6. inv H6.
        rename i into locIdx.
        exists idx. split.
        dostep'. apply r_get_local. eassumption. apply rt_refl. split.
        econstructor; eauto. eauto. }
      { (* direct call *)
        inv H3. unfold translate_var in H4. destruct (fenv ! f) eqn:Hf; inv H4.
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
    rewrite H7 in H1. inv H1. rename H18 into Hexpr.

    repeat rewrite map_cat. cbn.
    have HrelE' := rel_env_app_letapp _ _ _ _ _ _ _ _ _ HrelE.
    have Hfargs := fun_args_reduce state _ _ _ _ _ _ _ _ _ Hinv H0 HenvsDisjoint HfenvWf HfenvRho HrelE' H11.
    destruct Hfargs as [args [HfargsRed HfargsRes]].

    remember {| f_locs := [seq nat_to_value a | a <- args] ++
                     n_zeros (repeat T_i32 (Datatypes.length (collect_local_variables e_body)));
               f_inst := f_inst fr |} as f_before_IH.

    (* prepare IH1 for e_body *)
    remember (create_local_variable_mapping (xs ++ collect_local_variables e_body)) as lenv_before_IH.

    assert (Hfds_before_IH: (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) errMsg,
      find_def a fds = Some (t, ys, e) ->
        expression_restricted e /\
        (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++
           collect_local_variables e ++
           collect_function_vars (Efun fds e)) /\
        (exists fidx : immediate,
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

    assert (HlocInBound_before_IH: (forall (var : positive) (varIdx : immediate),
          @repr_var nenv (create_local_variable_mapping (xs ++ collect_local_variables e_body)) var varIdx -> varIdx < Datatypes.length (f_locs f_before_IH))). {
      intros ?? Hvar. subst f_before_IH. cbn. inv Hvar. apply var_mapping_list_lt_length in H1.
      rewrite app_length in H1. apply const_val_list_length_eq in HfargsRes.
      rewrite app_length. rewrite map_length -HfargsRes.
      rewrite map_repeat_eq. do 2! rewrite map_length. apply set_lists_length_eq in H2.
      now rewrite -H2.
    }

    assert (Hinv_before_IH : INV sr f_before_IH). {
       subst. eapply init_locals_preserves_INV; try eassumption; try reflexivity.
       intros.
       repeat f_equal. unfold n_zeros. rewrite map_repeat_eq.
       rewrite <- map_map_seq. cbn. now erewrite map_repeat_eq. }

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

        unfold stored_in_locals. subst lenv_before_IH f_before_IH. exists k'.
        split. {
          intros. unfold create_local_variable_mapping.
          rewrite (var_mapping_list_lt_length_nth_error_idx _ k'); auto.
          apply Hfds with (errMsg:=""%bs) in H7. destruct H7 as [_ [_ [HnodupE _]]].
          rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE. assumption.
          rewrite nth_error_app1; auto. apply nth_error_Some. intro.
          rewrite H5 in Hxk'. inv Hxk'. }
        cbn.
        rewrite nth_error_app1. 2: {
          rewrite length_is_size size_map -length_is_size.
          apply const_val_list_length_eq in HfargsRes.
          rewrite -HfargsRes.
          apply nth_error_Some. congruence. } assumption.
        subst f_before_IH. assumption. }
    }

    assert (HeRestr' : expression_restricted e_body). {
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
          destruct (fenv ! x); auto. exfalso. eauto. }
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
      reduce_trans (state, sr_after_call, fAny, [AI_local 0 fr (lfill lh ([ AI_basic (BI_get_global result_out_of_mem)
                                                                         ; AI_basic (BI_if (Tf [::] [::]) [:: BI_return ] [::])
                                                                         ; AI_basic (BI_get_global result_var)
                                                                         ; AI_basic (BI_set_local x') ] ++ (map AI_basic e')))])
                   (state, sr_final, fAny, [AI_local 0 fr_final (lfill lh' [:: AI_basic BI_return])])
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
        remember ({|f_locs := set_nth (VAL_int32 w) (f_locs fr) x' (VAL_int32 (wasm_value_to_i32 wal));
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

        assert (HeRestr': expression_restricted e_cont). { now inv HeRestr. }

        assert (Hunbound': (forall x : var, In x (collect_local_variables e_cont) ->
                               (map_util.M.set x_res v rho) ! x = None)). {
          intros.
          assert (~ In x_res (collect_local_variables e_cont)). {
            apply NoDup_app_remove_r in Hnodup. cbn in Hnodup.
            now apply NoDup_cons_iff in Hnodup. }
          rewrite M.gso; auto.
          apply Hunbound. now right. now intro.
        }

        assert (HlocInBound_before_cont_IH: (forall (var : positive) (varIdx : immediate),
          @repr_var nenv lenv var varIdx -> varIdx < Datatypes.length (f_locs f_before_cont))). {
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
            expression_restricted e /\
            (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
            NoDup
              (ys ++
               collect_local_variables e ++
               collect_function_vars (Efun fds e)) /\
            (exists fidx : immediate,
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

              have H' := step_preserves_empty_env_fds _ _ _ _ fds _ _ _ _ _ Hev1 H3.
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
              destruct (lenv ! x); auto. inv H4. cbn.
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
                destruct (lenv ! x_res) eqn:Heqn; inv H8.
                specialize H4 with err_str. unfold translate_var in H4.
                destruct (lenv ! x) eqn:Heqn'; inv H4.
                have Hcontra := HlenvInjective _ _ _ _ _ Heqn Heqn'.
                now apply Hcontra. }
              exists x1'. split; auto. subst f_before_cont. cbn.
              rewrite set_nth_nth_error_other; auto.
              have Hl := HlocInBound _ _ H9. assumption.
              subst f_before_cont f_before_IH. rewrite -Hfinst in HvalPres.
              apply HvalPres. assumption.
            }
          }
        }

        have IH_cont := IHHev2 Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny lh lenv HlenvInjective HenvsDisjoint
                   state _ _ _ Hfds_before_cont_IH HlocInBound_before_cont_IH Hinv_before_cont_IH Hexpr HrelE_before_cont_IH.
        destruct IH_cont as [sr_final [fr_final [k_final [lh_final [Hred' [Hval' [Hfinst' [Hfuncs' [HvalPres' H_INV']]]]]]]]]. clear IHHev2.

        exists sr_final, fr_final, k_final, lh_final. split.

        eapply rt_trans. apply reduce_trans_local'.
        apply reduce_trans_label'. apply app_trans.
        dostep_nary 0. apply r_get_global. subst f_before_IH. eassumption.
        dostep_nary 1. constructor. apply rs_if_false. reflexivity.
        dostep_nary 0. constructor. eapply rs_block with (vs := []); eauto. cbn.
        dostep_nary 0. constructor. apply rs_label_const =>//.
        dostep_nary 0. apply r_get_global. subst f_before_IH. eassumption.
        dostep_nary' 1. eapply r_set_local with (f' := f_before_cont).
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
         (BI_if (Tf [::] [::]) [:: BI_return] [::]) *)
        separate_instr.
        match goal with
        |- context C [reduce_trans (_, _, _, [:: AI_local _ _ (lfill _
           (_ ++ [:: AI_basic (BI_if (Tf [::] [::]) [:: BI_return] [::])] ++ ?es))])] =>
            let es_tail := fresh "es_tail" in
            remember es as es_tail
        end.

        have Hlh := lholed_nested_label _ lh [AI_basic BI_return] es_tail. subst es_tail.
        destruct Hlh as [k' [lh' Heq']]. cbn in Heq'.

        exists sr_after_call, fr. eexists. exists lh'. split.

        eapply rt_trans.
        apply reduce_trans_local'. apply reduce_trans_label'.
        dostep_nary 0. apply r_get_global. subst f_before_IH. eassumption.
        dostep_nary 1. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
        dostep_nary 0. constructor. eapply rs_block with (vs := [])=>//. cbn. apply rt_refl.
        rewrite Heq'. apply rt_refl.

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
    eapply rt_trans. eapply reduce_trans_local'. apply reduce_trans_label'.
    eapply rt_trans. apply app_trans. apply HfargsRed.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    separate_instr. apply app_trans. apply HredF.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    apply app_trans with (es :=
             [:: AI_basic (BI_const (nat_to_value fidx));
                 AI_basic (BI_call_indirect (Datatypes.length ys))]).
    dostep'. eapply r_call_indirect_success; eauto.
    { (* table identity map *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htableid _]]]]]]]]]]]].
      inv H6. eapply Htableid. eassumption. }
    { (* type *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htype _]]]]]]]]]]]]].
      assert (Hlen: length xs = length ys). {
        apply set_lists_length_eq in H2.
        apply get_list_length_eq in H0. rewrite H2 H0. reflexivity. }
      rewrite Htype. 2: { inv HeRestr. congruence. } rewrite -Hlen. cbn. inv H9.
      now rewrite map_repeat_eq. } apply rt_refl.
    rewrite catA. cbn. eapply rt_trans.
    eapply app_trans with (es := ([seq AI_basic (BI_const (nat_to_value a)) | a <- args] ++ [:: AI_invoke fidx])).
    (* enter function *)
    dostep'. eapply r_invoke_native with (vcs:= map (fun a => (nat_to_value a)) args)
                                        (f':=f_before_IH); try eassumption.
    rewrite -Hfinst. subst f_before_IH.
    reflexivity. unfold v_to_e_list. now rewrite -map_map_seq.
    reflexivity. reflexivity.
    { rewrite map_length length_is_size length_is_size size_map
              -length_is_size -length_is_size.
    apply const_val_list_length_eq in HfargsRes.
    apply set_lists_length_eq in H2. rewrite H2. assumption. }
    reflexivity. reflexivity. subst; reflexivity. cbn.
    eapply reduce_trans_local'.
    dostep'. constructor. eapply rs_block with (vs:=[]); auto. cbn. apply rt_refl.
    (* apply IH1: function body *)
    eapply rt_trans. apply app_trans. apply Hred. apply rt_refl.
    eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.
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
      remember (Build_frame [N_to_value page_size] (f_inst fr)) as fM.
      assert (HinvM: INV sr fM). {
        subst fM. eapply change_locals_preserves_INV. eassumption.
        intros i ? Hl. destruct i; last by destruct i.
        inv Hl. now eexists. reflexivity.
      }
      assert (Hloc0: nth_error (f_locs fM) 0 = Some (N_to_value page_size)) by (subst fM; reflexivity). 
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
        assert ((Z.of_nat gmp' < Wasm_int.Int32.modulus)%Z). {
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5. simpl_modulus. cbn. lia. }

        (* There exists memory containing the new value *)
        assert (exists mem, store m (Wasm_int.N_of_uint i32m (nat_to_i32 gmp')) 0%N
                              (bits (VAL_int64 v0))
                              (t_length T_i64) = Some mem) as Htest.
        { apply enough_space_to_store. cbn.
          assert ((Datatypes.length (serialise_i64 v0)) = 8) as Hl.
          { unfold serialise_i64, encode_int, bytes_of_int, rev_if_be.
            destruct (Archi.big_endian); reflexivity. } rewrite Hl. clear Hl. cbn.
          rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
          unfold page_size in HenoughM. lia. }
        destruct Htest as [m_after_store Hm_after_store].

        remember (upd_s_mem s' (set_nth m_after_store s'.(s_mems) 0 m_after_store)) as s_prim.

        assert (HgmpPreserved: sglob_val (host_function:=host_function) s_prim (f_inst fr) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp'))). {
          subst s_prim.
          unfold upd_s_mem, sglob_val, sglob. cbn.
          unfold sglob_val, sglob in Hgmp. subst fM. cbn in Hgmp.
          destruct (inst_globs (f_inst fr)); first by inv Hgmp.
          assumption.
        }

        assert (Hgmp_v_mult_two: exists n, gmp' = 2 * n). {
          destruct Hinv' as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hgmp_mult_two]]]]]]]]]]]]].
          eapply Hgmp_mult_two; try eassumption; try lia.
          rewrite -HgmpPreserved Heqs_prim. reflexivity.
        }

        assert (HmemLengthPreserved: mem_length m = mem_length m_after_store). {
          apply mem_store_preserves_length in Hm_after_store. congruence. }

        assert (HmemPreserved: nth_error (s_mems s_prim) 0 = Some m_after_store). {
          subst s_prim. cbn. by destruct (s_mems s').
        }

        assert (Hinv_prim : INV s_prim fr). {
          subst.
          assert (mem_length m = mem_length m_after_store). {
            apply mem_store_preserves_length in Hm_after_store. congruence. }
          assert (mem_max_opt m = mem_max_opt m_after_store). {
            apply mem_store_preserves_max_pages in Hm_after_store. congruence. }
          eapply update_mem_preserves_INV. apply Hinv'. eassumption. erewrite <- H0. lia.
          congruence. exists (mem_size m); split; auto. unfold mem_size. congruence.  reflexivity. }

        remember ({|f_locs := set_nth (VAL_int32 (nat_to_i32 gmp')) (f_locs fr) x' (VAL_int32 (nat_to_i32 gmp'));
                    f_inst := f_inst fr|}) as f_before_IH.


        have I := Hinv_prim. destruct I as [_ [_ [_ [Hgmp_w _]]]].

        (* New store with gmp incremented by 8 *)
        destruct (Hgmp_w (Wasm_int.Int32.iadd (nat_to_i32 gmp') (nat_to_i32 8))) as [s_before_IH Hs_before_IH].
        edestruct i32_exists_nat as [gmp [HgmpEq HgmpBound]].
        erewrite HgmpEq in Hs_before_IH.
        assert (gmp = gmp' + 8). {
          inversion HgmpEq.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H1; try lia.
          unfold store in Hm_after_store.
          destruct ((Wasm_int.N_of_uint i32m (nat_to_i32 gmp') + 0 + N.of_nat (t_length T_i64)
                     <=? mem_length m)%N) eqn:Har. 2: by now inv Har.
          apply N.leb_le in Har. cbn in Har.
          rewrite Wasm_int.Int32.Z_mod_modulus_id in Har; try lia.
          apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
          simpl_modulus. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        subst gmp.

        assert (Hinv_before_IH : INV s_before_IH f_before_IH). {
          assert (INV s_prim f_before_IH). { eapply update_local_preserves_INV; eauto. }
          eapply update_global_preserves_INV with (i:=global_mem_ptr); eauto.
          { unfold global_mem_ptr, result_out_of_mem. lia. }
          { move => _.
            assert ((8 + 8 < Z.of_N page_size)%Z). { unfold page_size. lia. }
            lia. }
          destruct Hgmp_v_mult_two as [n Hn].
          exists (n + 4). lia.
          now subst f_before_IH.
        }

        assert (HmemPreserved': nth_error (s_mems s_before_IH) 0 = Some m_after_store). {
          subst s_prim. cbn.
          apply update_global_preserves_memory in Hs_before_IH. rewrite -Hs_before_IH. cbn.
          by destruct (s_mems s'). }

        assert (HlocInBound' : forall (var : positive) (varIdx : immediate),
                   @repr_var nenv lenv var varIdx -> varIdx < Datatypes.length (f_locs f_before_IH)). {
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

        assert (HeRestr' : expression_restricted e) by now inv HeRestr.

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
                   expression_restricted e /\
                     (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
                     NoDup (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)) /\
                     (exists fidx : immediate,
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

        assert (Hvalue : repr_val_LambdaANF_Wasm (Vprim p) s_before_IH (f_inst f_before_IH) (Val_ptr gmp')). {
          apply Rprim_v with (v:=v0) (gmp := gmp' + 8) (m := m_after_store) (addr := gmp'); auto.
          { apply update_global_get_same with (sr:=s_prim). subst f_before_IH. assumption. }
          { apply store_load_i64 in Hm_after_store; auto.
            assert (wasm_deserialise (bits (VAL_int64 v0)) T_i64 = VAL_int64 v0) by now apply deserialise_bits.
            rewrite H0 in Hm_after_store.
            replace (Wasm_int.N_of_uint i32m (nat_to_i32 gmp')) with (N.of_nat gmp') in Hm_after_store. assumption.
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

        assert (HenoughMem': (Z.of_nat gmp' + 8 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z). {
          unfold page_size in HenoughM. lia.
        }

        assert (HenoughMem'': (Z.of_nat gmp' + 8 + 8 <= Z.of_N (mem_length m_after_store) < Wasm_int.Int32.modulus)%Z). {
          unfold page_size in HenoughM. lia.
        }

        (* Before the continuation, the gmp global contains the old gmp value incremented by 8 *)
        assert (HglobalUpdatedGmp: sglob_val (host_function:=host_function) s_before_IH (f_inst fr) global_mem_ptr = Some (VAL_int32 (nat_to_i32 (gmp' + 8)))) by now apply update_global_get_same with (sr:=s_prim) (sr':=s_before_IH).

        (* All values in memory below the gmp are preserved *)
        assert (HvalsInMemPreserved: forall a, (a + 4 <= N.of_nat gmp')%N -> load_i32 m a = load_i32 m_after_store a). {
          intros a Ha.
          assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i32' m m_after_store a (Wasm_int.N_of_uint i32m (nat_to_i32 gmp')) v' (bits (VAL_int64 v0))); auto.
          cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
        }

        assert (HvalsInMemPreserved': forall a, (a + 8 <= N.of_nat gmp')%N -> load_i64 m a = load_i64 m_after_store a). {
          intros a Ha.
          assert (Hex: exists v, load_i64 m a = Some v). {
            apply enough_space_to_load_i64. lia. }
          destruct Hex as [v' Hv'].
          rewrite Hv'. symmetry.
          apply (load_store_load_i64' m m_after_store a (Wasm_int.N_of_uint i32m (nat_to_i32 gmp')) v' (bits (VAL_int64 v0))); auto.
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
              assert (~ subval_or_eq (Vfun rho' fds' f) (Vprim p)). { apply subval_or_eq_fun_not_prim. intros. congruence. }
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
              subst x1. exists (Vprim p), (Val_ptr gmp').
              rewrite M.gss. split; auto. split.
              subst f_before_IH. exists x'. cbn. split.
              inv H3.  unfold translate_var. unfold translate_var in H2. destruct (lenv ! x); inv H2; reflexivity.
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
              rewrite set_nth_nth_error_other; auto.
              intro. subst x'. inv H3.
              specialize Hl1 with err_str.
              unfold translate_var in Hl1, H2.
              destruct (lenv ! x1) eqn:Hlx1; inv Hl1.
              destruct (lenv ! x) eqn:Hlx2; inv H2.
              have H'' := HlenvInjective _ _ _ _ n Hlx2 Hlx1. contradiction.
              apply nth_error_Some. congruence.
              subst f_before_IH fM.
              by eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with (sr:=s')
                  (sr':=s_before_IH) (gmp' := gmp' + 8); eauto; try lia.
            }
          }
        }

        have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ fAny lh lenv HlenvInjective HenvsDisjoint state _ _ _ Hfds' HlocInBound' Hinv_before_IH H5 HrelE'.
        destruct IH as [s_final [f_final [k'' [lh'' [Hred_IH [Hval [Hfinst [Hsfuncs' [HvalPres H_INV]]]]]]]]].

        assert (Hfinst': f_inst f_before_IH = f_inst fr) by now subst.

        exists s_final, f_final, k'', lh''.

        split.
        eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.
        eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
        apply r_eliml=>//. elimr_nary_instr 0. apply r_call.
        apply HfuncsId. unfold grow_mem_function_idx.
        unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
        dostep_nary 1.
        eapply r_invoke_native with (ves:= [AI_basic (BI_const (N_to_value page_size))])
          (vcs:= [N_to_value page_size]) (f':=fM); try eassumption; eauto; try by (rewrite HeqfM; auto).

        eapply rt_trans. apply app_trans.
        eapply reduce_trans_local. dostep_nary' 0. constructor. eapply rs_block with (vs:=[])=>//.
        apply reduce_trans_label. apply Hred. cbn.

        dostep_nary 0. apply r_get_global. apply Hinv'.
        dostep_nary 2. constructor. apply rs_relop. cbn.
        dostep_nary 1. constructor. apply rs_if_false. reflexivity.
        dostep_nary 0. constructor. eapply rs_block with (vs:=[]) =>//.
        dostep_nary 0. constructor. apply rs_label_const=>//.

        cbn.
        dostep_nary 0. apply r_get_global. subst fM. eassumption.
        dostep_nary 2. eapply r_store_success; subst fM; eauto. rewrite -Heqs_prim. cbn.
        dostep_nary 0. apply r_get_global. apply HgmpPreserved.
        cbn. dostep_nary 1. eapply r_set_local with (f':=f_before_IH). subst f_before_IH. reflexivity.
        apply /ssrnat.leP.
        apply HlocInBound in H3. lia. subst. reflexivity.
        cbn.
        dostep_nary 0. apply r_get_global. now rewrite Hfinst'.
        dostep_nary 2. constructor. apply rs_binop_success. reflexivity.
        dostep_nary 1. apply r_set_global. rewrite HgmpEq. subst f_before_IH. eassumption.
        apply rt_refl.
        (* apply IH *)
        apply Hred_IH.

        repeat split=>//; try congruence.
        intros wal val Hval'. subst f_before_IH fM.
        apply HvalPres.
        by eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs with
           (sr:=s') (gmp := gmp') (gmp' := gmp' + 8); eauto; try lia.
      } { (* Growing the memory failed *)

       (* split of dead instructions after
         (BI_if (Tf [::] [::]) [:: BI_return] [::]) *)
        separate_instr. do 4 rewrite catA.
        match goal with
        |- context C [reduce_trans (_, _, _, [:: AI_local _ _ (lfill _
           (_ ++ [:: AI_basic (BI_if (Tf [::] [::]) [:: BI_return] [::])] ++ ?es))])] =>
            let es_tail := fresh "es_tail" in
            remember es as es_tail
        end. do 4 rewrite <- catA.

        have Hlh := lholed_nested_label _ lh [AI_basic BI_return] es_tail. subst es_tail.
        destruct Hlh as [k' [lh' Heq']]. cbn in Heq'.

        do 3! eexists. exists lh'. split.
        eapply rt_trans. apply reduce_trans_local'. apply reduce_trans_label'.
        eapply rt_trans with (y := (state, sr, fr, ?[s'] ++ ?[t'])); first (apply rt_step; separate_instr).
        apply r_eliml=>//. elimr_nary_instr 0. apply r_call.
        apply HfuncsId. unfold grow_mem_function_idx.
        unfold INV_num_functions_bounds, num_custom_funs in HfnsBound. lia.
        dostep_nary 1.
        eapply r_invoke_native with (ves:= [AI_basic (BI_const (N_to_value page_size))])
          (vcs:= [N_to_value page_size]) (f':=fM); try eassumption; eauto; try by (rewrite HeqfM; auto).

        eapply rt_trans. apply app_trans.
        eapply reduce_trans_local. dostep_nary' 0. constructor. eapply rs_block with (vs:=[])=>//.
        apply reduce_trans_label. apply Hred. cbn.

        dostep_nary 0. apply r_get_global. subst fM. eassumption.
        dostep_nary 2. constructor. apply rs_relop.
        dostep_nary 1. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
        dostep_nary 0. constructor. eapply rs_block with (vs:=[])=>//. apply rt_refl. cbn.
        rewrite Heq'. apply rt_refl.
        split. right. subst fM. assumption. split. reflexivity. split. congruence.
        split.
        { intros. subst fM. apply HvalPreserved. assumption. }
        intro Hcontra. subst fM. rewrite Hcontra in HoutofM. inv HoutofM. }
    }
  - (* Eprim *) inv Hrepr_e.
  - (* Ehalt *)
    cbn. inv Hrepr_e. destruct HrelE as [_ [_ Hvar]].
    assert (HfNone: find_def x fds = None). {
      apply HfenvWf_None with (f:=x) in HfenvWf. rewrite HfenvWf.
      inv H1. unfold translate_var in H0. destruct (lenv ! x) eqn:Hx; inv H0. now apply HenvsDisjoint in Hx. }
     destruct (Hvar x) as [v6 [wal [Henv [Hloc Hrepr]]]]; auto.
    rewrite Henv in H. inv H.

    have I := Hinv. destruct I as [INVres [_ [HMzero [Hgmp_r [_ [Hmuti32 [Hlinmem [HgmpInMem [_ [Hfuncs [Hinstglobs [_ [_ Hgmp_mult_two]]]]]]]]]]]]].
    apply global_var_w_implies_global_var_r in Hgmp_r; auto. destruct Hgmp_r.
    edestruct i32_exists_nat as [x'' [Hx'' ?]]. erewrite Hx'' in H. subst.

    destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst.
    apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
    have HinM := HgmpInMem _ _ Hmem2 H.

    unfold INV_result_var_writable, global_var_w in INVres.
    specialize INVres with (wasm_value_to_i32 wal).
    destruct INVres as [s' Hs].

    destruct Hloc as [ilocal [H4 Hilocal]]. inv H1. erewrite H4 in H2. injection H2 => H'. subst.

    exists s', fr, k, lh.  cbn. split.

    (* execute wasm instructions *)
    apply reduce_trans_local'. apply reduce_trans_label'.
    dostep_nary 0. eapply r_get_local. eassumption.
    dostep_nary' 1. apply r_set_global. eassumption. apply rt_refl.

    split.
    left. exists (wasm_value_to_i32 wal). exists wal.
    repeat split. eapply update_global_get_same. eassumption.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply Hrepr; eauto.
    eapply update_global_preserves_funcs; try eassumption.
    erewrite <- update_global_preserves_memory; try eassumption.
    simpl_modulus. cbn. lia.
    eapply update_global_get_other; try eassumption.
    unfold global_mem_ptr, result_var. lia.
    simpl_modulus. cbn. lia.
    eapply update_global_get_other; try eassumption. now intro. split; first auto.
    split. eapply update_global_preserves_funcs; eassumption.
    split. { intros.
      assert (nth_error (s_mems s') 0 = Some m). {
        now rewrite -(update_global_preserves_memory _ _ _ _ _ _ Hs). }
      assert (sglob_val (host_function:=host_function) s' (f_inst fr) global_mem_ptr =
                                                    Some (VAL_int32 (nat_to_i32 x''))). {
      erewrite update_global_get_other; try eassumption. reflexivity. now intro.
    }
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H; eauto.
    eapply update_global_preserves_funcs. eassumption.
    simpl_modulus. cbn. lia. simpl_modulus. cbn. lia.
    }
    intro H_INV. eapply update_global_preserves_INV. 7: eassumption.
    assumption. now intro. eassumption.
    eapply value_bounds; eauto.
    now intro.
    now intro.
    Unshelve. all: try assumption; try apply ""%bs; try apply [].
Qed.

End MAIN.


(* Top level corollary *)
Section INSTANTIATION.

Import host instantiation_spec.
Import Lia.
Import Relations.Relation_Operators.

Variable cenv:LambdaANF.cps.ctor_env.
Variable funenv:LambdaANF.cps.fun_env.
Variable nenv : LambdaANF.cps_show.name_env.

Variable host_function : eqType.
Variable hfn : host_function.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
(*Let administrative_instruction := administrative_instruction host_function.*)
Let host_state := host_state host_instance.
Let reduce_trans := @reduce_trans host_function host_instance.


Ltac simpl_modulus := unfold Wasm_int.Int32.modulus, Wasm_int.Int32.half_modulus, two_power_nat.

Ltac separate_instr :=
  cbn;
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end.
Ltac dostep :=
  eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s] ++ ?[t])); first apply rt_step; separate_instr.

(* only returns single list of instructions *)
Ltac dostep' :=
   eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s])); first  apply rt_step.

Definition initial_store  := {|
    (* imported funcs write_int and write_char, they are not called
       but need to be present *)
    s_funcs := [FC_func_host (Tf [T_i32] []) hfn; FC_func_host (Tf [T_i32] []) hfn];
    s_tables := nil;
    s_mems := nil;
    s_globals := nil;
  |}.

Lemma inductive_eq_dec : forall e, {exists fds e', e = Efun fds e'} + {~exists fds e', e = Efun fds e'}.
Proof.
   destruct e; try (right; move => [fds' [e' Hcontra]]; inv Hcontra; done). left. eauto.
Qed.

Lemma eqseq_true {T : eqType} : forall (l1 l2 : seq.seq T), eqseq l1 l2 = true -> l1 = l2.
Proof.
  intros. destruct (@eqseqP _ l1 l2); auto. inv H.
Qed.

Lemma store_record_eqb_true : forall s s',
  store_record_eqb (host_function:=host_function) s s' = true -> s = s'.
Proof.
  intros. unfold store_record_eqb in H.
  destruct (store_record_eq_dec _ _); auto. inv H.
Qed.

Fixpoint funcidcs (funs : nat) (startidx : nat) : list funcidx :=
  match funs with
  | 0 => []
  | S funs' => Mk_funcidx startidx :: funcidcs funs' (S startidx)
  end.

Lemma add_funcs_effect : forall s' s'' l l1 l2 f,
    fold_left
          (fun '(s, ys) (x : module_func) =>
           (add_func host_function s
              (FC_func_native (f_inst f)
                 (List.nth match modfunc_type x with
                      | Mk_typeidx n => n
                      end (inst_types (f_inst f)) (Tf [] []))
                 (modfunc_locals x) (modfunc_body x)),
           (Mk_funcidx (Datatypes.length (s_funcs s)) :: ys)%SEQ)) l
          (s', l1) = (s'', l2) ->

    (s_globals s' = s_globals s'') /\
    (s_mems s' = s_mems s'') /\
    (s_tables s' = s_tables s'') /\
    (s_funcs s'' = (s_funcs s') ++
    (map (fun a => FC_func_native (f_inst f)
                   (List.nth match modfunc_type a with
                        | Mk_typeidx n => n
                        end (inst_types (f_inst f)) (Tf [] []))
                   (modfunc_locals a) (modfunc_body a)) l ))%list /\
    l2 = List.app (List.rev (funcidcs (length l) (length (s_funcs s')))) l1.
Proof.
  intros. generalize dependent l1. revert s' s'' f l2.
  induction l; intros.
  - inv H. cbn. rewrite app_nil_r. auto.
  - cbn in H. apply IHl in H.
    destruct H as [H1 [H2 [H3 [H4 H5]]]]. subst l2. rewrite -H1 -H2 -H3 H4.
    rewrite -app_assoc. auto. cbn.
    repeat split; auto.
    cbn. rewrite app_length. cbn. now rewrite Nat.add_comm -app_assoc.
Qed.

Lemma reduce_forall_elem_effect : forall fns l f s state,
  Forall2 (fun (e : module_element) (c : Wasm_int.Int32.T) =>
                  reduce_trans (state, s, {| f_locs := []; f_inst := f_inst f |},
                    to_e_list (modelem_offset e))
                    (state, s, {| f_locs := []; f_inst := f_inst f |},
                    [AI_basic (BI_const (VAL_int32 c))]))
                 (map
                    (fun f : wasm_function =>
                     {|
                       modelem_table := Mk_tableidx 0;
                       modelem_offset :=
                         [BI_const (nat_to_value (LambdaANF_to_Wasm.fidx f))];
                       modelem_init := [Mk_funcidx (LambdaANF_to_Wasm.fidx f)]
                     |}) fns) l -> l = map (fun f => nat_to_i32 (LambdaANF_to_Wasm.fidx f)) fns.
Proof.
  induction fns; intros.
  - now inv H.
  - cbn in H. inv H. cbn in H2. apply reduce_trans_const in H2. cbn. inv H2.
    erewrite (IHfns l'); eauto.
Qed.

Lemma length_list_function_types : forall n,
  length (list_function_types n) = S n.
Proof.
  induction n; cbn; auto. f_equal. now rewrite map_length.
Qed.
Lemma nth_list_function_types : forall m n def,
    m <= n ->
    List.nth m (list_function_types n) def =
    Tf (List.repeat T_i32 m) [].
Proof.
  induction m; intros; try lia.
  - destruct n; try lia; reflexivity.
  - have Hlen := length_list_function_types n.
    destruct n. lia. assert (Hlt: m <= n) by lia.
    remember (fun t : function_type =>
      match t with
      | Tf args rt => Tf (T_i32 :: args)%SEQ rt
      end) as f.
    have Hindep := nth_indep _ _ (f def).
    rewrite Hindep; try lia.
       cbn. subst f. rewrite map_nth.
    rewrite IHm; auto.
Qed.

Lemma nth_list_function_types_map : forall fns fr,
  (forall f, In f fns -> match type f with
                         | Tf args _ => (Z.of_nat (length args) <= max_function_args)%Z
                         end) ->
  map (fun x : wasm_function =>
            FC_func_native (host_function:=host_function)  (f_inst fr)
                            (List.nth
                               match type x with
                               | Tf args _ => Datatypes.length args
                               end (list_function_types (Z.to_nat max_function_args))
                               (Tf [] [])) (locals x)
                            (body x)) fns =
  map (fun x => FC_func_native (f_inst fr)
                  (match type x with
                   | Tf args _ => Tf (repeat T_i32 (length args)) []
                   end) (locals x) (body x)) fns.
Proof.
  induction fns; intros; auto. cbn.
  rewrite nth_list_function_types. 2: {
  assert (Hargs: In a (a :: fns)). { cbn. auto. }
  apply H in Hargs. destruct (type a). unfold max_function_args in Hargs. lia. }
  f_equal. destruct (type a); reflexivity.
  rewrite IHfns; auto. intros.
  apply H. cbn. auto.
Qed.

Lemma translate_fvar_fname_mapping_aux : forall fds e f i N env,
  (forall x j, env ! x = Some j -> j < numOf_fundefs fds + N) ->
  (create_var_mapping N (collect_function_vars (Efun fds e))
        env) ! f = Some i -> i < numOf_fundefs fds + N.
Proof.
  induction fds; intros.
  - cbn. destruct i. lia.
    cbn in H0. rename H0 into Hf.
    destruct (var_dec f0 v).
    { (* f0=v *) subst f0. rewrite M.gss in Hf. inv Hf. lia. }
    { (* f0<>v *) cbn in Hf. rewrite M.gso in Hf; auto.
      eapply IHfds in Hf. lia. assumption. intros.
      apply H in H0. cbn in H0. lia. }
  - inv H0. now apply H in H2.
Qed.


Lemma translate_fvar_fname_mapping : forall e f errMsg i,
    translate_var nenv (create_fname_mapping e) f errMsg = Ret i ->
    match e with Efun fds _ => i < numOf_fundefs fds + num_custom_funs | _ => True end.
Proof.
  intros. unfold create_fname_mapping, translate_var in H.
  destruct ((create_var_mapping num_custom_funs (collect_function_vars e)
         (M.empty nat)) ! f) eqn:Hf; inv H.
  destruct e; auto. rename f0 into fds.
  have H' := translate_fvar_fname_mapping_aux _ _ _ _ _ _ _ Hf.
  apply H'. intros. inv H.
Qed.

Lemma e_offs_increasing' : forall len n i l  s fr state,
  Forall2
        (fun (e : module_element) (c : Wasm_int.Int32.T) =>
         reduce_trans
           (state, s, {| f_locs := []; f_inst := f_inst fr |},
           to_e_list (modelem_offset e))
           (state, s, {| f_locs := []; f_inst := f_inst fr |},
           [AI_basic (BI_const (VAL_int32 c))]))
        (table_element_mapping len n) l ->
 i < len ->
nth_error l i = Some (nat_to_i32 (n + i)).
Proof.
  induction len; intros; first lia.
  inv H. apply reduce_trans_const in H3. inv H3.
  destruct i.
  (* i=0 *) rewrite Nat.add_0_r. reflexivity.
  (* i=Si' *) assert (i < len) as Hi by lia. clear H0.
  cbn. replace (n + S i) with ((S n) + i) by lia.
  eapply IHlen; eauto.
Qed.

Lemma table_element_mapping_length : forall len i,
  Datatypes.length (table_element_mapping len i) = len.
Proof.
  by induction len; intros; cbn; auto.
Qed.

Lemma e_offs_increasing : forall e_offs len state s fr,
  Forall2  (fun (e : module_element) (c : Wasm_int.Int32.T) =>
               reduce_trans
                 (state, s, {| f_locs := []; f_inst := f_inst fr |}, to_e_list (modelem_offset e))
                 (state, s, {| f_locs := []; f_inst := f_inst fr |},
                 [AI_basic (BI_const (VAL_int32 c))]))
   ([{| modelem_table := Mk_tableidx 0;
       modelem_offset := [BI_const (nat_to_value 0)];
       modelem_init := [Mk_funcidx 0]
     |};
    {| modelem_table := Mk_tableidx 0;
       modelem_offset := [BI_const (nat_to_value 1)];
       modelem_init := [Mk_funcidx 1]
     |};
     {| modelem_table := Mk_tableidx 0;
        modelem_offset := [BI_const (nat_to_value 2)];
        modelem_init := [Mk_funcidx 2]
      |};
     {| modelem_table := Mk_tableidx 0;
        modelem_offset := [BI_const (nat_to_value 3)];
        modelem_init := [Mk_funcidx 3]
      |};
     {| modelem_table := Mk_tableidx 0;
        modelem_offset := [BI_const (nat_to_value 4)];
        modelem_init := [Mk_funcidx 4]
      |}] ++ (table_element_mapping len num_custom_funs))%list e_offs ->
 (forall i, i < len + num_custom_funs -> nth_error e_offs i = Some (nat_to_i32 i)) /\
 length e_offs = len + num_custom_funs.
Proof.
  intros.
  apply Forall2_app_inv_l in H.
  destruct H as [l1 [l2 [Hl1 [Hl2 Heq]]]]. subst e_offs.
  inv Hl1. inv H3. inv H5. inv H6. inv H7. inv H8.
  apply reduce_trans_const in H1, H2, H3, H4, H5.
  inv H1. inv H2. inv H3. inv H4. inv H5.
  unfold num_custom_funs.
  split.
  - intros.
    do 5 (destruct i; first reflexivity). cbn.
    assert (Hi: i < len) by lia. clear H.
    have H' := e_offs_increasing' _ _ _ _ _ _ _ Hl2 Hi. assumption.
  - apply Forall2_length in Hl2. cbn.
    rewrite table_element_mapping_length in Hl2. lia.
Qed.

Fixpoint increasing_nats (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => (increasing_nats n') ++ [n']
  end.

Lemma nth_error_funcidcs {A} : forall (l : list A) len n idx,
  n < len ->
  nth_error (map (fun '(Mk_funcidx i) => i) (funcidcs len idx)) n =
  Some (idx + n).
Proof.
  induction len; intros; cbn in H. lia.
  destruct n; cbn. f_equal. lia.
  assert (n < len) by lia.
  replace (idx + S n) with (S idx + n) by lia.
  now apply IHlen.
Qed.

Lemma init_tab_nth_error_same : forall s s' f t n anything,
  inst_tab (f_inst f) = [0] ->
  inst_funcs (f_inst f) = [:: 0, 1, 2, 3, 4 & map (fun '(Mk_funcidx i) => i)
                             (funcidcs (Datatypes.length (table_data t) - num_custom_funs) num_custom_funs)] ->
  s_tables s = [t] ->
  n < length (table_data t) ->
  init_tab host_function s (f_inst f) n {| modelem_table := (Mk_tableidx 0)
                             ; modelem_offset := anything
                             ; modelem_init := [Mk_funcidx n]
                             |} = s' ->
  exists t', s_tables s' = [t'] /\
  nth_error (table_data t') n = Some (Some n).
Proof.
  intros ? ? ? ? ? ? HinstT HinstF Ht Hlen Hinit.
  unfold init_tab in Hinit. cbn in Hinit.
  rewrite HinstT in Hinit. cbn in Hinit.
  rewrite Ht in Hinit. cbn in Hinit.
  destruct t. cbn in Hlen.
  subst. eexists. cbn. split. reflexivity.
  assert (Datatypes.length (firstn n table_data) = n). {
    rewrite firstn_length. lia. }
  rewrite nth_error_app2; try lia.
  replace (n - Datatypes.length (firstn n table_data)) with 0 by lia. cbn. f_equal.
  rewrite HinstF. cbn.
  destruct (Nat.leb_spec n 4).
  (* n <= 4 *)
  do 5 (destruct n; cbn; auto). lia.
  (* 4 < n *)
  assert ([:: 0, 1, 2, 3, 4
    & map (fun '(Mk_funcidx i) => i)
        (funcidcs (Datatypes.length table_data - num_custom_funs) num_custom_funs)] = map (fun '(Mk_funcidx i) => i)
        (funcidcs (Datatypes.length table_data) 0)). {
     assert (length table_data = num_custom_funs + (length table_data - num_custom_funs)) by (unfold num_custom_funs in *; lia).
     rewrite H1. cbn. rewrite OrdersEx.Nat_as_OT.sub_0_r. reflexivity. }
  rewrite H1.
  now erewrite nth_error_funcidcs.
Qed.

Lemma nth_error_firstn {A} : forall n' n (l : list A) val,
  nth_error l n = Some val ->
  n < n' ->
  nth_error (firstn n' l) n = Some val.
Proof.
  induction n'; intros. lia.
  cbn. destruct l. destruct n; inv H.
  destruct n; inv H. auto.
  cbn. erewrite IHn'; eauto. lia.
Qed.

Lemma init_tab_nth_error_other : forall s s' f t n n' val,
  n <> n' ->
  n' < length (table_data t) ->
  inst_tab (f_inst f) = [0] ->
  s_tables s = [t] ->
  nth_error (table_data t) n = val ->
  init_tab host_function s (f_inst f) n' {| modelem_table := (Mk_tableidx 0)
                                          ; modelem_offset := [BI_const (nat_to_value n')]
                                          ; modelem_init := [Mk_funcidx n']
                                          |} = s' ->
  exists t', s_tables s' = [t'] /\
  nth_error (table_data t') n = val.
Proof.
  intros ? ? ? ? ? ? ? Hneq Hlen HinstT Ht Hval Hinit.
  unfold init_tab in Hinit. cbn in Hinit.
  rewrite HinstT in Hinit. cbn in Hinit. rewrite Ht in Hinit.
  replace (ssrnat.addn_rec n' 1) with (S n') in Hinit. 2: { unfold ssrnat.addn_rec. lia. }
  cbn in Hinit. destruct t.

  destruct (Nat.leb_spec n' n).
  { (* n' < n *)
    assert (Hn: n' < n) by lia. clear H.
    subst. eexists. split. reflexivity. cbn.
    assert (length (firstn n' table_data) = n'). { rewrite firstn_length. cbn in Hlen. lia. }
    rewrite nth_error_app2; try lia. rewrite H.
    assert (exists m, S m = n - n'). { destruct n. lia. exists (n - n'). lia. }
    destruct H0. rewrite -H0. cbn.
    rewrite MCList.nth_error_skipn.
    replace (ssrnat.addn_rec n' 1 + x) with n. 2: { unfold ssrnat.addn_rec. lia. }
    now replace (S n' + x) with n by lia.
  }
  { (* n < n' *)
    subst. eexists. split. reflexivity. cbn. cbn in Hlen.
    rewrite nth_error_app1. 2: { rewrite firstn_length. lia. }
    assert (Hlen' : n < length table_data) by lia.
    apply nth_error_Some in Hlen'. apply notNone_Some in Hlen'; auto. destruct Hlen'.
    erewrite nth_error_firstn; eauto. }
Qed.

Lemma init_tab_preserves_length : forall s s' f t t' n n',
  n' < length (table_data t) ->
  inst_tab (f_inst f) = [0] ->
  s_tables s = [t] ->
  init_tab host_function s (f_inst f) n' {| modelem_table := (Mk_tableidx 0)
                                          ; modelem_offset :=  [BI_const (nat_to_value n)]
                                          ; modelem_init := [Mk_funcidx n]
                                          |} = s' ->
  s_tables s' = [t'] -> length (table_data t') = length (table_data t).
Proof.
  intros ? ? ? ? ? ? ? Hlen HinstT Ht Hinit Ht'.
  unfold init_tab in Hinit. cbn in Hinit.
  rewrite HinstT in Hinit. cbn in Hinit. rewrite Ht in Hinit. cbn in Hinit.
  destruct t. subst. inv Ht'. cbn. cbn in Hlen.
  rewrite app_length. cbn. rewrite firstn_length. rewrite skipn_length.
  unfold ssrnat.addn_rec. lia.
Qed.

Lemma init_tabs_effect_general : forall iis vvs t s s' f,
  inst_funcs (f_inst f) = [:: 0, 1, 2, 3, 4 & map (fun '(Mk_funcidx i0) => i0)
                          (funcidcs (Datatypes.length (table_data t) - num_custom_funs) num_custom_funs)] ->
  s_tables s = [t] ->
  vvs = map (fun i => {| modelem_table := Mk_tableidx 0;
                         modelem_offset := [ BI_const (nat_to_value i) ]
;
                         modelem_init := [Mk_funcidx i] |}) iis ->
  NoDup iis ->
  (forall i, In i iis -> i < length (table_data t)) ->
  table_max_opt t = None ->
  s' = init_tabs host_function s (f_inst f) iis vvs ->
  inst_tab (f_inst f) = [0] ->
  exists t', (forall i,   In i iis -> nth_error (table_data t') i = Some (Some i))
          /\ (forall i, ~ In i iis -> nth_error (table_data t') i = nth_error (table_data t) i)
          /\ table_max_opt t' = None
          /\ s_tables s' = [t'].
Proof.
  unfold init_tabs. induction iis; intros ? ? ? ? ? HinstF Ht Hvvs Hnodup Hilen HtNone Hs' HinstT.
  { destruct vvs; try inv Hvvs. cbn. exists t. now intros. }
  { cbn in Hvvs. subst vvs.
    remember (map
                (fun i : nat =>
                 {| modelem_table := Mk_tableidx 0;
                    modelem_offset := [BI_const (nat_to_value i)];
                    modelem_init := [Mk_funcidx i] |}) iis) as vvs.
    assert (Hnodup': NoDup iis). { now inv Hnodup. }
    cbn in Hs'.
    assert (Hext: exists t, s_tables
       (init_tab host_function s (f_inst f) a
          {|
            modelem_table := Mk_tableidx 0;
            modelem_offset := [ BI_const (nat_to_value a) ];
            modelem_init := [Mk_funcidx a]
          |}) = [t] /\ table_max_opt t = None). {
      unfold init_tab. cbn. rewrite HinstT.
      cbn. rewrite Ht. cbn. destruct t. cbn.
      eexists. split; auto. }
    destruct Hext as [t' [Ht' Htnone]].
    assert (Halen: a < length (table_data t)). { apply Hilen. now cbn. }
    have HlenEq := init_tab_preserves_length _ _ _ _ _ _ _ Halen HinstT Ht Logic.eq_refl Ht'. clear Halen.
    rewrite <- HlenEq in HinstF.
    assert (Hilen' : forall i : nat, In i iis -> i < Datatypes.length (table_data t')).
     { intros. rewrite HlenEq. apply Hilen. now cbn. }
    have IH := IHiis vvs _ _ _ _ HinstF Ht' Logic.eq_refl Hnodup' Hilen' Htnone Hs' HinstT.
    destruct IH as [t'' [IH1 [IH2 [IHnone Ht'']]]].
    exists t''. cbn. split; intros.
    { (* if i in (a::is) then is set in table *)
      destruct H.
      { (* i=a *) subst a.
        assert (Hnotin: ~ In i iis) by (now inv Hnodup).
        apply IH2 in Hnotin. rewrite Hnotin.
        remember (init_tab host_function s (f_inst f) i
             {|
               modelem_table := Mk_tableidx 0;
               modelem_offset := [BI_const (nat_to_value i)];
               modelem_init := [Mk_funcidx i]
             |}) as sIH. symmetry in HeqsIH.
             rewrite HlenEq in HinstF.
             assert (Hilen'': i < Datatypes.length (table_data t)). { apply Hilen. now cbn. }
        have H' := init_tab_nth_error_same _ _ _ _ _ _ HinstT HinstF Ht Hilen'' HeqsIH.
        edestruct H' as [tfinal [Ht1 Ht2]].
        assert (tfinal = t') by congruence. congruence. }
      { (* i<>a *) now apply IH1. }
    }
    { (* if i not in (a::is) then the previous value is still in table *)
      split; intros; auto.
      assert (Hai: a <> i) by auto.
      assert (Hnotin: ~ In i iis) by auto. clear H IH1.
      apply IH2 in Hnotin. rewrite Hnotin. clear Hnotin.
      remember (init_tab host_function s (f_inst f) a
           {|
             modelem_table := Mk_tableidx 0;
             modelem_offset :=  [ BI_const (nat_to_value a) ];
             modelem_init := [Mk_funcidx a]
           |}) as sEnd. symmetry in HeqsEnd. assert (Hia: i<>a) by auto. clear Hai.
      assert (Halen: a < Datatypes.length (table_data t)). { apply Hilen. now cbn. }
      have H' := init_tab_nth_error_other _ _ _ _ _ _ _ Hia Halen HinstT Ht Logic.eq_refl HeqsEnd.
      destruct H' as [t''' [Ht1 Ht2]]. congruence.
   }}
Qed.

Lemma init_tabs_only_changes_tables : forall s s' f l1 l2,
  length l1 = length l2 ->
  s' = init_tabs host_function s (f_inst f) l1 l2 ->
     s_funcs s = s_funcs s'
  /\ s_mems s = s_mems s'
  /\ s_globals s = s_globals s'.
Proof.
  intros. subst. revert s f l2 H.
  induction l1; intros; cbn; auto.
  destruct l2; first inv H.
  assert (Hlen: length l1 = length l2). { cbn in H. lia. } clear H.
  have IH := IHl1 (init_tab host_function s (f_inst f) a m) f _ Hlen.
  destruct IH as [IH1 [IH2 IH3]]. cbn. unfold init_tabs in IH2.
  rewrite -IH1 -IH2 -IH3.
  unfold init_tab.
  now destruct (List.nth _ _ _).
Qed.

Lemma eoffs_nodup : forall e_offs,
  (Z.of_nat (Datatypes.length e_offs) < Wasm_int.Int32.modulus)%Z ->
  (forall i, i < Datatypes.length e_offs ->
             nth_error e_offs i = Some (nat_to_i32 i)) ->
  NoDup [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_offs].
Proof.
  intros ? HmaxLen Hvals.
  apply NoDup_nth_error. intros ? ? Hlen Hsame.
  do 2! rewrite nth_error_map in Hsame.
  rewrite map_length in Hlen.
  rewrite Hvals in Hsame; auto.
  destruct (Nat.ltb_spec j (length e_offs)).
  { (* j < length e_offs *)
    rewrite Hvals in Hsame; auto. inv Hsame.
    repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H1; try lia.
  }
  { (* j >= length e_offs *)
    cbn in Hsame.
    apply nth_error_None in H.
    rewrite H in Hsame. inv Hsame.
  }
Qed.

Lemma table_element_mapping_nth: forall len n startIdx,
  n < len ->
  nth_error (table_element_mapping len startIdx) n =
  Some {| modelem_table := Mk_tableidx 0;
          modelem_offset := [BI_const (nat_to_value (n + startIdx))];
          modelem_init := [Mk_funcidx (n + startIdx)] |}.
Proof.
  induction len; intros; first lia.
  destruct n.
  - (* n=0 *) reflexivity.
  - (* n=Sn'*) cbn. replace (S (n + startIdx)) with (n + (S startIdx)) by lia.
               now apply IHlen.
Qed.

Lemma table_element_mapping_alternative : forall e_offs,
  (forall i : nat,
            i < Datatypes.length e_offs ->
            nth_error e_offs i = Some (nat_to_i32 i)) ->
  (Z.of_nat (Datatypes.length e_offs) < Wasm_int.Int32.modulus)%Z ->
  table_element_mapping (Datatypes.length e_offs) 0 = map
  (fun i : nat =>
   {|
     modelem_table := Mk_tableidx 0;
     modelem_offset := [BI_const (nat_to_value i)];
     modelem_init := [Mk_funcidx i]
   |}) [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_offs].
Proof.
  intros.
  apply nth_error_ext. intros.
  destruct (Nat.ltb_spec n (length e_offs)).
  { (* n < length e_offs *)
    do 2! rewrite nth_error_map. rewrite H; auto. cbn.
    repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
    rewrite table_element_mapping_nth; auto. repeat f_equal; try lia.
  }
  { (* n >= length e_offs *)
    have H' := H1. apply nth_error_None in H1.
    do 2! rewrite nth_error_map. rewrite H1. cbn.
    apply nth_error_None. now rewrite table_element_mapping_length.
  }
Qed.


Lemma init_tabs_effect : forall s s' f e_offs t,
  s_tables s = [t] ->
  table_max_opt t = None ->
  inst_tab (f_inst f) = [0] ->
  inst_funcs (f_inst f) =
     [:: 0, 1, 2, 3, 4
       & map (fun '(Mk_funcidx i0) => i0)
           (funcidcs (Datatypes.length (table_data t) - num_custom_funs) num_custom_funs)] ->
  s' = init_tabs host_function s (f_inst f)
          [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_offs]
          (table_element_mapping (length e_offs) 0) ->
  (forall i : nat,
             i < Datatypes.length e_offs ->
             nth_error e_offs i = Some (nat_to_i32 i)) ->
  (Z.of_nat (Datatypes.length e_offs) < Wasm_int.Int32.modulus)%Z ->
  length e_offs = length (table_data t) ->
  exists t, s_tables s' = [t]
         /\ (forall i : nat, In i [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_offs] ->
             nth_error (table_data t) i = Some (Some i))
         /\ table_max_opt t = None
         /\ s_tables s' = [t]
         /\ s_funcs s' = s_funcs s
         /\ s_mems s' = s_mems s
         /\ s_globals s' = s_globals s.
Proof.
  intros ? ? ? ? ? Ht HtNone HinstT HinstF Hinit HeoffsVal HeoffsMaxLen HlenEq.
  have Hmapping := table_element_mapping_alternative _ HeoffsVal HeoffsMaxLen.
  assert (Hnodup: NoDup [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_offs]). {
    apply eoffs_nodup; auto.
  }
  assert (HoffsLeLen: (forall i : nat,
      In i [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_offs] ->
      i < Datatypes.length (table_data t))). {
   intros. apply In_nth_error in H.
   destruct H as [idx H].
   assert (idx < length e_offs). {
     apply nth_error_Some.
     rewrite nth_error_map in H. intro. rewrite H0 in H. inv H.
   }
   rewrite nth_error_map in H.
   rewrite HeoffsVal in H; auto. cbn in H. inv H; auto.
   rewrite Wasm_int.Int32.Z_mod_modulus_id; lia.
  }
  have H' := init_tabs_effect_general _ _ _ _ _ _ HinstF Ht Hmapping Hnodup HoffsLeLen HtNone Hinit HinstT.
  destruct H' as [t' [HtVals [_ [Hnone Ht']]]].
  assert (Hlen: length [seq Z.to_nat (Wasm_int.Int32.intval o) | o <- e_offs] =
                length (table_element_mapping (Datatypes.length e_offs) 0)). {
    rewrite length_is_size size_map -length_is_size.
    now rewrite table_element_mapping_length.
  }
  have H' := init_tabs_only_changes_tables _ _ _ _ _ Hlen Hinit.
  destruct H' as [H1' [H2' H3']].
  exists t'. repeat (split; auto).
Qed.

Lemma translate_functions_exists_original_fun : forall fds fds'' fns wasmFun e eAny fenv,
  NoDup (collect_function_vars (Efun fds e)) ->
  translate_functions nenv cenv fenv fds = Ret fns ->
  fenv = create_fname_mapping (Efun fds'' eAny) ->
  In wasmFun fns ->
  exists f t ys e, find_def f fds = Some (t, ys, e) /\ match wasmFun.(type) with
                                                       | Tf args _ => length ys = length args
                                                       end /\ @repr_funvar fenv nenv f (wasmFun.(fidx)).
Proof.
  induction fds; intros fds'' fns wasmFun e' eAny fenv Hnodup Htrans Hfenv Hin. 2: { inv Htrans. inv Hin. }
  simpl in Htrans.
  destruct (translate_function nenv cenv _ v l e) eqn:transF. inv Htrans.
  cbn. destruct (translate_functions _ _ _ ) eqn:Htra; inv Htrans. destruct Hin.
  - (* wasmFun is first fn *) subst w.
    exists v, f, l, e. destruct (M.elt_eq); last contradiction.
    split; auto.
    unfold translate_function in transF.
    destruct (translate_var _ _ _ _) eqn:HtransFvar. inv transF.
    destruct (translate_exp _ _ _ _) eqn:HtransE. inv transF.
    inv transF. cbn. split; first by rewrite map_length. now econstructor.
  - (* wasmFun is not first fn *)
    eapply IHfds in H; eauto. 2: { now inv Hnodup. }
    destruct H as [f' [t' [ys' [e'' [Hfdef Hty]]]]].
    exists f', t', ys', e''. split; auto. rewrite -Hfdef.
    destruct (M.elt_eq f' v); auto. subst v. exfalso.
    inv Hnodup. apply H1. clear H2. cbn.
    now eapply find_def_in_collect_function_vars.
Unshelve. all: assumption.
Qed.

Lemma translate_functions_length {fenv} : forall fds fns,
  translate_functions nenv cenv fenv fds = Ret fns ->
  numOf_fundefs fds = length fns.
Proof.
  induction fds; intros. 2: { now inv H. }
  simpl in H.
  destruct (translate_function nenv cenv fenv v l e). inv H.
  destruct (translate_functions _ _ _ fds). inv H. destruct fns; inv H. cbn. now rewrite -IHfds.
Qed.

Lemma translate_functions_fenv : forall fds fns fenv e i x,
  map_injective fenv ->
  translate_functions nenv cenv fenv fds = Ret fns ->
  i < numOf_fundefs fds ->
  nth_error (collect_function_vars (Efun fds e)) i = Some x ->
  option_map (fun f => fidx f) (nth_error fns i) = fenv ! x.
Proof.
  induction fds; intros ????? Hinj Hfns Hlt Hnth. 2:{ cbn in Hlt. lia. }
  destruct fns; first by apply translate_functions_length in Hfns. simpl in Hfns.
  destruct (translate_function _ _ _ _ _ _) eqn:HtransF. inv Hfns.
  destruct (translate_functions _ _ _ _) eqn:Hfuns; inv Hfns.
  destruct i.
  - (* i=0 *)
    cbn. inv Hnth.
    unfold translate_function in HtransF.
    destruct (translate_var _ _ _ _) eqn:HtransV. inv HtransF.
    destruct (translate_exp _ _ _ _ _). inv HtransF. inv HtransF.
    unfold translate_var in HtransV.
    by destruct (fenv ! x) eqn:HtransV'; inv HtransV.
  - (* i=Si' *)
    cbn in Hlt. cbn.
    eapply IHfds; eauto. lia.
Unshelve. assumption.
Qed.

Lemma translate_functions_idx_bounds : forall fds fns fenv min max,
  (forall f f', fenv ! f = Some f' -> min <= f' < max) ->
  translate_functions nenv cenv fenv fds = Ret fns ->
  forall idx, In idx (map fidx fns) -> min <= idx < max.
Proof.
  induction fds; intros ???? Hbounds Hfns ? Hin; last by inv Hfns.
  destruct fns. inv Hin. simpl in Hfns.
  destruct (translate_function _ _ _ _ _ _) eqn:HtransF. inv Hfns.
  destruct (translate_functions _ _ _ fds) eqn:Hfix; inv Hfns.
  destruct Hin.
  - (* i=0 *)
    subst. unfold translate_function in HtransF.
    destruct (translate_var _ _ _ _) eqn:HtransV. inv HtransF.
    destruct (translate_exp _ _ _ _ _). inv HtransF. inv HtransF.
    unfold translate_var in HtransV. cbn.
    destruct (fenv ! v) eqn:HtransV'; inv HtransV. now apply Hbounds in HtransV'.
  - (* i=Si' *)
    by eapply IHfds; eauto.
Qed.

Lemma translate_functions_increasing_fids : forall fds fns fenv e e',
  fenv = create_fname_mapping e ->
  match e with Efun fds' _ => fds' = fds | _ => True end ->
  map_injective fenv ->
  NoDup (collect_function_vars (Efun fds e')) ->
  translate_functions nenv cenv fenv fds = Ret fns ->
  (forall i j i' j', i > j -> nth_error (map (fun f => fidx f) fns) i = Some i' ->
                              nth_error (map (fun f => fidx f) fns) j = Some j' -> i' > j').
Proof.
  intros ? ? ? ? ? ? Hfds Hinj Hnodup HtransFns ? ? ? ? Hgt Hi Hj.
  rewrite nth_error_map in Hi. rewrite nth_error_map in Hj.
  destruct (nth_error fns i) eqn:Hio. 2: inv Hi. cbn in Hi. inv Hi.
  destruct (nth_error fns j) eqn:Hjo. 2: inv Hj. cbn in Hj. inv Hj.

  have Hlen := translate_functions_length _ _ HtransFns. symmetry in Hlen.

  assert (Hilen: i < numOf_fundefs fds). { rewrite -Hlen. now apply nth_error_Some. }
  have Hilen' := Hilen. rewrite <- (collect_function_vars_length _ e) in Hilen'.
  apply nth_error_Some in Hilen'. apply notNone_Some in Hilen'. destruct Hilen' as [v Hiv].
  have Hi' := translate_functions_fenv _ _ _ _ _ _ Hinj HtransFns Hilen Hiv.
  rewrite Hio in Hi'. cbn in Hi'.

  assert (Hjlen: j < numOf_fundefs fds). { rewrite -Hlen. now apply nth_error_Some. }
  have Hjlen' := Hjlen. rewrite <- (collect_function_vars_length _ e) in Hjlen'.
  apply nth_error_Some in Hjlen'. apply notNone_Some in Hjlen'. destruct Hjlen' as [v' Hjv'].
  have Hj' := translate_functions_fenv _ _ _ _ _ _ Hinj HtransFns Hjlen Hjv'.

  rewrite Hjo in Hj'. cbn in Hj'.
  symmetry in Hj', Hi'.
  destruct e; (try now inv Hjv'). subst f. clear HtransFns.
  remember (fidx w) as i'. remember (fidx w0) as j'. clear Heqi' Heqj'.

  assert (Hi'': translate_var nenv (create_fname_mapping (Efun fds e)) v ""%bs = Ret i'). {
    unfold translate_var. now rewrite Hi'. }
  assert (Hj'': translate_var nenv (create_fname_mapping (Efun fds e)) v' ""%bs = Ret j'). {
    unfold translate_var. now rewrite Hj'. }
  unfold create_fname_mapping in Hi'.
  rewrite (var_mapping_list_lt_length_nth_error_idx _ _ num_custom_funs _ _ _ Hiv) in Hi''; auto.
  rewrite (var_mapping_list_lt_length_nth_error_idx _ _ num_custom_funs _ _ _ Hjv') in Hj''; auto.
  inv Hi''. inv Hj''. lia.
Qed.

Lemma increasing_list_fact_trans : forall n l i i' i'n,
  (forall i j i' j', i > j -> nth_error l i = Some i' ->
                              nth_error l j = Some j' -> i' > j') ->
  nth_error l i = Some i' ->
  nth_error l (i + n) = Some i'n -> i'n >= i' + n.
Proof.
  induction n; intros. replace (i+0) with i in H1 by lia.
  assert (i' = i'n) by congruence. lia.

  assert (Hnext: S i < length l). {
    assert (nth_error l (i + S n) <> None) by congruence.
    apply nth_error_Some in H2. lia. }
  apply nth_error_Some in Hnext. apply notNone_Some in Hnext.
  destruct Hnext as [m Hm].
  replace (i + S n) with (S i + n) in H1 by lia.
  have IH := IHn _ _ _ _ _ Hm H1.
  assert (i'n >= m + n). { apply IH. assumption. }

  have H' := H (S i) i _ _ _ Hm H0. lia.
Qed.

Lemma increasing_list_fact_id : forall l i i' n,
  (forall i j i' j', i > j -> nth_error l i = Some i' ->
                              nth_error l j = Some j' -> i' > j') ->
  (forall j j', nth_error l j = Some j' -> n <= j' < length l + n) ->
  nth_error l i = Some i' -> n+i = i'.
Proof.
  intros.
  assert (n + i >= i'). {
    assert (Hl: length l - 1 < length l). { destruct l. destruct i; inv H1. cbn. lia. }
    apply nth_error_Some in Hl. apply notNone_Some in Hl. destruct Hl as [v Hv].
    assert (i < length l). { now apply nth_error_Some. }
    replace (length l - 1) with (i + (length l - 1 - i)) in Hv by lia.
    have H' := increasing_list_fact_trans _ _ _ _ _ H H1 Hv.
    apply H0 in Hv. lia. }
  assert (n + i <= i'). {
    assert (exists v, nth_error l 0 = Some v). {
      apply notNone_Some. apply nth_error_Some. destruct l. destruct i; inv H1.  cbn. lia. }
    destruct H3 as [v Hv].
    have H' := increasing_list_fact_trans _ _ _ _ _ H Hv H1.
    apply H0 in Hv. lia. }
  lia.
Qed.

Lemma fns_fidx_nth_error_fidx : forall fns func j,
  (forall (i j : nat) (i' j' : immediate),
      i > j ->
      nth_error [seq fidx f | f <- fns] i = Some i' ->
      nth_error [seq fidx f | f <- fns] j = Some j' -> i' > j') ->
  (forall idx, In idx (map fidx fns) -> num_custom_funs <= idx < length fns + num_custom_funs) ->
  nth_error fns j = Some func ->
  nth_error fns (fidx func - num_custom_funs) = Some func.
Proof.
  intros. unfold num_custom_funs in *.
  assert (Hin: In func fns). { eapply nth_error_In. eassumption. }
  apply in_map with (f:=fidx) in Hin.
  apply H0 in Hin.
  destruct (fidx func) eqn:Hfi. lia. do 4! (destruct i; try lia). cbn.
  replace (i-0) with i by lia.
  assert (Hlen: i < length fns) by lia.

  assert (Ho: option_map fidx (nth_error fns j) = option_map fidx (Some func)) by congruence.
  rewrite <- nth_error_map in Ho.

  assert (Hbounds: (forall j j' : nat,
    nth_error [seq fidx f | f <- fns] j = Some j' ->
    num_custom_funs <= j' < Datatypes.length [seq fidx f | f <- fns] + num_custom_funs)). {
    intros. apply nth_error_In in H2. apply H0 in H2.  now rewrite map_length.
  }

  have H' := increasing_list_fact_id _ _ _ num_custom_funs H Hbounds Ho.
  unfold num_custom_funs in H'.
  assert (i=j) by lia. congruence.
Qed.

Lemma translate_functions_NoDup : forall fds fns fenv e e',
  fenv = create_fname_mapping e ->
  match e with Efun fds' _ => fds' = fds | _ => True end ->
  map_injective fenv ->
  NoDup (collect_function_vars (Efun fds e')) ->
  translate_functions nenv cenv fenv fds = Ret fns ->
  NoDup (map (fun f => fidx f) fns).
Proof.
  intros ? ? ? ? ? ? Hfds Hinj Hnodup HtransFns. subst fenv.
  have H' := translate_functions_increasing_fids _ _ _ _ _ Logic.eq_refl Hfds Hinj Hnodup HtransFns.
  apply NoDup_nth_error. intros ? ? HiLen Heq.
  destruct (Nat.eq_dec i j); auto. exfalso.
  apply nth_error_Some in HiLen. apply notNone_Some in HiLen. destruct HiLen as [v Hv].
  rewrite Hv in Heq. symmetry in Heq.
  destruct (Nat.ltb_spec i j).
  (* i<j *)
  have Hcontra := H' _ _ _ _ H Heq Hv. lia.
  (* i>j *)
  assert (Hgt: i>j) by lia.
  have Hcontra := H' _ _ _ _ Hgt Hv Heq. lia.
Qed.

Lemma translate_functions_nth_error_idx : forall eTop e eAny fds fns j func,
  match eTop with
  | Efun _ _ => eTop
  | _ => Efun Fnil eTop
  end = Efun fds e ->
  NoDup (collect_function_vars (Efun fds eAny)) ->
  translate_functions nenv cenv (create_fname_mapping eTop) fds = Ret fns ->
  nth_error fns j = Some func ->
  j = fidx func - num_custom_funs.
Proof.
  intros ??????? Htop Hnodup Hfns Hin.
  assert (Hinj: map_injective (create_fname_mapping eTop)). {
    apply create_local_variable_mapping_injective.
    destruct eTop; try (by constructor). now inv Htop.
  }
  assert (Hfds: match eTop with | Efun fds' _ => fds' = fds | _ => True end). {
    destruct eTop=>//. now inv Htop. }
  have H'' := translate_functions_increasing_fids _ _ _ _ _ Logic.eq_refl Hfds
                    Hinj Hnodup Hfns.
 assert (Hbounds: forall idx, In idx [seq fidx i | i <- fns] ->
                               num_custom_funs <= idx < Datatypes.length fns + num_custom_funs). {
    intros ? Hidx.
    have H' := translate_functions_idx_bounds _ _ _ _ _ _ Hfns _ Hidx. apply H'.
    intros ? ? Hf.
    split. { now apply local_variable_mapping_gt_idx in Hf. }
    assert (HtransF: translate_var nenv (create_fname_mapping (Efun fds eAny)) f ""%bs = Ret f'). {
    unfold translate_var. destruct eTop=>//. subst f0. now rewrite Hf. }
    apply var_mapping_list_lt_length' in HtransF.
    rewrite collect_function_vars_length in HtransF.
    now erewrite <-translate_functions_length.
  }
  have Hnth := fns_fidx_nth_error_fidx _ _ _ H'' Hbounds Hin.
  assert (Hlt: fidx func - num_custom_funs < Datatypes.length fns)
      by (apply nth_error_Some; congruence).
  rewrite <- Hin in Hnth.
  apply NoDup_nth_error in Hnth =>//.
  have Hnodup' := translate_functions_NoDup _ _ _ _ _ Logic.eq_refl Hfds Hinj Hnodup Hfns.
  now eapply NoDup_map_inv.
Qed.

Lemma translate_functions_find_def : forall fds f fns t ys e fenv,
  NoDup (collect_function_vars (Efun fds e)) ->
  translate_functions nenv cenv fenv fds = Ret fns ->
  find_def f fds = Some (t, ys, e) ->
  (forall f t ys e, find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e) ->
  exists idx e' locs ftype func, repr_funvar fenv nenv f idx /\
    locs = repeat T_i32 (length (collect_local_variables e)) /\
    ftype = Tf (List.map (fun _ => T_i32) ys) [] /\
    In func fns /\
    func.(fidx) = idx /\ func.(type) = ftype /\ func.(locals) = locs /\ func.(body) = e' /\
    repr_expr_LambdaANF_Wasm cenv fenv nenv e e'
     (lenv := create_local_variable_mapping (ys ++ collect_local_variables e)).
Proof.
  induction fds; intros ? ? ? ? ? ? Hnodup HtransFns HfDef HcorrCenv; last by inv HfDef.
  simpl in HtransFns.
  destruct (translate_function _ _ _ _ _ _) eqn:Hf. inv HtransFns.
  destruct (translate_functions _ _ _ fds) eqn:Hfns; inv HtransFns.
  cbn in HfDef. destruct (M.elt_eq f0 v).
  - (* f0=v *)
    inv HfDef.
    unfold translate_function in Hf.
    destruct (translate_var _ _ _ _) eqn:Hvar. inv Hf.
    destruct (translate_exp _ _ _ _ _) eqn:Hexp; inv Hf.
    exists i, l. eexists. eexists. eexists.
    split. { now econstructor. }
    do 2! (split; try reflexivity).
    split. now left.
    cbn. rewrite map_repeat_eq.
    repeat (split; first reflexivity).
    eapply translate_exp_correct in Hexp; eauto. eapply HcorrCenv with (f:=v). cbn.
    by destruct (M.elt_eq v v).
  - (* f0<>v *)
    assert (Hnodup': NoDup (collect_function_vars (Efun fds e0))) by inv Hnodup=>//.
    assert (HcorrCenv': (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
      find_def f fds = Some (t, ys, e) ->
      correct_cenv_of_exp cenv e)). {
      intros. have H' := HcorrCenv f1 t0 ys0 e1. apply H'. cbn.
      assert (f1 <> v). {
        inv Hnodup. intro. subst. apply H2.
        apply find_def_in_collect_function_vars; auto. congruence. }
      destruct (M.elt_eq f1 v); auto; congruence.
    }
    have IH := IHfds _ _ _ _ _ _ Hnodup' Hfns HfDef HcorrCenv'.
    destruct IH as [idx [e' [locs [type [func [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
    inversion H.
    repeat eexists.
    repeat (split; eauto). subst idx. eassumption.
    now right. all: congruence.
Qed.

Theorem module_instantiate_INV_and_more_hold :
forall e eAny topExp fds num_funs module fenv main_lenv sr f exports,
  NoDup (collect_function_vars (Efun fds eAny)) ->
  expression_restricted e ->
  topExp = match e with | Efun _ _ => e | _ => Efun Fnil e end ->
  (match topExp with Efun fds' _ => fds' | _ => Fnil end) = fds ->
  (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
      find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e) ->
  num_funs = match topExp with | Efun fds _ => numOf_fundefs fds | _ => 42 (* unreachable*) end ->
  (Z.of_nat num_funs < max_num_functions)%Z ->
  LambdaANF_to_Wasm nenv cenv e = Ret (module, fenv, main_lenv) ->
  (* for INV_locals_all_i32, the initial context has no local vars for simplicity *)
  (f_locs f) = [] ->
  (* instantiate with the two imported functions *)
  instantiate host_function host_instance initial_store module
    [MED_func (Mk_funcidx 0); MED_func (Mk_funcidx 1)] (sr, (f_inst f), exports, None) ->

  (* invariants hold initially *)
  INV fenv nenv _ sr f /\
  inst_funcs (f_inst f) = [:: 0, 1, 2, 3, 4 & map (fun '(Mk_funcidx i) => i) (funcidcs num_funs num_custom_funs)] /\
  (* value relation holds for all funcs in fds *)
  (forall a errMsg, find_def a fds <> None ->
	exists fidx : immediate,
	  translate_var nenv fenv a errMsg = Ret fidx /\
	  repr_val_LambdaANF_Wasm cenv fenv nenv host_function
	    (Vfun (M.empty _) fds a) sr (f_inst f) (Val_funidx fidx)) /\
  (* pp_fn not called, discard *)
  exists pp_fn e' fns, s_funcs sr =
    [:: FC_func_host (Tf [T_i32] []) hfn,
        FC_func_host (Tf [T_i32] []) hfn,
        pp_fn,
        FC_func_native (f_inst f) (Tf [::T_i32] []) [] grow_memory_if_necessary,
        FC_func_native (f_inst f) (Tf [] []) (map (fun _ : var => T_i32)
          (collect_local_variables match e with
                                   | Efun _ exp => exp
                                   | _ => e end)) e' &
        map (fun f0 : wasm_function =>
             FC_func_native (f_inst f) (Tf (repeat T_i32 match type f0 with
                                                         | Tf args _ => Datatypes.length args
                                                         end) []) (locals f0) (body f0))
            fns
     ] /\
  (* translation of e *)
  translate_exp nenv cenv
          (create_local_variable_mapping
             (collect_local_variables
                match e with
                | Efun _ exp => exp
                | _ => e
                end)) fenv match e with
                           | Efun _ exp => exp
                           | _ => e
                           end = Ret e' /\
  (* translation of functions *)
  match topExp with
  | Efun fds _ => translate_functions nenv cenv fenv fds
  | _ => Ret []
  end = Ret fns.
Proof.
  intros e eAny topExp fds num_funs module fenv lenv s f exports Hnodup HeRestr HtopExp Hfds HcenvCorrect Hnumfuns
    HfdsLength Hcompile Hflocs Hinst. subst num_funs topExp.
  unfold instantiate in Hinst.
  unfold LambdaANF_to_Wasm in Hcompile.
  remember (list_function_types (Z.to_nat max_function_args)) as types.
  simpl in Hcompile.
  destruct (check_restrictions e) eqn:HRestr. inv Hcompile.
  destruct (generate_constr_pp_function cenv nenv e) eqn:HgenPP. inv Hcompile.
  destruct (match _ with | Efun fds _ => _ fds | _ => Err _ end) eqn:HtransFns. inv Hcompile.
  destruct (match e with
            | Efun _ _ => e
            | _ => Efun Fnil e
            end) eqn:HtopExp'; try (by inv Hcompile).
  destruct (translate_exp nenv cenv _ _ _) eqn:Hexpr. inv Hcompile. rename l0 into e'.
  inv Hcompile.
  unfold INV. unfold is_true in *.
  destruct Hinst as [t_imps [t_exps [state [s' [ g_inits [e_offs [d_offs
      [Hmodule [Himports [HallocModule [HinstGlobals [HinstElem
         [HinstData [HboundsElem [HboundsData [_ Hinst]]]]]]]]]]]]]]]].
  rename l into fns.
  (* module typing *) clear Hmodule.

  (* globals red. to const *)
  unfold instantiate_globals in HinstGlobals. cbn in HinstGlobals.
  inv HinstGlobals. inv H3. inv H5. inv H6. inv H7.
  apply reduce_trans_const in H1, H2, H3. subst y y0 y1.
  (* data offsets of mem init. red. to const, empty list *)
  inv HinstData. apply reduce_trans_const in H4. subst y2.
  (* elem vals red. to const *)
  unfold instantiate_elem in HinstElem. cbn in Hinst.
  repeat rewrite -app_assoc in HinstElem. cbn in HinstElem.
  rewrite Nat.add_comm in HinstElem. cbn in HinstElem.
  destruct (e_offs_increasing _ _ _ _ _ HinstElem) as [HeoffsVals HeoffsLen].
  clear HinstElem.

  apply store_record_eqb_true in Hinst.
  unfold alloc_module, alloc_funcs, alloc_globs, add_mem, alloc_Xs in HallocModule.
  cbn in HallocModule. repeat rewrite map_app in HallocModule. cbn in HallocModule.
  destruct (fold_left _ (map _ fns) _) eqn:HaddF.

  unfold add_glob in HallocModule. cbn in HallocModule.
  repeat (apply andb_prop in HallocModule;
           destruct HallocModule as [HallocModule ?F]).
  apply store_record_eqb_true in HallocModule.
  apply eqseq_true in F0,F1,F2,F3,F4,F. cbn in HaddF.
  apply add_funcs_effect in HaddF. cbn in HaddF. destruct HaddF as [Hs01 [Hs02 [Hs03 [Hs04 Hs05]]]].

  rewrite <- Hs01 in HallocModule, F0. rewrite <- Hs02 in HallocModule, F1.
  rewrite <- Hs03 in HallocModule, F2. cbn in Hinst.
  rewrite Hs04 in HallocModule. subst l.
  cbn in F0, F1, F2, F3. clear Hs01 Hs02 Hs03 Hs04 s0.
  rewrite map_length in F3. rewrite rev_app_distr in F3.
  rewrite map_app in F3. cbn in F3.
  clear HboundsData HboundsElem. (* clear for now *)
  rewrite rev_involutive in F3.
  rewrite F4 in HallocModule. cbn in HallocModule.

  remember (s_tables s') as ts. rewrite HallocModule in Heqts.
  destruct ts. inv Heqts. destruct ts. 2: inv Heqts.
  symmetry in Heqts. rewrite -HallocModule in Heqts.

  assert (Hnone: table_max_opt t = None). { subst s'. now inv Heqts. }
  assert (Hlen: (length (table_data t) - num_custom_funs) = length fns /\
                 length (table_data t) >= num_custom_funs). {
    subst s'. inv Heqts. cbn. rewrite repeat_length. cbn.
    replace (ssrnat.nat_of_bin (N.of_nat (Datatypes.length fns + num_custom_funs))) with
      (Z.to_nat (Z.of_nat (ssrnat.nat_of_bin (N.of_nat (Datatypes.length fns + num_custom_funs))))) by lia.
    rewrite Z_nat_bin. lia.
  } destruct Hlen as [Hlen HminLen]. rewrite -Hlen in F3.
  assert (Hlen': length e_offs = length fns + num_custom_funs). { now rewrite HeoffsLen -Hlen. }
  rewrite -Hlen' in HeoffsVals.
  assert (HlenMax: (Z.of_nat (Datatypes.length e_offs) < Wasm_int.Int32.modulus)%Z). {
    apply translate_functions_length in HtransFns.
    unfold max_num_functions in HfdsLength. rewrite Hlen'.
    simpl_modulus; cbn. unfold num_custom_funs in *. lia. }
  assert (Hlen'': Datatypes.length e_offs = Datatypes.length (table_data t)) by lia.
  have H' := init_tabs_effect s' _ _ e_offs _ Heqts Hnone F2 F3 Logic.eq_refl HeoffsVals HlenMax Hlen''.
  rewrite Hlen' in H'.
  destruct H' as [t' [Ht' [HtVal' [NtNone' [Htables [Hfuncs [Hmems Hglobals]]]]]]].
  rewrite -Hinst in Hglobals, Hmems, Hfuncs.

  assert (Hw: type w = Tf [T_i32] [] /\ locals w = []). {
    unfold generate_constr_pp_function in HgenPP. cbn in HgenPP.
    destruct (sequence _). inv HgenPP. inv HgenPP.
    split; reflexivity.
  } destruct Hw as [Hw1 Hw2].
  rewrite Hw1 Hw2 in HallocModule. clear Hw1 Hw2.
  rewrite nth_list_function_types in HallocModule. 2: { cbn. lia. }
  rewrite nth_list_function_types in HallocModule; try lia.
  rewrite -map_map_seq in HallocModule. cbn in HallocModule.
  rewrite nth_list_function_types_map in HallocModule. 2: {
    intros wFun Hin. destruct e; inv HtopExp'; try by (inv HtransFns; inv Hin).
    have H' := translate_functions_exists_original_fun _ _ _ _ _ _ _ Hnodup HtransFns Logic.eq_refl Hin.
    destruct H' as [f'' [t'' [ys'' [e'' [Hdef [Hty Hvar]]]]]].
    destruct (type wFun).
    inv HeRestr. apply H2 in Hdef. lia. }
  split.
  (* INV globals *)
  unfold INV_result_var_writable, INV_result_var_out_of_mem_writable, INV_global_mem_ptr_writable,
  INV_constr_alloc_ptr_writable. unfold global_var_w, supdate_glob, supdate_glob_s.
  subst s'; cbn; cbn in Hglobals, Hfuncs, Hmems. rewrite F0. cbn.
  split. (* res_var_w *) eexists. cbn. rewrite Hglobals. reflexivity.
  split. (* res_var_M_w *) eexists. rewrite Hglobals. reflexivity.
  split. (* res_var_M_0 *) unfold INV_result_var_out_of_mem_is_zero. unfold sglob_val, sglob.
  cbn. rewrite F0. rewrite Hglobals. reflexivity.
  split. (* gmp_w *) eexists. rewrite Hglobals. reflexivity.
  split. (* cap_w *) eexists. rewrite Hglobals. reflexivity.
  (* globals mut i32 *)
  split. unfold INV_globals_all_mut_i32, globals_all_mut_i32. intros. cbn. cbn in H. subst s.
  { rewrite Hglobals in H. cbn in H.
    destruct g. inv H. eexists. reflexivity.
    destruct g. inv H. eexists. reflexivity.
    destruct g. inv H. eexists. reflexivity.
    destruct g. inv H. eexists. reflexivity.
    destruct g; inv H. }
  split. (* linmem *)
  { unfold INV_linear_memory. unfold smem_ind. cbn. rewrite F1.
    split; auto. eexists; auto. split. rewrite Hmems. reflexivity. unfold mem_mk. cbn.
    unfold mem_size, operations.mem_length, memory_list.mem_length. cbn. eexists. split. reflexivity.
    split; auto. unfold max_mem_pages. rewrite repeat_length. cbn.
    replace (N.of_nat (Pos.to_nat 65536)) with 65536%N by lia. cbn. lia. }
   split. (* gmp in linmem *)
   { unfold INV_global_mem_ptr_in_linear_memory.
   unfold sglob_val, sglob. cbn. intros. rewrite F0 in H0. inv H0.
   rewrite Hmems in H. rewrite Hglobals in H3. inv H. cbn.
   unfold mem_mk, operations.mem_length, memory_list.mem_length. rewrite repeat_length. cbn.
   inv H3. rewrite Wasm_int.Int32.Z_mod_modulus_id in H0; try lia. }
   split. (* all locals i32 *)
   { unfold INV_locals_all_i32. intros. rewrite Hflocs in H. rewrite nth_error_nil in H. inv H. }
   split. (* num functions upper bound *)
   { unfold INV_num_functions_bounds. cbn.
     rewrite Hfuncs. cbn.
     rewrite map_length.
     destruct e; inv HtopExp'; try (inv HtransFns; simpl_modulus; cbn; lia).
     erewrite <- translate_functions_length; eauto.
     unfold max_num_functions in HfdsLength. simpl_modulus. cbn. lia. }
   split. (* inst_globs (f_inst f) no dups *)
   unfold INV_inst_globs_nodup. rewrite F0.
   repeat constructor; cbn; lia.
   split. (* INV_table_id *)
   { unfold INV_table_id. intros.
     unfold stab_addr, stab_index. rewrite F2. cbn.
     intros.
     assert (Z.of_nat i < max_num_functions + Z.of_nat num_custom_funs)%Z. {
       destruct e; inv H. apply translate_fvar_fname_mapping in H1.
       inv HtopExp'. lia. }
     (* from translate_var *)
     rewrite Wasm_int.Int32.Z_mod_modulus_id. 2: {
      simpl_modulus; cbn. unfold max_num_functions in H0.
      unfold num_custom_funs in H0. lia. }
      subst s. rewrite Ht'. cbn.
      rewrite HtVal'. cbn. f_equal. lia.
      have H' := H.
      apply translate_fvar_fname_mapping in H'.
      destruct e; inv H. symmetry in HtopExp'; inv HtopExp'.
      apply translate_functions_length in HtransFns. rewrite HtransFns in H'.
      apply nth_error_In with (n:=i). rewrite nth_error_map.
      rewrite HeoffsVals; try lia. cbn. f_equal.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
  }
  split. (* types *)
  { unfold INV_types. intros. unfold stypes. cbn. unfold max_function_args in H.
    rewrite F4. erewrite nth_error_nth'.
    rewrite nth_list_function_types =>//. lia.
    rewrite length_list_function_types. lia. }
  split. (* gmp multiple of two *)
  { unfold INV_global_mem_ptr_multiple_of_two.
    intros.
    exists 0.
    subst.
    unfold global_mem_ptr, sglob_val, sglob in H0.
    rewrite Hglobals in H0. cbn in H0.
    rewrite F0 in H0. cbn in H0.
    inv H0.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H3; now lia. }
  split. (* func grow_mem exists *)
  { unfold INV_exists_func_grow_mem.
    by rewrite Hfuncs. }
  (* inst_funcs_id *)
  { unfold INV_inst_funcs_id. intros.
    rewrite F3.
    destruct (Nat.leb_spec i 4).
    (* n <= 4 *)
    do 5 (destruct i; cbn; auto). lia.
    (* 4 < n *)
    separate_instr. do 4 rewrite catA.
    erewrite nth_error_app2=>//. cbn.
    erewrite nth_error_funcidcs; eauto.
    f_equal. lia. unfold num_custom_funs in *.
    rewrite Hfuncs in H. cbn in H.
    rewrite Hlen. rewrite map_length in H. lia.
  }
  split. (* inst_funcs (f_inst f) *)
  { rewrite F3. repeat f_equal. intros. rewrite H2. reflexivity.
    destruct e; inv HtopExp'; inv HtransFns; auto.
    symmetry. rewrite Hlen. cbn. eapply translate_functions_length. eassumption. }
  split. (* val relation holds for functions *)
  { intros. apply notNone_Some in H. destruct H as [[[v' ys'] e''] Hfd].
    assert (Hnodup' : NoDup (collect_function_vars (Efun fds e))). {
      replace (collect_function_vars (Efun fds e'')) with
              (collect_function_vars (Efun fds e0)) by reflexivity. assumption. }

    have H' := translate_functions_find_def _ _ _ _ _ e'' _ Hnodup' HtransFns Hfd HcenvCorrect.
    destruct H' as [fidx [e''' [? [? [func [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
    subst. eauto.
    exists (fidx func).
    split. { inv H. unfold translate_var. unfold translate_var in H0.
      now destruct ((create_fname_mapping e) ! a). }
    econstructor; eauto. rewrite Hfuncs. cbn.
    assert (fidx func >= num_custom_funs). { inv H. unfold translate_var in H0.
      destruct ((create_fname_mapping e) ! a) eqn:Ha; inv H0.
      now apply local_variable_mapping_gt_idx in Ha. }

    assert (nth_error fns (fidx func - num_custom_funs) = Some func). {
      apply In_nth_error in H2. destruct H2 as [j Hj].
      erewrite <- translate_functions_nth_error_idx; eauto. }
    unfold num_custom_funs in *.

    assert (HnodupFns: NoDup fns). {
      assert (Hinj: map_injective (create_fname_mapping e)). {
        apply create_local_variable_mapping_injective.
        destruct e; try (by constructor). now inv HtopExp'.
      }
      assert (Hfds: match e with | Efun fds' _ => fds' = fds | _ => True end). {
        destruct e;auto. now inv HtopExp'. }
      have H' := translate_functions_NoDup _ _ _ _ _ Logic.eq_refl Hfds Hinj Hnodup' HtransFns.
      now eapply NoDup_map_inv.
    }

    destruct (fidx func). lia. do 4! (destruct i; try lia). cbn.
    replace (S (S (S (S (S i)))) - 5) with i in H1 by lia.

    rewrite nth_error_map.
    rewrite H1. cbn. f_equal. f_equal. rewrite H4.
    now rewrite map_repeat_eq -map_map_seq.
  }
  exists (FC_func_native (f_inst f) (Tf [T_i32] []) [] (body w)), e', fns.
  subst s'; cbn; cbn in Hglobals, Hfuncs, Hmems. rewrite Hfuncs.

  assert (HfRepeat: (fun x : wasm_function =>
     FC_func_native (host_function:=host_function) (f_inst f)
         match type x with
         | Tf args _ => Tf (repeat T_i32 (Datatypes.length args)) []
         end (locals x) (body x)) = (fun x : wasm_function =>
     FC_func_native (f_inst f)
         (Tf (repeat T_i32
               match type x with
               | Tf args _ => Datatypes.length args
               end) []) (locals x) (body x))). {
      apply functional_extensionality. intros.
      now destruct (type x).
  }
  rewrite HfRepeat.
  replace (collect_local_variables
              match e with
              | Efun _ exp => exp
              | _ => e
              end) with
            (collect_local_variables
	            match e with
	            | Efun _ _ => e
	            | _ => Efun Fnil e
	            end) by now destruct e.
	rewrite HtopExp'. split. reflexivity.
	split=>//. rewrite -Hexpr.
	replace (match e with | Efun _ exp => exp
                        | _ => e end) with e0 by now destruct e.
  reflexivity.
Unshelve. apply (Tf [] []).
Qed.

Lemma repeat0_n_zeros : forall l,
   repeat (nat_to_value 0) (Datatypes.length l)
 = n_zeros (map (fun _ : var => T_i32) l).
Proof.
  induction l; cbn; auto.
  now rewrite IHl.
Qed.


(* MAIN THEOREM, corresponds to 4.3.1 in Olivier's thesis *)
Theorem LambdaANF_Wasm_related :
  forall (v : cps.val) (e : exp) (n : nat) (vars : list cps.var)
         (hs : host_state) module fenv lenv
         (sr : store_record) (fr : frame) exports,
  (* evaluation of LambdaANF expression *)
  bstep_e (M.empty _) cenv (M.empty _) e v n ->
  (* compilation function *)
  LambdaANF_to_Wasm nenv cenv e = Ret (module, fenv, lenv) ->
  (* constructors wellformed *)
  correct_cenv_of_exp cenv e ->
  (* vars unique (guaranteed by previous stage) *)
  vars = ((collect_all_local_variables e) ++ (collect_function_vars e))%list ->
  NoDup vars ->
  (* expression must be closed *)
  (~ exists x, occurs_free e x ) ->
  (* instantiation with the two imported functions *)
  instantiate _ host_instance initial_store module [MED_func (Mk_funcidx 0); MED_func (Mk_funcidx 1)]
    ((sr, (f_inst fr), exports), None) ->
  (* reduces to some sr' that has the result variable set to the corresponding value *)
  exists (sr' : store_record),
       reduce_trans (hs, sr,  (Build_frame [] (f_inst fr)), [ AI_basic (BI_call main_function_idx) ])
                    (hs, sr', (Build_frame [] (f_inst fr)), [])    /\

       result_val_LambdaANF_Wasm cenv fenv nenv _ v sr' (f_inst fr).
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? Hstep LANF2Wasm Hcenv HvarsEq HvarsNodup Hfreevars Hinst.
  subst vars.

  assert (HeRestr: expression_restricted e).
  { unfold LambdaANF_to_Wasm in LANF2Wasm. destruct (check_restrictions e) eqn:HeRestr.
    inv LANF2Wasm. destruct u. eapply check_restrictions_expression_restricted; eauto.
    apply rt_refl. }

  remember ({| f_locs := []; f_inst := f_inst fr |}) as f.
  assert (Hmaxfuns : (Z.of_nat match match e with
                                     | Efun _ _ => e
                                     | _ => Efun Fnil e
                                     end with
                               | Efun fds _ => numOf_fundefs fds
                               | _ => 42 (* unreachable *)
                               end < max_num_functions)%Z). {
    unfold max_num_functions. destruct e; cbn; try lia. inv HeRestr. assumption.
  }
  assert (HflocsNil : f_locs f = []). { subst. reflexivity. }
  assert (Hfinst : f_inst f = f_inst fr) by (subst; reflexivity). rewrite -Hfinst in Hinst.
  assert (Hnodup: NoDup (collect_function_vars (Efun Fnil e))) by constructor.

  assert (Hcenv' : (forall (f : var) (t : fun_tag) (ys : seq var) (e1 : exp),
    find_def f match
                 match e with
                 | Efun _ _ => e
                 | _ => Efun Fnil e
                 end
               with
               | Efun fds' _ => fds'
               | _ => Fnil
               end = Some (t, ys, e1) ->
      correct_cenv_of_exp cenv e1)). { intros. destruct e; try discriminate. cbn in Hcenv.
      eapply Forall_constructors_subterm; try apply Hcenv. constructor. apply dsubterm_fds.
      now eapply find_def_dsubterm_fds_e.
  }

  assert (Hnodup': NoDup
    (collect_function_vars (Efun match
                                   match e with
                                   | Efun _ _ => e
                                   | _ => Efun Fnil e
                                   end
                                 with
                                 | Efun fds' _ => fds'
                                 | _ => Fnil
                                 end e))). {
    destruct e; cbn; auto.
    now eapply NoDup_app_remove_l in HvarsNodup.
  }

  have HI := module_instantiate_INV_and_more_hold _ _ _ _ _ _ _ _ _ _ _ Hnodup' HeRestr
               Logic.eq_refl Logic.eq_refl Hcenv' Logic.eq_refl Hmaxfuns LANF2Wasm HflocsNil Hinst.
  clear Hfinst Hnodup' Hcenv'.
  destruct HI as [Hinv [HinstFuncs [HfVal [pp_fn [e' [fns' [HsrFuncs [Hexpr' Hfns']]]]]]]].

  remember (Build_frame (repeat (nat_to_value 0) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.

  unfold LambdaANF_to_Wasm in LANF2Wasm.
  remember (list_function_types (Z.to_nat max_function_args)) as ftypes.
  simpl in LANF2Wasm.
  destruct (check_restrictions e). inv LANF2Wasm.
  destruct (generate_constr_pp_function cenv nenv e) eqn:Hppconst. inv LANF2Wasm.
  destruct (match _ with
       | Efun fds _ => _ fds
       | _ => Err _
       end) eqn:Hfuns. inv LANF2Wasm. rename l into fns.
  destruct (match e with
                    | Efun _ _ => e
                    | _ => Efun Fnil e
                    end) eqn:HtopExp; try (by inv LANF2Wasm).
  destruct (translate_exp nenv cenv _ _ _) eqn:Hexpr. inv LANF2Wasm. rename l into wasm_main_instr.
  inv LANF2Wasm.

  (* from lemma module_instantiate_INV_and_more_hold *)
  assert (e' = wasm_main_instr). { destruct e; inv HtopExp; congruence. } subst e'. clear Hexpr'.
  assert (fns = fns'). { destruct e; inv HtopExp; congruence. } subst fns'. clear Hfns'.

  remember (Build_frame (repeat (nat_to_value 0) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.
  remember (create_local_variable_mapping (collect_local_variables e)) as lenv.
  remember (create_fname_mapping e) as fenv.

   assert (HlocInBound: (forall (var : positive) (varIdx : immediate),
          repr_var (lenv:=lenv) nenv var varIdx -> varIdx < Datatypes.length (f_locs f_before_IH))).
   { intros ? ? Hvar. subst f_before_IH. cbn. rewrite repeat_length. inv Hvar.
     eapply var_mapping_list_lt_length. eassumption. }

  assert (Hinv_before_IH: INV fenv nenv _ sr f_before_IH). { subst.
    destruct Hinv as [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]].
    unfold INV. repeat (split; try assumption).
    unfold INV_locals_all_i32. cbn. intros. exists (nat_to_i32 0).
    assert (i < (length (repeat (nat_to_value 0) (Datatypes.length (collect_local_variables e))))).
    { subst. now apply nth_error_Some. }
    rewrite nth_error_repeat in H12. inv H12. reflexivity. rewrite repeat_length in H13. assumption.
  }

  have Heqdec := inductive_eq_dec e. destruct Heqdec.
  { (* top exp is Efun _ _ *)
    destruct e1 as [fds' [e'' He]]. subst e. rename e'' into e.
    inversion HtopExp. subst e0 f0. rename fds' into fds.
    inversion Hstep. subst fl e0 v0 c rho. clear Hstep. rename H4 into Hstep.

    eapply translate_exp_correct in Hexpr; try eassumption.
    2:{ eapply Forall_constructors_subterm. eassumption. constructor.
        apply dsubterm_fds2. }

    (* prepare IH *)

    assert (HlenvInjective : map_injective lenv). {
      subst lenv.
      intros x y x' y' Hneq Hx Hy Heq. subst y'.
      apply NoDup_app_remove_r in HvarsNodup. cbn in HvarsNodup.
      apply NoDup_app_remove_r in HvarsNodup.
      cbn in Hx, Hy.
      have H' := create_local_variable_mapping_injective _ 0 HvarsNodup _ _ _ _ Hneq Hx Hy. auto. }

    assert (HenvsDisjoint : domains_disjoint lenv fenv). {
      rewrite Heqfenv. subst lenv. eapply variable_mappings_nodup_disjoint; eauto.
      cbn in HvarsNodup. rewrite <-catA in HvarsNodup.
      now eapply NoDup_app_remove_middle in HvarsNodup.
    }

    assert (Hnodup': NoDup (collect_local_variables e ++
                            collect_function_vars (Efun fds e))). {
      cbn in HvarsNodup. rewrite <-catA in HvarsNodup.
      now eapply NoDup_app_remove_middle in HvarsNodup.
    }

    assert (HfenvWf: (forall f : var,
         (exists res : fun_tag * seq var * exp,
            find_def f fds = Some res) <->
         (exists i : nat,
            fenv ! f = Some i))). {
      subst fenv. intros; split; intros.
      - apply notNone_Some in H.
        rewrite find_def_in_collect_function_vars in H.
        apply notNone_Some. apply variable_mapping_In_Some.
        + now eapply NoDup_app_remove_l in HvarsNodup.
        + assumption.
      - destruct H as [i H]. apply variable_mapping_Some_In in H; auto.
        rewrite <- find_def_in_collect_function_vars in H.
        now apply notNone_Some.
    }

    assert (HfenvRho: (forall (a : positive) (v0 : cps.val),
         (def_funs fds fds (M.empty _) (M.empty _)) ! a = Some v0 ->
         find_def a fds <> None -> v0 = Vfun (M.empty _) fds a)). {
      intros ? ? H H0. eapply def_funs_find_def in H0; eauto. erewrite H in H0.
      now inv H0. }

    assert (HeRestr' : expression_restricted e). { now inv HeRestr. }
    assert (Hunbound: (forall x : var,
         In x (collect_local_variables e) ->
         (def_funs fds fds (M.empty _) (M.empty _)) ! x = None)). {
      intros. eapply def_funs_not_find_def; eauto.
      destruct (find_def x fds) eqn:Hdec; auto. exfalso.
      assert (Hdec': find_def x fds <> None) by congruence. clear Hdec p.
      apply find_def_in_collect_function_vars with (e:=e) in Hdec'.
      cbn in HvarsNodup. rewrite <- catA in HvarsNodup.
      eapply NoDup_app_remove_middle in HvarsNodup; eauto.
      by eapply NoDup_app_In in H; eauto.
    }

    assert (Hfds : forall (a : var) (t : fun_tag) (ys : seq var) (e0 : exp) errMsg,
        find_def a fds = Some (t, ys, e0) ->
        expression_restricted e0 /\
        (forall x : var, occurs_free e0 x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++
           collect_local_variables e0 ++
           collect_function_vars (Efun fds e0)) /\
        (exists fidx : immediate,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Wasm cenv fenv nenv
             host_function (Vfun (M.empty _) fds a)
             sr (f_inst f_before_IH) (Val_funidx fidx))). {
      intros ? ? ? ? ? Hcontra.
      split. { inv HeRestr. eapply H2. eassumption. }
      split. { intros x Hocc.
      assert (Hdec: decidable_eq var). {
        intros n' m'. unfold Decidable.decidable. now destruct (var_dec n' m'). }
      have H' := In_decidable Hdec x ys. destruct H'. now left.
      right. intro Hcontra'.
      exfalso. apply Hfreevars. exists x. apply Free_Efun2.
      eapply find_def_is_Some_occurs_free_fundefs; eauto.
      intro Hfd. revert Hcontra'.
      apply name_in_fundefs_find_def_is_Some in Hfd.
      now destruct Hfd as [? [? [? ?]]]. }
      split. { rewrite catA. eapply NoDup_collect_all_local_variables_find_def; eauto. }
      (* exists fun values *)
      { assert (Hc: find_def a fds <> None) by congruence.
        apply HfVal with (errMsg:=errMsg) in Hc; auto.
        destruct Hc as [fidx [HtransF Hval]].
        exists fidx. split. assumption. subst f_before_IH. assumption. }
    }

    assert (HrelE : @rel_env_LambdaANF_Wasm cenv fenv nenv host_function
                   (create_local_variable_mapping (collect_local_variables e)) e (def_funs fds fds (M.empty _) (M.empty _))
          sr f_before_IH fds). {
      split.
      { (* funs1 (follows from previous Hfds) *)
        intros ? ? ? ? ? Hdf Hval. have H' := Hdf.
        apply def_funs_spec in Hdf.
        destruct Hdf as [[? ?] | [? H]]. 2: inv H.
        rewrite def_funs_eq in H'. 2: assumption.
        inv H'. apply subval_fun in Hval. 2: assumption.
        destruct Hval as [? [Hval ?]]. inv Hval => //.
      } split.
      { (* funs2 *)
        intros ? ? Hnfd. apply name_in_fundefs_find_def_is_Some in Hnfd.
        destruct Hnfd as [? [? [? Hfd]]]. apply Hfds with (errMsg:=errMsg) in Hfd.
        destruct Hfd as [_ [_ [_ [i [Htrans Hval]]]]]. eauto. }
      { (* vars *)
        intros x Hocc Hfd. exfalso. apply Hfreevars. exists x. constructor; auto.
        intro Hcontra. apply name_in_fundefs_find_def_is_Some in Hcontra.
        now destruct Hcontra as [? [? [? ?H]]]. }
    }

    (* eval context after fn entry: one label for the main fn block *)
    remember (LH_rec [] 0 [] (LH_base [] []) []) as lh.
    remember ({| f_locs := [::]; f_inst := f_inst fr |}) as frameInit.

    subst lenv.
    have HMAIN := repr_bs_LambdaANF_Wasm_related cenv fenv nenv _ host_instance
                    _ _ _ _ _ _ _ frameInit _ lh HlenvInjective
                      HenvsDisjoint Logic.eq_refl Hnodup' HfenvWf HfenvRho
                      HeRestr' Hunbound Hstep hs _ _ _ Hfds HlocInBound Hinv_before_IH Hexpr HrelE.

    destruct HMAIN as [s' [f' [k' [lh' [Hred [Hval [Hfinst _]]]]]]]. cbn.
    subst frameInit.
    exists s'. split.
    dostep'. apply r_call. cbn.
    rewrite HinstFuncs. reflexivity.
    dostep'. eapply r_invoke_native with (ves:=[]) (vcs:=[]) (t1s:=[]) (t2s:=[])(f' := f_before_IH); eauto.
    rewrite HsrFuncs. subst f_before_IH. cbn. rewrite Hfinst. reflexivity.
    subst f_before_IH. cbn. apply repeat0_n_zeros. cbn. subst lh. cbn in Hred.
    (* reduce block to push label *)
    dostep'. eapply r_local. constructor. eapply rs_block with (vs:=[]); eauto. cbn.
    rewrite cats0 in Hred. eapply rt_trans. apply Hred.
    dostep'. constructor. apply rs_return with (lh:=lh') (vs:=[::]) =>//. apply rt_refl.
    subst f_before_IH. apply Hval.
  }

  { (* top exp is not Efun _ _ *)
    rename f0 into fds. assert (fds = Fnil). {
      destruct e; inv HtopExp; auto. exfalso. eauto.
    } subst fds. injection Hfuns => ?. subst fns. clear Hfuns.
    cbn in HsrFuncs, HinstFuncs, Hmaxfuns.
    assert (e0 = e). { destruct e; inv HtopExp; auto. exfalso. eauto. }
    subst e0. clear HtopExp.

    eapply translate_exp_correct in Hexpr; eauto.

    assert (HrelE : @rel_env_LambdaANF_Wasm cenv fenv nenv host_function
                    (create_local_variable_mapping (collect_local_variables e)) e (M.empty _) sr f_before_IH Fnil). {
    split.
    { intros. exfalso. cbn in HsrFuncs. inv H. } split.
    { intros. inv H. }
    { intros. exfalso. eauto. }}

    assert (HlenvInjective : map_injective (create_local_variable_mapping
             (collect_local_variables e))). {
      assert (Heqvars : (collect_local_variables e) = (collect_all_local_variables e)). {
       unfold collect_all_local_variables. destruct e; eauto. exfalso. now apply n0. }
      intros x y x' y' Hneq Hx Hy Heq. subst y'.
      rewrite Heqvars in Hx, Hy.
      apply NoDup_app_remove_r in HvarsNodup. cbn in HvarsNodup.
      cbn in Hx, Hy.
      have H' := create_local_variable_mapping_injective _ 0 HvarsNodup _ _ _ _ Hneq Hx Hy. auto.
    }
    assert (HenvsDisjoint : domains_disjoint
                             (create_local_variable_mapping (collect_local_variables e))
                             fenv). {
      subst fenv. eapply variable_mappings_nodup_disjoint; eauto.
      destruct e; auto. cbn. cbn in HvarsNodup.
      rewrite <- app_assoc in HvarsNodup. now eapply NoDup_app_remove_middle in HvarsNodup.
    }

    assert (Hfds : forall (a : var) (t : fun_tag) (ys : seq var) (e0 : exp) errMsg,
        find_def a Fnil = Some (t, ys, e0) ->
        expression_restricted e0 /\
        (forall x : var, occurs_free e0 x -> In x ys \/ find_def x Fnil <> None) /\
        NoDup
          (ys ++
           collect_local_variables e0 ++
           collect_function_vars (Efun Fnil e0)) /\
        (exists fidx : immediate,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Wasm cenv fenv nenv
             host_function (Vfun (M.empty _) Fnil a)
             sr (f_inst f_before_IH) (Val_funidx fidx))). {
        intros ? ? ? ? ? Hcontra. inv Hcontra. }

    assert (Hunbound : (forall x : var,
         In x (collect_local_variables e) ->
         (M.empty cps.val) ! x = None)). { intros. reflexivity. }

    assert (Hnodup': NoDup (collect_local_variables e ++
                           collect_function_vars (Efun Fnil e))). {
      cbn. rewrite cats0.
      apply NoDup_app_remove_r in HvarsNodup.
      replace (collect_local_variables e) with (collect_all_local_variables e). assumption.
      destruct e; try reflexivity. exfalso. eauto. }

    assert (HfenvWf: (forall f : var,
         ((exists res : fun_tag * seq.seq var * exp,
            find_def f Fnil = Some res) <->
         (exists i : nat, fenv ! f = Some i)))). {
      split; intros. { destruct H. inv H. }
      { subst fenv. destruct H. exfalso.
        destruct e; inv H. now exfalso. }}

    assert (HfenvRho: forall (a : positive) (v : cps.val),
        (M.empty _) ! a = Some v ->
        find_def a Fnil <> None -> v = Vfun (M.empty _) Fnil a). {
      intros. discriminate. }

   (* eval context after fn entry: one label for the main fn block *)
    remember (LH_rec [] 0 [] (LH_base [] []) []) as lh.
    remember ({| f_locs := [::]; f_inst := f_inst fr |}) as frameInit.

    subst lenv.

    have HMAIN := repr_bs_LambdaANF_Wasm_related cenv fenv nenv _ host_instance _ (M.empty _)
                    _ _ _ _ _ frameInit _ lh HlenvInjective HenvsDisjoint Logic.eq_refl Hnodup' HfenvWf
                      HfenvRho HeRestr Hunbound Hstep hs _ _ _ Hfds HlocInBound Hinv_before_IH Hexpr HrelE.

    subst lh frameInit.

    destruct HMAIN as [s' [f' [k' [lh' [Hred [Hval [Hfinst _]]]]]]]. cbn.
    exists s'. split.
    dostep'. apply r_call. cbn.
    rewrite HinstFuncs. reflexivity.
    dostep'. eapply r_invoke_native with (ves:=[]) (vcs:=[]) (t1s:=[]) (t2s:=[])(f' := f_before_IH); eauto.
    rewrite HsrFuncs. subst f_before_IH. cbn. rewrite Hfinst.  reflexivity.
    subst f_before_IH. cbn.
    assert (HexpEq: match e with | Efun _ exp => exp
                                 | _ => e end= e).
    { destruct e; auto. exfalso. eauto. } rewrite HexpEq. clear HexpEq. apply repeat0_n_zeros. cbn.

    dostep'. eapply r_local. constructor. eapply rs_block with (vs:=[]) => //=. cbn. cbn in Hred.
    rewrite cats0 in Hred. eapply rt_trans. apply Hred.
    dostep'. constructor. apply rs_return with (lh:=lh') (vs:=[::]) =>//. apply rt_refl.
    subst. assumption.
  } Unshelve. all: auto.
Qed.

End INSTANTIATION.
