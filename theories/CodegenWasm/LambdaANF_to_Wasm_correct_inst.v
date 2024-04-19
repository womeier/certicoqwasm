Set Printing Compact Contexts.

From compcert Require Import Coqlib.
Require Import LambdaANF.cps LambdaANF.eval LambdaANF.cps_util LambdaANF.List_util
               LambdaANF.Ensembles_util LambdaANF.identifiers
               LambdaANF.shrink_cps_corresp.

Require Import Coq.Program.Program Coq.Sets.Ensembles
               Coq.Logic.Decidable Coq.Lists.ListDec
               Coq.Relations.Relations Relations.Relation_Operators Lia.

Require Import compcert.lib.Integers compcert.common.Memory.

From CertiCoq.CodegenWasm Require Import LambdaANF_to_Wasm LambdaANF_to_Wasm_utils LambdaANF_to_Wasm_correct.

From Wasm Require Import datatypes operations host
                         type_preservation instantiation_spec instantiation_properties
                         memory_list opsem properties common.

Require Import Libraries.maps_util.
From Coq Require Import List.

Import ssreflect eqtype ssrbool eqtype.
Import LambdaANF.toplevel LambdaANF.cps compM.
Import bytestring.
Import ExtLib.Structures.Monad MonadNotation.
Import bytestring.
Import ListNotations.
Import seq.


Section INSTRUCTION_TYPING.
Variable cenv   : ctor_env.
Variable funenv : fun_env.
Variable fenv   : fname_env.
Variable nenv   : name_env.
Variable penv   : prim_env.
Let repr_expr_LambdaANF_Wasm := @repr_expr_LambdaANF_Wasm cenv fenv nenv penv.

Ltac separate_instr :=
  cbn;
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end.

(* for main function, translated fns *)
Definition context_restr (lenv: localvar_env) (c: t_context) :=
  (* locals in bound, i32 *)
  (forall x x', @repr_var nenv lenv x x' -> nth_error (tc_local c) x' = Some T_i32) /\
  (* globals i32, mut *)
  (forall var, In var [global_mem_ptr; constr_alloc_ptr; result_var; result_out_of_mem] ->
    nth_error (tc_global c) var = Some {| tg_mut:= MUT_mut; tg_t:= T_i32|}) /\
  (* no return value *)
  (tc_return c = Some []) /\
  (* mem exists *)
  (tc_memory c <> []) /\
  (* table *)
  (tc_table c <> [::]) /\
  (* grow mem func *)
  (grow_mem_function_idx < length (tc_func_t c)) /\
  (nth_error (tc_func_t c) grow_mem_function_idx = Some (Tf [:: T_i32] [::])) /\
  (* function types *)
  (Z.of_nat (length (tc_types_t c)) > max_function_args)%Z /\
  (forall i, (Z.of_nat i <= max_function_args)%Z -> nth_error (tc_types_t c) i = Some (Tf (repeat T_i32 i) [::])).

Lemma update_label_preserves_context_restr lenv c :
  context_restr lenv c ->
  context_restr lenv (upd_label c ([:: [::]] ++ tc_label c)%list).
Proof. auto. Qed.

(* Prove that a list of instructions is well-typed, context_restr is required to hold *)
Ltac solve_bet Hcontext :=
  let Hglob := fresh "Hglob" in
  simpl; try rewrite List.app_nil_r;
  match goal with
  (* locals general *)
  | H: repr_var _ _ ?x' |- be_typing _ [:: BI_get_local ?x'] (Tf [::] _) =>
      apply Hcontext in H; apply bet_get_local; last eassumption; apply /ssrnat.leP; simpl in *; now apply nth_error_Some
  | H: repr_var _ _ ?x' |- be_typing _ [:: BI_set_local ?x'] (Tf [::_] _) =>
      apply Hcontext in H; apply bet_set_local; last eassumption; apply /ssrnat.leP; simpl in *; now apply nth_error_Some
  (* param for pp *)
  | H: nth_error (tc_local _) ?i = Some T_i32 |- be_typing _ [:: BI_get_local ?i] (Tf [::] _) =>
      apply bet_get_local; last eassumption; apply /ssrnat.leP; apply nth_error_Some; simpl in *; congruence
  | H: nth_error (tc_local _) ?i = Some T_i32 |- be_typing _ [:: BI_set_local ?i] (Tf [::_] _) =>
      apply bet_set_local; last eassumption; apply /ssrnat.leP; apply nth_error_Some; simpl in *; congruence
  (* general automation *)
  | |- be_typing _ [::] (Tf [::] [::]) => by apply bet_empty
  | |- be_typing _ [:: BI_const _] (Tf [::] _) => apply bet_const
  | |- be_typing _ [:: BI_current_memory] (Tf [::] _) => apply bet_current_memory; by apply Hcontext
  | |- be_typing _ [:: BI_grow_memory] (Tf [:: T_i32] _) => apply bet_grow_memory; by apply Hcontext
  | |- be_typing _ [:: BI_call write_char_function_idx] (Tf [:: T_i32] _) =>
         apply bet_call; try apply Hcontext; apply /ssrnat.leP; apply Hcontext
  | |- be_typing _ [:: BI_call write_int_function_idx] (Tf [:: T_i32] _) =>
         apply bet_call; try apply Hcontext; apply /ssrnat.leP; apply Hcontext
  | |- be_typing _ [:: BI_call constr_pp_function_idx] (Tf [:: T_i32] _) =>
         apply bet_call; try apply Hcontext; apply /ssrnat.leP; apply Hcontext
  | |- be_typing _ [:: BI_call grow_mem_function_idx] (Tf [:: T_i32] _) =>
         apply bet_call; try apply Hcontext; apply /ssrnat.leP; apply Hcontext
  | |- be_typing _ [:: BI_testop T_i32 _] (Tf [:: _] _) => apply bet_testop; by simpl
  | |- be_typing _ [:: BI_binop T_i32 _] (Tf [:: T_i32; T_i32] _) => apply bet_binop; apply Binop_i32_agree
  | |- be_typing _ [:: BI_relop T_i32 _] (Tf [:: T_i32; T_i32] _) => apply bet_relop; apply Relop_i32_agree
  | |- be_typing _ [:: BI_store _ None _ _] (Tf [:: T_i32; _] _) => apply bet_store; simpl; auto; by apply Hcontext
  | |- be_typing _ [:: BI_load T_i32 None _ _] (Tf [:: T_i32] _) => apply bet_load; simpl; auto; by apply Hcontext
  | |- be_typing _ [:: BI_unreachable] _ => apply bet_unreachable
  | |- be_typing _ [:: BI_return] _ => apply bet_return with (t1s:=[::]); by apply Hcontext
  | |- be_typing ?context [:: BI_set_global ?var] (Tf [:: T_i32] _) =>
         assert (nth_error (tc_global context) var = Some {| tg_mut:= MUT_mut; tg_t := T_i32 |}) as Hglob by
          (apply Hcontext; now cbn); eapply bet_set_global; eauto; apply /ssrnat.leP; now apply nth_error_Some
  | |- be_typing ?context [:: BI_get_global ?var] _ =>
         assert (nth_error (tc_global context) var = Some {| tg_mut:= MUT_mut; tg_t := T_i32 |}) as Hglob by
          (apply Hcontext; now cbn); eapply bet_get_global with (t:=T_i32); last (by rewrite Hglob); apply /ssrnat.leP; now apply nth_error_Some
  | |- be_typing _ [:: BI_if (Tf [::] [::]) _ _] _ => apply bet_if_wasm;
      apply update_label_preserves_context_restr in Hcontext; separate_instr; repeat rewrite catA;
      repeat eapply bet_composition'; try solve_bet Hcontext
  (* if above failed, try to frame the leading i32 *)
  | |- be_typing _ _ (Tf [:: T_i32] _) => apply bet_weakening with (ts:=[::T_i32]); solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_i32; T_i32] _) => apply bet_weakening with (ts:=[::T_i32]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_i32; T_i32; T_i32] _) => apply bet_weakening with (ts:=[::T_i32; T_i32]); by solve_bet Hcontext
  end.

Ltac prepare_solve_bet :=
  separate_instr; repeat rewrite catA; repeat eapply bet_composition'.

(* PP function is well-typed *)

(* only for the pp function, TODO consider combining with context_restr_pp *)
Definition context_restr_pp (c: t_context) :=
  (* memory *)
  (tc_memory c <> [::]) /\
  (* no return value *)
  (tc_return c = Some []) /\
  (* imported funcs *)
  (write_char_function_idx < length (tc_func_t c)) /\
  (write_int_function_idx  < length (tc_func_t c)) /\
  (constr_pp_function_idx  < length (tc_func_t c)) /\
  (nth_error (tc_func_t c) write_char_function_idx = Some (Tf [:: T_i32] [::])) /\
  (nth_error (tc_func_t c) write_int_function_idx = Some (Tf [:: T_i32] [::])) /\
  (nth_error (tc_func_t c) constr_pp_function_idx = Some (Tf [:: T_i32] [::])) /\
  (* param *)
  (nth_error (tc_local c) 0 = Some T_i32).

Lemma update_label_preserves_context_restr_pp c :
  context_restr_pp c ->
  context_restr_pp (upd_label c ([:: [::]] ++ tc_label c)%list).
Proof. auto. Qed.

Lemma instr_write_string_typing : forall s c,
  context_restr_pp c ->
  be_typing c (instr_write_string s) (Tf [::] [::]).
Proof.
  induction s; intros ? Hcontext; first by apply bet_empty.
  unfold instr_write_string. simpl.
  prepare_solve_bet. all: try solve_bet Hcontext.
  by apply IHs.
Qed.

Lemma pp_constr_args_typing : forall calls arity c,
  context_restr_pp c ->
  be_typing c (generate_constr_pp_constr_args calls arity) (Tf [::] [::]).
Proof.
  induction calls; intros ?? Hcontext.
  - apply bet_empty.
  - simpl.
    assert (nth_error (tc_local c) 0 = Some T_i32) as Hloc1 by apply Hcontext.
    prepare_solve_bet. all: try solve_bet Hcontext.
    by apply IHcalls.
Qed.

Lemma pp_constr_single_constr_typing : forall tag instr c,
  context_restr_pp c ->
  generate_constr_pp_single_constr cenv nenv tag = Ret instr ->
  be_typing c instr (Tf [::] [::]).
Proof.
  intros ??? Hcontext Hconstr.
  unfold generate_constr_pp_single_constr in Hconstr.
  remember (instr_write_string _) as s.
  remember (instr_write_string _) as s1 in Hconstr.
  remember (instr_write_string _) as s2 in Hconstr.
  destruct (get_ctor_arity cenv tag) eqn:Har =>//. simpl in Hconstr.
  assert (nth_error (tc_local c) 0 = Some T_i32) as Hloc0 by apply Hcontext.
  destruct (n =? 0) eqn:?; inversion Hconstr; subst instr; clear Hconstr.
  - prepare_solve_bet. all: try solve_bet Hcontext.
    + apply bet_weakening with(ts:=[::T_i32]). solve_bet Hcontext.
    + solve_bet Hcontext.
    + apply bet_if_wasm; try by solve_bet Hcontext.
      eapply bet_composition'. subst s.
      apply instr_write_string_typing =>//.
      solve_bet Hcontext.
  - prepare_solve_bet. all: try solve_bet Hcontext.
    apply bet_if_wasm; try by solve_bet Hcontext.
    eapply bet_composition'. subst s1.
    apply instr_write_string_typing =>//.
    prepare_solve_bet. all: try solve_bet Hcontext.
    by apply pp_constr_args_typing.
    subst s2. by apply instr_write_string_typing.
Qed.

Lemma sequence_concat_map_typing : forall tags f blocks c,
  (forall (t:ctor_tag) instr, f t = Ret instr -> be_typing c instr (Tf [::] [::])) ->
  sequence (map f tags) = Ret blocks ->
  be_typing c (concat blocks) (Tf [::] [::]).
Proof.
  induction tags; intros ??? Hf Hseq.
  - injection Hseq as <-. apply bet_empty.
  - simpl in Hseq.
    destruct (f a) eqn:Hfa=>//.
    destruct (sequence _) eqn:Hseq'; inv Hseq.
    simpl. eapply bet_composition'.
    + now eapply Hf.
    + now eapply IHtags.
Qed.

Theorem pp_function_body_typing : forall e fn c,
  context_restr_pp c ->
  generate_constr_pp_function cenv nenv e = Ret fn ->
  be_typing c (body fn) (Tf [::] [::]).
Proof.
  intros ??? Hcontext Hfn.
  unfold generate_constr_pp_function in Hfn.
  destruct (sequence _) eqn:Hseq =>//.
  remember (instr_write_string _) as s.
  remember (instr_write_string _) as s1 in Hfn.
  inversion Hfn; subst fn; clear Hfn. simpl.
  eapply bet_composition'.
  eapply sequence_concat_map_typing;
    [ by move => ?? Hconstr; now eapply pp_constr_single_constr_typing | eassumption].
  eapply bet_composition'. subst s. by apply instr_write_string_typing.
  assert (nth_error (tc_local c) 0 = Some T_i32) as Hloc0 by apply Hcontext.
  prepare_solve_bet; try solve_bet Hcontext.
  subst s1. by apply instr_write_string_typing.
Qed.


Definition context_restr_grow_mem (c: t_context) :=
  (* globals i32, mut *)
  (forall var, In var [global_mem_ptr; constr_alloc_ptr; result_var; result_out_of_mem] ->
    nth_error (tc_global c) var = Some {| tg_mut:= MUT_mut; tg_t:= T_i32|}) /\
  (* memory *)
  (tc_memory c <> [::]) /\
  (* param *)
  (nth_error (tc_local c) 0 = Some T_i32).

Lemma update_label_preserves_context_restr_grow_mem c :
  context_restr_grow_mem c ->
  context_restr_grow_mem (upd_label c ([:: [::]] ++ tc_label c)%list).
Proof. auto. Qed.

(* Translated expression (= all other functions bodies) has type (Tf [::] [::]) *)

Lemma grow_memory_if_necessary_typing : forall c,
  context_restr_grow_mem c ->
  be_typing c grow_memory_if_necessary (Tf [::] [::]).
Proof.
  intros c Hcontext. unfold grow_memory_if_necessary.
  assert (nth_error (tc_local c) 0 = Some T_i32) as Hloc0 by apply Hcontext.
  prepare_solve_bet. all: try solve_bet Hcontext.
  apply bet_if_wasm. prepare_solve_bet. all: try solve_bet Hcontext.
  apply bet_if_wasm; prepare_solve_bet; solve_bet Hcontext.
Qed.

Lemma constr_args_store_typing {lenv} : forall args n instr c,
  @context_restr lenv c ->
  Forall_statements_in_seq' (@set_nth_constr_arg fenv nenv lenv) args instr n ->
  be_typing c instr (Tf [::] [::]).
Proof.
  induction args; intros ??? Hcontext Hargs.
  - inv Hargs. apply bet_empty.
  - inv Hargs. inv H5. inv H.
    + (* local var *)
      apply update_label_preserves_context_restr in Hcontext.
      prepare_solve_bet. all: try solve_bet Hcontext.
      by eapply IHargs; eauto.
    + (* fn idx *)
      apply update_label_preserves_context_restr in Hcontext.
      prepare_solve_bet. all: try solve_bet Hcontext.
      by eapply IHargs; eauto.
Qed.

Lemma fun_args_typing {lenv} : forall l args' c,
  @context_restr lenv c ->
  @repr_fun_args_Wasm fenv nenv lenv l args' ->
  be_typing c args' (Tf [::] (repeat T_i32 (length l))).
Proof.
  induction l; intros ?? Hcontext Hargs =>/=.
  - inv Hargs. apply bet_empty.
  - inv Hargs.
    + (* var *)
      prepare_solve_bet. solve_bet Hcontext.
      apply bet_weakening with (ts:=[::T_i32]). by apply IHl.
    + (* fun idx *)
      prepare_solve_bet. solve_bet Hcontext.
      apply bet_weakening with (ts:=[::T_i32]). by apply IHl.
Qed.


Theorem repr_expr_LambdaANF_Wasm_typing {lenv} : forall e e' c,
  @context_restr lenv c ->
  expression_restricted cenv e ->
  @repr_expr_LambdaANF_Wasm lenv e e' ->
  be_typing c e' (Tf [::] [::]).
Proof.
  intros ??? Hcontext Hrestr Hexpr.
  have IH := repr_expr_LambdaANF_Wasm_mut cenv fenv nenv penv lenv
  (fun (e: exp) (e': list basic_instruction) (H: repr_expr_LambdaANF_Wasm lenv e e') =>
    forall c,
      @context_restr lenv c ->
      expression_restricted cenv e ->
      be_typing c e' (Tf [::] [::]))
  (fun y' cl brs1 brs2 (H: repr_branches cenv fenv nenv penv y' cl brs1 brs2) =>
    forall y c brs1' brs2',
      @context_restr lenv c ->
      expression_restricted cenv (Ecase y cl) ->
      @repr_var nenv lenv y y' ->
      repr_case_boxed y' brs1 brs1' ->
      repr_case_unboxed y' brs2 brs2' ->
         be_typing c brs1' (Tf [::] [::])
      /\ be_typing c brs2' (Tf [::] [::])).
  apply IH with (c:=c) in Hexpr; clear IH; auto.
  - (* Ehalt *)
    intros ???? Hcontext' Hrestr'.
    by prepare_solve_bet; solve_bet Hcontext'.
  - (* Eproj *)
    intros ???????? Hexpr' IH ??? Hcontext' Hrestr'.
    prepare_solve_bet; try solve_bet Hcontext'. inv Hrestr'. now apply IH.
  - (* Econstr *)
    intros ??????? Hexpr' IH ? Hargs ? Hcontext' Hrestr'.
    inv Hargs.
    + (* boxed constr. *)
      prepare_solve_bet; try solve_bet Hcontext'.
      * now eapply constr_args_store_typing.
      * inv Hrestr'. now eapply IH.
    + (* unboxed constr. *)
      prepare_solve_bet; try solve_bet Hcontext'. inv Hrestr'. now apply IH.
  - (* Ecase *)
    intros ???????? Hbranch IH ??? Hcontext' Hrestr'.
    have Hcontext'' := Hcontext'. apply update_label_preserves_context_restr in Hcontext''.
    have Htyping := IH _ _ _ _ Hcontext'' Hrestr' r r0 r1. destruct Htyping as [Hty1 Hty2]. clear IH Hcontext''.
    by prepare_solve_bet; solve_bet Hcontext' =>//.
  - (* Eapp *)
    intros ????? Hargs Hv ? Hcontext' Hrestr'.
    assert (be_typing c0 [::instr] (Tf [::] [::T_i32])) as Ht. { inv Hv; solve_bet Hcontext'. }
    prepare_solve_bet. inv Hrestr'. now eapply fun_args_typing.
    apply bet_weakening with (ts:=(repeat T_i32 (Datatypes.length args))) in Ht.
    now rewrite List.app_nil_r in Ht. inv Hrestr'.
    eapply bet_return_call_indirect with (t3s:=[::]); try by apply Hcontext'. apply /ssrnat.leP.
    assert (Z.of_nat (length (tc_types_t c0)) > max_function_args)%Z by apply Hcontext'. lia.
  - (* Eletapp *)
    intros ?????????? Hexpr' IH Hargs Hv ? Hcontext' Hrestr'.
    assert (be_typing c0 [::instr] (Tf [::] [::T_i32])) as Ht. { inv Hv; solve_bet Hcontext'. }
    prepare_solve_bet; try solve_bet Hcontext'. now eapply fun_args_typing.
    apply bet_weakening with (ts:=(repeat T_i32 (Datatypes.length args))) in Ht.
    now rewrite List.app_nil_r in Ht. inv Hrestr'.
    eapply bet_call_indirect; try by apply Hcontext'. apply /ssrnat.leP.
    assert (Z.of_nat (length (tc_types_t c0)) > max_function_args)%Z by apply Hcontext'. lia.
    inv Hrestr'. now eapply IH.
  - (* Eprim_val *)
    intros ?????? Hvar Hexpr' IH Hprim ? Hcontext' Hrestr'.
    eapply bet_composition'. prepare_solve_bet; try solve_bet Hcontext'.
    inv Hrestr'. by apply IH.
  - (* Eprim *) (* TODO: Martin *)
    intros ???????? Hvar Hexpr' IH Hp' HprimOp ? Hcontext' Hrestr'.
    eapply bet_composition'. prepare_solve_bet; try solve_bet Hcontext'.
    inv HprimOp.
    unfold apply_binop_and_store_i64.
    eapply bet_composition'.
    prepare_solve_bet. all: try solve_bet Hcontext'.
    solve_bet Hcontext'.
    apply bet_weakening with (ts:=[::T_i32]).
    solve_bet Hcontext'.
    apply bet_weakening with (ts:=[::T_i32]).
    apply bet_load; simpl; auto; by apply Hcontext'.
    apply bet_weakening with (ts:=[::T_i32] ++ [::T_i64]).
    solve_bet Hcontext'.
    apply bet_weakening with (ts:=[::T_i32] ++ [::T_i64]).
    apply bet_load; simpl; auto; by apply Hcontext'.
    apply bet_weakening with (ts:=[::T_i32]).
    apply bet_binop; simpl; by constructor.
    apply bet_weakening with (ts:=[::T_i32] ++ [::T_i64]).
    constructor.
    apply bet_weakening with (ts:=[::T_i32]).
    apply bet_binop; simpl; by constructor.
    apply bet_store; simpl; auto; by apply Hcontext'.
    solve_bet Hcontext'.
    solve_bet Hcontext'.
    solve_bet Hcontext'.
    apply bet_weakening with (ts:=[::T_i32]).
    apply bet_binop; simpl; by constructor.
    apply bet_weakening with (ts:=[::T_i32]).
    solve_bet Hcontext'.
    solve_bet Hcontext'.
    inv Hrestr'. by apply IH.
  - (* repr_branches nil *)
    intros ????? Hcontext' Hrestr' Hvar Hboxed Hunboxed.
    inv Hboxed. inv Hunboxed. by split; solve_bet Hcontext'.
  - (* repr_branches cons_boxed *)
    intros ????????? Hbranch IH1 ??? Hexpr' IH2 ???? Hcontext' Hrestr' Hvar Hboxed Hunboxed.
    inv Hboxed. split. 2:{ inv Hrestr'. inv H1. eapply IH1; eauto. by constructor. }
    prepare_solve_bet; try solve_bet Hcontext'.
    + apply IH2=>//. inv Hrestr'. now inv H1.
    + eapply IH1 in H4; try apply Hunboxed; eauto. now destruct H4. inv Hrestr'. inv H1. by constructor.
  - (* repr_branches cons_unboxed *)
    intros ????????? Hbranch IH1 ??? Hexpr' IH2 ???? Hcontext' Hrestr' Hvar Hboxed Hunboxed.
    inv Hunboxed. split. { eapply IH1 in Hboxed; eauto. now destruct Hboxed. inv Hrestr'. inv H1. by constructor. }
    prepare_solve_bet; try solve_bet Hcontext'.
    + apply IH2=>//. inv Hrestr'. now inv H1.
    + eapply IH1 in H4; try apply Hunboxed; eauto. now destruct H4. inv Hrestr'. inv H1. by constructor.
Qed.

End INSTRUCTION_TYPING.

Section INSTANTIATION.
Variable cenv   : ctor_env.
Variable funenv : fun_env.
Variable nenv   : name_env.
Variable penv   : prim_env.

Variable host_function : eqType.
Variable hfn : host_function.
Let host := host host_function.
Let store_record := store_record host_function.
Variable host_instance : host.
Let host_state := host_state host_instance.
Variable hs : host_state.
Let reduce_trans := @reduce_trans host_function host_instance.

Definition initial_store  := {|
    (* imported funcs write_int and write_char, they are only called in prettyprint_constr (unverified) *)
    s_funcs := [FC_func_host (Tf [T_i32] []) hfn; FC_func_host (Tf [T_i32] []) hfn];
    s_tables := nil;
    s_mems := nil;
    s_globals := nil;
  |}.

Fixpoint elem_vals (funs : nat) (startidx : nat) : list i32 :=
  match funs with
  | 0 => []
  | S funs' => nat_to_i32 startidx :: elem_vals funs' (S startidx)
  end.

Lemma elems_instantiate : forall len n hs s inst,
  List.Forall2 (fun e c =>
      reduce_trans (hs, s, (Build_frame nil inst), operations.to_e_list e.(modelem_offset))
                   (hs, s, (Build_frame nil inst), [::AI_basic (BI_const (VAL_int32 c))]))
    (table_element_mapping len n)
    (elem_vals len n).
Proof.
  induction len; intros ????.
  - cbn. by apply Forall2_nil.
  - cbn. apply Forall2_cons. cbn. apply rt_refl.
    eapply IHlen.
Qed.

Lemma module_typing_module_elem_typing : forall fns c,
  (* types of print_char, print_int, pp, grow_mem, main, fns *)
  tc_func_t c = [:: Tf [:: T_i32] [::], Tf [:: T_i32] [::], Tf [:: T_i32] [::], Tf [:: T_i32] [::], Tf [::] [::] &
                [seq type f | f <- fns]] ->
  length (tc_table c) > 0 ->
  Forall (module_elem_typing c) (table_element_mapping (Datatypes.length fns + num_custom_funs) 0).
Proof.
  intros ?? Hft Htab. unfold num_custom_funs.
  apply Forall_forall. intros ? Hnth.
  apply In_nth_error in Hnth. destruct Hnth as [n Hnth].
  have Hlen := Hnth. apply Some_notNone in Hlen. apply nth_error_Some in Hlen. rewrite table_element_mapping_length in Hlen.
  erewrite table_element_mapping_nth in Hnth=>//.
  injection Hnth as <-. repeat split =>//.
  - by apply bet_const.
  - by apply /ssrnat.leP.
  - rewrite Hft. cbn. rewrite length_is_size. rewrite size_map.
    rewrite length_is_size in Hlen.
    rewrite -ssrnat.subnE -ssrnat.minusE. rewrite Nat.add_0_r.
    now replace (n - S (S (S (S (size fns))))) with 0 by lia.
Qed.

Theorem module_instantiate : forall e module fenv venv,
  correct_cenv_of_exp cenv e ->
  NoDup (collect_function_vars e) ->
  LambdaANF_to_Wasm nenv cenv penv e = Ret (module, fenv, venv) ->
  exists sr inst exports, instantiate host_function host_instance initial_store module
    [MED_func (Mk_funcidx 0); MED_func (Mk_funcidx 1)] (sr, inst, exports, None).
Proof.
  intros ???? Hcenv Hnodup' H. unfold LambdaANF_to_Wasm in H.
  destruct (check_restrictions cenv e) eqn:Hrestr. inv H. destruct u.
  eapply check_restrictions_expression_restricted in Hrestr; last by apply rt_refl.
  destruct (generate_constr_pp_function cenv nenv e) eqn:Hpp. inv H.
  destruct (match e with
            | Efun _ _ => e
            | _ => Efun Fnil e
            end) eqn:He; try (by inv H).
  destruct (translate_functions _ _ _ _ f) eqn:Hfuns. inv H. rename l into fns, f into fds.
  cbn in H.
  destruct (translate_body nenv cenv _ _) eqn:Hexpr. inv H.
  rename l into wasm_main_instr.

  remember (list_function_types (Z.to_nat max_function_args)) as ts. rewrite -Heqts in H.
  inversion H. clear H. cbn. rename venv into lenv.

  assert (Hnodup: NoDup (collect_function_vars (Efun fds e))). {
    destruct e; inv He; inv Hfuns; try by apply NoDup_nil. assumption. } clear Hnodup'.

  destruct (interp_alloc_module _ initial_store module
            [:: MED_func (Mk_funcidx 0); MED_func (Mk_funcidx 1)] (repeat (nat_to_value 0) 4))
         as [[s' inst] exps] eqn:HallocM.

  subst module.

  assert (Hpp': type w = Tf [::T_i32] [::] /\ fidx w = constr_pp_function_idx). {
    unfold generate_constr_pp_function in Hpp. destruct (sequence _) =>//.
    by inv Hpp.
  } destruct Hpp' as [Hty HwId]. rewrite Hty HwId in HallocM.
  rewrite Heqts in HallocM.

  (* final store *)
  exists s'.
  (* module instance *)
  exists inst.
  (* exports *)
  exists exps.

  (* import types *)
  exists [:: ET_func (Tf [::T_i32] [::]); ET_func (Tf [::T_i32] [::])].
  (* export types *)
  exists ([:: ET_func (Tf [::T_i32] [::]); ET_func (Tf [::T_i32] [::]);   (* pp, grow_mem *)
              ET_func (Tf [::] [::])] ++                                  (* main *)
         (map (fun f => ET_func f.(type)) fns) ++                         (* all fns exported *)
         [:: ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |}
           ; ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |}
           ; ET_glob {| tg_mut := MUT_mut; tg_t := T_i32 |}               (* global vars *)
           ; ET_mem {| lim_min := 1%N; lim_max := Some max_mem_pages|}]). (* global mem *)
  exists hs.
  exists s'. (* store after init_mems TODO update to new WasmCert *)
  (* initial values of globals: 0 *)
  exists ([:: nat_to_value 0; nat_to_value 0; nat_to_value 0; nat_to_value 0]).
  (* element values (table entries) *)
  exists (elem_vals (length fns + num_custom_funs) 0).
  (* data values *)
  exists [::].

  repeat split.
  (* module typing *) {
  - unfold module_typing. simpl.
    exists ([:: (Tf [::T_i32] [::]); (Tf [::T_i32] [::]); (Tf [::] [::])] ++
             map (fun f => type f) fns). (* pp, grow_mem, main, fns *)
    exists (repeat ({| tg_mut := MUT_mut; tg_t := T_i32 |}) 4).
    repeat split=>//.
    + (* module_func_typing *)
      apply Forall2_cons.
      { (* pp function *)
        subst ts. cbn. rewrite length_list_function_types.
        replace (type w) with (Tf [::T_i32] [::]) by
          (unfold generate_constr_pp_function in Hpp; now destruct (sequence _); inv Hpp).
        repeat split =>//.
        eapply pp_function_body_typing; eauto. repeat split =>//=.
        unfold write_char_function_idx. lia.
        unfold write_int_function_idx. lia.
        unfold constr_pp_function_idx. lia. }
      apply Forall2_cons.
      { (* grow mem func *)
        subst ts. cbn. rewrite length_list_function_types.
        split. cbn. rewrite -ssrnat.subnE -ssrnat.minusE. apply /ssrnat.eqnP. lia.
        split=>//. apply grow_memory_if_necessary_typing.
        repeat split =>//.
        intros ? Hin'. cbn. by repeat destruct Hin' as [|Hin']; subst =>//. }
      apply Forall2_cons.
      { (* main func *)
        subst ts. cbn. rewrite length_list_function_types. repeat split =>//.
        apply translate_body_correct in Hexpr.
        2:{ destruct e; inv He =>//. eapply Forall_constructors_subterm. eassumption.
            apply t_step. by apply dsubterm_fds2. }
        eapply repr_expr_LambdaANF_Wasm_typing =>//; last by eassumption.
        2: { (* expr restr *) destruct e; inv He =>//. by inv Hrestr. }
        repeat split =>//.
        * (* locals in bound *)
          intros ?? Hvar. cbn.
          rewrite nth_error_map. destruct (nth_error _ x') eqn:Hcontra =>//.
          inv Hvar. apply var_mapping_list_lt_length in H. by apply nth_error_Some in H.
        * (* globals *)
          intros var Hin. cbn.
          by repeat destruct Hin as [|Hin]; subst =>//.
        * (* grow_mem func id *)
          cbn. unfold grow_mem_function_idx; lia.
        * (* types *)
          intros ? Hmax. cbn. unfold max_function_args in Hmax.
          erewrite nth_error_nth'; first rewrite nth_list_function_types =>//. lia.
          rewrite length_list_function_types. lia.
      }
      { (* funcs *)
        apply Forall2_spec; first by rewrite map_length length_is_size length_is_size size_map.
        intros ?? [t1s t2s] Hnth1 Hnth2. cbn. unfold module_func_typing. repeat split =>//.
        rewrite nth_error_map in Hnth1. simpl in Hfuns.
        destruct (nth_error fns n) eqn:Hin =>//. cbn. inv Hnth1.
        rewrite nth_error_map in Hnth2. rewrite Hin in Hnth2. injection Hnth2 as Hnth2.
        rewrite Hnth2.
        assert (n = fidx w0 - num_custom_funs).
        { eapply translate_functions_nth_error_idx; eauto. } subst n.

        replace (create_fname_mapping e) with (create_fname_mapping (Efun fds e)) in Hfuns by
          (destruct e; inv He =>//).
        have H' := translate_functions_exists_original_fun cenv nenv _ _ host_instance fds fds fns _ _ _ _ Hnodup Hfuns Logic.eq_refl (nth_error_In _ _ Hin).
        destruct H' as [f [t [ys [e1 [Hfd [Htype Hvarr]]]]]].
        rewrite Hnth2 in Htype.

        assert (HcenvFds : (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
                            find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e)). {
          intros ???? Hfd'.
          destruct e; inv He =>//. eapply Forall_constructors_subterm. eassumption.
          apply t_step. apply dsubterm_fds. now eapply find_def_dsubterm_fds_e.
        }
        have H' := translate_functions_find_def cenv nenv _ _ host_instance fds _ _ _ _ e1 _ Hnodup Hfuns Hfd HcenvFds.

        destruct H' as [f' [e' [locs [ty [func [Hvar [-> [Hty' [Hin' [<- [<- [Hlocs [<- Hexpr']]]]]]]]]]]]].
        assert (func = w0). {
          assert (Heq: fidx func = fidx w0). {
            inv Hvar. inv Hvarr. unfold translate_var in H, H0.
            now destruct ((create_fname_mapping (Efun fds e)) ! f).
          }
          apply In_nth_error in Hin'. destruct Hin' as [j Hj].
          assert (j = fidx func - num_custom_funs). eapply translate_functions_nth_error_idx; try apply Hfuns; eauto.
          congruence.
        } subst w0. clear Hvarr Hin'.
        rewrite Hty' in Hnth2. inv Hnth2.

        split. { destruct e; inv He; try by inv Hfd. inv Hrestr.
          apply H3 in Hfd. destruct Hfd as [Hfd _]. rewrite -ssrnat.subnE -ssrnat.minusE.
          rewrite length_list_function_types map_length. cbn.
          assert (Heq: Datatypes.length ys - Z.to_nat max_function_args = 0) by lia.
          now rewrite Heq. }
        split. { rewrite nth_list_function_types. rewrite map_repeat_eq -map_map_seq -map_repeat_eq.
                 erewrite <-map_repeat_eq. by apply /eqfunction_typeP.
                 rewrite map_length.
                 destruct e; inv He; try by inv Hfd.
                  inv Hrestr. apply H3 in Hfd. destruct Hfd as [Hfd _]. lia. }
        eapply repr_expr_LambdaANF_Wasm_typing =>//; last by apply Hexpr'.
        { (* context restrictions *)
          repeat split =>//.
          * (* locs i32 *)
            intros ?? Hvar'.
            rewrite Hlocs. rewrite <-map_repeat_eq. cbn.
            rewrite <-repeat_app, <- app_length.
            apply nth_error_repeat. inv Hvar'. now eapply var_mapping_list_lt_length.
          * (* globals *)
            intros ? Hin'. cbn. by repeat destruct Hin' as [|Hin']; subst =>//.
          * (* grow_mem func id *)
            cbn. unfold grow_mem_function_idx; lia.
          * (* types *)
            intros ? Hmax.
            erewrite nth_error_nth'. rewrite nth_list_function_types. reflexivity. lia.
            rewrite length_list_function_types. lia.
        }
        { destruct e; inv He; try by inv Hfd. inv Hrestr. now eapply H3. }
      }
    + (* module_glob_typing *)
      repeat (apply Forall2_cons; repeat split; try by apply bet_const =>//).
      by apply Forall2_nil.
    + (* module_elem_typing *)
      simpl. by apply module_typing_module_elem_typing.
    + (* module_import_typing *)
      apply Forall2_cons. subst ts. cbn. rewrite length_list_function_types. by unfold Pos.to_nat.
      apply Forall2_cons. subst ts. cbn. rewrite length_list_function_types. by unfold Pos.to_nat.
      by apply Forall2_nil.
    + (* module_export_typing *)
      apply Forall2_cons.
      { (* pp func *)
        cbn. by rewrite HwId. }
      apply Forall2_cons.
      { (* grow_mem func *)
        now cbn. }
      apply Forall2_cons.
      { (* main func *)
        now cbn. }
      apply Forall2_app.
      { (* fns *)
        intros. cbn. apply Forall2_spec; first by repeat rewrite map_length.
        intros ??? Hnth1 Hnth2. rewrite nth_error_map in Hnth2.
        destruct (nth_error fns n) eqn:Hnth =>//.
        rewrite nth_error_map in Hnth1. rewrite Hnth in Hnth1. inv Hnth1. inv Hnth2.
        rewrite -ssrnat.subnE -ssrnat.minusE. simpl.
        rewrite map_length.
        destruct e; try by inv He; inv Hfuns; destruct n=>//. inv He.
        assert (n = fidx w0 - num_custom_funs). { now eapply translate_functions_nth_error_idx; eauto. } subst n.
        assert (Hbounds: num_custom_funs <= fidx w0 < length fns + num_custom_funs). {
          eapply translate_functions_idx_bounds; eauto.
          * intros. split; first by apply local_variable_mapping_gt_idx in H.
            assert (Hvar: translate_var nenv (create_fname_mapping (Efun fds e0)) f ""%bs = Ret f')
              by (unfold translate_var; rewrite H=>//). clear H.
            have H' := Hvar.
            apply var_mapping_list_lt_length' in Hvar.
            rewrite collect_function_vars_length in Hvar.
            now erewrite translate_functions_length in Hvar.
          * apply In_map. now eapply nth_error_In. }
        unfold num_custom_funs in *.
        replace (fidx w0 - S (S (S (S (Datatypes.length fns))))) with 0 by lia.
        destruct (fidx w0); first by lia.
        do 4! (destruct i; first by lia). cbn in Hnth.
        rewrite Nat.sub_0_r in Hnth. cbn.
        rewrite nth_error_map. rewrite Hnth. by apply /eqfunction_typeP.
      }
      (* global vars, memory *)
      repeat apply Forall2_cons =>//. }
  - (* imports typing *)
    apply Forall2_cons. eapply ETY_func; cbn; eauto.
    apply Forall2_cons. eapply ETY_func; cbn; eauto. by apply Forall2_nil.
  - (* alloc_module is true *) { cbn.
    unfold interp_alloc_module, initial_store in HallocM.
    destruct (alloc_funcs _) eqn:Hfuncs. cbn in Hfuncs. rewrite Hty.
    have Hfuncs' := Hfuncs.
    cbn in HallocM.
    apply alloc_func_gen_index in Hfuncs.
    destruct Hfuncs as [Hfuncs1 [Hfuncs2 [Hfuncs3 [Hfuncs4 Hfuncs5]]]].
    cbn in Hfuncs1, Hfuncs2, Hfuncs3, Hfuncs4, Hfuncs5.
    unfold add_table, add_glob in HallocM. cbn in HallocM.
    rewrite Hfuncs2 -Hfuncs3 -Hfuncs4 -Hfuncs5 in HallocM. cbn in HallocM.
    unfold gen_func_instance in HallocM. cbn in HallocM.
    rewrite -Heqts in HallocM. (* fold list of types again *)
    injection HallocM as <-<-<-.

    rewrite -Heqts in Hfuncs'. rewrite Hfuncs'. cbn.
    unfold add_glob. cbn.
    rewrite map_length map_map HwId. rewrite Hfuncs1 Hfuncs2 -Hfuncs3 -Hfuncs4 -Hfuncs5. cbn.
    repeat (apply andb_true_iff; split =>//).
    + apply /eqstore_recordP.
      unfold gen_func_instance. cbn. rewrite map_length.
      repeat rewrite map_map. by subst ts; reflexivity.
    + by apply /eqseqP.
    + apply /eqseqP. rewrite map_length.
      cbn. repeat f_equal. erewrite map_id.
      rewrite -gen_index_iota. by apply imap_aux_offset.
    + by apply /eqmodule_exportP.
    + by apply /eqseqP. }
  - (* instantiate globals *)
    unfold instantiate_globals. cbn.
    repeat (apply Forall2_cons; first by apply rt_refl).
    by apply Forall2_nil.
  - (* instantiate elem *)
    unfold instantiate_elem. cbn.
    by apply elems_instantiate.
  - (* instantiate data *)
    by apply Forall2_nil.
  - (* check_bounds elem *) { (* TODO changes with update to 2.0 *) admit. }
  - (* data *) { cbn. admit. (* TODO false, but will change with the update to 2.0 *) }
Admitted.

End INSTANTIATION.
