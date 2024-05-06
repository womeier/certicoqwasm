Set Printing Compact Contexts.

From compcert Require Import Coqlib.
Require Import LambdaANF.cps LambdaANF.eval LambdaANF.cps_util LambdaANF.List_util
               LambdaANF.Ensembles_util LambdaANF.identifiers
               LambdaANF.shrink_cps_corresp.

Require Import Coq.Program.Program Coq.Sets.Ensembles
               Coq.Logic.Decidable Coq.Lists.ListDec
               Coq.Relations.Relations Relations.Relation_Operators Lia Nnat.

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


(* Top level corollary *)
Section INSTANTIATION.

Import host instantiation_spec.
Import Lia.
Import Relations.Relation_Operators.

Variable cenv:LambdaANF.cps.ctor_env.
Variable funenv:LambdaANF.cps.fun_env.
Variable nenv : LambdaANF.cps_show.name_env.
Variable penv : LambdaANF.toplevel.prim_env.

Context `{ho : host}.
Variable hfn : host_function.

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
    s_funcs := [FC_func_host (Tf [T_num T_i32] []) hfn; FC_func_host (Tf [T_num T_i32] []) hfn];
    s_tables := nil;
    s_mems := nil;
    s_datas := nil;
    s_elems := [];
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
  store_record_eqb s s' = true -> s = s'.
Proof.
  intros. unfold store_record_eqb in H.
  destruct (store_record_eq_dec _ _); auto. inv H.
Qed.

Fixpoint funcidcs (funs : nat) (startidx : funcidx) : list funcidx :=
  match funs with
  | 0 => []
  | S funs' => startidx :: funcidcs funs' (N.succ startidx)
  end.

Lemma add_funcs_effect : forall s' s'' l l1 l2 mi,
    fold_left
          (fun '(s, ys) (x : module_func) =>
           (add_func s (gen_func_instance x mi),
            N.of_nat (Datatypes.length (s_funcs s)) :: ys)) l
          (s', l1) = (s'', l2) ->

    (s_datas s' = s_datas s'') /\
    (s_elems s' = s_elems s'') /\
    (s_globals s' = s_globals s'') /\
    (s_mems s' = s_mems s'') /\
    (s_tables s' = s_tables s'') /\
    (s_funcs s'' = (s_funcs s') ++
    (map (fun a => gen_func_instance a mi) l ))%list /\
    l2 = List.app (List.rev (funcidcs (length l) (N.of_nat (length (s_funcs s'))))) l1.
Proof.
  intros. generalize dependent l1. revert s' s'' l2.
  induction l; intros.
  - inv H. cbn. rewrite app_nil_r. tauto.
  - cbn in H. apply IHl in H.
    destruct H as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]. subst l2. rewrite -H1 -H2 -H3 -H4 -H5 H6.
    rewrite -app_assoc. auto.
    repeat split; auto.
    replace (N.of_nat (Datatypes.length (s_funcs s')) :: l1) with ([:: N.of_nat (Datatypes.length (s_funcs s'))]  ++ l1) by reflexivity.
    rewrite app_length Nat.add_comm. cbn.
    rewrite -app_assoc. cbn.
    f_equal. f_equal. f_equal. cbn. lia.
Qed.

Lemma length_list_function_types : forall n,
  length (list_function_types n) = S n.
Proof.
  induction n; cbn; auto. f_equal. now rewrite map_length.
Qed.

Lemma nth_list_function_types : forall m n def,
    m <= n ->
    List.nth m (list_function_types n) def =
    Tf (List.repeat (T_num T_i32) m) [].
Proof.
  induction m; intros; try lia.
  - destruct n; try lia; reflexivity.
  - have Hlen := length_list_function_types n.
    destruct n. lia. assert (Hlt: m <= n) by lia.
    remember (fun t : function_type =>
      match t with
      | Tf args rt => Tf (T_num T_i32 :: args)%SEQ rt
      end) as f.
    have Hindep := nth_indep _ _ (f def).
    rewrite Hindep; try lia.
       cbn. subst f. rewrite map_nth.
    rewrite IHm; auto.
Qed.

Lemma translate_fvar_fname_mapping_aux : forall fds e f i n env,
  (forall x j, env ! x = Some j -> j < N.of_nat (numOf_fundefs fds) + n)%N ->
  (create_var_mapping n (collect_function_vars (Efun fds e))
        env) ! f = Some i -> (i < N.of_nat (numOf_fundefs fds) + n)%N.
Proof.
  induction fds; intros.
  - remember (numOf_fundefs (Fcons v f l e fds)) as len. cbn in Heqlen. destruct len. lia.
    cbn in H0. rename H0 into Hf.
    destruct (var_dec f0 v).
    { (* f0=v *) subst f0. rewrite M.gss in Hf. inv Hf. lia. }
    { (* f0<>v *) cbn in Hf. rewrite M.gso in Hf; auto.
      apply IHfds in Hf. injection Heqlen as ->. cbn. destruct n; try lia.
      assumption. intros.
      apply H in H0. cbn in H0. destruct n; lia. }
  - inv H0. now apply H in H2.
Qed.

Lemma translate_fvar_fname_mapping : forall e f errMsg i,
    translate_var nenv (create_fname_mapping e) f errMsg = Ret i ->
    match e with Efun fds _ => N.to_nat i < numOf_fundefs fds + num_custom_funs | _ => True end.
Proof.
  intros. unfold create_fname_mapping, translate_var in H.
  destruct ((create_var_mapping (N.of_nat num_custom_funs) (collect_function_vars e)
         (M.empty _)) ! f) eqn:Hf; rewrite Hf in H; inv H.
  destruct e; auto. rename f0 into fds.
  apply translate_fvar_fname_mapping_aux in Hf. lia.
  intros. inv H.
Qed.

Lemma table_element_mapping_length : forall len i,
  Datatypes.length (table_element_mapping len i) = len.
Proof.
  by induction len; intros; cbn; auto.
Qed.

Lemma nth_error_funcidcs {A} : forall (l : list A) len n idx,
  n < len ->
  nth_error (funcidcs len idx) n = Some (idx + N.of_nat n)%N.
Proof.
  induction len; intros; cbn in H. lia.
  destruct n; cbn. f_equal. lia.
  assert (n < len) by lia.
  replace (idx + N.pos (Pos.of_succ_nat n))%N with (N.succ idx + N.of_nat n)%N by lia.
  now apply IHlen.
Qed.

Lemma translate_functions_exists_original_fun : forall fds fds'' fns wasmFun e eAny fenv,
  NoDup (collect_function_vars (Efun fds e)) ->
  translate_functions nenv cenv fenv penv fds = Ret fns ->
  fenv = create_fname_mapping (Efun fds'' eAny) ->
  In wasmFun fns ->
  exists f t ys e, find_def f fds = Some (t, ys, e) /\ (type wasmFun) = N.of_nat (length ys) /\ @repr_funvar fenv nenv f (wasmFun.(fidx)).
Proof.
  induction fds; intros fds'' fns wasmFun e' eAny fenv Hnodup Htrans Hfenv Hin. 2: { inv Htrans. inv Hin. }
  simpl in Htrans.
  destruct (translate_function nenv cenv _ penv v l e) eqn:transF. inv Htrans.
  cbn. destruct (translate_functions _ _ _ ) eqn:Htra; inv Htrans. destruct Hin.
  - (* wasmFun is first fn *) subst w.
    exists v, f, l, e. destruct (M.elt_eq); last contradiction.
    split; auto.
    unfold translate_function in transF.
    destruct (translate_var _ _ _ _) eqn:HtransFvar. inv transF.
    destruct (translate_body _ _ _ _) eqn:HtransE. inv transF.
    inv transF. cbn.  split=>//. now econstructor.
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
  translate_functions nenv cenv fenv penv fds = Ret fns ->
  numOf_fundefs fds = length fns.
Proof.
  induction fds; intros. 2: { now inv H. }
  simpl in H.
  destruct (translate_function nenv cenv fenv penv v l e). inv H.
  destruct (translate_functions _ _ _ _ fds). inv H. destruct fns; inv H. cbn. now rewrite -IHfds.
Qed.

Lemma translate_functions_fenv : forall fds fns fenv e i x,
  map_injective fenv ->
  translate_functions nenv cenv fenv penv fds = Ret fns ->
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
    destruct (translate_body _ _ _ _ _). inv HtransF. inv HtransF.
    unfold translate_var in HtransV.
    destruct (fenv ! x) eqn:HtransV'; rewrite HtransV' in HtransV=>//=. by injection HtransV as ->.
  - (* i=Si' *)
    cbn in Hlt. cbn.
    eapply IHfds; eauto. lia.
Unshelve. assumption.
Qed.

Lemma translate_functions_idx_bounds : forall fds fns fenv min max,
  (forall f f', fenv ! f = Some f' -> min <= f' < max)%N ->
  translate_functions nenv cenv fenv penv fds = Ret fns ->
  forall idx, In idx (map fidx fns) -> (min <= idx < max)%N.
Proof.
  induction fds; intros ???? Hbounds Hfns ? Hin; last by inv Hfns.
  destruct fns. inv Hin. simpl in Hfns.
  destruct (translate_function _ _ _ _ _ _) eqn:HtransF. inv Hfns.
  destruct (translate_functions _ _ _ _ fds) eqn:Hfix; inv Hfns.
  destruct Hin.
  - (* i=0 *)
    subst. unfold translate_function in HtransF.
    destruct (translate_var _ _ _ _) eqn:HtransV. inv HtransF.
    destruct (translate_body _ _ _ _ _). inv HtransF. inv HtransF.
    unfold translate_var in HtransV. cbn.
    destruct (fenv ! v) eqn:HtransV'; rewrite HtransV' in HtransV; inv HtransV. now apply Hbounds in HtransV'.
  - (* i=Si' *)
    by eapply IHfds; eauto.
Qed.

Lemma translate_functions_increasing_fids : forall fds fns fenv e e',
  fenv = create_fname_mapping e ->
  match e with Efun fds' _ => fds' = fds | _ => True end ->
  map_injective fenv ->
  NoDup (collect_function_vars (Efun fds e')) ->
  translate_functions nenv cenv fenv penv fds = Ret fns ->
  (forall i j i' j', i > j -> nth_error (map (fun f => fidx f) fns) i = Some i' ->
                              nth_error (map (fun f => fidx f) fns) j = Some j' -> (i' > j')%N).
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
  rewrite -(Nat2N.id i) in Hiv. rewrite -(Nat2N.id j) in Hjv'.
  rewrite (var_mapping_list_lt_length_nth_error_idx _ _ (N.of_nat num_custom_funs) _ _ _ Hiv) in Hi''; auto.
  rewrite (var_mapping_list_lt_length_nth_error_idx _ _ (N.of_nat num_custom_funs) _ _ _ Hjv') in Hj''; auto.
  remember (_ + N.of_nat i)%N as i''. injection Hi'' as ->.
  remember (_ + N.of_nat j)%N as j''. injection Hj'' as ->. lia.
Qed.

Lemma increasing_list_fact_trans : forall n l i i' i'n,
  (forall i j i' j', i > j -> nth_error l i = Some i' ->
                              nth_error l j = Some j' -> (i' > j')%N) ->
  nth_error l i = Some i' ->
  nth_error l (i + n) = Some i'n -> (i'n >= i' + N.of_nat n)%N.
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
  assert (i'n >= m + N.of_nat n)%N. { apply IH. assumption. }

  have H' := H (S i) i _ _ _ Hm H0. lia.
Qed.

Lemma increasing_list_fact_id : forall l i i' n,
  (forall i j i' j', i > j -> nth_error l i = Some i' ->
                              nth_error l j = Some j' -> (i' > j')%N) ->
  (forall j j', nth_error l j = Some j' -> n <= N.to_nat j' < length l + n) ->
  nth_error l i = Some i' -> n+i = N.to_nat i'.
Proof.
  intros.
  assert (n + i >= N.to_nat i'). {
    assert (Hl: length l - 1 < length l). { destruct l. destruct i; inv H1. cbn. lia. }
    apply nth_error_Some in Hl. apply notNone_Some in Hl. destruct Hl as [v Hv].
    assert (i < length l). { now apply nth_error_Some. }
    replace (length l - 1) with (i + (length l - 1 - i)) in Hv by lia.
    have H' := increasing_list_fact_trans _ _ _ _ _ H H1 Hv.
    apply H0 in Hv. lia. }
  assert (n + i <= N.to_nat i'). {
    assert (exists v, nth_error l 0 = Some v). {
      apply notNone_Some. apply nth_error_Some. destruct l. destruct i; inv H1.  cbn. lia. }
    destruct H3 as [v Hv].
    have H' := increasing_list_fact_trans _ _ _ _ _ H Hv H1.
    apply H0 in Hv. lia. }
  lia.
Qed.

Lemma fns_fidx_nth_error_fidx : forall fns func j,
  (forall (i j : nat) (i' j' : funcidx),
      i > j ->
      nth_error [seq fidx f | f <- fns] i = Some i' ->
      nth_error [seq fidx f | f <- fns] j = Some j' -> (i' > j')%N) ->
  (forall idx, In idx (map fidx fns) -> num_custom_funs <= N.to_nat idx < length fns + num_custom_funs) ->
  nth_error fns j = Some func ->
  nth_error fns (N.to_nat (fidx func - N.of_nat num_custom_funs)) = Some func.
Proof.
  intros. unfold num_custom_funs in *.
  assert (Hin: In func fns). { eapply nth_error_In. eassumption. }
  apply in_map with (f:=fidx) in Hin.
  apply H0 in Hin.
  destruct (N.to_nat (fidx func)) eqn:Hfi. lia. do 3! (destruct n; try lia). cbn.
  replace (N.to_nat (fidx func - 4)) with n by lia.
  assert (Hlen: n < length fns) by lia.

  assert (Ho: option_map fidx (nth_error fns j) = option_map fidx (Some func)) by congruence.
  rewrite <- nth_error_map in Ho.

  assert (Hbounds: (forall j j',
    nth_error [seq fidx f | f <- fns] j = Some j' ->
    num_custom_funs <= N.to_nat j' < Datatypes.length [seq fidx f | f <- fns] + num_custom_funs)). {
    intros. apply nth_error_In in H2. apply H0 in H2.  now rewrite map_length.
  }

  have H' := increasing_list_fact_id _ _ _ num_custom_funs H Hbounds Ho.
  unfold num_custom_funs in H'.
  assert (n=j) by lia. congruence.
Qed.

Lemma translate_functions_NoDup : forall fds fns fenv e e',
  fenv = create_fname_mapping e ->
  match e with Efun fds' _ => fds' = fds | _ => True end ->
  map_injective fenv ->
  NoDup (collect_function_vars (Efun fds e')) ->
  translate_functions nenv cenv fenv penv fds = Ret fns ->
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
  have Hcontra := H' _ _ _ _ _ Heq Hv. lia.
  (* i>j *)
  assert (Hgt: i>j) by lia.
  have Hcontra := H' _ _ _ _ Hgt Hv Heq. lia.
Qed.

Lemma translate_functions_type_bound {fenv} : forall fds fns fn eAny,
  NoDup (collect_function_vars (Efun fds eAny)) ->
  (forall f t ys e', find_def f fds = Some (t, ys, e') ->
             Z.of_nat (length ys) <= max_function_args /\
             expression_restricted cenv e')%Z ->
  translate_functions nenv cenv fenv penv fds = Ret fns ->
  In fn fns ->
  (type fn <= 20)%N.
Proof.
  induction fds. 2:{ intros. by inv H1. }
  intros ??? Hnodup Hrestr Htrans Hin. cbn in Htrans.
  destruct (translate_var nenv fenv v _) eqn:Hvar=>//.
  destruct (translate_body _ _ _ _ _) eqn:Hbody=>//.
  destruct (translate_functions _ _ _ _ _) eqn:Hfns=>//. inv Htrans.
  have H' := Hrestr v f l e. cbn in H'. destruct (M.elt_eq v v)=>//. destruct H' as [H' _]=>//.
  unfold max_function_args in H'.
  destruct Hin as [Hin|Hin].
  - subst. cbn. lia.
  - eapply IHfds; eauto.
    + cbn in Hnodup. inv Hnodup. eassumption.
    + intros. eapply Hrestr with (f:=f0); eauto. cbn.
      destruct (M.elt_eq f0 v); eauto. exfalso.
      subst. inv Hnodup. apply H2. apply find_def_in_collect_function_vars; auto. congruence.
Unshelve. assumption.
Qed.

Lemma translate_functions_nth_error_idx : forall eTop e eAny fds fns j func,
  match eTop with
  | Efun _ _ => eTop
  | _ => Efun Fnil eTop
  end = Efun fds e ->
  NoDup (collect_function_vars (Efun fds eAny)) ->
  translate_functions nenv cenv (create_fname_mapping eTop) penv fds = Ret fns ->
  nth_error fns j = Some func ->
  (j = N.to_nat (fidx func) - num_custom_funs).
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
                              (N.of_nat num_custom_funs <= idx < N.of_nat (Datatypes.length fns + num_custom_funs))%N). {
    intros ? Hidx.
    have H' := translate_functions_idx_bounds _ _ _ _ _ _ Hfns _ Hidx. apply H'.
    intros ? ? Hf.
    split. { apply local_variable_mapping_gt_idx in Hf. lia. }
    assert (HtransF: translate_var nenv (create_fname_mapping (Efun fds eAny)) f ""%bs = Ret f'). {
    unfold translate_var. destruct eTop=>//. subst f0. now rewrite Hf. }
    apply var_mapping_list_lt_length' in HtransF.
    rewrite collect_function_vars_length in HtransF.
    erewrite <- (translate_functions_length fds); eauto. lia.
  }
  assert (Hnth: nth_error fns (N.to_nat (fidx func - N.of_nat num_custom_funs)) = Some func). {
    eapply fns_fidx_nth_error_fidx; eauto. intros.
    apply Hbounds in H. lia. }
  rewrite -Hin in Hnth.
  have Hnodup' := translate_functions_NoDup _ _ _ _ _ Logic.eq_refl Hfds Hinj Hnodup Hfns.
  apply NoDup_map_inv in Hnodup'.
  eapply NoDup_nth_error; eauto.
  now apply nth_error_Some. rewrite -Hnth. f_equal. lia.
Qed.

Lemma translate_functions_find_def : forall fds f fns t ys e fenv,
  NoDup (collect_function_vars (Efun fds e)) ->
  translate_functions nenv cenv fenv penv fds = Ret fns ->
  find_def f fds = Some (t, ys, e) ->
  (forall f t ys e, find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e) ->
  exists idx e' locs func, repr_funvar fenv nenv f idx /\
    locs = repeat (T_num T_i32) (length (collect_local_variables e)) /\
    In func fns /\
    func.(fidx) = idx /\
    func.(type) = N.of_nat (length ys) /\
    func.(locals) = locs /\
    func.(body) = e' /\
    repr_expr_LambdaANF_Wasm cenv fenv nenv penv e e'
     (lenv := create_local_variable_mapping (ys ++ collect_local_variables e)).
Proof.
  induction fds; intros ? ? ? ? ? ? Hnodup HtransFns HfDef HcorrCenv; last by inv HfDef.
  simpl in HtransFns.
  destruct (translate_function _ _ _ _ _ _) eqn:Hf. inv HtransFns.
  destruct (translate_functions _ _ _ _ fds) eqn:Hfns; inv HtransFns.
  cbn in HfDef. destruct (M.elt_eq f0 v).
  - (* f0=v *)
    inv HfDef.
    unfold translate_function in Hf.
    destruct (translate_var _ _ _ _) eqn:Hvar. inv Hf.
    destruct (translate_body _ _ _ _ _) eqn:Hexp; inv Hf.
    exists u, l. eexists. eexists. eexists.
    now econstructor.
    do 2! (split; try reflexivity). now left.
    cbn. rewrite map_repeat_eq.
    repeat split=>//.
    eapply translate_body_correct in Hexp; eauto. eapply HcorrCenv with (f:=v). cbn.
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
    destruct IH as [idx [e' [locs [func [? [? [? [? [? [? [? ?]]]]]]]]]]].
    inversion H. subst. inv H.
    repeat eexists; eauto. now right.
Qed.

Lemma gen_fun_instance_simplify_eq : forall fns mi,
  (Z.of_nat (length fns) < max_num_functions)%Z ->
  (forall fn, In fn fns -> type fn <= 20)%N ->
  inst_types mi = list_function_types (Pos.to_nat 20) ->
  [seq gen_func_instance {| modfunc_type := type fn; modfunc_locals := locals fn; modfunc_body := body fn |}
         mi
     | fn <- fns] =
  [seq FC_func_native (Tf (repeat (T_num T_i32) (N.to_nat (type fn))) [::])
         (f_inst {| f_locs := [::]; f_inst := mi |})
         {| modfunc_type := type fn; modfunc_locals := locals fn; modfunc_body := body fn |}
     | fn <- fns].
Proof.
  induction fns; intros=>//. cbn. f_equal.
  - unfold gen_func_instance. rewrite H1.
    assert (type a <= 20)%N by (apply H0; cbn; auto).
    unfold lookup_N. cbn. rewrite (nth_error_nth' _ (Tf [] [])). 2:{ rewrite length_list_function_types. lia. }
    rewrite nth_list_function_types; try lia=>//. reflexivity.
  - cbn in H. apply IHfns; eauto; try lia.
    intros. by apply H0; cbn; auto.
Qed.

Lemma table_element_mapping_nth_error : forall num_funs idx x,
  x < num_funs ->
  nth_error (table_element_mapping num_funs idx) x =
    Some {| modelem_type := T_funcref
          ; modelem_init := [:: [:: BI_ref_func (N.of_nat (idx + x))]]
          ; modelem_mode := ME_active 0%N [:: BI_const_num (nat_to_value (idx + x))]
          |}.
Proof.
  induction num_funs; intros; cbn.
  - intros. lia.
  - destruct x. cbn. eauto. repeat f_equal; lia. cbn.
    replace (idx + S x) with (S idx + x) by lia.
    apply IHnum_funs. lia.
Qed.

Lemma funcidcs_length : forall n m,
  length (funcidcs n m) = n.
Proof.
  induction n; intros; cbn; eauto.
Qed.

Lemma init_elems_effect : forall num_funs state sr fr mi r_inits idx,
  Forall2
  (fun (e1 : module_element) (rs : seq value_ref) =>
   Forall2
     (fun (bes : seq basic_instruction) (r : value_ref) =>
      reduce_trans
        (state, sr, fr, to_e_list bes)
        (state, sr, fr, [:: vref_to_e r])) (modelem_init e1) rs)
  (table_element_mapping num_funs idx) r_inits ->
  fr.(f_inst).(inst_funcs) = mi.(inst_funcs) ->
  inst_funcs mi = funcidcs num_funs 0%N ->
  inst_elems mi = iota_N 0 num_funs ->
  s_elems sr = [ seq {| eleminst_type := modelem_type elem; eleminst_elem := refs |} |
                          '(elem, refs) <- combine (table_element_mapping num_funs 0) r_inits ] ->

  (forall x, N.to_nat x < num_funs -> selem sr mi x = Some (Build_eleminst T_funcref [:: VAL_ref_func (N.of_nat idx + x)%N])).
Proof.
  intros ??????????????. unfold selem. rewrite H2. unfold lookup_N.
  rewrite iota_N_lookup; last by apply /ssrnat.leP.
  rewrite N2Nat.id. rewrite H3. rewrite nth_error_map.
  erewrite nth_error_nth'. 2:{ rewrite combine_length table_element_mapping_length.
                               apply Forall2_length in H. rewrite table_element_mapping_length in H. lia. }
  erewrite combine_nth. 2:{ apply Forall2_length in H. now rewrite -> table_element_mapping_length in *. }
  erewrite nth_error_nth; last by eapply table_element_mapping_nth_error.
  have H' := table_element_mapping_nth_error _ idx _ H4.
  assert (exists l, nth_error r_inits (N.to_nat x) = Some l) as [l Hl]. {
    apply notNone_Some. apply nth_error_Some.
    apply Forall2_length in H. rewrite table_element_mapping_length in H. lia.
  }
  have H'' := Forall2_nth_error H H' Hl. cbn in H''. inv H''. inv H9. cbn in H7.
  cbn. erewrite nth_error_nth; last eassumption.
  apply Operators_Properties.clos_rt_rt1n_iff in H7. inv H7. destruct y=>//.
  destruct y0 as [[[??]?]?]. apply reduce_ref_func in H5.
  destruct H5 as [addr [Hf ->]]. rewrite H0 H1 in Hf. unfold lookup_N in Hf.
  erewrite nth_error_funcidcs in Hf; eauto.
  2:{ apply Some_notNone in Hf. apply nth_error_Some in Hf. rewrite funcidcs_length in Hf. lia. }
  rewrite N2Nat.id in Hf. cbn in Hf. inv Hf.
  apply Operators_Properties.clos_rt_rt1n_iff in H6. eapply reduce_trans_value with (v2:=VAL_ref y) in H6.
  inv H6. repeat f_equal. lia.
Unshelve. repeat constructor. apply [].
Qed.

Definition INV_instantiation_elems s f num_funs := forall x,
  N.to_nat x < num_funs ->
  selem s f.(f_inst) x = Some (Build_eleminst T_funcref [:: VAL_ref_func x]).

(* same as INV, except INV_table_id since it doesn't hold yet *)
Definition INV_instantiation (s : store_record) (f : frame) (num_funs : nat) :=
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
 /\ INV_inst_globals_nodup f
 /\ INV_types s f
 /\ INV_global_mem_ptr_multiple_of_two s f
 /\ INV_exists_func_grow_mem s f
 /\ INV_inst_funcs_id s f
(* additional *)
 /\ INV_instantiation_elems s f num_funs.

Theorem module_instantiate_INV_and_more_hold :
forall e eAny topExp fds num_funs module fenv main_lenv sr f es_post,
  NoDup (collect_function_vars (Efun fds eAny)) ->
  expression_restricted cenv e ->
  topExp = match e with | Efun _ _ => e | _ => Efun Fnil e end ->
  (match topExp with Efun fds' _ => fds' | _ => Fnil end) = fds ->
  (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
      find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e) ->
  num_funs = match topExp with | Efun fds _ => numOf_fundefs fds | _ => 42 (* unreachable*) end ->
  (Z.of_nat num_funs < max_num_functions)%Z ->
  LambdaANF_to_Wasm nenv cenv penv e = Ret (module, fenv, main_lenv) ->
  (* instantiate with the two imported functions *)
  instantiate initial_store module [EV_func 0%N; EV_func 1%N] (sr, f, es_post) ->

  (* invariants hold initially *)
  INV_instantiation sr f (num_funs + num_custom_funs) /\
  inst_funcs (f_inst f) = [:: 0%N, 1%N, 2%N, 3%N & (funcidcs num_funs (N.of_nat num_custom_funs))] /\
  (* value relation holds for all funcs in fds *)
  (forall a errMsg, find_def a fds <> None ->
	exists fidx : funcidx,
	  translate_var nenv fenv a errMsg = Ret fidx /\
	  repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vfun (M.empty _) fds a) sr (f_inst f) (Val_funidx fidx)) /\

  exists grow_mem_fn main_fn e' fns,
    grow_mem_fn = {| modfunc_type := 1%N (* [i32] -> [] *)
                   ; modfunc_locals := [::]
                   ; modfunc_body := grow_memory_if_necessary
                   |} /\
    main_fn = {| modfunc_type := 0%N (* [] -> [] *)
               ; modfunc_locals := map (fun _ : var => T_num T_i32)
                                       (collect_local_variables match e with | Efun _ exp => exp | _ => e end)
               ; modfunc_body := e'
               |} /\
    s_funcs sr =
    [:: FC_func_host (Tf [T_num T_i32] [::]) hfn,
        FC_func_host (Tf [T_num T_i32] [::]) hfn,
        FC_func_native (Tf [::T_num T_i32] [::]) (f_inst f) grow_mem_fn,
        FC_func_native (Tf [::] [::]) (f_inst f) main_fn
    &   map (fun f0 : wasm_function =>
             FC_func_native (Tf (repeat (T_num T_i32) (N.to_nat (type f0))) [::]) (f_inst f)
             {| modfunc_type := type f0; modfunc_locals := locals f0; modfunc_body := body f0 |})
            fns
     ] /\
  es_post = concat (mapi_aux (0, [::]) (fun n : nat => get_init_expr_elem n)
                             (table_element_mapping (Datatypes.length fns + num_custom_funs) 0)) /\
  (* links e and e' in main_fn above *)
  translate_body nenv cenv
          (create_local_variable_mapping
             (collect_local_variables
                match e with
                | Efun _ exp => exp
                | _ => e
                end)) fenv penv match e with
                           | Efun _ exp => exp
                           | _ => e
                           end = Ret e' /\
  (* translation of functions *)
  match topExp with
  | Efun fds _ => translate_functions nenv cenv fenv penv fds
  | _ => Ret []
  end = Ret fns.
Proof.
  intros e eAny topExp fds num_funs module fenv lenv s f es_post Hnodup HeRestr HtopExp Hfds HcenvCorrect Hnumfuns
    HfnsLength Hcompile Hinst. subst num_funs topExp.
  unfold instantiate in Hinst.
  unfold LambdaANF_to_Wasm in Hcompile.
  remember (list_function_types (Z.to_nat max_function_args)) as types.
  simpl in Hcompile.
  destruct (check_restrictions cenv e) eqn:HRestr. inv Hcompile.
  destruct (match _ with | Efun fds _ => _ fds | _ => Err _ end) eqn:HtransFns. inv Hcompile.
  destruct (match e with
            | Efun _ _ => e
            | _ => Efun Fnil e
            end) eqn:HtopExp'; try (by inv Hcompile).
  destruct (translate_body nenv cenv _ _ _) eqn:Hexpr. inv Hcompile. rename l0 into e'.
  inv Hcompile.
  unfold INV_instantiation. unfold is_true in *.
  destruct Hinst as [t_imps_mod [t_imps [t_exps [state [mi [ g_inits [r_inits
          [Hmodule [Himports [HimportsSt [HallocModule [HinstGlobals [HinstElem [Hframe HinitExprs]]]]]]]]]]]]]].
  rename l into fns. cbn in HinitExprs.

  (* globals red. to const *)
  unfold instantiate_globals in HinstGlobals. cbn in HinstGlobals.
  inv HinstGlobals. inv H3. inv H5. inv H6. inv H7. cbn in H1.
  apply reduce_trans_value with (v1:=VAL_num (nat_to_value 0)) in H1, H2, H3, H4. subst y y0 y1 y2.

  unfold alloc_module, alloc_funcs, alloc_globs, add_mem, alloc_Xs in HallocModule.
  cbn in HallocModule. repeat rewrite map_app in HallocModule. cbn in HallocModule.
  destruct (fold_left _ (map _ fns) _) eqn:HaddF.
  destruct (alloc_elems _ _ _) eqn:HallocElems.
  apply alloc_elem_iota_N in HallocElems. 2:{ by apply Forall2_length in HinstElem. }
  cbn in HallocElems.
  destruct HallocElems as [-> [E0 [E1 [E2 [E3 [E4 E5]]]]]].

  unfold add_glob in HallocModule. cbn in HallocModule.
  repeat (apply andb_prop in HallocModule;
           destruct HallocModule as [HallocModule ?F]).
  apply store_record_eqb_true in HallocModule. subst s1.
  apply eqseq_true in F0,F1,F2,F3,F4,F5,F6,F. cbn in HaddF.
  rewrite table_element_mapping_length in F1.

  (* main fn, grow_mem_fn *)
  destruct ((add_func (add_func initial_store _)) _) eqn:HaddF'.
  unfold add_func, gen_func_instance in HaddF'. rewrite F6 in HaddF'.
  replace (Pos.to_nat 20) with 20 in HaddF' by reflexivity. cbn in HaddF'.
  replace (Pos.to_nat 1) with 1 in HaddF' by reflexivity. cbn in HaddF'.
  injection HaddF' as <- <- <- <- <- <-.

  apply add_funcs_effect in HaddF. cbn in HaddF. destruct HaddF as [Hs01 [Hs02 [Hs03 [Hs04 [Hs05 [Hs06 ->]]]]]].

  rewrite <- Hs01 in *. rewrite <- Hs02 in *. rewrite <- Hs03 in *.
  rewrite <- Hs04 in *. rewrite <- Hs05 in *. rewrite -> Hs06 in *. cbn in F.
  (* clear Hs01 Hs02 Hs03 Hs04. *)
  cbn in E0, E1, E2, E3, E4, E5.
  cbn in F0, F1, F2, F3.
  rewrite map_length in F5, F. rewrite rev_app_distr in F, F5.
  rewrite rev_involutive in F5, F.
  cbn in F0, F1, F2, F3, F4, F5, F.

  split.
  (* INV *)
  unfold INV_result_var_writable, INV_result_var_out_of_mem_writable, INV_global_mem_ptr_writable,
  INV_constr_alloc_ptr_writable. unfold global_var_w, supdate_glob, supdate_glob_s.
  cbn. rewrite F2.
  (* cbn in Hglobals, Hfuncs, Hmems. rewrite F0. cbn. *)
  split. (* res_var_w *)   eexists. rewrite -E3. reflexivity.
  split. (* res_var_M_w *) eexists. rewrite -E3. reflexivity.
  split. (* res_var_M_0 *) unfold INV_result_var_out_of_mem_is_zero. unfold sglob_val, sglob.
  cbn. rewrite F2. rewrite -E3. reflexivity.
  split. (* gmp_w *) eexists. rewrite -E3. reflexivity.
  split. (* cap_w *) eexists. rewrite -E3. reflexivity.
  (* globals mut i32 *)
  split. unfold INV_globals_all_mut_i32, globals_all_mut_i32. intros. unfold lookup_N in H.
  { rewrite -E3 in H. cbn in H.
    destruct (N.to_nat g). inv H. eexists. reflexivity.
    destruct n. inv H. eexists. reflexivity.
    destruct n. inv H. eexists. reflexivity.
    destruct n. inv H. eexists. reflexivity.
    destruct n; inv H. }
  split. (* linmem *)
  { unfold INV_linear_memory. unfold smem. cbn. rewrite F3.
    split; auto. unfold smem. eexists; auto.
    split. rewrite -E2. reflexivity.
    unfold mem_size, operations.mem_length, memory_list.mem_length. cbn. eexists. split. reflexivity.
    split; auto. unfold max_mem_pages. rewrite repeat_length. cbn.
    replace (N.of_nat (Pos.to_nat 65536)) with 65536%N by lia. cbn. lia. }
   split. (* gmp in linmem *)
   { unfold INV_global_mem_ptr_in_linear_memory.
   unfold sglob_val, sglob. cbn. intros ?? Hm Hm0 Hbound. unfold smem in Hm.
   rewrite F2 in Hm0, Hm. rewrite -E2 in Hm. rewrite -E3 in Hm0.
   rewrite F3 in Hm. inv Hm. inv Hm0.
   unfold operations.mem_length, memory_list.mem_length. rewrite repeat_length. cbn.
   rewrite Wasm_int.Int32.Z_mod_modulus_id in H0; lia. }
   split. (* all locals i32 *)
   { unfold INV_locals_all_i32. intros. rewrite nth_error_nil in H. inv H. }
   split. (* num functions upper bound *)
   { unfold INV_num_functions_bounds. cbn.
     rewrite -E0. cbn.
     do 2! rewrite map_length.
     destruct e; inv HtopExp'; try (inv HtransFns; simpl_modulus; cbn; lia).
     erewrite <- translate_functions_length; eauto.
     unfold max_num_functions in HfnsLength. simpl_modulus. cbn. lia. }
   split. (* inst_globals (f_inst f) no dups *)
   unfold INV_inst_globals_nodup. rewrite F2.
   repeat constructor; cbn; lia.
  split. (* types *)
  { unfold INV_types. intros. unfold stypes. cbn. unfold max_function_args in H.
    rewrite F6. unfold lookup_N. erewrite nth_error_nth'.
    rewrite nth_list_function_types =>//. lia.
    rewrite length_list_function_types. lia. }
  split. (* gmp multiple of two *)
  { unfold INV_global_mem_ptr_multiple_of_two.
    intros ?? Hm Hgmp Hbound. exists 0%N.
    unfold global_mem_ptr, sglob_val, sglob in Hgmp.
    rewrite -E3 in Hgmp. cbn in Hgmp. rewrite F2 in Hgmp. inv Hgmp.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H0; lia. }
  split. (* func grow_mem exists *)
  { unfold INV_exists_func_grow_mem.
    by rewrite -E0. }
  split. (* inst_funcs_id *)
  { unfold INV_inst_funcs_id. intros ? Hbound. cbn. rewrite F5. unfold lookup_N.
    remember (N.to_nat i) as i'.
    destruct (Nat.leb_spec i' 3).
    { (* n <= 3 *)
      do 4 (destruct i'; cbn; f_equal; try lia). }
    { (* 3 < n *)
      separate_instr. do 3 rewrite catA.
      erewrite nth_error_app2=>//. cbn.
      erewrite nth_error_funcidcs; eauto.
      f_equal. lia. unfold num_custom_funs in *.
      rewrite -E0 in Hbound. cbn in Hbound.
      do 2! rewrite map_length in Hbound. lia. }
  }
  (* instantiation_elems *)
  { unfold INV_instantiation_elems. intros.
    erewrite init_elems_effect; eauto. f_equal; lia. rewrite F5. by rewrite Nat.add_comm.
    now apply translate_functions_length in HtransFns.
  }
  split. (* inst_funcs (f_inst f) *)
  { rewrite F5. repeat f_equal.
    destruct e; inv HtopExp'; inv HtransFns; auto.
    symmetry. eapply translate_functions_length. eassumption. }
  split. (* val relation holds for functions *)
  { intros. apply notNone_Some in H. destruct H as [[[v' ys'] e''] Hfd].
    assert (Hnodup' : NoDup (collect_function_vars (Efun fds e))). {
      replace (collect_function_vars (Efun fds e'')) with
              (collect_function_vars (Efun fds e0)) by reflexivity. assumption. }

    have H' := translate_functions_find_def _ _ _ _ _ e'' _ Hnodup' HtransFns Hfd HcenvCorrect.
    destruct H' as [fidx [e''' [? [func [? [? [? [? [? [? [? ?]]]]]]]]]]].
    subst. eauto.
    exists (fidx func).
    split. { inv H. unfold translate_var. unfold translate_var in H0.
      destruct ((create_fname_mapping e) ! a) eqn:Hmap; rewrite Hmap in H0=>//.
      rewrite Hmap. by injection H0 as ->. }
    econstructor; eauto. rewrite -E0. cbn.
    unfold lookup_N.
    assert ((N.to_nat (fidx func)) >= num_custom_funs). { inv H. unfold translate_var in H0.
      destruct ((create_fname_mapping e) ! a) eqn:Ha; rewrite Ha in H0=>//. injection H0 as ->.
      apply local_variable_mapping_gt_idx in Ha. lia. }

    assert (nth_error fns ((N.to_nat (fidx func)) - num_custom_funs) = Some func). {
      apply In_nth_error in H1. destruct H1 as [j Hj].
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

    destruct (N.to_nat (fidx func)). lia. do 3! (destruct n; try lia). cbn.
    replace (_ - _) with n in H2 by lia.

    do 2! rewrite nth_error_map. rewrite H2.
    cbn. f_equal. unfold gen_func_instance.
    rewrite F6. cbn. f_equal. rewrite H4.
    assert (HtypeBound : (type func <= 20)%N). {
      eapply translate_functions_type_bound; eauto.
      destruct e; inv HtopExp'=>//. by inv HeRestr.
    }
    unfold lookup_N. erewrite nth_error_nth'. 2:{ rewrite length_list_function_types. lia. }
    rewrite nth_list_function_types; try lia.
    rewrite H3. by rewrite Nat2N.id.
  }
  (* from exists statement on *)
  do 2 eexists. exists e', fns. do 2 split=>//. rewrite -E0.
  split. do 4 f_equal.
  by destruct e; inv HtopExp'.
  rewrite <- map_map_seq.
  { clear Hmodule E1 F.
   rewrite gen_fun_instance_simplify_eq; eauto.
   - apply translate_functions_length in HtransFns. lia.
   - intros. eapply translate_functions_type_bound; eauto.
     destruct e; inv HtopExp'=>//. inv HeRestr. assumption. }
	split; first by rewrite cats0.
	split=>//. rewrite -Hexpr.
	destruct e; inv HtopExp'=>//.
Unshelve. all: apply (Tf [] []).
Qed.

Theorem post_instantiation_reduce {fenv} : forall hs sr fr fr' num_funs,
  INV_instantiation sr fr num_funs ->
  f_inst fr = f_inst fr' ->
  exists sr',
    reduce_trans (hs, sr, fr', [seq AI_basic i | i <- concat
                                                (mapi_aux (0, [::])
                                                  (fun n : nat => get_init_expr_elem n)
                                                  (table_element_mapping num_funs 0))])
                 (hs, sr', fr', [::]) /\
  INV fenv nenv sr' fr' /\
  s_funcs sr = s_funcs sr'.
Proof.
  intros ????? Hinv Hfinst.
  destruct Hinv as [? [? [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]]].
Admitted.

(* MAIN THEOREM, corresponds to 4.3.1 in Olivier's thesis *)
Theorem LambdaANF_Wasm_related :
  forall (v : cps.val) (e : exp) (n : nat) (vars : list cps.var)
         (hs : host_state) module fenv lenv
         (sr : store_record) (fr : frame) (pfs : M.t (list val -> option val)) (es_post : list basic_instruction),
  (* evaluation of LambdaANF expression *)
    bstep_e pfs cenv (M.empty _) e v n ->
        bstep_prim_funs_no_fun_return_values pfs ->
  bs_LambdaANF_prim_fun_env_extracted_prim_env_related cenv penv pfs ->
  (* compilation function *)
  LambdaANF_to_Wasm nenv cenv penv e = Ret (module, fenv, lenv) ->
  (* constructors wellformed *)
  correct_cenv_of_exp cenv e ->
  cenv_restricted cenv ->

  (* vars unique (guaranteed by previous stage) *)
  vars = ((collect_all_local_variables e) ++ (collect_function_vars e))%list ->
  NoDup vars ->
  (* expression must be closed *)
  (~ exists x, occurs_free e x ) ->
  (* instantiation with the two imported functions *)

  instantiate initial_store module [EV_func 0%N; EV_func 1%N] (sr, fr, es_post) ->
  (* perform post_instantiation: initialises table for indirect calls *)
  exists (sr' : store_record),
       reduce_trans (hs, sr,  (Build_frame [] (f_inst fr)), map AI_basic es_post)
                    (hs, sr', (Build_frame [] (f_inst fr)), [])    /\

  (* reduces to some sr' that has the result variable set to the corresponding value *)
  exists (sr'' : store_record),
       reduce_trans (hs, sr',  (Build_frame [] (f_inst fr)), [ AI_basic (BI_call main_function_idx) ])
                    (hs, sr'', (Build_frame [] (f_inst fr)), [])    /\

       result_val_LambdaANF_Wasm cenv fenv nenv penv v sr'' (f_inst fr).
Proof.
  intros ???????????? Hstep HprimFunsRet HprimFunsRelated LANF2Wasm Hcenv HcenvRestr HvarsEq HvarsNodup Hfreevars Hinst.
  subst vars.

  assert (HeRestr: expression_restricted cenv e).
  { unfold LambdaANF_to_Wasm in LANF2Wasm. destruct (check_restrictions cenv e) eqn:HeRestr.
    inv LANF2Wasm. destruct u. eapply check_restrictions_expression_restricted; eauto.
    apply rt_refl. }

  assert (Hmaxfuns : (Z.of_nat match match e with
                                     | Efun _ _ => e
                                     | _ => Efun Fnil e
                                     end with
                               | Efun fds _ => numOf_fundefs fds
                               | _ => 42 (* unreachable *)
                               end < max_num_functions)%Z). {
    unfold max_num_functions. destruct e; cbn; try lia. inv HeRestr. assumption.
  }
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
               Logic.eq_refl Logic.eq_refl Hcenv' Logic.eq_refl Hmaxfuns LANF2Wasm Hinst.
  clear Hnodup' Hcenv'.
  destruct HI as [Hinv [HinstFuncs [HfVal [grow_mem_fn [main_fn [e' [fns' [-> [-> [HsrFuncs [-> [Hexpr' Hfns']]]]]]]]]]]].

  have HpostInst := @post_instantiation_reduce fenv hs sr fr {| f_locs := [::]; f_inst := f_inst fr |} _ Hinv Logic.eq_refl.
  destruct HpostInst as [sr' [HredPost [Hinv' Hsr'F]]].

  remember (Build_frame (repeat (VAL_num (nat_to_value 0)) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.

  unfold LambdaANF_to_Wasm in LANF2Wasm.
  remember (list_function_types (Z.to_nat max_function_args)) as ftypes.
  simpl in LANF2Wasm.
  destruct (check_restrictions cenv e). inv LANF2Wasm.
  destruct (match _ with
       | Efun fds _ => _ fds
       | _ => Err _
       end) eqn:Hfuns. inv LANF2Wasm. rename l into fns.
  destruct (match e with
                    | Efun _ _ => e
                    | _ => Efun Fnil e
                    end) eqn:HtopExp; try (by inv LANF2Wasm).
  destruct (translate_body nenv cenv _ _ _) eqn:Hexpr. inv LANF2Wasm. rename l into wasm_main_instr.
  inv LANF2Wasm.

  (* from lemma module_instantiate_INV_and_more_hold *)
  assert (e' = wasm_main_instr). { destruct e; inv HtopExp; congruence. } subst e'. clear Hexpr'.
  assert (fns = fns'). { destruct e; inv HtopExp; congruence. } subst fns'. clear Hfns'.

  (* step through post instantiation *)
  exists sr'. split. apply translate_functions_length in Hfuns. rewrite -Hfuns. apply HredPost.

  remember (Build_frame (repeat (VAL_num (nat_to_value 0)) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.
  remember (create_local_variable_mapping (collect_local_variables e)) as lenv.
  remember (create_fname_mapping e) as fenv.

   assert (HlocInBound: (forall (var : positive) (varIdx : funcidx),
          repr_var (lenv:=lenv) nenv var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs f_before_IH))).
   { intros ? ? Hvar. subst f_before_IH. cbn. rewrite repeat_length. inv Hvar.
     eapply var_mapping_list_lt_length. eassumption. }

  assert (Hinv_before_IH: INV fenv nenv sr' f_before_IH). {
    subst f_before_IH.
    eapply init_locals_preserves_INV with (args:=[]). apply Hinv'. reflexivity.
  }

  have Heqdec := inductive_eq_dec e. destruct Heqdec.
  { (* top exp is Efun _ _ *)
    destruct e1 as [fds' [e'' He]]. subst e. rename e'' into e.
    inversion HtopExp. subst e0 f. rename fds' into fds.
    inversion Hstep. subst fl e0 v0 c rho. clear Hstep. rename H4 into Hstep.

    eapply translate_body_correct in Hexpr; try eassumption.
    2:{ eapply Forall_constructors_subterm. eassumption. constructor.
        apply dsubterm_fds2. }

    (* prepare IH *)

    assert (HlenvInjective : map_injective lenv). {
      subst lenv.
      intros x y x' y' Hneq Hx Hy Heq. subst y'.
      apply NoDup_app_remove_r in HvarsNodup. cbn in HvarsNodup.
      apply NoDup_app_remove_r in HvarsNodup.
      cbn in Hx, Hy.
      have H' := create_local_variable_mapping_injective _ 0%N HvarsNodup _ _ _ _ Hneq Hx Hy. auto. }

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
         (exists i : funcidx,
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
      intros ? ? H H1. eapply def_funs_find_def in H1; eauto. now erewrite H in H1. }

    assert (HeRestr' : expression_restricted cenv e). { now inv HeRestr. }
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
        expression_restricted cenv e0 /\
        (forall x : var, occurs_free e0 x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++
           collect_local_variables e0 ++
           collect_function_vars (Efun fds e0)) /\
        (exists fidx : funcidx,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vfun (M.empty _) fds a) sr' (f_inst f_before_IH) (Val_funidx fidx))). {
      intros ????? Hcontra.
      split. { inv HeRestr. eapply H3. eassumption. }
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
        exists fidx. split. assumption. subst f_before_IH.
        eapply val_relation_func_depends_on_funcs. 2: apply Hval.
        congruence. }
    }

    assert (HrelE : @rel_env_LambdaANF_Wasm cenv fenv nenv penv
                   _ (create_local_variable_mapping (collect_local_variables e)) e (def_funs fds fds (M.empty _) (M.empty _))
          sr' f_before_IH fds). {
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
    have HMAIN := repr_bs_LambdaANF_Wasm_related cenv fenv nenv penv _
                    _ _ _ _ _ _ _ frameInit _ lh HcenvRestr HprimFunsRet HprimFunsRelated HlenvInjective
                    HenvsDisjoint Logic.eq_refl Hnodup' HfenvWf HfenvRho
                    HeRestr' Hunbound Hstep hs sr' _ _ Hfds HlocInBound Hinv_before_IH Hexpr HrelE.
    destruct HMAIN as [s' [f' [k' [lh' [Hred [Hval [Hfinst _]]]]]]]. cbn. subst frameInit.
    exists s'. split.
    dostep'. apply r_call. cbn.
    rewrite HinstFuncs. reflexivity.
    dostep'. eapply r_invoke_native with (ves:=[]) (vs:=[]); eauto.
    rewrite- Hsr'F HsrFuncs. subst f_before_IH. cbn. rewrite Hfinst. reflexivity. reflexivity.
    erewrite <-map_repeat_eq. by apply default_vals_i32_Some.
    subst f_before_IH. cbn. subst lh. cbn in Hred. rewrite <- Hfinst. rewrite cats0 in Hred.
    eapply rt_trans. cbn. unfold to_e_list. apply Hred.
    dostep'. constructor. apply rs_return with (lh:=lh') (vs:=[::]) =>//. apply rt_refl.
    subst f_before_IH. apply Hval.
  }

  { (* top exp is not Efun _ _ *)
    rename f into fds. assert (fds = Fnil). {
      destruct e; inv HtopExp; auto. exfalso. eauto.
    } subst fds. injection Hfuns => ?. subst fns. clear Hfuns.
    cbn in HsrFuncs, HinstFuncs, Hmaxfuns.
    assert (e0 = e). { destruct e; inv HtopExp; auto. exfalso. eauto. }
    subst e0. clear HtopExp.

    eapply translate_body_correct in Hexpr; eauto.

    assert (HrelE : @rel_env_LambdaANF_Wasm cenv fenv nenv penv
                    _ (create_local_variable_mapping (collect_local_variables e)) e (M.empty _) sr' f_before_IH Fnil). {
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
      have H' := create_local_variable_mapping_injective _ 0%N HvarsNodup _ _ _ _ Hneq Hx Hy. auto.
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
        expression_restricted cenv e0 /\
        (forall x : var, occurs_free e0 x -> In x ys \/ find_def x Fnil <> None) /\
        NoDup
          (ys ++
           collect_local_variables e0 ++
           collect_function_vars (Efun Fnil e0)) /\
        (exists fidx : funcidx,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vfun (M.empty _) Fnil a)
             sr' (f_inst f_before_IH) (Val_funidx fidx))). {
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
         (exists i : funcidx, fenv ! f = Some i)))). {
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
    have HMAIN := repr_bs_LambdaANF_Wasm_related cenv fenv nenv penv _
                    _ _ _ _ _ _ _ frameInit _ lh HcenvRestr HprimFunsRet HprimFunsRelated HlenvInjective
                    HenvsDisjoint Logic.eq_refl Hnodup' HfenvWf HfenvRho
                    HeRestr Hunbound Hstep hs sr' _ _ Hfds HlocInBound Hinv_before_IH Hexpr HrelE.

    subst lh frameInit.

    destruct HMAIN as [s' [f' [k' [lh' [Hred [Hval [Hfinst _]]]]]]]. cbn.
    exists s'. split.
    dostep'. apply r_call. cbn.
    rewrite HinstFuncs. reflexivity.
    dostep'. eapply r_invoke_native with (ves:=[]) (vs:=[]); eauto.
    rewrite -Hsr'F HsrFuncs. subst f_before_IH. cbn. rewrite Hfinst. reflexivity. reflexivity.
    subst f_before_IH. cbn.
    assert (HexpEq: match e with | Efun _ exp => exp
                                 | _ => e end= e).
    { destruct e; auto. exfalso. eauto. } rewrite HexpEq. clear HexpEq.
      rewrite <- map_repeat_eq. by apply default_vals_i32_Some.
    cbn in Hred. rewrite -Hfinst. subst f_before_IH. rewrite cats0 in Hred.
    eapply rt_trans. apply Hred.
    dostep'. constructor. apply rs_return with (lh:=lh') (vs:=[::]) =>//. apply rt_refl.
    subst. assumption.
  } Unshelve. all: auto.
Qed.

End INSTANTIATION.


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
  (forall x x', @repr_var nenv lenv x x' -> lookup_N (tc_locals c) x' = Some (T_num T_i32)) /\
  (* globals i32, mut *)
  (forall var, In var [global_mem_ptr; constr_alloc_ptr; result_var; result_out_of_mem] ->
    lookup_N (tc_globals c) var = Some {| tg_mut:= MUT_var; tg_t:= T_num T_i32|}) /\
  (* no return value *)
  (tc_return c = Some []) /\
  (* mem exists *)
  (tc_mems c <> []) /\ (* TODO consider better automation for mem, table *)
  (* table *)
  (exists t, lookup_N (tc_tables c) 0%N = Some t /\ tt_elem_type t = T_funcref) /\
  (* grow mem func *)
  (N.to_nat grow_mem_function_idx < length (tc_funcs c)) /\
  (lookup_N (tc_funcs c) grow_mem_function_idx = Some (Tf [:: T_num T_i32] [::])) /\
  (* function types *)
  (Z.of_nat (length (tc_types c)) > max_function_args)%Z /\
  (forall i, (Z.of_nat i <= max_function_args)%Z -> lookup_N (tc_types c) (N.of_nat i) = Some (Tf (repeat (T_num T_i32) i) [::])).

Lemma update_label_preserves_context_restr lenv c :
  context_restr lenv c ->
  context_restr lenv (upd_label c ([:: [::]] ++ tc_labels c)%list).
Proof. auto. Qed.

(* Prove that a list of instructions is well-typed, context_restr is required to hold *)
Ltac solve_bet Hcontext :=
  let Hglob := fresh "Hglob" in
  simpl; try rewrite List.app_nil_r;
  match goal with
  | |- be_typing _ [::] (Tf [::] [::]) => by apply bet_empty
  | |- be_typing _ [:: BI_return] _ => apply bet_return with (t1s:=[::]); by apply Hcontext
  | |- be_typing _ [:: BI_unreachable] _ => by apply bet_unreachable
  (* globals *)
  | |- be_typing ?context [:: BI_global_get ?var] _ =>
         assert (lookup_N (tc_globals context) var = Some {| tg_mut:= MUT_var; tg_t := T_num T_i32 |}) as Hglob by
          (apply Hcontext; now cbn); eapply bet_global_get with (t:=T_num T_i32); [eassumption | now cbn]
  | |- be_typing ?context [:: BI_global_set ?var] _ =>
         assert (lookup_N (tc_globals context) var = Some {| tg_mut:= MUT_var; tg_t := T_num T_i32 |}) as Hglob by
          (apply Hcontext; now cbn); eapply bet_global_set with (t:=T_num T_i32); [eassumption | now cbn | now cbn]
  (* locals with mapping *)
  | H: repr_var _ _ ?x' |- be_typing _ [:: BI_local_get ?x'] (Tf [::] _) => apply bet_local_get; eapply Hcontext; eassumption
  | H: repr_var _ _ ?x' |- be_typing _ [:: BI_local_set ?x'] (Tf [::_] _) => apply bet_local_set; eapply Hcontext; eassumption
  (* locals without mapping (e.g. grow_mem) *)
  | |- be_typing ?context [:: BI_local_set 0%N] _ => apply bet_local_set; eassumption
  | |- be_typing ?context [:: BI_local_get 0%N] _ => apply bet_local_get; eassumption
  (* arithmetic *)
  | |- be_typing _ [:: BI_const_num _] (Tf [::] _) => apply bet_const_num
  | |- be_typing _ [:: BI_testop T_i32 _] (Tf [:: T_num T_i32] _) => apply bet_testop; by simpl
  | |- be_typing _ [:: BI_binop T_i32 _] (Tf [:: T_num T_i32; T_num T_i32] _) => apply bet_binop; apply Binop_i32_agree
(*   | |- be_typing _ [:: BI_binop T_i32 _] (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32] _) =>
         apply bet_weakening with (ts:=[::T_num T_i32]); apply bet_binop; apply Binop_i32_agree *)
  | |- be_typing _ [:: BI_binop T_i64 _] (Tf [:: T_num T_i64; T_num T_i64] _) => apply bet_binop; apply Binop_i64_agree
  | |- be_typing _ [:: BI_relop T_i32 _] (Tf [:: T_num T_i32; T_num T_i32] _) => apply bet_relop; apply Relop_i32_agree
  (* memory *)
  | H: lookup_N (tc_mems _) 0 = Some _ |- be_typing _ [:: BI_memory_size] (Tf [::] _) => eapply bet_memory_size; apply H
  | H: lookup_N (tc_mems _) 0 = Some _ |- be_typing _ [:: BI_memory_grow] (Tf [:: T_num T_i32] _) => eapply bet_memory_grow; apply H
  | |- be_typing _ [:: BI_store _ None _ _] (Tf [:: T_num _; T_num _] _) => by eapply bet_store; first eassumption; cbn=>//
  | |- be_typing _ [:: BI_load _ None _ _] (Tf [:: T_num _] _) => by eapply bet_load; first eassumption; cbn=>//
  (* function call *)
  | |- be_typing _ [:: BI_call grow_mem_function_idx] (Tf [:: T_num T_i32] _) => by apply bet_call; apply Hcontext
  (* simple if statement *)
  | |- be_typing _ [:: BI_if (BT_valtype None) _ _] _ =>
         apply bet_if_wasm with (tn:=[])=>//; separate_instr; repeat rewrite catA; repeat eapply bet_composition'; try solve_bet Hcontext
  (* if above failed, try to frame the leading const *)
  | |- be_typing _ _ (Tf [:: T_num T_i32] _) => apply bet_weakening with (ts:=[::T_num T_i32]); solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i32] _) => apply bet_weakening with (ts:=[::T_num T_i32]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i32; T_num T_i32] _) =>
         apply bet_weakening with (ts:=[::T_num T_i32; T_num T_i32]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i32; T_num T_i64]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i64; T_num T_i64] _) => apply bet_weakening with (ts:=[::T_num T_i32]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_num T_i32; T_num T_i64; T_num T_i32] _) => apply bet_weakening with (ts:=[::T_num T_i32; T_num T_i64]); by solve_bet Hcontext
  end.

Ltac prepare_solve_bet :=
  separate_instr; repeat rewrite catA; repeat eapply bet_composition'.

Definition context_restr_grow_mem (c: t_context) :=
  (* globals i32, mut *)
  (forall var, In var [global_mem_ptr; constr_alloc_ptr; result_var; result_out_of_mem] ->
    lookup_N (tc_globals c) var = Some {| tg_mut:= MUT_var; tg_t:= T_num T_i32|}) /\
  (* memory *)
  (tc_mems c <> []) /\
  (* param *)
  (lookup_N (tc_locals c) 0 = Some (T_num T_i32)).

Lemma update_label_preserves_context_restr_grow_mem c :
  context_restr_grow_mem c ->
  context_restr_grow_mem (upd_label c ([:: [::]] ++ tc_labels c)%list).
Proof. auto. Qed.

(* Translated expressions (all functions bodies other than the first few) have type (Tf [::] [::]) *)

Lemma grow_memory_if_necessary_typing : forall c,
  context_restr_grow_mem c ->
  be_typing c grow_memory_if_necessary (Tf [::] [::]).
Proof.
  intros c Hcontext. unfold grow_memory_if_necessary.
  assert (lookup_N (tc_locals c) 0 = Some (T_num T_i32)) as Hloc0 by apply Hcontext.
  assert (exists m, lookup_N (tc_mems c) 0 = Some m) as [m Hm]. {
    destruct (tc_mems c) eqn:Hc; cbn; eauto. exfalso. by apply Hcontext. }
  prepare_solve_bet; solve_bet Hcontext.
Qed.

Lemma constr_args_store_typing {lenv} : forall args n instr c,
  @context_restr lenv c ->
  Forall_statements_in_seq' (@set_nth_constr_arg fenv nenv lenv) args instr n ->
  be_typing c instr (Tf [::] [::]).
Proof.
  induction args; intros ??? Hcontext Hargs.
  - inv Hargs. apply bet_empty.
  - inv Hargs. inv H5.
    assert (exists m, lookup_N (tc_mems c) 0 = Some m) as [m Hm]. {
        destruct (tc_mems c) eqn:Hc; cbn; eauto. by apply Hcontext in Hc. }
    inv H.
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
  be_typing c args' (Tf [::] (repeat (T_num T_i32) (length l))).
Proof.
  induction l; intros ?? Hcontext Hargs =>/=.
  - inv Hargs. apply bet_empty.
  - inv Hargs.
    + (* var *)
      prepare_solve_bet. solve_bet Hcontext.
      apply bet_weakening with (ts:=[::T_num T_i32]). by apply IHl.
    + (* fun idx *)
      prepare_solve_bet. solve_bet Hcontext.
      apply bet_weakening with (ts:=[::T_num T_i32]). by apply IHl.
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
    by prepare_solve_bet; try solve_bet Hcontext'.
  - (* Eproj *)
    intros ???????? Hexpr' IH ??? Hcontext' Hrestr'.
    assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
    destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
    prepare_solve_bet; try solve_bet Hcontext'. inv Hrestr'. now apply IH.
  - (* Econstr *)
    intros ??????? Hexpr' IH ? Hargs ? Hcontext' Hrestr'.
    inv Hargs.
    + (* boxed constr. *)
      assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
        destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
      prepare_solve_bet; try solve_bet Hcontext'.
      * now eapply constr_args_store_typing.
      * inv Hrestr'. now eapply IH.
    + (* unboxed constr. *)
      prepare_solve_bet; try solve_bet Hcontext'. inv Hrestr'. now apply IH.
  - (* Ecase *)
    intros ???????? Hbranch IH ??? Hcontext' Hrestr'.
    have Hcontext'' := Hcontext'. apply update_label_preserves_context_restr in Hcontext''.
    have Htyping := IH _ _ _ _ Hcontext'' Hrestr' r r0 r1. destruct Htyping as [Hty1 Hty2]. clear IH Hcontext''.
    by prepare_solve_bet; solve_bet Hcontext'.
  - (* Eapp *)
    intros ????? Hargs Hv ? Hcontext' Hrestr'.
    assert (be_typing c0 [::instr] (Tf [::] [::T_num T_i32])) as Ht. { inv Hv; solve_bet Hcontext'. }
    prepare_solve_bet. inv Hrestr'. now eapply fun_args_typing.
    apply bet_weakening with (ts:=(repeat (T_num T_i32) (Datatypes.length args))) in Ht.
    now rewrite cats0 in Ht. inv Hrestr'.
    assert (exists t, lookup_N (tc_tables c0) 0%N = Some t /\ tt_elem_type t = T_funcref) as [t' [Ht1' Ht2']] by apply Hcontext'.
    eapply bet_return_call_indirect with (t3s:=[::]); try apply Hcontext'; eauto.
  - (* Eletapp *)
    intros ?????????? Hexpr' IH Hargs Hv ? Hcontext' Hrestr'.
    assert (be_typing c0 [::instr] (Tf [::] [::T_num T_i32])) as Ht. { inv Hv; solve_bet Hcontext'. }
    prepare_solve_bet; try solve_bet Hcontext'. now eapply fun_args_typing.
    apply bet_weakening with (ts:=(repeat (T_num T_i32) (Datatypes.length args))) in Ht.
    now rewrite cats0 in Ht. inv Hrestr'.
    assert (exists t, lookup_N (tc_tables c0) 0%N = Some t /\ tt_elem_type t = T_funcref) as [t' [Ht1' Ht2']] by apply Hcontext'.
    eapply bet_call_indirect; (try by apply Hcontext'); eauto.
    inv Hrestr'. now eapply IH.
  - (* Eprim_val *)
    intros ?????? Hvar Hexpr' IH Hprim ? Hcontext' Hrestr'.
    assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
      destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
    eapply bet_composition'. prepare_solve_bet; try solve_bet Hcontext'.
    inv Hrestr'. by apply IH.
  - (* Eprim *) {
    intros ???????? Hvar Hexpr' IH Hp' HprimOp ? Hcontext' Hrestr'.
    assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
      destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
    eapply bet_composition'. prepare_solve_bet; try solve_bet Hcontext'.
    inv HprimOp.
    unfold apply_binop_and_store_i64.
    prepare_solve_bet. all: try solve_bet Hcontext'.
    all: admit. (* TODO Martin prim_ops_typing *)
    (* inv Hrestr'. by apply IH. *) }
  - (* repr_branches nil *)
    intros ????? Hcontext' Hrestr' Hvar Hboxed Hunboxed.
    inv Hboxed. inv Hunboxed. by split; solve_bet Hcontext'.
  - (* repr_branches cons_boxed *)
    intros ????????? Hbranch IH1 ??? Hexpr' IH2 ???? Hcontext' Hrestr' Hvar Hboxed Hunboxed.
    inv Hboxed. split. 2:{ inv Hrestr'. inv H1. eapply IH1; eauto. by constructor. }
    assert (exists m, lookup_N (tc_mems c0) 0 = Some m) as [m Hm]. {
      destruct (tc_mems c0) eqn:Hc; cbn; eauto. by apply Hcontext' in Hc. }
    prepare_solve_bet; try solve_bet Hcontext'.
    + apply IH2=>//. inv Hrestr'. now inv H1.
    + eapply IH1 in H4; try apply Hunboxed; first (now destruct H4); eauto. inv Hrestr'. inv H1. by constructor.
  - (* repr_branches cons_unboxed *)
    intros ????????? Hbranch IH1 ??? Hexpr' IH2 ???? Hcontext' Hrestr' Hvar Hboxed Hunboxed.
    inv Hunboxed. split. { eapply IH1 in Hboxed; eauto. now destruct Hboxed. inv Hrestr'. inv H1. by constructor. }
    prepare_solve_bet; try solve_bet Hcontext'.
    + apply IH2=>//. inv Hrestr'. now inv H1.
    + eapply IH1 in H4; try apply Hunboxed; first (now destruct H4); eauto; try eassumption. inv Hrestr'. inv H1. by constructor.
Admitted.
End INSTRUCTION_TYPING.

Section INSTANTIATION.

Variable cenv   : ctor_env.
Variable funenv : fun_env.
Variable nenv   : name_env.
Variable penv   : prim_env.

Context `{ho : host}.
Variable hfn : host_function.

Fixpoint elem_vals (funs : nat) (startidx : nat) : seq (seq value_ref) :=
  match funs with
  | 0 => []
  | S funs' => [:: VAL_ref_func (N.of_nat startidx)] :: elem_vals funs' (S startidx)
  end.

Lemma elem_vals_length : forall num_funs idx,
  length (elem_vals num_funs idx) = num_funs.
Proof.
  induction num_funs; cbn; intros; eauto.
Qed.

Lemma elem_vals_nth_error : forall num_funs idx n,
  n < num_funs ->
  nth_error (elem_vals num_funs idx) n = Some [:: VAL_ref_func (N.of_nat (idx + n))].
Proof.
  induction num_funs; intros; try lia.
  destruct n.
  - cbn. do 3 f_equal. lia.
  - cbn. replace (idx + S n) with (S idx + n) by lia.
    rewrite IHnum_funs. reflexivity. lia.
Qed.

Lemma list_function_types_valid :
  Forall (fun ft : function_type => functype_valid ft)
         (list_function_types (Z.to_nat max_function_args)).
Proof.
  by apply Forall_forall.
Qed.

Lemma elems_instantiate : forall hs sr fr num_funs,
  fr.(f_inst).(inst_funcs) = [seq N.of_nat i | i <- iota 0 num_funs] ->
  Forall2
  (fun (e1 : module_element) (rs : seq value_ref) =>
   Forall2
     (fun (bes : seq basic_instruction) (r : value_ref) =>
      reduce_trans
        (hs, sr, fr, to_e_list bes)
        (hs, sr, fr, [:: vref_to_e r])) (modelem_init e1) rs)
  (table_element_mapping num_funs 0)
  (elem_vals num_funs 0).
Proof.
  intros ?????.
  apply Forall2_spec.
  - by rewrite table_element_mapping_length elem_vals_length.
  - intros ??? Hnth1 Hnth2.
    assert (n < num_funs). {
      apply nth_error_Some_length in Hnth1.
      by rewrite table_element_mapping_length in Hnth1.
    }
    rewrite table_element_mapping_nth_error in Hnth1=>//. injection Hnth1 as <-.
    cbn in H. cbn.
    rewrite elem_vals_nth_error in Hnth2; auto.
    injection Hnth2 as <-.
    apply Forall2_spec=>//.
    intros.
    destruct n0; last by destruct n0.
    injection H1 as <-. injection H2 as <-.
    apply rt_step. apply r_ref_func.
    rewrite H.
    unfold lookup_N. rewrite nth_error_map.
    rewrite iota_lookup. cbn. f_equal. lia.
    apply /ssrnat.leP. lia.
Qed.

Lemma funcidx_in_table_element_mapping : forall num_funs n idx,
  n < num_funs ->
  In (N.of_nat (idx + n))
  (concat
     (List.map module_elem_get_funcidx
        (table_element_mapping num_funs idx))).
Proof.
  induction num_funs; intros; first lia.
  destruct n. left. lia. cbn. right.
  replace (idx + S n) with (S idx + n) by lia.
  apply IHnum_funs. lia.
Qed.

Lemma module_typing_module_elem_typing : forall fns c t,
  (* types of print_char, print_int, grow_mem, main, fns *)
  tc_funcs c = [:: Tf [:: T_num T_i32] [::], Tf [:: T_num T_i32] [::], Tf [:: T_num T_i32] [::], Tf [::] [::] &
                [seq Tf (repeat (T_num T_i32) (N.to_nat (type f))) [::] | f <- fns]] ->
  lookup_N (tc_tables c) 0%N = Some t ->
  tt_elem_type t = T_funcref ->
  tc_refs c = nlist_nodup (module_elems_get_funcidx (table_element_mapping (Datatypes.length fns + num_custom_funs) 0)) ->
  Forall2 (module_elem_typing c) (table_element_mapping (Datatypes.length fns + num_custom_funs) 0)
                                 (repeat T_funcref (Datatypes.length fns + num_custom_funs)).
Proof.
  intros ??? Hft Htab1 Htab2 Hrefs. unfold num_custom_funs.
  apply Forall2_spec. by rewrite table_element_mapping_length repeat_length.
  intros ??? Hnth1 Hnth2.
  assert (n < length fns + 4). {
    apply nth_error_Some_length in Hnth1.
    by rewrite table_element_mapping_length in Hnth1.
  }
  rewrite table_element_mapping_nth_error in Hnth1=>//. injection Hnth1 as <-.
  rewrite nth_error_repeat in Hnth2=>//. injection Hnth2 as <-.
  do 2 split=>//.
  - apply Forall_forall.
    intros. cbn in H0. destruct H0=>//. subst x.
    split=>//.
    assert (length (tc_funcs c) = 4 + length fns). { rewrite Hft. cbn. now rewrite map_length. }
    assert (exists x, lookup_N (tc_funcs c) (N.of_nat n) = Some x) as [x Hx].
    { apply notNone_Some. apply nth_error_Some. lia. }
    eapply bet_ref_func; eauto. rewrite Hrefs. apply nodup_In.
    unfold module_elems_get_funcidx. apply nodup_In.
    by apply funcidx_in_table_element_mapping with (idx:=0).
  - cbn. exists t. cbn in Htab1. rewrite Htab1.
    destruct t. cbn in Htab2.
    repeat split=>//. apply bet_const_num.
Qed.

Theorem module_instantiate : forall e module fenv venv (hs : host_state),
  correct_cenv_of_exp cenv e ->
  NoDup (collect_function_vars e) ->
  LambdaANF_to_Wasm nenv cenv penv e = Ret (module, fenv, venv) ->
  exists sr fr es_post,
  instantiate (initial_store hfn) module [EV_func 0%N; EV_func 1%N] (sr, fr, es_post).
Proof.
  intros ????? Hcenv Hnodup' H. unfold LambdaANF_to_Wasm in H.
  destruct (check_restrictions cenv e) eqn:Hrestr. inv H. destruct u.
  eapply check_restrictions_expression_restricted in Hrestr; last by apply rt_refl.
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

  destruct (interp_alloc_module (initial_store hfn) module [:: EV_func 0%N; EV_func 1%N]
                                (repeat (VAL_num (nat_to_value 0)) 4)
                                (elem_vals (Datatypes.length fns + num_custom_funs) 0))
         as [s' inst] eqn:HallocM.

  subst module.
  rewrite Heqts in HallocM.

  (* final store *)
  exists s'.
  (* module instance *)
  exists (Build_frame [] inst).
  (* es_post: instructions post-instantiation *)
  exists (concat (mapi_aux (0, [::]) (fun n : nat => get_init_expr_elem n)
                                     (table_element_mapping (length fns + num_custom_funs) 0))).
  (* import types *)
  exists [:: ET_func (Tf [::T_num T_i32] [::]); ET_func (Tf [::T_num T_i32] [::])].
  exists [:: ET_func (Tf [::T_num T_i32] [::]); ET_func (Tf [::T_num T_i32] [::])].

  (* export types *)
  exists ([:: ET_func (Tf [::T_num T_i32] [::]); (* grow_mem *)
              ET_func (Tf [::] [::])] ++         (* main *)
         map (fun f => ET_func (Tf (repeat (T_num T_i32) (N.to_nat f.(type))) [::])) fns ++ (* all fns exported *)
         [:: ET_global {| tg_mut := MUT_var; tg_t := T_num T_i32 |}
           ; ET_global {| tg_mut := MUT_var; tg_t := T_num T_i32 |}
           ; ET_global {| tg_mut := MUT_var; tg_t := T_num T_i32 |}           (* global vars *)
           ; ET_mem {| lim_min := 1%N; lim_max := Some max_mem_pages|}]).     (* global mem *)
  exists hs.
  exists inst.
  (* initial values of globals: 0 *)
  exists (repeat (VAL_num (nat_to_value 0)) 4).
  (* element values (table entries) *)
  exists (elem_vals (length fns + num_custom_funs) 0).

  repeat split.
  (* module typing *) {
  - unfold module_typing. simpl.
    (* function types *)
    exists ([:: (Tf [::T_num T_i32] [::]); (Tf [::] [::])] ++ (* grow_mem, main, fns *)
             map (fun f => Tf (repeat (T_num T_i32) (N.to_nat (type f)))[::]) fns).
    (* table types *)
    exists ([{| tt_limits := {| lim_min := N.of_nat (Datatypes.length fns + num_custom_funs);
                                lim_max := None |}
              ; tt_elem_type := T_funcref |}]).
    (* mem types *)
    exists [{| lim_min := 1%N; lim_max := Some max_mem_pages |}].
    (* global types *)
    exists (repeat ({| tg_mut := MUT_var; tg_t := T_num T_i32 |}) 4).
    (* elem types *)
    exists (repeat T_funcref (Datatypes.length fns + num_custom_funs)).
    (* data types *)
    exists [].

    repeat split=>//.
    + (* func_types valid *)
      subst ts. by apply list_function_types_valid.
    + (* module_func_typing *)
      apply Forall2_cons.
      { (* grow mem func *)
        subst ts. cbn.
        repeat split=>//. apply grow_memory_if_necessary_typing=>//.
        repeat split=>//.
        intros ? Hin'. cbn. by repeat destruct Hin' as [|Hin']; subst =>//. }
      apply Forall2_cons.
      { (* main func *)
        subst ts. cbn. repeat split =>//.
        apply translate_body_correct in Hexpr.
        2:{ destruct e; inv He =>//. eapply Forall_constructors_subterm. eassumption.
            apply t_step. by apply dsubterm_fds2. }
        eapply repr_expr_LambdaANF_Wasm_typing =>//; last by eassumption.
        2: { (* expr restr *) destruct e; inv He =>//. by inv Hrestr. }
        repeat split =>//.
        * (* locals in bound *)
          intros ?? Hvar. cbn.
          unfold lookup_N. rewrite nth_error_map.
          destruct (nth_error _ (N.to_nat x')) eqn:Hcontra =>//.
          inv Hvar. apply var_mapping_list_lt_length in H.
          by apply nth_error_Some in H.
        * (* globals *)
          intros var Hin. cbn.
          by repeat destruct Hin as [|Hin]; subst =>//.
        * (* table *)
          eexists. cbn. split; reflexivity.
        * (* grow_mem func id *)
          cbn. unfold grow_mem_function_idx; lia.
        * (* types *)
          intros ? Hmax. cbn. unfold max_function_args in Hmax. unfold lookup_N.
          erewrite nth_error_nth'; first rewrite nth_list_function_types =>//.
          by rewrite Nat2N.id. lia. rewrite length_list_function_types. lia.
          apply notNone_Some. rewrite <- map_repeat_eq. eexists. apply default_vals_i32_Some.
      }
      { (* funcs *)
        apply Forall2_spec; first by rewrite map_length length_is_size length_is_size size_map.
        intros ?? [t1s t2s] Hnth1 Hnth2. cbn. unfold module_func_typing. repeat split =>//.
        rewrite nth_error_map in Hnth1. simpl in Hfuns.
        destruct (nth_error fns n) eqn:Hin =>//. cbn. inv Hnth1.
        rewrite nth_error_map in Hnth2. rewrite Hin in Hnth2. injection Hnth2 as Hnth2. subst t1s t2s.
        assert (n = N.to_nat (fidx w) - num_custom_funs).
        { eapply translate_functions_nth_error_idx; eauto. } subst n.

        replace (create_fname_mapping e) with (create_fname_mapping (Efun fds e)) in Hfuns by
          (destruct e; inv He =>//).
        have H' := translate_functions_exists_original_fun cenv nenv _ fds fds fns _ _ _ _ Hnodup Hfuns Logic.eq_refl (nth_error_In _ _ Hin).
        destruct H' as [f [t [ys [e1 [Hfd [Htype Hvarr]]]]]].

        assert (HcenvFds : (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
                            find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e)). {
          intros ???? Hfd'.
          destruct e; inv He =>//. eapply Forall_constructors_subterm. eassumption.
          apply t_step. apply dsubterm_fds. now eapply find_def_dsubterm_fds_e.
        }
        have H' := translate_functions_find_def cenv nenv _ fds _ _ _ _ e1 _ Hnodup Hfuns Hfd HcenvFds.

        destruct H' as [f' [e' [locs [func [Hvar [-> [Hin' [<- [Hty [Hlocs [<- Hexpr']]]]]]]]]]].
        assert (func = w). {
          assert (Heq: fidx func = fidx w). {
            inv Hvar. inv Hvarr. unfold translate_var in H, H0.
            destruct ((create_fname_mapping (Efun fds e)) ! f) eqn:Hf; rewrite Hf in H, H0; congruence.
          }
          apply In_nth_error in Hin'. destruct Hin' as [j Hj].
          assert (j = N.to_nat (fidx func) - num_custom_funs). eapply translate_functions_nth_error_idx; try apply Hfuns; eauto.
          congruence.
        } subst w. clear Hvarr Hin'.

        split. { destruct e; inv He; try by inv Hfd. inv Hrestr.
          apply H3 in Hfd. destruct Hfd as [Hfd _].
          unfold lookup_N. erewrite nth_error_nth'.
          2:{ rewrite length_list_function_types. lia. }
          rewrite nth_list_function_types; auto. lia. }
        split.
        eapply repr_expr_LambdaANF_Wasm_typing =>//; last by apply Hexpr'.
        { (* context restrictions *)
          repeat split =>//.
          * (* locs i32 *)
            intros ?? Hvar'.
            rewrite Hlocs Htype Nat2N.id. unfold lookup_N. cbn.
            rewrite <-repeat_app, <-app_length.
            apply nth_error_repeat. inv Hvar'. now eapply var_mapping_list_lt_length.
          * (* globals *)
            intros ? Hin'. cbn. by repeat destruct Hin' as [|Hin']; subst =>//.
          * (* table *)
            eexists. cbn. unfold lookup_N. split; reflexivity.
          * (* grow_mem func id *)
            cbn. unfold grow_mem_function_idx; lia.
          * (* types *)
            intros ? Hmax. unfold lookup_N.
            erewrite nth_error_nth'. rewrite nth_list_function_types. now rewrite Nat2N.id. lia.
            rewrite length_list_function_types. lia.
        }
        { destruct e; inv He; try by inv Hfd. inv Hrestr. now eapply H3. }
        { rewrite Hlocs. apply notNone_Some. eexists. apply default_vals_i32_Some. }
      }
    + (* module_table_typing *)
      apply Forall2_cons. unfold module_table_typing, tabletype_valid, limit_valid_range. cbn.
      assert (HfnsBound: (N.of_nat (Datatypes.length fns + num_custom_funs) <= 4294967295)%N).
      { apply translate_functions_length in Hfuns. rewrite -Hfuns.
        destruct e; inv He=>//. inv Hrestr. unfold num_custom_funs.
        unfold max_num_functions in H4. lia. }
        apply N.leb_le in HfnsBound. rewrite HfnsBound. by apply /eqtable_typeP.
      apply Forall2_nil.
    + (* module_mem_typing *)
      apply Forall2_cons=>//.
    + (* module_glob_typing *)
      repeat (apply Forall2_cons; repeat split; try by apply bet_const_num =>//).
      by apply Forall2_nil.
    + (* module_elem_typing *)
      simpl. by eapply module_typing_module_elem_typing.
    + (* module_import_typing *)
      apply Forall2_cons. subst ts. unfold module_import_typing. cbn.
        erewrite nth_error_nth'. 2: { rewrite length_list_function_types. lia. }
        rewrite nth_list_function_types; last lia. cbn. by apply /eqextern_typeP.
      apply Forall2_cons. subst ts. unfold module_import_typing. cbn.
        erewrite nth_error_nth'. 2: { rewrite length_list_function_types. lia. }
        rewrite nth_list_function_types; last lia. cbn. by apply /eqextern_typeP.
      by apply Forall2_nil.
    + (* module_export_typing *)
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
        destruct e; try by inv He; inv Hfuns; destruct n=>//. inv He.
        assert (n = N.to_nat (fidx w) - num_custom_funs). { now eapply translate_functions_nth_error_idx; eauto. } subst n. cbn.
        assert (Hbounds: (N.of_nat num_custom_funs <= fidx w < N.of_nat (length fns + num_custom_funs))%N). {
          eapply translate_functions_idx_bounds; eauto.
          2:{ apply In_map. now eapply nth_error_In. }
          intros. split; first by apply local_variable_mapping_gt_idx in H; lia.
          assert (Hvar: translate_var nenv (create_fname_mapping (Efun fds e0)) f ""%bs = Ret f')
            by (unfold translate_var; rewrite H=>//). clear H.
          have H' := Hvar.
          apply var_mapping_list_lt_length' in Hvar.
          rewrite collect_function_vars_length in Hvar.
          erewrite (translate_functions_length _ _ _ _ fns) in Hvar; eauto. lia.
        }
        unfold num_custom_funs in *. unfold lookup_N.
        destruct (N.to_nat (fidx w)) eqn:Hidx; first by lia.
        do 3! (destruct n; first by lia). cbn in Hnth.
        rewrite Nat.sub_0_r in Hnth. cbn.
        rewrite nth_error_map. rewrite Hnth. by apply /eqfunction_typeP.
      }
      (* global vars, memory *)
      repeat apply Forall2_cons =>//.
      (* export names unique *)
      admit.
    }
  - (* imports typing *)
    apply Forall2_cons=>//.
    apply Forall2_cons=>//.
  - (* imports subtyping *)
    apply Forall2_cons=>//.
    apply Forall2_cons=>//.
  - (* alloc_module is true *) { cbn.
    unfold interp_alloc_module, initial_store in HallocM.
    destruct (alloc_funcs _ _ _) eqn:Hfuncs.
    have Hfuncs' := Hfuncs.
    apply alloc_func_iota_N in Hfuncs.
    cbn in HallocM.
    destruct Hfuncs as [Hfuncs1 [Hfuncs2 [Hfuncs3 [Hfuncs4 [Hfuncs5 [Hfuncs6 Hfuncs7]]]]]].
    cbn in Hfuncs1, Hfuncs2, Hfuncs3, Hfuncs4, Hfuncs5, Hfuncs6, Hfuncs7.

    destruct (alloc_elems _ _ _) eqn:Helems.
    injection HallocM as <-<-.
    have Helems' := Helems.
    apply alloc_elem_iota_N in Helems. cbn in Helems.
    rewrite Hfuncs2 -Hfuncs3 -Hfuncs4 -Hfuncs5 -Hfuncs6 -Hfuncs7 in Helems.
    (*  clear Hfuncs2 Hfuncs3 Hfuncs4 Hfuncs5 Hfuncs6 Hfuncs7. *)
    destruct Helems as [Helems1 [Helems2 [Helems3 [Helems4 [Helems5 [Helems6 Helems7]]]]]].
    cbn in Helems1, Helems2, Helems3, Helems4, Helems5, Helems6, Helems7.

    rewrite Hfuncs'. rewrite Helems'. cbn. clear Hfuncs' Helems'.
    (* rewrite Helems1. -Helems2. Helems3. -Helems4 -Helems5. *)

    rewrite Hfuncs1 -Hfuncs3 -Hfuncs4 -Hfuncs5.
    repeat (apply andb_true_iff; split=>//).
    + by apply /eqstore_recordP.
    + by apply /eqseqP. (* TODO types shouldn't be unfolded here, slow *)
    + subst l. by apply /eqseqP.
    + subst l0. by apply /eqseqP.
    + by apply /eqexportinstP.
    + by apply /eqexportinstP.
    + by apply /eqseqP.
    + rewrite table_element_mapping_length elem_vals_length. reflexivity.  }
  - (* instantiate globals *)
    unfold instantiate_globals. cbn.
    repeat (apply Forall2_cons; first by apply rt_refl).
    by apply Forall2_nil.
  - (* instantiate elem *)
    unfold instantiate_elems. cbn. unfold interp_alloc_module in HallocM.
    destruct (alloc_funcs _ _ _) eqn:Hfuncs.
    apply alloc_func_iota_N in Hfuncs. cbn in Hfuncs. cbn in HallocM.
    destruct (alloc_elems _ _) eqn:Helems.
    injection HallocM as <-.
    apply elems_instantiate. subst inst. cbn.
    rewrite Nat.add_comm. by rewrite map_length.
  - by rewrite cats0.
Unshelve. all: apply (Tf [] []).
Admitted.

End INSTANTIATION.
