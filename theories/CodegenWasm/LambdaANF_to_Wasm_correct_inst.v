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
  | S funs' => startidx :: funcidcs funs' (1 + startidx)%N
  end.

(* Lemma add_funcs_effect : forall s' s'' l l1 l2 f,
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
Qed. *)

(* Lemma reduce_forall_elem_effect : forall fns l f s state,
  Forall2 (fun (e : module_element) (c : Wasm_int.Int32.T) =>
                  reduce_trans (state, s, {| f_locs := []; f_inst := f_inst f |},
                    to_e_list (modelem_offset e))
                    (state, s, {| f_locs := []; f_inst := f_inst f |},
                    [AI_basic (BI_const_num (VAL_int32 c))]))
                 (map
                    (fun f : wasm_function =>
                     {|
                       modelem_table := Mk_tableidx 0;
                       modelem_offset :=
                         [BI_const_num (nat_to_value (LambdaANF_to_Wasm.fidx f))];
                       modelem_init := [Mk_funcidx (LambdaANF_to_Wasm.fidx f)]
                     |}) fns) l -> l = map (fun f => nat_to_i32 (LambdaANF_to_Wasm.fidx f)) fns.
Proof.
  induction fns; intros.
  - now inv H.
  - cbn in H. inv H. cbn in H2. apply reduce_trans_const in H2. cbn. inv H2.
    erewrite (IHfns l'); eauto.
Qed. *)

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

(* Lemma nth_list_function_types_map : forall fns fr,
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
Qed. *)

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
      destruct p; lia. assumption. intros.
      apply H in H0. cbn in H0. destruct n; try lia. destruct p; lia. }
  - inv H0. now apply H in H2.
Qed.


(* Lemma translate_fvar_fname_mapping : forall e f errMsg i,
    translate_var nenv (create_fname_mapping e) f errMsg = Ret i ->
    match e with Efun fds _ => i < numOf_fundefs fds + num_custom_funs | _ => True end.
Proof.
  intros. unfold create_fname_mapping, translate_var in H.
  destruct ((create_var_mapping num_custom_funs (collect_function_vars e)
         (M.empty nat)) ! f) eqn:Hf; inv H.
  destruct e; auto. rename f0 into fds.
  have H' := translate_fvar_fname_mapping_aux _ _ _ _ _ _ _ Hf.
  apply H'. intros. inv H.
Qed. *)

(* Lemma e_offs_increasing' : forall len n i l  s fr state,
  Forall2
        (fun (e : module_element) (c : Wasm_int.Int32.T) =>
         reduce_trans
           (state, s, {| f_locs := []; f_inst := f_inst fr |},
           to_e_list (modelem_offset e))
           (state, s, {| f_locs := []; f_inst := f_inst fr |},
           [AI_basic (BI_const_num (VAL_int32 c))]))
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
Qed. *)

Lemma table_element_mapping_length : forall len i,
  Datatypes.length (table_element_mapping len i) = len.
Proof.
  by induction len; intros; cbn; auto.
Qed.

(* Lemma e_offs_increasing : forall e_offs len state s fr,
  Forall2  (fun (e : module_element) (c : Wasm_int.Int32.T) =>
               reduce_trans
                 (state, s, {| f_locs := []; f_inst := f_inst fr |}, to_e_list (modelem_offset e))
                 (state, s, {| f_locs := []; f_inst := f_inst fr |},
                 [AI_basic (BI_const_num (VAL_int32 c))]))
   ([{| modelem_table := Mk_tableidx 0;
        modelem_offset := [BI_const_num (nat_to_value 0)];
        modelem_init := [Mk_funcidx 0]
     |};
    {| modelem_table := Mk_tableidx 0;
       modelem_offset := [BI_const_num (nat_to_value 1)];
       modelem_init := [Mk_funcidx 1]
     |};
     {| modelem_table := Mk_tableidx 0;
        modelem_offset := [BI_const_num (nat_to_value 2)];
        modelem_init := [Mk_funcidx 2]
     |};
     {| modelem_table := Mk_tableidx 0;
        modelem_offset := [BI_const_num (nat_to_value 3)];
        modelem_init := [Mk_funcidx 3]
      |};
     {| modelem_table := Mk_tableidx 0;
        modelem_offset := [BI_const_num (nat_to_value 4)];
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
Qed. *)

Fixpoint increasing_nats (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => (increasing_nats n') ++ [n']
  end.

(* Lemma nth_error_funcidcs {A} : forall (l : list A) len n idx,
  n < len ->
  nth_error (map (fun '(Mk_funcidx i) => i) (funcidcs len idx)) n =
  Some (idx + n).
Proof.
  induction len; intros; cbn in H. lia.
  destruct n; cbn. f_equal. lia.
  assert (n < len) by lia.
  replace (idx + S n) with (S idx + n) by lia.
  now apply IHlen.
Qed. *)

(* Lemma init_tab_nth_error_same : forall s s' f t n anything,
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
Qed. *)

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

(* Lemma init_tab_nth_error_other : forall s s' f t n n' val,
  n <> n' ->
  n' < length (table_data t) ->
  inst_tab (f_inst f) = [0] ->
  s_tables s = [t] ->
  nth_error (table_data t) n = val ->
  init_tab host_function s (f_inst f) n' {| modelem_table := (Mk_tableidx 0)
                                          ; modelem_offset := [BI_const_num (nat_to_value n')]
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
Qed. *)

(* Lemma init_tab_preserves_length : forall s s' f t t' n n',
  n' < length (table_data t) ->
  inst_tab (f_inst f) = [0] ->
  s_tables s = [t] ->
  init_tab host_function s (f_inst f) n' {| modelem_table := (Mk_tableidx 0)
                                          ; modelem_offset :=  [BI_const_num (nat_to_value n)]
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
Qed. *)

(* Lemma init_tabs_effect_general : forall iis vvs t s s' f,
  inst_funcs (f_inst f) = [:: 0, 1, 2, 3, 4 & map (fun '(Mk_funcidx i0) => i0)
                          (funcidcs (Datatypes.length (table_data t) - num_custom_funs) num_custom_funs)] ->
  s_tables s = [t] ->
  vvs = map (fun i => {| modelem_table := Mk_tableidx 0;
                         modelem_offset := [ BI_const_num (nat_to_value i) ]
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
                    modelem_offset := [BI_const_num (nat_to_value i)];
                    modelem_init := [Mk_funcidx i] |}) iis) as vvs.
    assert (Hnodup': NoDup iis). { now inv Hnodup. }
    cbn in Hs'.
    assert (Hext: exists t, s_tables
       (init_tab host_function s (f_inst f) a
          {|
            modelem_table := Mk_tableidx 0;
            modelem_offset := [ BI_const_num (nat_to_value a) ];
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
               modelem_offset := [BI_const_num (nat_to_value i)];
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
             modelem_offset :=  [ BI_const_num (nat_to_value a) ];
             modelem_init := [Mk_funcidx a]
           |}) as sEnd. symmetry in HeqsEnd. assert (Hia: i<>a) by auto. clear Hai.
      assert (Halen: a < Datatypes.length (table_data t)). { apply Hilen. now cbn. }
      have H' := init_tab_nth_error_other _ _ _ _ _ _ _ Hia Halen HinstT Ht Logic.eq_refl HeqsEnd.
      destruct H' as [t''' [Ht1 Ht2]]. congruence.
   }}
Qed. *)

(* Lemma init_tabs_only_changes_tables : forall s s' f l1 l2,
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
Qed. *)

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

(* Lemma table_element_mapping_nth: forall len n startIdx,
  n < len ->
  nth_error (table_element_mapping len startIdx) n =
  Some {| modelem_table := Mk_tableidx 0;
          modelem_offset := [BI_const_num (nat_to_value (n + startIdx))];
          modelem_init := [Mk_funcidx (n + startIdx)] |}.
Proof.
  induction len; intros; first lia.
  destruct n.
  - (* n=0 *) reflexivity.
  - (* n=Sn'*) cbn. replace (S (n + startIdx)) with (n + (S startIdx)) by lia.
               now apply IHlen.
Qed. *)

(* Lemma table_element_mapping_alternative : forall e_offs,
  (forall i : nat,
            i < Datatypes.length e_offs ->
            nth_error e_offs i = Some (nat_to_i32 i)) ->
  (Z.of_nat (Datatypes.length e_offs) < Wasm_int.Int32.modulus)%Z ->
  table_element_mapping (Datatypes.length e_offs) 0 = map
  (fun i : nat =>
   {|
     modelem_table := Mk_tableidx 0;
     modelem_offset := [BI_const_num (nat_to_value i)];
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
Qed. *)


(* Lemma init_tabs_effect : forall s s' f e_offs t,
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
Qed. *)

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
(*
Lemma translate_functions_increasing_fids : forall fds fns fenv e e',
  fenv = create_fname_mapping e ->
  match e with Efun fds' _ => fds' = fds | _ => True end ->
  map_injective fenv ->
  NoDup (collect_function_vars (Efun fds e')) ->
  translate_functions nenv cenv fenv penv fds = Ret fns ->
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
  translate_functions nenv cenv (create_fname_mapping eTop) penv fds = Ret fns ->
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
  translate_functions nenv cenv fenv penv fds = Ret fns ->
  find_def f fds = Some (t, ys, e) ->
  (forall f t ys e, find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e) ->
  exists idx e' locs ftype func, repr_funvar fenv nenv f idx /\
    locs = repeat T_i32 (length (collect_local_variables e)) /\
    ftype = Tf (List.map (fun _ => T_i32) ys) [] /\
    In func fns /\
    func.(fidx) = idx /\ func.(type) = ftype /\ func.(locals) = locs /\ func.(body) = e' /\
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
    exists i, l. eexists. eexists. eexists.
    split. { now econstructor. }
    do 2! (split; try reflexivity).
    split. now left.
    cbn. rewrite map_repeat_eq.
    repeat (split; first reflexivity).
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
    destruct IH as [idx [e' [locs [type [func [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
    inversion H.
    repeat eexists.
    repeat (split; eauto). subst idx. eassumption.
    now right. all: congruence.
Qed.
*)

Theorem module_instantiate_INV_and_more_hold :
forall e eAny topExp fds num_funs module fenv main_lenv sr f,
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
  instantiate initial_store module [EV_func 0%N; EV_func 1%N] (sr, f, [::]) ->

  (* invariants hold initially *)
  INV fenv nenv sr f /\
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
  (* translation of e *)
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
Admitted.
(*
  intros e eAny topExp fds num_funs module fenv lenv s f exports Hnodup HeRestr HtopExp Hfds HcenvCorrect Hnumfuns
    HfdsLength Hcompile Hflocs Hinst. subst num_funs topExp.
  unfold instantiate in Hinst.
  unfold LambdaANF_to_Wasm in Hcompile.
  remember (list_function_types (Z.to_nat max_function_args)) as types.
  simpl in Hcompile.
  destruct (check_restrictions cenv e) eqn:HRestr. inv Hcompile.
  destruct (generate_constr_pp_function cenv nenv e) eqn:HgenPP. inv Hcompile.
  destruct (match _ with | Efun fds _ => _ fds | _ => Err _ end) eqn:HtransFns. inv Hcompile.
  destruct (match e with
            | Efun _ _ => e
            | _ => Efun Fnil e
            end) eqn:HtopExp'; try (by inv Hcompile).
  destruct (translate_body nenv cenv _ _ _) eqn:Hexpr. inv Hcompile. rename l0 into e'.
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
    inv HeRestr. apply H3 in Hdef. lia. }
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
   split. (* inst_globals (f_inst f) no dups *)
   unfold INV_inst_globals_nodup. rewrite F0.
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
 *)

(* MAIN THEOREM, corresponds to 4.3.1 in Olivier's thesis *)
Theorem LambdaANF_Wasm_related :
  forall (v : cps.val) (e : exp) (n : nat) (vars : list cps.var)
         (hs : host_state) module fenv lenv
         (sr : store_record) (fr : frame) (pfs : M.t (list val -> option val)),
  (* evaluation of LambdaANF expression *)
    bstep_e pfs cenv (M.empty _) e v n ->
        bstep_prim_funs_no_fun_return_values pfs ->
  bs_LambdaANF_prim_fun_env_extracted_prim_env_related penv pfs ->
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

  instantiate initial_store module [EV_func 0%N; EV_func 1%N] (sr, fr, [::]) ->
  (* reduces to some sr' that has the result variable set to the corresponding value *)
  exists (sr' : store_record),
       reduce_trans (hs, sr,  (Build_frame [] (f_inst fr)), [ AI_basic (BI_call main_function_idx) ])
                    (hs, sr', (Build_frame [] (f_inst fr)), [])    /\

       result_val_LambdaANF_Wasm cenv fenv nenv penv v sr' (f_inst fr).
Proof.
  intros ??????????? Hstep HprimFunsRet HprimFunsRelated LANF2Wasm Hcenv HcenvRestr HvarsEq HvarsNodup Hfreevars Hinst.
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

  have HI := module_instantiate_INV_and_more_hold _ _ _ _ _ _ _ _ _ _ Hnodup' HeRestr
               Logic.eq_refl Logic.eq_refl Hcenv' Logic.eq_refl Hmaxfuns LANF2Wasm Hinst.
  clear Hnodup' Hcenv'.
  destruct HI as [Hinv [HinstFuncs [HfVal [grow_mem_fn [main_fn [e' [fns' [-> [-> [HsrFuncs [Hexpr' Hfns']]]]]]]]]]].

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

  remember (Build_frame (repeat (VAL_num (nat_to_value 0)) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.
  remember (create_local_variable_mapping (collect_local_variables e)) as lenv.
  remember (create_fname_mapping e) as fenv.

   assert (HlocInBound: (forall (var : positive) (varIdx : funcidx),
          repr_var (lenv:=lenv) nenv var varIdx -> N.to_nat varIdx < Datatypes.length (f_locs f_before_IH))).
   { intros ? ? Hvar. subst f_before_IH. cbn. rewrite repeat_length. inv Hvar.
     eapply var_mapping_list_lt_length. eassumption. }

  assert (Hinv_before_IH: INV fenv nenv sr f_before_IH). { subst.
    destruct Hinv as [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]].
    unfold INV. repeat (split; try assumption).
    unfold INV_locals_all_i32. cbn. intros. exists (nat_to_i32 0).
    assert (i < (length (repeat (VAL_num (nat_to_value 0)) (Datatypes.length (collect_local_variables e))))).
    { subst. now apply nth_error_Some. }
    rewrite nth_error_repeat in H12. inv H12. reflexivity. rewrite repeat_length in H13. assumption.
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
           repr_val_LambdaANF_Wasm cenv fenv nenv penv (Vfun (M.empty _) fds a) sr (f_inst f_before_IH) (Val_funidx fidx))). {
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
        exists fidx. split. assumption. subst f_before_IH. assumption. }
    }

    assert (HrelE : @rel_env_LambdaANF_Wasm cenv fenv nenv penv
                   _ (create_local_variable_mapping (collect_local_variables e)) e (def_funs fds fds (M.empty _) (M.empty _))
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
    have HMAIN := repr_bs_LambdaANF_Wasm_related cenv fenv nenv penv _
                    _ _ _ _ _ _ _ frameInit _ lh HcenvRestr HprimFunsRet HprimFunsRelated HlenvInjective
                    HenvsDisjoint Logic.eq_refl Hnodup' HfenvWf HfenvRho
                    HeRestr' Hunbound Hstep hs _ _ _ Hfds HlocInBound Hinv_before_IH Hexpr HrelE.

    destruct HMAIN as [s' [f' [k' [lh' [Hred [Hval [Hfinst _]]]]]]]. cbn.
    subst frameInit.
    exists s'. split.
    dostep'. apply r_call. cbn.
    rewrite HinstFuncs. reflexivity.
    dostep'. eapply r_invoke_native with (ves:=[]) (vs:=[]); eauto.
    rewrite HsrFuncs. subst f_before_IH. cbn. rewrite Hfinst. reflexivity. reflexivity.
    erewrite <-map_repeat_eq. by apply default_vals_i32_Some.
    subst f_before_IH. cbn. cbn. subst lh. cbn in Hred. rewrite <- Hfinst. rewrite cats0 in Hred.
    eapply rt_trans. apply Hred.
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
                    _ (create_local_variable_mapping (collect_local_variables e)) e (M.empty _) sr f_before_IH Fnil). {
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
                    HeRestr Hunbound Hstep hs _ _ _ Hfds HlocInBound Hinv_before_IH Hexpr HrelE.

    subst lh frameInit.

    destruct HMAIN as [s' [f' [k' [lh' [Hred [Hval [Hfinst _]]]]]]]. cbn.
    exists s'. split.
    dostep'. apply r_call. cbn.
    rewrite HinstFuncs. reflexivity.
    dostep'. eapply r_invoke_native with (ves:=[]) (vs:=[]); eauto.
    rewrite HsrFuncs. subst f_before_IH. cbn. rewrite Hfinst. reflexivity. reflexivity.
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

(*
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
  | |- be_typing _ [:: BI_binop T_i32 _] (Tf [:: T_i32; T_i32; T_i32] _) => apply bet_weakening with (ts:=[::T_i32]); apply bet_binop; apply Binop_i32_agree
  | |- be_typing _ [:: BI_binop T_i64 _] (Tf [:: T_i64; T_i64] _) => apply bet_binop; apply Binop_i64_agree
  | |- be_typing _ [:: BI_relop T_i32 _] (Tf [:: T_i32; T_i32] _) => apply bet_relop; apply Relop_i32_agree
  | |- be_typing _ [:: BI_store _ None _ _] (Tf [:: T_i32; _] _) => apply bet_store; simpl; auto; by apply Hcontext
  | |- be_typing _ [:: BI_load T_i32 None _ _] (Tf [:: T_i32] _) => apply bet_load; simpl; auto; by apply Hcontext
  | |- be_typing _ [:: BI_load T_i64 None _ _] (Tf [:: T_i32] _) => apply bet_load; simpl; auto; by apply Hcontext
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
  | |- be_typing _ _ (Tf [:: T_i32; T_i64] _) => apply bet_weakening with (ts:=[::T_i32; T_i64]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_i32; T_i64; T_i64] _) => apply bet_weakening with (ts:=[::T_i32]); by solve_bet Hcontext
  | |- be_typing _ _ (Tf [:: T_i32; T_i64; T_i32] _) => apply bet_weakening with (ts:=[::T_i32; T_i64]); by solve_bet Hcontext
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
    apply bet_if_wasm; try by solve_bet Hcontext.
    eapply bet_composition'. subst s.
    apply instr_write_string_typing =>//.
    solve_bet Hcontext.
    prepare_solve_bet. all: try solve_bet Hcontext.
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
  - (* Eprim *)
    intros ???????? Hvar Hexpr' IH Hp' HprimOp ? Hcontext' Hrestr'.
    eapply bet_composition'. prepare_solve_bet; try solve_bet Hcontext'.
    inv HprimOp.
    unfold apply_binop_and_store_i64.
    prepare_solve_bet. all: try solve_bet Hcontext'.
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
*)
End INSTRUCTION_TYPING.

Section INSTANTIATION.
(*
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

*)
End INSTANTIATION.
