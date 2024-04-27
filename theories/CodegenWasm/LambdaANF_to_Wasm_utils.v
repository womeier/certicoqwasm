From compcert Require Import Coqlib.

Require Import LambdaANF.cps LambdaANF.eval LambdaANF.cps_util LambdaANF.List_util
               LambdaANF.identifiers.

Require Import Lia.
Require Import Coq.Logic.Decidable Coq.Lists.ListDec
               Coq.Relations.Relations Relations.Relation_Operators.

Require Import compcert.lib.Integers compcert.common.Memory.
Require Import CodegenWasm.LambdaANF_to_Wasm.

From Wasm Require Import datatypes operations host instantiation_spec instantiation_properties memory_list opsem properties.

Require Import Libraries.maps_util.
From Coq Require Import List.

Import Common.compM Common.Pipeline_utils.
Import bytestring.
Import ExtLib.Structures.Monad MonadNotation.
Import ssreflect ssrbool eqtype.

Import ListNotations.
Import seq.


Section General.

Lemma notNone_Some {A} : forall (o : option A),
  o <> None <-> exists v, o = Some v.
Proof.
  intros. destruct o; split; intros.
  eauto. congruence. contradiction. now destruct H.
Qed.

Lemma Some_notNone {A} : forall (o : option A) v,
  o = Some v -> o <> None.
Proof.
  congruence.
Qed.

Lemma In_map {A} {B} (f : A -> B) x xs : In x xs -> In (f x) (map f xs).
Proof.
  induction xs; auto; simpl.
  intros [Heq|Hin]; auto.
  intuition congruence.
Qed.

Lemma NoDup_app_In {A} : forall l1 l2 (x:A),
  NoDup (l1 ++ l2) ->
  In x l1 ->
  ~ In x l2.
Proof.
  induction l1; cbn; intros; auto.
  destruct H0.
  { (* a = x *)
    subst. intro. inv H. apply H3.
    now apply in_app_iff. }
  { intro Hcontra. inv H. now eapply IHl1. }
Qed.

Lemma NoDup_app_remove_middle : forall A (a b c : list A),
  NoDup (a ++ b ++ c) -> NoDup (a ++ c).
Proof.
  intros. generalize dependent a. revert c.
  induction b; intros; auto.
  cbn in H. now apply NoDup_remove_1 in H.
Qed.

Lemma NoDup_incl_NoDup' {A} : forall (l1' l1 l2 : list A),
  NoDup (l1 ++ l2) -> NoDup l1' -> incl l1' l1 -> NoDup (l1' ++ l2).
Proof.
  induction l1'; intros.
  - destruct l1. assumption. cbn. inv H. now apply NoDup_app_remove_l in H5.
  - cbn. inv H0.
    assert (Hincl: incl l1' l1). { intros a' Hain'. apply H1. now right. }
    constructor. intro Hcontra. apply in_app_or in Hcontra. destruct Hcontra; auto.
    assert (In a l1). apply H1. now left. now eapply NoDup_app_In in H.
    now eapply IHl1'.
Qed.

Lemma set_nth_nth_error_same : forall {X:Type} (l:seq X) e e' i vd,
    nth_error l i = Some e ->
    nth_error (set_nth vd l i e') i = Some e'.
Proof.
  intros. revert l H. induction i; intros.
  - inv H. destruct l; inv H1. reflexivity.
  - cbn in H. destruct l. inv H. now apply IHi in H.
Qed.


Lemma set_nth_nth_error_other : forall {X:Type} (l:seq X) e i j vd,
    i <> j -> j < length l ->
    List.nth_error (set_nth vd l j e) i = List.nth_error l i.
Proof.
  induction l; intros.
  - cbn in H0. lia.
  - cbn in H0. destruct i.  cbn. destruct j. contradiction. reflexivity. cbn in *.
    destruct j; cbn; auto. apply IHl. lia. lia.
Qed.

Lemma nth_error_ext {A} (l l' : list A) :
  (forall n, nth_error l n = nth_error l' n) -> l = l'.
Proof.
  revert l'. induction l as [|a l IHl];
    intros l' Hnth; destruct l'.
  - reflexivity.
  - discriminate (Hnth 0).
  - discriminate (Hnth 0).
  - injection (Hnth 0) as ->. f_equal. apply IHl.
    intro n. exact (Hnth (S n)).
Qed.

Lemma nthN_nth_error {A} : forall (l : list A) i,
  nthN l (N.of_nat i) = nth_error l i.
Proof.
  induction l; intros.
  - destruct i; reflexivity.
  - destruct i; try reflexivity.
    replace (N.of_nat (S i)) with (1 + N.of_nat i)%N by lia.
    cbn. rewrite -IHl. cbn.
    destruct (N.of_nat i) eqn:Heqn; auto.
    destruct p; auto.
    replace (N.pos (Pos.succ p)~0 - 1)%N with (N.pos p~1)%N by lia. reflexivity.
Qed.

Lemma map_repeat_eq {A} {B} : forall (l : list A) (v : B),
  repeat v (Datatypes.length l) = map (fun _ => v) l.
Proof.
  induction l; cbn; intros; auto. f_equal. apply IHl.
Qed.

Lemma map_map_seq {A B C}: forall (l:seq A) (f: A -> B) (g : B -> C),
   [seq g (f a) | a <- l] = [seq (g v) | v <- [seq f a | a <- l]].
Proof.
  induction l; intros; cbn; auto. f_equal. now apply IHl.
Qed.

(* Lemma imap_aux_offset : forall l a a' b b',
  a + a' = b + b' ->
  imap_aux (fun i x : nat => i + a + x) l a' =
  imap_aux (fun i x : nat => i + b + x) l b'.
Proof.
  induction l; intros ???? Heq=>//.
  cbn. replace (a' + a0 + a) with (b' + b + a) by lia.
  f_equal. apply IHl. lia.
Qed. *)

Lemma drop_is_skipn {A} : forall l n, @drop A n l = List.skipn n l.
Proof.
  induction l; intros; auto.
  - induction n; cbn; auto.
  - destruct n. reflexivity. cbn. now rewrite IHl.
Qed.

Lemma take_drop_is_set_nth {B} : forall a (b : B) (l : list B),
  a < length l ->
  take a l ++ b :: drop (a + 1) l = set_nth b l a b.
Proof.
  intros. apply nth_error_ext; intros.
  assert (Hlen: length (take a l) = a). {
    rewrite length_is_size size_take -length_is_size.
    assert (ssrnat.leq (S a) (Datatypes.length l)). { apply /ssrnat.leP. lia. }
    now rewrite H0. }
  destruct (Nat.lt_total n a). 2: destruct H0.
  { (* n < a *)
    erewrite set_nth_nth_error_other; auto; try lia.
    assert (n < Datatypes.length (take a l)). {
      rewrite length_is_size size_take -length_is_size.
      destruct (ssrnat.leq (S a) (Datatypes.length l)); lia. }
    rewrite nth_error_app1; auto.
    assert (H': n < length l) by lia. apply nth_error_Some in H'. apply notNone_Some in H'.
    destruct H'.
    erewrite nth_error_take; eauto. apply /ssrnat.leP. lia. }
  { (* n=a *)
    subst.
    have H' := H. apply nth_error_Some in H'. apply notNone_Some in H'. destruct H'.
    erewrite set_nth_nth_error_same; eauto.
    rewrite nth_error_app2. replace (a - Datatypes.length (take a l)) with 0.
    reflexivity. lia. lia. }
  { (* a < n *)
    rewrite nth_error_app2. 2: lia.
    rewrite set_nth_nth_error_other; try lia.
    rewrite Hlen drop_is_skipn.
    destruct n; first lia. destruct l; first inv H.
    replace (a + 1) with (S a) by lia.
    replace (S n - a) with (S (n - a)) by lia. cbn.
    rewrite MCList.nth_error_skipn. cbn.
    now replace (a + (n - a)) with n by lia. }
Qed.

End General.


Section Vars.

Fixpoint fds_collect_local_variables (fds : fundefs) : list cps.var :=
  match fds with
  | Fnil => []
  | Fcons _ _ ys e fds' => (ys ++ collect_local_variables e) ++ (fds_collect_local_variables fds')
  end.

Definition collect_all_local_variables (e : cps.exp) : list cps.var :=
  match e with
  | Efun fds e' => collect_local_variables e' ++ fds_collect_local_variables fds
  | _ => collect_local_variables e
  end.

Lemma find_def_collect_all_local_variables : forall fds f t ys e e',
  find_def f fds = Some (t, ys, e) ->
  incl (ys ++ collect_local_variables e) (collect_all_local_variables (Efun fds e')).
Proof.
  unfold incl.
  induction fds; intros. 2: inv H.
  cbn in H. destruct (M.elt_eq f0 v).
  { (* f0=v *) subst v. inv H. cbn. apply in_or_app. right. apply in_or_app. now left. }
  { (* f0<>v *) have H' := IHfds _ _ _ _ e H _ H0. cbn. cbn in H'.
    apply in_or_app. right. rewrite <-app_assoc. apply in_or_app. now right. }
Qed.


Lemma NoDup_collect_all_local_variables_find_def : forall fds e f t ys e0,
 NoDup
   (collect_all_local_variables (Efun fds e) ++
    collect_function_vars (Efun fds e))%list ->
  find_def f fds = Some (t, ys, e0) ->
 NoDup
  ((ys ++ collect_local_variables e0) ++
   collect_function_vars (Efun fds e0)).
Proof.
  intros.
  assert (Hnodup: NoDup (ys ++ collect_local_variables e0)). {
    generalize dependent e. generalize dependent e0. revert f t ys.
    induction fds; intros. 2: inv H0. cbn in H0. destruct (M.elt_eq f0 v).
    { (* v=f0 *) inv H0. cbn in H. rewrite <- catA in H. apply NoDup_app_remove_l in H.
      apply NoDup_app_remove_r in H. now apply NoDup_app_remove_r in H. }
    { (* v<>f0 *)
      eapply IHfds with (e:=e1); eauto. cbn in H. cbn.
      rewrite <- catA. repeat rewrite <- catA in H. apply NoDup_app_remove_middle in H.
      apply NoDup_app_remove_middle in H. rewrite catA in H.
      replace (v
       :: (fix iter (fds : fundefs) : seq var :=
             match fds with
             | Fcons x _ _ _ fds' => x :: iter fds'
             | Fnil => [::]
             end) fds) with ([v] ++
       (fix iter (fds : fundefs) : seq var :=
             match fds with
             | Fcons x _ _ _ fds' => x :: iter fds'
             | Fnil => [::]
             end) fds) in H by reflexivity.
      apply NoDup_app_remove_middle in H. rewrite <- catA in H. assumption.
    }}
  have Hincl := find_def_collect_all_local_variables _ _ _ _ _ e H0.
  now eapply NoDup_incl_NoDup'.
Qed.

Lemma NoDup_case: forall cl t e y,
    findtag cl t  = Some e ->
    NoDup (collect_local_variables (Ecase y cl)) ->
    NoDup (collect_local_variables e).
Proof.
  induction cl; intros.
  - inv H.
  - destruct a.
    destruct (M.elt_eq c t). inv H. assert (e = e0). { destruct (M.elt_eq t t). now inv H2. destruct n. reflexivity. }
    subst e0.
    cbn in H0.
    now apply NoDup_app_remove_r in H0.
    cbn in H0.
    apply NoDup_app_remove_l in H0.
    apply IHcl with (t:=t) (e:=e) (y:=y).
    inv H. destruct (M.elt_eq c t). contradiction. reflexivity.
    cbn. apply H0.
Qed.

Lemma find_def_in_collect_function_vars : forall fds f e,
  find_def f fds <> None <->
  In f (collect_function_vars (Efun fds e)).
Proof.
  induction fds; intros; split.
  { intro H. cbn in H.
    destruct (M.elt_eq f0 v).
    (* v=f0*) subst. now cbn.
    (* v<>f0*) right. eapply IHfds. eassumption.
  }
  { intros H Hcontra. cbn in H. cbn in Hcontra.
    destruct (M.elt_eq f0 v).
    (* v=f0*) subst. now cbn.
    (* v<>f0*) destruct H as [H | H]. now subst.
               eapply IHfds. eassumption. assumption.
  }
  { intro H. contradiction. }
  { intro H. inv H. }
  Unshelve. all: auto.
Qed.

Lemma find_def_not_in_collect_function_vars : forall fds f e,
  find_def f fds = None ->
  ~ In f (collect_function_vars (Efun fds e)).
Proof.
  intros ? ? ? Hfd Hcontra.
  by apply find_def_in_collect_function_vars in Hcontra.
Qed.

Lemma collect_function_vars_length : forall fds e,
  length (collect_function_vars (Efun fds e)) = numOf_fundefs fds.
Proof.
  induction fds; intros; auto. cbn. f_equal. now eapply IHfds with (e:=e).
Qed.

(* Var maps: var -> local idx / fn idx *)

Definition map_injective (m : M.tree u32) := forall x y x' y',
  x <> y ->
  m ! x = Some x' ->
  m ! y = Some y' ->
  x' <> y'.

Definition domains_disjoint (m1 m2: M.tree u32) :=
  (forall x v1, m1 ! x = Some v1 -> m2 ! x = None) /\
  (forall x v2, m2 ! x = Some v2 -> m1 ! x = None).

Lemma HfenvWf_None {fenv} : forall fds,
   (forall f : var,
          (exists res : fun_tag * seq var * exp,
             find_def f fds = Some res) <->
          (exists i : N, fenv ! f = Some i)) ->

  (forall f, find_def f fds = None <-> fenv ! f = None).
Proof.
  intros. split; intros; specialize H with f.
  - assert (~ exists p, fenv ! f = Some p). {
      intro Hcontra. rewrite <- H in Hcontra. now destruct Hcontra. }
    destruct (fenv ! f); auto. exfalso. now apply H1.
  - assert (~ exists p, find_def f fds = Some p). {
      intro Hcontra. rewrite H in Hcontra. now destruct Hcontra. }
    destruct (find_def f fds); auto. exfalso. now apply H1.
Qed.

Lemma var_mapping_list_lt_length' {nenv} : forall l loc loc' err_str n,
  translate_var nenv (create_var_mapping n l (M.empty _)) loc err_str = Ret loc' ->
  N.to_nat loc' < length l + N.to_nat n.
Proof.
  intros ? ? ? ? ? H.
  unfold translate_var in H.
  destruct (create_var_mapping n l (M.empty _)) ! loc eqn:Heqn; rewrite Heqn in H; inv H.
  generalize dependent loc. revert loc' err_str n.
  induction l; intros. inv Heqn.
  destruct (var_dec loc a).
  (* loc = a *) subst. cbn in Heqn. rewrite Maps.PTree.gss in Heqn. inv Heqn. cbn. lia.
  (* loc <> a *) cbn in Heqn. rewrite Maps.PTree.gso in Heqn; auto. cbn.
  replace (S (Datatypes.length l + N.to_nat n)) with (Datatypes.length l + N.to_nat (N.succ n)) by lia.
  eapply IHl; eauto.
Qed.

Lemma var_mapping_list_lt_length {nenv} : forall l loc loc' err_str,
  translate_var nenv (create_local_variable_mapping l) loc err_str = Ret loc' ->
  N.to_nat loc' < length l.
Proof.
  intros. apply var_mapping_list_lt_length' in H. lia.
Qed.

Lemma var_mapping_list_lt_length_nth_error_idx {nenv} : forall l i n x err,
  NoDup l ->
  lookup_N l i = Some x ->
  translate_var nenv (create_var_mapping n l (M.empty _)) x err = Ret (n + i)%N.
Proof.
  induction l; intros.
  - unfold lookup_N in H0.
    destruct (N.to_nat i)=>//.
  - destruct (var_dec a x).
    { (* x=a *)
      subst. unfold lookup_N in H0.
      destruct (N.to_nat i) eqn:Hi.
      + cbn. unfold translate_var. rewrite M.gss. f_equal. lia.
      + cbn in H0. apply nth_error_In in H0.
        apply NoDup_cons_iff in H. now destruct H. }
    { (* x<> a *)
      (* cbn. rewrite M.gso; auto. cbn. *)
      unfold lookup_N in H0. destruct i; cbn in H0; first by inv H0.
      destruct (Pos.to_nat p) eqn:Hp; try lia. cbn in H0.
      replace (n + N.pos p)%N with (N.succ n + N.of_nat n1)%N by lia.
      cbn. unfold translate_var. rewrite M.gso; auto.
      inv H. apply IHl; auto.
      rewrite -H0. unfold lookup_N. f_equal. lia.
    }
Qed.

Lemma local_variable_mapping_gt_idx : forall l idx x x',
  (create_var_mapping idx l (M.empty u32)) ! x = Some x' -> (x' >= idx)%N.
Proof.
  induction l; intros. inv H.
  cbn in H.
  destruct (Pos.eq_dec a x).
  { (* a=x *) subst a. rewrite M.gss in H. inv H. lia. }
  { (* a<>x *) rewrite M.gso in H; auto.
    apply IHl in H. lia. }
Qed.

Lemma variable_mapping_Some_In : forall l x v idx lenv,
  lenv ! x = None ->
  (create_var_mapping idx l lenv) ! x = Some v ->
  In x l.
Proof.
  induction l; intros.
  - inv H0. congruence.
  - cbn in H0. destruct (var_dec a x).
    + (* a = x*) subst. now cbn.
    + (* a <> x *) right. rewrite M.gso in H0; auto.
      eapply IHl; eauto.
Qed.

 Lemma variable_mapping_NotIn_None : forall l x idx lenv,
  ~ In x l ->
  lenv ! x = None ->
  (create_var_mapping idx l lenv) ! x = None.
Proof.
  induction l; intros; cbn; auto. cbn in H.
  assert (x <> a) by auto.
  assert (~ In x l) by auto. clear H.
  rewrite M.gso; auto.
Qed.

Lemma variable_mapping_In_Some : forall l x idx lenv,
  NoDup l ->
  In x l ->
  (create_var_mapping idx l lenv) ! x <> None.
Proof.
  induction l; intros.
  - inv H0.
  - cbn in H0. destruct H0.
    (* a = x*) subst. cbn. intro. now rewrite M.gss in H0.
    (* In x l *) cbn. inv H. rewrite M.gso; auto. intro. now subst.
Qed.

Lemma variable_mappings_nodup_disjoint : forall l1 l2 idx1 idx2,
  NoDup (l1 ++ l2) ->
  domains_disjoint (create_var_mapping idx1 l1 (M.empty _))
                   (create_var_mapping idx2 l2 (M.empty _)).
Proof.
  intros. unfold domains_disjoint.
  split; intros.
  - apply variable_mapping_Some_In in H0; auto.
    apply variable_mapping_NotIn_None; auto. intro. now eapply NoDup_app_In.
  - apply variable_mapping_Some_In in H0; auto.
    apply variable_mapping_NotIn_None; auto. intro. now eapply NoDup_app_In.
Qed.

Lemma create_local_variable_mapping_injective : forall l idx,
   NoDup l -> map_injective (create_var_mapping idx l (M.empty u32)).
Proof.
  induction l; intros. { cbn. intros ????? H1. inv H1. }
  inv H. cbn. unfold map_injective in *. intros.
  destruct (Pos.eq_dec a x).
  { (* a=x *) subst a. intro. subst y'.
    rewrite M.gss in H0. inv H0. rewrite M.gso in H1; auto.
    apply local_variable_mapping_gt_idx in H1. lia. }
  { (* a<>x *) destruct (Pos.eq_dec a y).
    { (* a=y *) subst a. intro. subst y'. rewrite M.gss in H1. inv H1.
      rewrite M.gso in H0; auto. apply local_variable_mapping_gt_idx in H0. lia. }
    { (* a<>y *) rewrite M.gso in H0; auto.
                 rewrite M.gso in H1; auto.
                 have H' := IHl _ H3 _ _ _ _ H H0 H1. assumption. } }
Qed.

End Vars.


Section LambdaANF.

(* some of the following taken from C backend *)

Inductive dsubval_v: LambdaANF.cps.val -> LambdaANF.cps.val -> Prop :=
| dsubval_constr: forall v vs c,
  List.In v vs ->
  dsubval_v v (Vconstr c vs)
| dsubval_fun : forall x fds rho f,
  name_in_fundefs fds x ->
    dsubval_v (Vfun rho fds x) (Vfun rho fds f).

Definition subval_v := clos_trans _ dsubval_v.
Definition subval_or_eq := clos_refl_trans _ dsubval_v.

Lemma t_then_rt:
  forall A R (v v':A),
  clos_trans _ R v v'  ->
  clos_refl_trans _ R v v'.
Proof.
  intros. induction H.
  apply rt_step. auto.
  eapply rt_trans; eauto.
Qed.

Lemma rt_then_t_or_eq:
  forall A R (v v':A),
    clos_refl_trans _ R v v' ->
    v = v' \/ clos_trans _ R v v'.
Proof.
  intros. induction H.
  right. apply t_step; auto.
  left; auto.
  inv IHclos_refl_trans1; inv IHclos_refl_trans2.
  left; auto.
  right; auto.
  right; auto. right.
  eapply t_trans; eauto.
Qed.

Lemma dsubterm_case_cons:
  forall v l e',
    dsubterm_e e' (Ecase v l) ->
  forall a, dsubterm_e e' (Ecase v (a:: l)).
Proof.
  intros. inv H. econstructor.
  right; eauto.
Qed.

Lemma subterm_case:
forall v l e',
  subterm_e e' (Ecase v l) ->
  forall a, subterm_e e' (Ecase v (a:: l)).
Proof.
  intros. remember (Ecase v l) as y.
  revert dependent v. revert l. induction H.
  - intros. subst. constructor.
    eapply dsubterm_case_cons; eauto.
  - intros. apply IHclos_trans2 in Heqy.
    eapply t_trans. apply H. eauto.
Qed.

Lemma subval_fun: forall v rho fl x,
    name_in_fundefs fl x ->
        subval_or_eq v (Vfun rho fl x) ->
        exists l, v = Vfun rho fl l /\ name_in_fundefs fl l.
Proof.
  intros. apply rt_then_t_or_eq in H0.
  inv H0.
  exists x; auto.
  remember (Vfun rho fl x) as y.
  assert (exists x, y = Vfun rho fl x /\ name_in_fundefs fl x ) by eauto.
  clear H. clear Heqy. clear x.
  induction H1.  destructAll. subst. inv H. eauto.
  destructAll.
  assert (exists x, Vfun rho fl x0 = Vfun rho fl x /\ name_in_fundefs fl x) by eauto.
  apply IHclos_trans2 in H. apply IHclos_trans1 in H. auto.
Qed.

Lemma subval_or_eq_constr:
forall v v' vs c,
  subval_or_eq v v' ->
  List.In v' vs ->
  subval_or_eq v (Vconstr c vs).
Proof.
  intros.
  eapply rt_trans; eauto.
  apply rt_step. constructor; auto.
Qed.

Lemma subval_v_constr:
  forall v vs t,
  subval_v v (Vconstr t vs) ->
  exists v',
    subval_or_eq v v' /\ List.In v' vs.
Proof.
  intros.
  remember (Vconstr t vs) as v'. revert t vs Heqv'.
  induction H; intros; subst.
  - inv H. exists x. split.
    apply rt_refl. apply H2.
  -  specialize (IHclos_trans2 t vs Logic.eq_refl).
     destruct IHclos_trans2.
     exists x0. destruct H1. split.
     apply t_then_rt in H.
     eapply rt_trans; eauto.
     auto.
Qed.

Lemma subval_or_eq_fun:
  forall rho' fds f vs t,
  subval_or_eq (Vfun rho' fds f) (Vconstr t vs) ->
  exists v',
    subval_or_eq (Vfun rho' fds f) v' /\ List.In v' vs.
Proof.
  intros.
  apply rt_then_t_or_eq in H. destruct H.
  inv H.
  eapply subval_v_constr; eauto.
Qed.

Lemma subval_or_eq_fun_not_prim :
 forall v p,
  (forall p', v <> Vprim p') ->
  ~ subval_or_eq v (Vprim p).
Proof.
  intros ? ? HnotPrim Hcontra.
  remember (Vprim p) as v'.
  generalize dependent p.
  apply clos_rt_rt1n in Hcontra. induction Hcontra; intros; subst.
  now specialize HnotPrim with p.
  eapply IHHcontra; eauto.
  intros p' Hcontra'. subst. inv H.
Qed.

Lemma find_def_dsubterm_fds_e : forall fds f t ys e,
   find_def f fds = Some (t, ys, e) ->
   dsubterm_fds_e e fds.
Proof.
  induction fds; intros. 2: inv H.
  cbn in H. destruct (M.elt_eq f0 v).
  (* f0=v *) inv H. constructor.
  (* f0<>v *) constructor. eapply IHfds; eauto.
Qed.

Lemma dsubterm_fds_e_find_def : forall (fds : fundefs) (e : exp) (eAny : exp),
  NoDup (collect_function_vars (Efun fds eAny)) ->
  dsubterm_fds_e e fds ->
  exists f ys t, find_def f fds = Some (t, ys, e).
Proof.
  induction fds; intros. 2: inv H0.
  inv H0. { exists v, l, f. cbn. now destruct (M.elt_eq v v). }
  eapply IHfds in H3. destruct H3 as [f' [ys' [t' H']]].
  assert (f' <> v). { intro. subst.
    assert (find_def v fds <> None). { now apply notNone_Some. }
    eapply find_def_in_collect_function_vars in H0.
    now inv H. } exists f'.
  cbn. now destruct (M.elt_eq f' v).
  now inv H.
  Unshelve. all: assumption.
Qed.

Lemma set_lists_In:
  forall {A} x xs (v:A) vs rho rho' ,
    List.In x xs ->
    M.get x rho' = Some v ->
    set_lists xs vs rho = Some rho' ->
    List.In  v vs.
Proof.
  induction xs; intros.
  -   inv H.
  - destruct vs. simpl in H1; inv H1. simpl in H1.
    destruct (set_lists xs vs rho) eqn:Hsl; inv H1.
    destruct (var_dec x a).
    + subst.
      rewrite M.gss in H0. inv H0. constructor; reflexivity.
    + rewrite M.gso in H0=>//.
      constructor 2.
      inv H. exfalso; apply n; reflexivity.
      eapply IHxs; eauto.
Qed.


(* TODO: move this to cps_util *)
Definition Forall_constructors_in_e (P: var -> ctor_tag -> list var -> Prop) (e:exp) :=
  forall x t  ys e',
    subterm_or_eq (Econstr x t ys e') e -> P x t ys.

Definition Forall_exp_in_caselist (P: exp -> Prop) (cl:list (ctor_tag * exp)) :=
  forall g e, List.In (g, e) cl -> P e.

Lemma crt_incl_ct:
          forall T P e e',
          clos_trans T P e e' ->
          clos_refl_trans T P e e'.
Proof.
  intros. induction H. constructor; auto.
  eapply rt_trans; eauto.
Qed.

Lemma Forall_constructors_subterm:
  forall P e e' ,
  Forall_constructors_in_e P e ->
  subterm_e e' e ->
  Forall_constructors_in_e P e'.
Proof.
  intros. intro; intros.
  eapply H.
  assert (subterm_or_eq e' e).
  apply crt_incl_ct.
  apply H0.
  eapply rt_trans; eauto.
Qed.
(* END TODO move *)


Lemma Forall_constructors_in_constr:
  forall P x t ys e,
  Forall_constructors_in_e P (Econstr x t ys e) ->
  P x t ys.
Proof.
  intros.
  unfold Forall_constructors_in_e in *.
  eapply H.
  apply rt_refl.
Qed.

(* TODO: consider using def_funs_eq, def_funs_neq instead *)
Lemma def_funs_find_def : forall fds fds' rho f,
  find_def f fds <> None ->
    (def_funs fds' fds rho rho) ! f = Some (Vfun rho fds' f).
Proof.
  induction fds; intros; last contradiction.
  cbn in H. destruct (M.elt_eq f0 v).
  (* f0 = v *) subst. cbn. now rewrite M.gss.
  (* f0 <> v *) cbn. now rewrite M.gso.
Qed.

Lemma def_funs_not_find_def : forall fds fds' rho f,
  find_def f fds = None ->
    (def_funs fds' fds rho rho) ! f = rho ! f.
Proof.
  induction fds; intros ? ? ? H; auto.
  cbn in H. destruct (M.elt_eq f0 v).
  (* f0 = v *) inv H.
  (* f0 <> v *) cbn. now rewrite M.gso.
Qed.

End LambdaANF.


Section Wasm.
Import Nnat Znat.

Context `{ho : host}.

(* taken from iriswasm *)
Lemma mem_update_length dat dat' k b:
  memory_list.mem_update k b dat = Some dat' ->
  length dat.(ml_data) = length dat'.(ml_data).
Proof.
  intros Hupd.
  unfold mem_update in Hupd.
  destruct ( _ <? _)%N eqn:Hl ; inversion Hupd; clear Hupd.
  subst => /=.
  rewrite split_preserves_length => //.
  remember (length _) as x.
  move/N.ltb_spec0 in Hl; by lias.
Qed.

(* taken from iriswasm orig name: store_length *)
Lemma mem_store_preserves_length (m m': meminst) (n: N) (off: static_offset) (bs: bytes) :
  store m n off bs (length bs) = Some m' ->
  mem_length m = mem_length m'.
Proof.
  intros. unfold mem_length, memory_list.mem_length.
  unfold store, write_bytes, fold_lefti in H.
  destruct (_ <=? _)%N eqn:Hlen ; try by inversion H.
  cut (forall j dat dat',
          j <= length bs ->
          let i := length bs - j in
          (let '(_,acc_end) :=
            fold_left
              (fun '(k, acc) x =>
                (k + 1,
                  match acc with
                  | Some dat => mem_update (n + off + N.of_nat k)%N x dat
                  | None => None
                  end)) (bytes_takefill #00%byte j (drop i bs))
              (i, Some dat) in acc_end) = Some dat' ->
                               length (ml_data dat) = length (ml_data (meminst_data m)) ->
                               length (ml_data dat') = length (ml_data (meminst_data m))).
  - intros Hi.
    assert (length bs <= length bs) ; first lia.
    destruct (let '(_, acc_end) := fold_left _ _ _ in acc_end) eqn:Hfl ; try by inversion H.
    apply (Hi _ (meminst_data m) m0) in H0 => //=.
    + destruct m' ; inversion H ; subst; cbn; congruence.
    + rewrite PeanoNat.Nat.sub_diag. rewrite drop0. exact Hfl.
  - induction j ; intros ; subst i.
    + rewrite Nat.sub_0_r in H1.
      rewrite drop_size in H1.
      simpl in H1. inversion H1. by rewrite - H4.
    + assert (j <= length bs) ; first lia.
      destruct (drop (length bs - S j) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S j) bs) = 0); first by rewrite Hdrop.
        clear H Hlen IHj H1 H2 H3 H4. exfalso.
        assert (size (drop (Datatypes.length bs - S j) bs) = 0).
        { rewrite Hdrop. reflexivity. } rewrite size_drop in H.
        rewrite <- length_is_size in H.
        unfold ssrnat.subn, ssrnat.subn_rec in H. lia.
      * assert (exists dat0, mem_update (n + off + N.of_nat (length bs - S j))%N
                                   b dat = Some dat0) as [dat0 Hdat0].
        { unfold mem_update. apply N.leb_le in Hlen.
          assert (n + off + N.of_nat (length bs - S j) <
                   N.of_nat (length (ml_data dat)))%N.
          rewrite H2.
          unfold mem_length, memory_list.mem_length in Hlen.
          lia.
          apply N.ltb_lt in H4.
          rewrite H4.
          by eexists _. }
        apply (IHj dat0 dat') in H3.
        ++ done.
        ++ simpl in H1.
           rewrite Hdat0 in H1.
           replace (length bs - j) with (1 + (length bs - S j)) ; last lia.
           rewrite <- drop_drop.
           rewrite Hdrop. cbn.
           replace (S (Datatypes.length bs - S j)) with (Datatypes.length bs - S j + 1) by lia.
           rewrite drop0. assumption.
        ++ erewrite <- mem_update_length; eauto.
Qed.

(* adjusted from iriswasm *)
Lemma enough_space_to_store m k off bs :
  (k + off + N.of_nat (length bs) <= mem_length m)%N ->
  exists mf, store m k off bs (length bs) = Some mf.
Proof.
  intros Hmlen.
  unfold store.
  apply N.leb_le in Hmlen.
  rewrite Hmlen.
  unfold write_bytes, fold_lefti.
  cut (forall i dat,
          i <= length bs ->
          length (ml_data dat) = N.to_nat (mem_length m) ->
          let j := length bs - i in
          exists datf, (let '(_, acc_end) :=
              fold_left (fun '(k0,acc) x =>
                          (k0 + 1,
                            match acc with
                            | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                            | None => None
                            end)) (bytes_takefill #00%byte (length (drop j bs))
                                                  (drop j bs))
                        (j, Some dat) in acc_end) = Some datf).
  - intros H.
    assert (length bs <= length bs) ; first lia.
    apply (H _ (meminst_data m)) in H0 as [datf' Hdatf'].
    + rewrite PeanoNat.Nat.sub_diag in Hdatf'.
      rewrite drop0 in Hdatf'.
      rewrite Hdatf'.
      by eexists _.
    + unfold mem_length, memory_list.mem_length.
      by rewrite Nat2N.id.
  - induction i ; intros ; subst j.
    + rewrite Nat.sub_0_r.
      repeat rewrite length_is_size. rewrite drop_size.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs) = 0); first by rewrite Hdrop.
        rewrite length_is_size in H2. rewrite size_drop in H2.
        rewrite -length_is_size in H2. rewrite ssrnat.subnE in H2.
        unfold ssrnat.subn_rec in H2. lia.
      * assert (exists datupd,
                   mem_update (k + off + N.of_nat (length bs - S i))%N b dat =
                     Some datupd ) as [datupd Hdatupd].
        { unfold mem_update.
           apply N.leb_le in Hmlen.
           assert ( k + off + N.of_nat (length bs - S i) <
                      N.of_nat (length (ml_data dat)))%N ;
             first lia.
           apply N.ltb_lt in H2 ; rewrite H2.
           by eexists _. }
        eapply (IHi datupd) in H1 as [datf Hdatf].
        ++ rewrite - Hdrop.
           have H' := (take_drop 1 _ (drop (length bs - S i) bs)).
           rewrite ssrnat.addnE in H'. cbn in H'.
           rewrite length_is_size. rewrite size_drop. rewrite -length_is_size.
           rewrite ssrnat.subnE. unfold ssrnat.subn_rec.
           replace (Datatypes.length bs - (Datatypes.length bs - S i)) with (S i) by lia. cbn.
           rewrite Hdrop. cbn.
           replace (Datatypes.length bs - S i + 1) with (Datatypes.length bs - i) by lia.
           rewrite Hdatupd.
           rewrite length_is_size in Hdatf. rewrite size_drop in Hdatf.
           rewrite -length_is_size in Hdatf. rewrite ssrnat.subnE in Hdatf.
           unfold ssrnat.subn_rec in Hdatf.
           replace (Datatypes.length bs - (Datatypes.length bs - i)) with i in Hdatf by lia.
           assert (drop 1 (drop (Datatypes.length bs - S i) bs) = l) as Hd. {
           rewrite Hdrop. now rewrite drop1. } rewrite -Hd.
           rewrite drop_drop. rewrite ssrnat.addnE. cbn.
           replace (S (Datatypes.length bs - S i)) with (Datatypes.length bs - i) by lia.
           now rewrite Hdatf.
        ++ rewrite <- H0.
           now apply mem_update_length in Hdatupd.
Qed.

Definition load_i32 m addr : option value_num :=
  match load m addr 0%N 4 with (* offset: 0, 4 bytes *)
  | None => None
  | Some bs => Some (wasm_deserialise bs T_i32)
  end.

Definition store_i32 mem addr (v : value_num) : option meminst :=
  store mem addr 0%N (bits v) 4.


Definition load_i64 m addr : option value_num :=
  match load m addr 0%N 8 with (* offset: 0, 4 bytes *)
  | None => None
  | Some bs => Some (wasm_deserialise bs T_i64)
  end.

Definition store_i64 mem addr (v : value_num) : option meminst :=
    store mem addr 0%N (bits v) 8.


Definition tag_to_i32 (t : ctor_tag) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat (Pos.to_nat t)).

(* TODO use ref types (WasmGC) instead *)
Inductive wasm_value :=
  | Val_unboxed : u32 -> wasm_value
  | Val_ptr     : u32 -> wasm_value
  | Val_funidx  : u32 -> wasm_value.

Definition wasm_value_to_u32 (v : wasm_value) :=
  match v with
  | Val_unboxed i => i
  | Val_ptr i => i
  | Val_funidx i => i
  end.

Definition wasm_value_to_i32 (v : wasm_value) :=
  Wasm_int.Int32.repr (BinInt.Z.of_N (wasm_value_to_u32 v)).

(* memory *)

Lemma load_store_i32 : forall m addr v b1 b2 b3 b4,
load_i32 m addr = Some v ->
exists m', store m addr 0%N [b1;b2;b3;b4] 4 = Some m'.
Proof.
  intros. unfold load_i32 in H.
  destruct (load m addr 0%N 4) eqn:Heqn; inv H.
  unfold load in Heqn.
  apply enough_space_to_store. cbn.
  destruct ((addr + (0 + N.of_nat 4) <=? mem_length m)%N) eqn:Harith. 2: inv Heqn.
  apply N.leb_le in Harith. cbn in Harith. lia.
Qed.

Lemma store_load_i32 : forall m m' addr v,
length v = 4 ->
store m addr 0%N v 4 = Some m' ->
load_i32 m' addr = Some (wasm_deserialise v T_i32).
Proof.
  intros. assert (mem_length m = mem_length m').
  { rewrite <- H in H0. now eapply mem_store_preserves_length. }
   unfold store in H. unfold store in H0.
  destruct ((addr + 0 + N.of_nat 4 <=? mem_length m)%N) eqn:Heq. 2: inv H0.
  unfold load_i32. unfold load. cbn. cbn in Heq. unfold store in H0.
  assert (Hbytes: exists b1 b2 b3 b4, v = [b1; b2; b3; b4]). {
    destruct v. inv H. destruct v. inv H.
    destruct v. inv H. destruct v. inv H. destruct v.
    exists b, b0, b1, b2. reflexivity. inv H. }
  destruct Hbytes as [b1 [b2 [b3 [b4 Hb]]]]. subst v. clear H.
  rewrite N.add_0_r. rewrite N.add_0_r in Heq, H0.
  unfold write_bytes in H0. cbn in H0. rewrite N.add_0_r in H0.
  destruct (mem_update addr b1 (meminst_data m)) eqn:Hupd1. 2: inv H0.
  destruct (mem_update (addr + 1)%N b2 m0) eqn:Hupd2. 2: inv H0.
  destruct (mem_update (addr + 2)%N b3 m1) eqn:Hupd3. 2: inv H0.
  destruct (mem_update (addr + 3)%N b4 m2) eqn:Hupd4. 2: inv H0.
  inv H0. cbn. unfold mem_length, memory_list.mem_length. cbn.
  have Hu1 := mem_update_length _ _ _ _ Hupd1.
  have Hu2 := mem_update_length _ _ _ _ Hupd2.
  have Hu3 := mem_update_length _ _ _ _ Hupd3.
  have Hu4 := mem_update_length _ _ _ _ Hupd4. rewrite -Hu4 -Hu3 -Hu2 -Hu1.
  cbn. rewrite Heq.
  apply N.leb_le in Heq.
  unfold mem_update in Hupd1, Hupd2, Hupd3, Hupd4.
  destruct (addr     <? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N eqn:Hl1. 2: inv Hupd1.
  destruct (addr + 1 <? N.of_nat (Datatypes.length (ml_data m0)))%N eqn:Hl2. 2: inv Hupd2.
  destruct (addr + 2 <? N.of_nat (Datatypes.length (ml_data m1)))%N eqn:Hl3. 2: inv Hupd3.
  destruct (addr + 3 <? N.of_nat (Datatypes.length (ml_data m2)))%N eqn:Hl4. 2: inv Hupd4.
  unfold read_bytes, those, mem_lookup. cbn.
  apply N.ltb_lt in Hl1, Hl2, Hl3, Hl4. cbn in Hl1, Hl2, Hl3, Hl4.
  rewrite take_drop_is_set_nth in Hupd1. 2: lia.
  rewrite take_drop_is_set_nth in Hupd2. 2: lia.
  rewrite take_drop_is_set_nth in Hupd3. 2: lia.
  rewrite take_drop_is_set_nth in Hupd4. 2: lia.
  inv Hupd1. inv Hupd2. inv Hupd3. inv Hupd4.
  cbn in *. repeat rewrite -> take_drop_is_set_nth; try lia.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  rewrite N.add_0_r.
  assert (He: exists e, nth_error (ml_data (meminst_data m)) (N.to_nat addr) = Some e). {
    apply notNone_Some. intro Hcontra.
    apply nth_error_Some in Hcontra; lia.
  } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b1 (ml_data (meminst_data m)) (N.to_nat addr) b1)
  (N.to_nat (addr + 1)) = Some e). { apply notNone_Some.
   intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b2
     (set_nth b1 (ml_data (meminst_data m)) (N.to_nat (addr)) b1)
     (N.to_nat (addr + 1)) b2)
  (N.to_nat (addr + 2)) = Some e). {
    apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b3
     (set_nth b2
        (set_nth b1 (ml_data (meminst_data m)) (N.to_nat addr)
           b1) (N.to_nat (addr + 1)) b2)
     (N.to_nat (addr + 2)) b3)
  (N.to_nat (addr + 3)) = Some e).
  { apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same; try lia; auto. eassumption.
Qed.

Lemma store_load_i64 : forall m m' addr v,
length v = 8 ->
store m addr 0%N v 8 = Some m' ->
load_i64 m' addr = Some (wasm_deserialise v T_i64).
Proof.
  intros. assert (mem_length m = mem_length m').
  { rewrite <- H in H0. now eapply mem_store_preserves_length. }
   unfold store in H. unfold store in H0.
  destruct ((addr + 0 + N.of_nat 8 <=? mem_length m)%N) eqn:Heq. 2: inv H0.
  unfold load_i64. unfold load. cbn. cbn in Heq. unfold store in H0.
  assert (Hbytes: exists b1 b2 b3 b4 b5 b6 b7 b8, v = [b1; b2; b3; b4; b5; b6; b7; b8]). {
    destruct v. inv H. destruct v. inv H.
    destruct v. inv H. destruct v. inv H.
    destruct v. inv H. destruct v. inv H.
    destruct v. inv H. destruct v. inv H. destruct v.
    exists b, b0, b1, b2, b3, b4, b5, b6. reflexivity. inv H. }
  destruct Hbytes as [b1 [b2 [b3 [b4 [b5 [b6 [b7 [b8 Hb]]]]]]]]. subst v. clear H.
  rewrite N.add_0_r. rewrite N.add_0_r in Heq, H0.
  unfold write_bytes in H0. cbn in H0. rewrite N.add_0_r in H0.
  destruct (mem_update addr b1 (meminst_data m)) eqn:Hupd1. 2: inv H0.
  destruct (mem_update (addr + 1)%N b2 m0) eqn:Hupd2. 2: inv H0.
  destruct (mem_update (addr + 2)%N b3 m1) eqn:Hupd3. 2: inv H0.
  destruct (mem_update (addr + 3)%N b4 m2) eqn:Hupd4. 2: inv H0.
  destruct (mem_update (addr + 4)%N b5 m3) eqn:Hupd5. 2: inv H0.
  destruct (mem_update (addr + 5)%N b6 m4) eqn:Hupd6. 2: inv H0.
  destruct (mem_update (addr + 6)%N b7 m5) eqn:Hupd7. 2: inv H0.
  destruct (mem_update (addr + 7)%N b8 m6) eqn:Hupd8. 2: inv H0.
  inv H0. cbn. unfold mem_length, memory_list.mem_length. cbn.
  have Hu1 := mem_update_length _ _ _ _ Hupd1.
  have Hu2 := mem_update_length _ _ _ _ Hupd2.
  have Hu3 := mem_update_length _ _ _ _ Hupd3.
  have Hu4 := mem_update_length _ _ _ _ Hupd4.
  have Hu5 := mem_update_length _ _ _ _ Hupd5.
  have Hu6 := mem_update_length _ _ _ _ Hupd6.
  have Hu7 := mem_update_length _ _ _ _ Hupd7.
  have Hu8 := mem_update_length _ _ _ _ Hupd8.
  rewrite -Hu8 -Hu7 -Hu6 -Hu5 -Hu4 -Hu3 -Hu2 -Hu1.
  cbn. rewrite Heq.
  apply N.leb_le in Heq.
  unfold mem_update in Hupd1, Hupd2, Hupd3, Hupd4, Hupd5, Hupd6, Hupd7, Hupd8.
  destruct (addr     <? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N eqn:Hl1. 2: inv Hupd1.
  destruct (addr + 1 <? N.of_nat (Datatypes.length (ml_data m0)))%N eqn:Hl2. 2: inv Hupd2.
  destruct (addr + 2 <? N.of_nat (Datatypes.length (ml_data m1)))%N eqn:Hl3. 2: inv Hupd3.
  destruct (addr + 3 <? N.of_nat (Datatypes.length (ml_data m2)))%N eqn:Hl4. 2: inv Hupd4.
  destruct (addr + 4 <? N.of_nat (Datatypes.length (ml_data m3)))%N eqn:Hl5. 2: inv Hupd5.
  destruct (addr + 5 <? N.of_nat (Datatypes.length (ml_data m4)))%N eqn:Hl6. 2: inv Hupd6.
  destruct (addr + 6 <? N.of_nat (Datatypes.length (ml_data m5)))%N eqn:Hl7. 2: inv Hupd7.
  destruct (addr + 7 <? N.of_nat (Datatypes.length (ml_data m6)))%N eqn:Hl8. 2: inv Hupd8.
  unfold read_bytes, those, mem_lookup. cbn.
  apply N.ltb_lt in Hl1, Hl2, Hl3, Hl4, Hl5, Hl6, Hl7, Hl8. cbn in Hl1, Hl2, Hl3, Hl4, Hl5, Hl6, Hl7, Hl8.
  rewrite take_drop_is_set_nth in Hupd1. 2: lia.
  rewrite take_drop_is_set_nth in Hupd2. 2: lia.
  rewrite take_drop_is_set_nth in Hupd3. 2: lia.
  rewrite take_drop_is_set_nth in Hupd4. 2: lia.
  rewrite take_drop_is_set_nth in Hupd5. 2: lia.
  rewrite take_drop_is_set_nth in Hupd6. 2: lia.
  rewrite take_drop_is_set_nth in Hupd7. 2: lia.
  rewrite take_drop_is_set_nth in Hupd8. 2: lia.
  inv Hupd1. inv Hupd2. inv Hupd3. inv Hupd4.
  inv Hupd5. inv Hupd6. inv Hupd7. inv Hupd8.
  cbn in *. repeat rewrite -> take_drop_is_set_nth; try lia.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  rewrite N.add_0_r.
  assert (He: exists e, nth_error (ml_data (meminst_data m)) (N.to_nat addr) = Some e). {
    apply notNone_Some. intro Hcontra.
    apply nth_error_Some in Hcontra; lia.
  } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b1 (ml_data (meminst_data m)) (N.to_nat addr) b1)
  (N.to_nat (addr + 1)) = Some e). { apply notNone_Some.
   intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b2
     (set_nth b1 (ml_data (meminst_data m)) (N.to_nat (addr)) b1)
     (N.to_nat (addr + 1)) b2)
  (N.to_nat (addr + 2)) = Some e). {
    apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b3
     (set_nth b2
        (set_nth b1 (ml_data (meminst_data m)) (N.to_nat addr)
           b1) (N.to_nat (addr + 1)) b2)
     (N.to_nat (addr + 2)) b3)
  (N.to_nat (addr + 3)) = Some e).
  { apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
                     (set_nth b4
  (set_nth b3
     (set_nth b2
        (set_nth b1 (ml_data (meminst_data m))
           (N.to_nat addr) b1)
        (N.to_nat (addr + 1)) b2)
     (N.to_nat (addr + 2)) b3)
  (N.to_nat (addr + 3)) b4)
                     (N.to_nat (addr + 4))
                   = Some e).
  { apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).

  assert (He: exists e, nth_error
                     (set_nth b5
                     (set_nth b4
  (set_nth b3
     (set_nth b2
        (set_nth b1 (ml_data (meminst_data m))
           (N.to_nat addr) b1)
        (N.to_nat (addr + 1)) b2)
     (N.to_nat (addr + 2)) b3)
  (N.to_nat (addr + 3)) b4)
                     (N.to_nat (addr + 4)) b5)
                     (N.to_nat (addr + 5))
                   = Some e).
  { apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
                     (set_nth b6
                     (set_nth b5
                     (set_nth b4
  (set_nth b3
     (set_nth b2
        (set_nth b1 (ml_data (meminst_data m))
           (N.to_nat addr) b1)
        (N.to_nat (addr + 1)) b2)
     (N.to_nat (addr + 2)) b3)
  (N.to_nat (addr + 3)) b4)
                     (N.to_nat (addr + 4)) b5)
                     (N.to_nat (addr + 5)) b6)
                     (N.to_nat (addr + 6))
                   = Some e).
  { apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).

  assert (He: exists e, nth_error
                     (set_nth b7
                     (set_nth b6
                     (set_nth b5
                     (set_nth b4
  (set_nth b3
     (set_nth b2
        (set_nth b1 (ml_data (meminst_data m))
           (N.to_nat addr) b1)
        (N.to_nat (addr + 1)) b2)
     (N.to_nat (addr + 2)) b3)
  (N.to_nat (addr + 3)) b4)
                     (N.to_nat (addr + 4)) b5)
                     (N.to_nat (addr + 5)) b6)
                     (N.to_nat (addr + 6)) b7)
                     (N.to_nat (addr + 7))
                   = Some e).
  { apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.

  erewrite set_nth_nth_error_same; try lia; auto. eassumption.
Qed.


Lemma enough_space_to_load m k :
  (k + 4 <= mem_length m)%N -> exists v, load_i32 m k = Some v.
Proof.
  intros. unfold load_i32, load.
  assert ((k + (0 + N.of_nat 4) <=? mem_length m)%N). { apply N.leb_le. lia. } rewrite H0.
  unfold read_bytes, those, mem_lookup. cbn.
  apply N.leb_le in H0. unfold mem_length, memory_list.mem_length in H0.
  assert (Hex1 : exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 0)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex1 as [x1 Hex1]. rewrite Hex1.
  assert (Hex2: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 1)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex2 as [x2 Hex2]. rewrite Hex2.
  assert (Hex3: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 2)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex3 as [x3 Hex3]. rewrite Hex3.
  assert (Hex4: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 3)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex4 as [x4 Hex4]. rewrite Hex4.
   eauto.
Qed.

Lemma enough_space_to_load_i64 m k :
  (k + 8 <= mem_length m)%N -> exists v, load_i64 m k = Some v.
Proof.
  intros. unfold load_i64, load.
  assert ((k + (0 + N.of_nat 8) <=? mem_length m)%N). { apply N.leb_le. lia. } rewrite H0.
  unfold read_bytes, those, mem_lookup. cbn.
  apply N.leb_le in H0. unfold mem_length, memory_list.mem_length in H0.
  assert (Hex1 : exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 0)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex1 as [x1 Hex1]. rewrite Hex1.
  assert (Hex2: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 1)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex2 as [x2 Hex2]. rewrite Hex2.
  assert (Hex3: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 2)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex3 as [x3 Hex3]. rewrite Hex3.
  assert (Hex4: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 3)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex4 as [x4 Hex4]. rewrite Hex4.
  assert (Hex5: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 4)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex5 as [x5 Hex5]. rewrite Hex5.
  assert (Hex6: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 5)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex6 as [x6 Hex6]. rewrite Hex6.
  assert (Hex7: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 6)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex7 as [x7 Hex7]. rewrite Hex7.
  assert (Hex8: exists v, nth_error (ml_data (meminst_data m)) (N.to_nat (k + 0 + 7)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex8 as [x8 Hex8]. rewrite Hex8.
  eauto.
Qed.

(* kept for compatability, TODO remove *)
Definition mem_max_opt := fun m => m.(meminst_type).(lim_max).

Lemma mem_store_preserves_max_pages : forall (m m' : meminst) v x l,
   store m x 0%N v l = Some m' ->
   mem_max_opt m = mem_max_opt m'.
Proof.
  intros.
  unfold store in H.
  destruct ((x + 0 + N.of_nat l <=? mem_length m)%N). 2 : inv H.
  unfold write_bytes in H.
  destruct (fold_lefti _ _ _) ; by inversion H.
Qed.

Lemma mem_grow_increases_length : forall m m' sgrow,
  mem_grow m sgrow = Some m' ->
  mem_length m' = ((sgrow * 65536) + mem_length m)%N.
Proof.
  intros. unfold mem_grow in H.
  destruct ((mem_size m + sgrow <=? page_limit)%N) eqn:Hari; rewrite Hari in H.
  2: inv H.
  destruct (lim_max (meminst_type m)) eqn:Hmaxpages.
  (* mem_max_opt = Some n0 *)
  destruct (mem_size m + sgrow <=? u)%N; inv H.
  unfold mem_length. unfold memory_list.mem_length.
  rewrite app_length. rewrite Nat2N.inj_add.
  rewrite N.add_comm. rewrite repeat_length. unfold page_size. lia.
  inv H.
  unfold mem_length, memory_list.mem_length. cbn. rewrite app_length.
  rewrite repeat_length. unfold page_size. lia.
Qed.

Lemma mem_grow_increases_size : forall m m' sgrow,
  mem_grow m sgrow = Some m' ->
  mem_size m' = (sgrow + mem_size m)%N.
Proof.
  intros. unfold mem_grow in H.
  destruct ((mem_size m + sgrow <=? page_limit)%N) eqn:Hari;
    rewrite Hari in H. 2: inv H.
  destruct (lim_max (meminst_type m)) eqn:Hmaxpages; cbn in H.
  (* mem_max_opt = Some n0 *)
  destruct (mem_size m + sgrow <=? u)%N. 2: inv H. inv H.
  unfold mem_size. unfold mem_length. unfold memory_list.mem_length.
  rewrite app_length. rewrite Nat2N.inj_add.
  rewrite N.add_comm. unfold page_size. rewrite <- N.div_add_l. 2: intro; lia.
  remember (N.of_nat (Datatypes.length (memory_list.ml_data (meminst_data m)))) as len.
  rewrite repeat_length. rewrite N2Nat.id.
  replace (sgrow * (64 * 1024))%N with (sgrow * 65536)%N; reflexivity.
  (* mem_max_opt = None *)
  inv H. unfold mem_size. unfold mem_length. unfold memory_list.mem_length.
  rewrite app_length. rewrite Nat2N.inj_add.
  rewrite N.add_comm. unfold page_size. rewrite <- N.div_add_l. 2: intro; lia.
  remember (N.of_nat (Datatypes.length (memory_list.ml_data (meminst_data m)))) as len.
  rewrite repeat_length. lia.
Qed.

Lemma mem_grow_preserves_max_pages : forall n m m' bytes,
  mem_grow m bytes = Some m' ->
  mem_max_opt m = Some n ->
  mem_max_opt m' = Some n.
Proof.
  intros. unfold mem_grow in H.
  destruct ((mem_size m + bytes <=? mem_limit_bound)%N). 2: inv H. cbn in H.
  unfold mem_max_opt in H0. rewrite H0 in H.
  destruct ((mem_size m + bytes <=? n)%N). 2: inv H. inv H. reflexivity.
Qed.

Lemma smem_grow_preserves_funcs : forall sr fr bytes sr' size,
  smem_grow sr (f_inst fr) bytes = Some (sr', size) ->
  s_funcs sr = s_funcs sr'.
Proof.
  intros. unfold smem_grow in H.
  destruct (lookup_N (inst_mems (f_inst fr)) 0)=>//.
  destruct (lookup_N (s_mems sr) m)=>//.
  destruct (mem_grow m0 bytes)=>//. inv H. reflexivity.
Qed.

Lemma smem_grow_peserves_globals : forall sr fr bytes sr' size var,
  smem_grow sr (f_inst fr) bytes = Some (sr', size) ->
  sglob_val sr (f_inst fr) var = sglob_val sr' (f_inst fr) var.
Proof.
  intros. unfold smem_grow in H.
  destruct (lookup_N (inst_mems (f_inst fr)) 0)=>//.
  destruct (lookup_N (s_mems sr) m)=>//.
  destruct (mem_grow m0 bytes)=>//. inv H. reflexivity.
Qed.

Lemma mem_grow_preserves_original_values : forall a m m' maxlim,
  (mem_max_opt m = Some maxlim)%N ->
  (maxlim <= page_limit)%N ->
  (mem_size m + 1 <= maxlim)%N ->
  mem_grow m 1 = Some m' ->
  (a + 8 <= mem_length m)%N ->
  load_i32 m a = load_i32 m' a /\ load_i64 m a = load_i64 m' a.
Proof.
  intros ? ? ? ? Hlim1 Hlim2 Hlim3 Hgrow Ha.
  have Hg := Hgrow. apply mem_grow_increases_length in Hg.
  unfold mem_grow in Hgrow.
  assert (Hlim4: (mem_size m + 1 <= page_limit)%N) by lia. apply N.leb_le in Hlim4, Hlim3.
  rewrite Hlim4 in Hgrow. unfold mem_max_opt in Hlim1.
  rewrite Hlim1 in Hgrow. rewrite Hlim3 in Hgrow. inv Hgrow.
  assert (Hlen: (a + 8 <=?
     mem_length {| meminst_data := {| ml_init := ml_init (meminst_data m);
                                  ml_data := ml_data (meminst_data m) ++
                                             repeat (ml_init (meminst_data m)) (Pos.to_nat 65536) |};
                  meminst_type := {| lim_min := (mem_size m + 1)%N; lim_max := Some maxlim |} |})%N). {
    unfold mem_length, memory_list.mem_length. cbn. rewrite app_length. rewrite repeat_length.
    unfold mem_length, memory_list.mem_length in Ha. apply N.leb_le. lia. }
  remember ((mem_length {| meminst_data := {| ml_init := ml_init (meminst_data m);
                                  ml_data := ml_data (meminst_data m) ++
                                             repeat (ml_init (meminst_data m)) (Pos.to_nat 65536) |};
                  meminst_type := {| lim_min := (mem_size m + 1)%N; lim_max := Some maxlim |} |})%N) as mem_len.
  split.
  - assert (Ha': (a+4 <= mem_length m)%N) by lia.
    unfold load_i32, load, memory_list.mem_grow, read_bytes, those. cbn.
    apply N.leb_le in Ha'. rewrite Ha'. apply N.leb_le in Ha'.
    assert (Hlen': (a + 4 <=? mem_len)%N). { apply N.leb_le in Hlen. apply N.leb_le. lia. }
    rewrite -Heqmem_len. rewrite Hlen'.
    unfold mem_length, memory_list.mem_length in Ha'.
    unfold mem_lookup.
    repeat rewrite nth_error_app1; try lia. reflexivity.
  - unfold load_i64, load, memory_list.mem_grow, read_bytes, those. cbn.
    rewrite -Heqmem_len. rewrite Hlen.
    apply N.leb_le in Ha. rewrite Ha. apply N.leb_le in Ha.
    unfold mem_length, memory_list.mem_length in Ha.
    unfold mem_lookup.
    repeat rewrite nth_error_app1; try lia. reflexivity.
Qed.

Lemma mem_length_upper_bound : forall m,
  (mem_size m <= max_mem_pages)%N ->
  (mem_length m <= (max_mem_pages + 1) * page_size)%N.
Proof.
  intros.
  unfold mem_size, page_size in H. unfold page_size. cbn in *.
  remember (mem_length m) as n. clear Heqn m.
  assert (Z.of_N n / 65536 <= Z.of_N max_mem_pages)%Z as Hn by lia. clear H.
  unfold max_mem_pages in Hn.
  assert (Hs: (65536 > 0)%Z) by lia.
  destruct (Zdiv_eucl_exist Hs (Z.of_N n)) as [[z z0] [H1 H2]].
  rewrite H1 in Hn.
  rewrite Z.add_comm in Hn.
  rewrite Z.mul_comm in Hn.
  rewrite Z.div_add in Hn; try lia.
  rewrite Zdiv_small in Hn; lia.
Qed.

Ltac solve_arith_load_store :=
  repeat (try rewrite length_is_size; try rewrite size_set_nth;
          try rewrite maxn_nat_max;
          try rewrite Nat2N.inj_max;
          try apply N.ltb_lt; try apply N.leb_le;
          try (apply N.max_lt_iff; right); try (apply Nat.max_lt_iff; right);
          rewrite -length_is_size; try lia).

Ltac assert_store_condition_and_rewrite Hname :=
  match goal with
  | [H : context[match (if ?E then _ else _) with | Some _ => _ | None => _ end] |- _] =>
      let H' := fresh Hname in
      assert E as H' by solve_arith_load_store;
      rewrite H' in H;
      try rewrite take_drop_is_set_nth in H;
      solve_arith_load_store
  end.


Lemma load_store_load_i32 : forall m m' a1 a2 v w,
  length w = 4 ->
  (a1 + 4 <= a2)%N ->
  load_i32 m a1 = Some v ->
  store m a2 0%N w 4 = Some m' ->
  load_i32 m' a1 = Some v.
Proof.
  intros ? ? ? ? ? ? Hlw Harith Hload Hstore.
  cbn in Harith. unfold store in Hstore.
  destruct (a2 + 0 + N.of_nat 4 <=? mem_length m)%N eqn:Ha. 2: inv Hstore.
  apply N.leb_le in Ha. cbn in Ha. unfold mem_length, memory_list.mem_length in Ha.
  destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw. destruct w.
  inv Hlw. destruct w. 2: inv Hlw. clear Hlw. unfold write_bytes in Hstore. cbn in Hstore.
  unfold mem_update in Hstore. cbn in Hstore.
  destruct (a2 + 0 + 0 <? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N eqn:Ha1.
  2: discriminate. cbn in Hstore. rewrite take_drop_is_set_nth in Hstore; try lia.
  rewrite take_drop_is_set_nth in Hstore. 2: solve_arith_load_store.
  assert_store_condition_and_rewrite Ha2.
  assert_store_condition_and_rewrite Ha3.
  assert_store_condition_and_rewrite Ha4.
  inv Hstore.

  unfold load_i32, load in *. cbn. unfold mem_length, memory_list.mem_length in *. cbn in *.
  destruct ((a1 + 4 <=? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N) eqn:Hr1. 2: discriminate.
  cbn in Ha4. unfold read_bytes, those, mem_lookup in Hload. cbn in Hload.

  destruct (nth_error (ml_data (meminst_data m))
              (N.to_nat (a1 + 0 + 0))) eqn:Hl1. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 1))) eqn:Hl2. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 2))) eqn:Hl3. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 3))) eqn:Hl4. 2: discriminate.
                cbn in Hload. rewrite -Hload.

  rewrite length_is_size in Ha2. rewrite size_set_nth in Ha2.
  rewrite maxn_nat_max in Ha2.
  assert ((a1 + 4 <=?
     N.of_nat
       (Datatypes.length
          (set_nth b2
             (set_nth b1
                (set_nth b0
                   (set_nth b (ml_data (meminst_data m))
                      (N.to_nat (a2 + 0 + 0)) b) (N.to_nat (a2 + 0 + 1)) b0) (N.to_nat (a2 + 0 + 2)) b1)
             (N.to_nat (a2 + 0 + 3)) b2)))%N) as Hdf by solve_arith_load_store. rewrite Hdf. cbn.

  unfold read_bytes, those, mem_lookup. cbn.
  repeat rewrite set_nth_nth_error_other; try by lia.
  rewrite Hl1 Hl2 Hl3 Hl4. reflexivity. all: solve_arith_load_store.
Qed.


(* TODO: The following helper lemmas may be removed in the future
   once the new memory model in WasmCert has been finalized.
   Then reduce verbosity.
*)
Lemma load_store_load_i32' : forall m m' a1 a2 v w,
  length w = 8 ->
  (a1 + 4 <= a2)%N ->
  load_i32 m a1 = Some v ->
  store m a2 0%N w 8 = Some m' ->
  load_i32 m' a1 = Some v.
Proof.
  intros ? ? ? ? ? ? Hlw Harith Hload Hstore.
  cbn in Harith. unfold store in Hstore.
  destruct (a2 + 0 + N.of_nat 8 <=? mem_length m)%N eqn:Ha. 2: inv Hstore.
  apply N.leb_le in Ha. cbn in Ha. unfold mem_length, memory_list.mem_length in Ha.
  destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw.
  destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw.
  destruct w. 2: inv Hlw.
  clear Hlw. unfold write_bytes in Hstore. cbn in Hstore.
  unfold mem_update in Hstore. cbn in Hstore.
  destruct (a2 + 0 + 0 <? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N eqn:Ha1.
  2: { apply N.ltb_nlt in Ha1. lia. }
  cbn in Hstore. rewrite take_drop_is_set_nth in Hstore; try lia.
  rewrite take_drop_is_set_nth in Hstore. 2: solve_arith_load_store.
  assert_store_condition_and_rewrite Ha2.
  assert_store_condition_and_rewrite Ha3.
  assert_store_condition_and_rewrite Ha4.
  assert_store_condition_and_rewrite Ha5.
  assert_store_condition_and_rewrite Ha6.
  assert_store_condition_and_rewrite Ha7.
  assert_store_condition_and_rewrite Ha8.
  inv Hstore.

  unfold load_i32, load in *. cbn. unfold mem_length, memory_list.mem_length in *. cbn in *.
  destruct ((a1 + 4 <=? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N) eqn:Hr1. 2: discriminate.
  cbn in Ha8. unfold read_bytes, those, mem_lookup in Hload. cbn in Hload.

  destruct (nth_error (ml_data (meminst_data m))
              (N.to_nat (a1 + 0 + 0))) eqn:Hl1. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 1))) eqn:Hl2. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 2))) eqn:Hl3. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
              (N.to_nat (a1 + 0 + 3))) eqn:Hl4. 2: discriminate.
  cbn in Hload. rewrite -Hload.

  rewrite length_is_size in Ha3. rewrite size_set_nth in Ha3.
  rewrite maxn_nat_max in Ha3.

  assert ((a1 + 4 <=?
             N.of_nat (Datatypes.length
                         (set_nth b6
                         (set_nth b5
                         (set_nth b4
                         (set_nth b3
                         (set_nth b2
                       (set_nth b1
                          (set_nth b0
                             (set_nth b (ml_data (meminst_data m))
                                (N.to_nat (a2 + 0 + 0)) b)
                             (N.to_nat (a2 + 0 + 1)) b0)
                          (N.to_nat (a2 + 0 + 2)) b1)
                       (N.to_nat (a2 + 0 + 3)) b2)
                         (N.to_nat (a2 + 0 + 4)) b3)
                         (N.to_nat (a2 + 0 + 5)) b4)
                         (N.to_nat (a2 + 0 + 6)) b5)
               (N.to_nat (a2 + 0 + 7)) b6)))%N) as Hdf by solve_arith_load_store.
  rewrite Hdf. cbn.

  unfold read_bytes, those, mem_lookup. cbn.
  repeat rewrite set_nth_nth_error_other; try by lia.
  cbn.
  rewrite Hl1 Hl2 Hl3 Hl4. cbn. reflexivity. all: solve_arith_load_store.
Qed.


Lemma load_store_load_i64 : forall m m' a1 a2 v w,
  length w = 4 ->
  (a1 + 8 <= a2)%N ->
  load_i64 m a1 = Some v ->
  store m a2 0%N w 4 = Some m' ->
  load_i64 m' a1 = Some v.
Proof.
  intros ? ? ? ? ? ? Hlw Harith Hload Hstore.
  cbn in Harith. unfold store in Hstore.
  destruct (a2 + 0 + N.of_nat 4 <=? mem_length m)%N eqn:Ha. 2: inv Hstore.
  apply N.leb_le in Ha. cbn in Ha. unfold mem_length, memory_list.mem_length in Ha.
  destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw. destruct w.
  inv Hlw. destruct w. 2: inv Hlw.
  clear Hlw. unfold write_bytes in Hstore. cbn in Hstore.
  unfold mem_update in Hstore. cbn in Hstore.
  destruct (a2 + 0 + 0 <? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N eqn:Ha1.
  2: { apply N.ltb_nlt in Ha1. lia. }
  cbn in Hstore. rewrite take_drop_is_set_nth in Hstore; try lia.
  rewrite take_drop_is_set_nth in Hstore. 2: solve_arith_load_store.
  assert_store_condition_and_rewrite Ha2.
  assert_store_condition_and_rewrite Ha3.
  assert_store_condition_and_rewrite Ha4.
  inv Hstore.

  unfold load_i64, load in *. cbn. unfold mem_length, memory_list.mem_length in *. cbn in *.
  destruct ((a1 + 8 <=? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N) eqn:Hr1. 2: discriminate.
  cbn in Ha4. unfold read_bytes, those, mem_lookup in Hload. cbn in Hload.

  destruct (nth_error (ml_data (meminst_data m))
              (N.to_nat (a1 + 0 + 0))) eqn:Hl1. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 1))) eqn:Hl2. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 2))) eqn:Hl3. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 3))) eqn:Hl4. 2: discriminate.
                cbn in Hload. rewrite -Hload.

  rewrite length_is_size in Ha2. rewrite size_set_nth in Ha2.
  rewrite maxn_nat_max in Ha2.
  assert ((a1 + 8 <=?
     N.of_nat
       (Datatypes.length
          (set_nth b2
             (set_nth b1
                (set_nth b0
                   (set_nth b (ml_data (meminst_data m))
                      (N.to_nat (a2 + 0 + 0)) b) (N.to_nat (a2 + 0 + 1)) b0) (N.to_nat (a2 + 0 + 2)) b1)
             (N.to_nat (a2 + 0 + 3)) b2)))%N) as Hdf by solve_arith_load_store. rewrite Hdf. cbn.

  unfold read_bytes, those, mem_lookup. cbn.
  repeat rewrite set_nth_nth_error_other; try by lia.
  rewrite Hl1 Hl2 Hl3 Hl4. reflexivity. all: solve_arith_load_store.
Qed.

Lemma load_store_load_i64' : forall m m' a1 a2 v w,
  length w = 8 ->
  (a1 + 8 <= a2)%N ->
  load_i64 m a1 = Some v ->
  store m a2 0%N w 8 = Some m' ->
  load_i64 m' a1 = Some v.
Proof.
  intros ? ? ? ? ? ? Hlw Harith Hload Hstore.
  cbn in Harith. unfold store in Hstore.
  destruct (a2 + 0 + N.of_nat 8 <=? mem_length m)%N eqn:Ha. 2: inv Hstore.
  apply N.leb_le in Ha. cbn in Ha. unfold mem_length, memory_list.mem_length in Ha.
  destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw.
  destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw.
  destruct w. 2: inv Hlw.
  clear Hlw. unfold write_bytes in Hstore. cbn in Hstore.
  unfold mem_update in Hstore. cbn in Hstore.
  destruct (a2 + 0 + 0 <? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N eqn:Ha1.
  2: { apply N.ltb_nlt in Ha1. lia. }
  cbn in Hstore. rewrite take_drop_is_set_nth in Hstore; try lia.
  rewrite take_drop_is_set_nth in Hstore. 2: solve_arith_load_store.
  assert_store_condition_and_rewrite Ha2.
  assert_store_condition_and_rewrite Ha3.
  assert_store_condition_and_rewrite Ha4.
  assert_store_condition_and_rewrite Ha5.
  assert_store_condition_and_rewrite Ha6.
  assert_store_condition_and_rewrite Ha7.
  assert_store_condition_and_rewrite Ha8.
  inv Hstore.

  unfold load_i64, load in *. cbn. unfold mem_length, memory_list.mem_length in *. cbn in *.
  destruct ((a1 + 8 <=? N.of_nat (Datatypes.length (ml_data (meminst_data m))))%N) eqn:Hr1. 2: discriminate.
  cbn in Ha8. unfold read_bytes, those, mem_lookup in Hload. cbn in Hload.

  destruct (nth_error (ml_data (meminst_data m))
              (N.to_nat (a1 + 0 + 0))) eqn:Hl1. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 1))) eqn:Hl2. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 2))) eqn:Hl3. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
              (N.to_nat (a1 + 0 + 3))) eqn:Hl4. 2: discriminate.

  destruct (nth_error (ml_data (meminst_data m))
              (N.to_nat (a1 + 0 + 4))) eqn:Hl5. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
              (N.to_nat (a1 + 0 + 5))) eqn:Hl6. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
              (N.to_nat (a1 + 0 + 6))) eqn:Hl7. 2: discriminate.
  destruct (nth_error (ml_data (meminst_data m))
                (N.to_nat (a1 + 0 + 7))) eqn:Hl8. 2: discriminate.

  cbn in Hload. rewrite -Hload.

  rewrite length_is_size in Ha3. rewrite size_set_nth in Ha3.
  rewrite maxn_nat_max in Ha3.

  assert ((a1 + 8 <=?
             N.of_nat (Datatypes.length
                         (set_nth b6
                         (set_nth b5
                         (set_nth b4
                         (set_nth b3
                         (set_nth b2
                       (set_nth b1
                          (set_nth b0
                             (set_nth b (ml_data (meminst_data m))
                                (N.to_nat (a2 + 0 + 0)) b)
                             (N.to_nat (a2 + 0 + 1)) b0)
                          (N.to_nat (a2 + 0 + 2)) b1)
                       (N.to_nat (a2 + 0 + 3)) b2)
                         (N.to_nat (a2 + 0 + 4)) b3)
                         (N.to_nat (a2 + 0 + 5)) b4)
                         (N.to_nat (a2 + 0 + 6)) b5)
               (N.to_nat (a2 + 0 + 7)) b6)))%N) as Hdf by solve_arith_load_store.
  rewrite Hdf. cbn.

  unfold read_bytes, those, mem_lookup. cbn.
  repeat rewrite set_nth_nth_error_other; try by lia.
  cbn.
  rewrite Hl1 Hl2 Hl3 Hl4 Hl5 Hl6 Hl7 Hl8. cbn. reflexivity. all: solve_arith_load_store.
Qed.


(* taken from iriswasm *)
Lemma deserialise_bits v t :
  typeof_num v == t -> wasm_deserialise (bits v) t = v.
Proof.
  intros Htv.
  unfold wasm_deserialise.
  destruct t ;
    unfold bits ;
    destruct v ; (try by inversion Htv).
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int32.repr_unsigned.
  destruct s ; simpl; replace (two_power_pos _)
    with Wasm_int.Int32.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int64.repr_unsigned.
  destruct s ; simpl ; replace (two_power_pos _)
    with Wasm_int.Int64.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int_4.
  by rewrite Wasm_float.FloatSize32.of_to_bits.
  rewrite Memdata.decode_encode_int_8.
  by rewrite Wasm_float.FloatSize64.of_to_bits.
Qed.

(* global vars *)

Lemma update_global_get_same : forall sr sr' i val fr,
  supdate_glob sr (f_inst fr) i (VAL_num (VAL_int32 val)) = Some sr' ->
     sglob_val sr' (f_inst fr) i = Some (VAL_num (VAL_int32 val)).
Proof.
  unfold supdate_glob, supdate_glob_s, sglob_val, sglob, sglob_ind. cbn. intros.
  destruct (lookup_N (inst_globals (f_inst fr)) i) eqn:H1. 2: inv H. cbn in H.
  destruct (lookup_N (s_globals sr) g) eqn:H2. 2: inv H. inv H. cbn.
  unfold lookup_N.
  erewrite set_nth_nth_error_same; auto. eassumption.
Qed.

Lemma update_global_get_other : forall i j sr sr' fr num val,
  NoDup (inst_globals (f_inst fr)) ->
  i <> j ->
  sglob_val sr (f_inst fr) i = Some (VAL_num (VAL_int32 val)) ->
  supdate_glob sr (f_inst fr) j (VAL_num (VAL_int32 num)) = Some sr' ->
  sglob_val sr' (f_inst fr) i = Some (VAL_num (VAL_int32 val)).
Proof.
  intros ? ? ? ? ? ? ? Hnodup Hneq Hr Hw.
    unfold supdate_glob, sglob_ind, supdate_glob_s in *.
    destruct (lookup_N (inst_globals (f_inst fr)) j) eqn:Heqn. 2: inv Hw. cbn in Hw.
    destruct (lookup_N (s_globals sr) g) eqn:Heqn'. 2: inv Hw. inv Hw.
    unfold sglob_val, sglob, sglob_ind in *.
    destruct (lookup_N (inst_globals (f_inst fr)) i) eqn:Heqn''.  2: inv Hr.
    cbn. cbn in Hr.
    assert (g <> g1). {
      intro. subst. rewrite <- Heqn'' in Heqn.
      apply Hneq. unfold lookup_N in Heqn, Heqn''.
      eapply NoDup_nth_error in Heqn; eauto. lia.
      apply nth_error_Some. congruence. }
    unfold lookup_N in *.
    erewrite set_nth_nth_error_other; auto; try lia.
     assert (N.to_nat g < length (s_globals sr)) as Hl. { apply nth_error_Some. intro. congruence. }
    lia.
Qed.

(* TODO get rid of, shouldn't be needed *)
Lemma update_global_preserves_memory' : forall sr sr' fr v j,
  supdate_glob sr (f_inst fr) j v = Some sr' ->
  sr.(s_mems) = sr'.(s_mems).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H. cbn in H.
  destruct (lookup_N (inst_globals (f_inst fr)) j). 2: inv H. cbn in H.
  destruct (lookup_N (s_globals sr) g). inv H. reflexivity. inv H.
Qed.

Lemma update_global_preserves_memory : forall sr sr' fr v j,
  supdate_glob sr (f_inst fr) j v = Some sr' ->
  smem sr (f_inst fr) = smem sr' (f_inst fr).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H. cbn in H.
  destruct (lookup_N (inst_globals (f_inst fr)) j). 2: inv H. cbn in H.
  destruct (lookup_N (s_globals sr) g). inv H. reflexivity. inv H.
Qed.

Lemma update_global_preserves_funcs : forall sr sr' fr v j,
  supdate_glob sr (f_inst fr) j v = Some sr' ->
  sr.(s_funcs) = sr'.(s_funcs).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H. cbn in H.
  destruct (lookup_N (inst_globals (f_inst fr)) j). 2: inv H. cbn in H.
  destruct (lookup_N (s_globals sr) g). inv H. reflexivity. inv H.
Qed.

End Wasm.

Section Arith.


Ltac simpl_modulus_in H :=
  unfold Wasm_int.Int32.modulus, Wasm_int.Int32.half_modulus, two_power_nat in H; cbn in H.
Ltac simpl_modulus :=
  unfold Wasm_int.Int32.modulus, Wasm_int.Int32.half_modulus, two_power_nat.

Lemma signed_upper_bound : forall x,
  (Wasm_int.Int32.signed (Wasm_int.Int32.repr x) < Wasm_int.Int32.half_modulus)%Z.
Proof.
  intros x.
  unfold Wasm_int.Int32.signed. destruct (zlt _ _); auto.
  unfold Wasm_int.Int32.unsigned in *. clear g.
  have H' := Wasm_int.Int32.Z_mod_modulus_range x. simpl_modulus_in H'. simpl_modulus. cbn. lia.
Qed.

Lemma N_div_ge0 : forall a b, (b > 0)%N -> (a >= 0)%N -> (a / b >= 0)%N.
Proof.
  intros. assert (Z.of_N a / Z.of_N b >= 0)%Z. apply Z_div_ge0; lia. lia.
Qed.

(* taken from iriswasm *)
Lemma N_nat_bin n:
  n = N.of_nat (ssrnat.nat_of_bin n).
Proof.
  destruct n => //=.
  replace (ssrnat.nat_of_pos p) with (Pos.to_nat p); first by rewrite positive_nat_N.
  induction p => //=.
  - rewrite Pos2Nat.inj_xI.
    f_equal.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
  - rewrite Pos2Nat.inj_xO.
    rewrite IHp.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
Qed.

Lemma Z_nat_bin : forall x, Z.of_nat (ssrnat.nat_of_bin x) = Z.of_N x.
Proof.
  intros.
  have H := N_nat_bin x. lia.
Qed.

Lemma small_signed_repr_n_n : forall n,
  (0 <= n <= Z.of_N max_mem_pages)%Z->
  Wasm_int.Int32.signed (Wasm_int.Int32.repr n) = n.
Proof.
  intros n H. unfold max_mem_pages in H.
  unfold Wasm_int.Int32.signed. cbn.
  rewrite zlt_true.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
Qed.

Lemma exists_i32 : exists (v : i32), True.
Proof.
  exists (nat_to_i32 1). constructor.
Qed.

Lemma i32_exists_N : forall (x : i32),
  exists n, x = N_to_i32 n /\ (-1 < Z.of_N n < Wasm_int.Int32.modulus)%Z.
Proof.
  intros [val H]. exists (Z.to_N val). split; try lia.
  destruct (N_to_i32 (Z.to_N val)) eqn:He. inv He. revert intrange.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
  rewrite Z2N.id; try lia. intros.
  destruct H as [low high].
  destruct intrange as [low' high'].
  rewrite (Wasm_int.Int32.Z_lt_irrelevant low low').
  rewrite (Wasm_int.Int32.Z_lt_irrelevant high high'). reflexivity.
Qed.

Lemma default_vals_i32_Some : forall n,
  default_vals (repeat (T_num T_i32) n) = Some (repeat (VAL_num (nat_to_value 0)) n).
Proof.
  induction n=>//. unfold default_vals in *. cbn in *.
  rewrite -cat1s. rewrite <- (cat1s (VAL_num (nat_to_value 0))).
  apply those_cat=>//.
Qed.

End Arith.
