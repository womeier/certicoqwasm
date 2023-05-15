(*
  Proof of correctness of the WASM code generation phase of CertiCoq
  (based on the proof for Clight code generation)

  > Relates values to location in memory (syntactic)
  > Relates expression to statements (syntactic)
  > Relates Codegen values (header, payload) to Codegen values after GC (syntactic, up to non-function pointer location)
  > Relates LambdaANF states to Codegen states according to execution semantics

 *)
Unset Universe Checking.

From compcert Require Import Coqlib.

Require Import LambdaANF.cps LambdaANF.eval LambdaANF.cps_util LambdaANF.List_util LambdaANF.Ensembles_util LambdaANF.identifiers LambdaANF.tactics LambdaANF.shrink_cps_corresp.


Require Import Coq.ZArith.BinInt.
Require Import Lia.
Require Export Int31.

(* Require Import RamifyCoq.CertiGC.GCGraph. *)



Require Import Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String ExtLib.Data.List Coq.Program.Program  Coq.Sets.Ensembles Coq.Logic.Decidable Coq.Lists.ListDec Coq.Relations.Relations Relations.Relation_Operators.

Require Import compcert.common.AST
        compcert.common.Errors
        compcert.lib.Integers
        compcert.cfrontend.Cop
        compcert.cfrontend.Ctypes
        compcert.cfrontend.Clight
        compcert.common.Values
        compcert.common.Globalenvs
        compcert.common.Memory.

Require Import (* CodegenWASM.tactics *)
               Codegen.LambdaANF_to_Clight
               CodegenWASM.LambdaANF_to_WASM.

From Wasm Require Import datatypes datatypes_properties operations host interpreter_sound
                         binary_format_parser binary_format_printer check_toks instantiation
                         opsem interpreter_func interpreter_func_sound properties common.


Require Import Libraries.maps_util.

Open Scope list.



Definition gc_size:Z := Z.shiftl 1%Z 16%Z.
Definition loc:Type := block * ptrofs.


Notation intTy := (Tint I32 Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation uintTy := (Tint I32 Unsigned
                         {| attr_volatile := false; attr_alignas := None |}).

Notation longTy := (Tlong Signed
                        {| attr_volatile := false; attr_alignas := None |}).

Notation ulongTy := (Tlong Unsigned
                           {| attr_volatile := false; attr_alignas := None |}).
Notation boolTy := (Tint IBool Unsigned noattr).



(* from CLight : TODO wasm *)
Definition int_chunk := Mint32.
Definition val := uintTy. (* NOTE: in Clight, SIZEOF_PTR == SIZEOF_INT *)
Definition uval := uintTy.
Definition sval := intTy.
Definition val_typ := Tany32:typ.
Definition Init_int x := Init_int32 (Int.repr x).
Definition make_vint z := Vint (Int.repr z).
Definition make_cint z t := Econst_int (Int.repr z) t.
Transparent val.
Transparent uval.
Transparent val_typ.
Transparent Init_int.
Transparent make_vint.
Transparent make_cint.


Import ListNotations.

 Definition int_size := 32%Z.
Definition max_args := 1024%Z. (* limited by space in boxed header *)


Theorem int_size_pos:
  (0 <= size_chunk int_chunk)%Z.
Proof.
  apply Z.lt_le_incl. apply Z.gt_lt.   apply size_chunk_pos.
Qed.


Definition uint_range : Z -> Prop :=
  fun i => (0 <= i <=   Ptrofs.max_unsigned)%Z.
Transparent uint_range.

Theorem uint_range_unsigned:
  forall i,
    uint_range (Ptrofs.unsigned i).
Proof.
  apply Ptrofs.unsigned_range_2.
Qed.

Ltac int_red := unfold int_size in *; simpl size_chunk in *.

Ltac chunk_red := unfold int_size in *; unfold int_chunk in *; destruct Archi.ptr64 eqn:Harchi; simpl size_chunk in *.

Ltac ulia := (unfold int_size; simpl size_chunk; lia).

Definition uint_range_l: list Z -> Prop :=
  fun l => Forall uint_range l.


Theorem ptrofs_mu_weak:
  (Int.max_unsigned <= Ptrofs.max_unsigned)%Z.
Proof.
  unfold Int.max_unsigned.
  unfold Ptrofs.max_unsigned.

  destruct (Archi.ptr64) eqn:Harchi.

  rewrite Ptrofs.modulus_eq64 by auto. unfold Int.modulus. unfold Int64.modulus. simpl. lia.
  rewrite Ptrofs.modulus_eq32 by auto. reflexivity.
Qed.

Theorem ptrofs_ms:
(Ptrofs.max_signed = if Archi.ptr64 then Int64.max_signed else Int.max_signed )%Z.
Proof.
  unfold Int.max_signed.
  unfold Ptrofs.max_signed.
  unfold Ptrofs.half_modulus.
  destruct (Archi.ptr64) eqn:Harchi.
  rewrite Ptrofs.modulus_eq64 by auto; reflexivity.
  rewrite Ptrofs.modulus_eq32 by auto; reflexivity.
Qed.


Theorem ptrofs_mu:
  (Ptrofs.max_unsigned = if Archi.ptr64 then Int64.max_unsigned else Int.max_unsigned )%Z.
Proof.
  unfold Int.max_unsigned.
  unfold Ptrofs.max_unsigned.

  destruct (Archi.ptr64) eqn:Harchi.
  rewrite Ptrofs.modulus_eq64 by auto; reflexivity.
  rewrite Ptrofs.modulus_eq32 by auto; reflexivity.
Qed.

Ltac uint_range_ptrofs :=
  unfold uint_range_l; unfold uint_range; rewrite ptrofs_mu.

Ltac solve_uint_range:=
  unfold Int64.max_unsigned in *; unfold Int64.modulus in *; unfold Int.max_unsigned in *; unfold Int.modulus in *;  simpl in *; (match goal with
          | [H:uint_range _ |- _] => unfold uint_range in H; rewrite ptrofs_mu in H; solve_uint_range
          | [H:uint_range_l _ |- _] => unfold uint_range_l in H;  solve_uint_range
          | [H: Forall uint_range _ |- _] => inv H; solve_uint_range
          | [|- uint_range _] => unfold uint_range; unfold Int.max_unsigned; unfold Int.modulus; simpl; try lia
          | [|- uint_range (Ptrofs.unsigned _)] => apply uint_range_unsigned
          | [|- uint_range (Int.unsigned _)] => apply uint_range_unsigned
          | [|- uint_range_l _] => unfold uint_range_l; solve_uint_range
          | [ |- Forall uint_range _] => constructor; solve_uint_range
          | _ => auto
          end).



Theorem int_z_mul :
  forall i y,
    uint_range_l [i; y] ->
  Ptrofs.mul (Ptrofs.repr i) (Ptrofs.repr y) = Ptrofs.repr (i * y)%Z.
Proof.
  intros.
  unfold Ptrofs.mul.
  rewrite Ptrofs.unsigned_repr.
  rewrite Ptrofs.unsigned_repr. reflexivity.
  inv H. inv H3; auto.
  inv H; auto.
Qed.


Theorem int_z_add:
  forall i y,
    uint_range_l [i; y] ->
    Ptrofs.add (Ptrofs.repr i) (Ptrofs.repr y) = Ptrofs.repr (i + y)%Z.
Proof.
  intros.
  unfold Ptrofs.add.
  rewrite Ptrofs.unsigned_repr.
  rewrite Ptrofs.unsigned_repr.
  reflexivity.
  inv H. inv H3; auto.
  inv H; auto.
Qed.


Theorem pointer_ofs_no_overflow:
forall ofs z,
  (0 <= z)%Z ->
  (Ptrofs.unsigned ofs + int_size * z <= Ptrofs.max_unsigned )%Z ->

                        Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (int_size * z))) =
        (Ptrofs.unsigned ofs + int_size * z)%Z.
Proof.
  intros.
  unfold int_size in *; simpl size_chunk in *.
  assert (0 <=  Ptrofs.unsigned ofs)%Z by apply Ptrofs.unsigned_range_2.
  unfold Ptrofs.add.
  assert (0 <= size_chunk int_chunk)%Z by apply int_size_pos.
  rewrite Ptrofs.unsigned_repr with (z := (_ * z)%Z).
  rewrite Ptrofs.unsigned_repr. reflexivity.

  split; auto. apply Z.add_nonneg_nonneg; auto. apply Z.mul_nonneg_nonneg; auto.
  split; auto. apply Z.mul_nonneg_nonneg; auto.
  lia.
Qed.


 (* TODO: move to identifiers *)
Inductive bound_var_val: LambdaANF.cps.val -> Ensemble cps.var :=
| Bound_Vconstr :
    forall c vs v x,
    bound_var_val v x ->
    List.In v vs ->
    bound_var_val (Vconstr c vs) x
| Bound_Vfun:
    forall fds rho x f,
    bound_var_fundefs fds x ->
    bound_var_val (Vfun rho fds f) x.


Inductive occurs_free_val: LambdaANF.cps.val -> Ensemble cps.var :=
| OF_Vconstr :
    forall c vs v x,
    occurs_free_val v x ->
    List.In v vs ->
    occurs_free_val (Vconstr c vs) x
| OF_Vfun:
    forall fds rho x f,
      occurs_free_fundefs fds x ->
      M.get x rho = None ->
      occurs_free_val (Vfun rho fds f) x.


Definition closed_val (v : LambdaANF.cps.val) : Prop :=
  Same_set cps.var (occurs_free_val v) (Empty_set cps.var).


Theorem closed_val_fun:
  forall fl f t vs e,
    closed_val (Vfun (M.empty cps.val) fl f) ->
    find_def f fl = Some (t, vs, e) ->
    (Included _ (occurs_free e) (Ensembles.Union _  (FromList vs) (name_in_fundefs fl)) ).
Proof.
Admitted.


Inductive dsubval_v: LambdaANF.cps.val -> LambdaANF.cps.val -> Prop :=
| dsubval_constr: forall v vs c,
  List.In v vs ->
  dsubval_v v (Vconstr c vs)
| dsubval_fun : forall x fds rho f,
  name_in_fundefs fds x ->
    dsubval_v (Vfun rho fds x) (Vfun rho fds f)
.

Definition subval_v := clos_trans _ dsubval_v.
Definition subval_or_eq := clos_refl_trans _ dsubval_v.



Theorem t_then_rt:
  forall A R (v v':A),
  clos_trans _ R v v'  ->
  clos_refl_trans _ R v v'.
Proof.
  intros. induction H.
  apply rt_step. auto.
  eapply rt_trans; eauto.
Qed.


Theorem rt_then_t_or_eq:
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

Theorem dsubterm_case_cons:
  forall v l e',
    dsubterm_e e' (Ecase v l) ->
  forall a, dsubterm_e e' (Ecase v (a:: l)).
Proof.
  intros. inv H. econstructor.
  right; eauto.
Qed.



Theorem subterm_case:
forall v l e',
  subterm_e e' (Ecase v l) ->
  forall a, subterm_e e' (Ecase v (a:: l)).
Proof.
  intros. remember (Ecase v l) as y. revert dependent v. revert l. induction H.
  - intros. subst. constructor.
    eapply dsubterm_case_cons; eauto.
  - intros. apply IHclos_trans2 in Heqy.
    eapply t_trans. apply H. eauto.
Qed.


Theorem subval_fun: forall v rho fl x,
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
  assert ( (exists x : cps.var, Vfun rho fl x0 = Vfun rho fl x /\ name_in_fundefs fl x)) by eauto.
  apply IHclos_trans2 in H. apply IHclos_trans1 in H. auto.
Qed.

Theorem subval_or_eq_constr:
forall v v' vs c,
  subval_or_eq v v' ->
  List.In v' vs ->
  subval_or_eq v (Vconstr c vs).
Proof.
  intros.
  eapply rt_trans; eauto.
  apply rt_step. constructor; auto.
Qed.



Theorem subval_v_constr:
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
  -  specialize (IHclos_trans2 t vs eq_refl).
     destruct IHclos_trans2.
     exists x0. destruct H1. split.
     apply t_then_rt in H.
     eapply rt_trans; eauto.
     auto.
Qed.

Theorem subval_or_eq_fun:
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


Theorem bound_var_subval:
  forall x v v',
  bound_var_val v x ->
  subval_or_eq v v' ->
  bound_var_val v' x.
Proof.
  intros. induction H0.
  - inv H0. econstructor; eauto.
    inv H. constructor. auto.
  - auto.
  - apply   IHclos_refl_trans2.
    apply   IHclos_refl_trans1.
    auto.
Qed.


(* bound_var_val - name_in_fds *)
Inductive bound_subvar_val : cps.val -> Ensemble cps.var :=
    Bound_SVconstr : forall (c : ctor_tag) (vs : list cps.val) (v : cps.val) (x : cps.var),
                    bound_var_val (Vconstr c vs) x -> bound_subvar_val (Vconstr c vs) x
  | Bound_SVfun : forall (fds : fundefs) (rho : cps.M.t cps.val) (x f : cps.var),
      bound_var_val (Vfun rho fds f) x -> ~name_in_fundefs fds x -> bound_subvar_val (Vfun rho fds f) x.



(* deep version of bound_subvar_val, likely what is needed for functions_not_bound inv *)
Inductive bound_notfun_val: cps.val -> Ensemble cps.var :=
  Bound_FVconstr : forall (c : ctor_tag) (vs : list cps.val)
                         (v : cps.val) (x : cps.var),
                    bound_notfun_val v x ->
                    List.In v vs -> bound_notfun_val (Vconstr c vs) x
| Bound_FVfun : forall (e:exp) (fds : fundefs) (rho : cps.M.t cps.val) ys (x f f' : cps.var) t,
    In _ (Ensembles.Union _ (FromList ys) (bound_var e)) x ->  find_def f' fds = Some (t, ys, e) ->  bound_notfun_val (Vfun rho fds f) x.


Theorem find_dsubterm:
  forall x t ys e fl,
find_def x fl = Some (t, ys, e) -> dsubterm_fds_e e fl.
Proof.
  induction fl; intros.
  - simpl in H. destruct (cps.M.elt_eq x v) eqn:Heq_xv. inv H. constructor.
    constructor 2. eapply IHfl; eauto.
  - inv H.
Qed.

Theorem bound_subvar_var: forall v x,
  bound_subvar_val v x -> bound_var_val v x.
Proof.
  intros. inv H; auto.
Qed.

Theorem bound_notfun_var: forall v x,
  bound_notfun_val v x -> bound_var_val v x.
Proof.
  intros. induction H.
  - econstructor; eauto.
  -  constructor. induction fds. simpl in H0.
     destruct  (cps.M.elt_eq f' v). inv H0. inv H. constructor; auto.
     constructor 3; auto.
     constructor 2. auto.
     inv H0.
Qed.


Theorem set_lists_In:
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
    + rewrite M.gso in H0 by auto.
      constructor 2.
      inv H. exfalso; apply n; reflexivity.
      eapply IHxs; eauto.
Qed.

Ltac inList := repeat (try (left; reflexivity); right).


Ltac solve_nodup :=
  let hxy := fresh "Hxy" in
  intro hxy; subst; try (clear hxy);
repeat (match goal with
        | [H: NoDup _ |- _] => let h2 := fresh "Hnd" in
                               let h1 := fresh "HinList" in
                               let x := fresh "x" in
                               let l := fresh "l" in
                               inversion H as [h1 | x l h1 h2];
                               subst; clear H;
                               try (solve [apply h1; inList])
        end).

(**** Representation relation for LambdaANF values, expressions and functions ****)
Section RELATION.

  (* same as LambdaANF_to_Clight *)
  Variable (argsIdent : ident).
  Variable (allocIdent : ident).
  Variable (limitIdent : ident).
  Variable (gcIdent : ident).
  Variable (mainIdent : ident).
  Variable (bodyIdent : ident).
  Variable (threadInfIdent : ident).
  Variable (tinfIdent : ident).
  Variable (heapInfIdent : ident).
  Variable (numArgsIdent : ident).
  Variable (isptrIdent: ident). (* ident for the isPtr external function *)
  Variable (caseIdent:ident).
  Variable (nParam:nat).

  Definition protectedIdent: list ident := (argsIdent::allocIdent::limitIdent::gcIdent::mainIdent::bodyIdent::threadInfIdent::tinfIdent::heapInfIdent::numArgsIdent::numArgsIdent::isptrIdent::caseIdent::[]).


  Variable cenv:LambdaANF.cps.ctor_env.
  Variable funenv:LambdaANF.cps.fun_env.
  Variable fenv : CodegenWASM.LambdaANF_to_WASM.fname_env.
  Variable venv : CodegenWASM.LambdaANF_to_WASM.var_env.
  Variable nenv : LambdaANF.cps_show.name_env.
  Variable finfo_env: LambdaANF_to_Clight.fun_info_env. (* map from a function name to its type info *)
  Variable p:program.

  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t ctor_rep.



Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show CodegenWASM.wasm_map_util.
Import Common.Common Common.compM Common.Pipeline_utils.

Import ExtLib.Structures.Monad.
Import MonadNotation.

(*
  Notation threadStructInf := (Tstruct threadInfIdent noattr).
  Notation threadInf := (Tpointer threadStructInf noattr).

  Notation funTy := (Tfunction (Tcons threadInf Tnil) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation pfunTy := (Tpointer funTy noattr).

Notation gcTy := (Tfunction (Tcons (Tpointer (Tint I32 Unsigned noattr) noattr) (Tcons threadInf Tnil)) Tvoid
                            {|
                              cc_vararg := false;
                              cc_unproto := false;
                              cc_structret := false |}).

Notation isptrTy := (Tfunction (Tcons (Tint I32 Unsigned noattr) Tnil) (Tint IBool Unsigned noattr)
                               {|
                                 cc_vararg := false;
                                 cc_unproto := false;
                                 cc_structret := false |}).







Notation valPtr := (Tpointer val
                            {| attr_volatile := false; attr_alignas := None |}).

Notation boolTy := (Tint IBool Unsigned noattr).

Notation "'var' x" := (Etempvar x val) (at level 20).
Notation "'ptrVar' x" := (Etempvar x valPtr) (at level 20).

Notation "'bvar' x" := (Etempvar x boolTy) (at level 20).
Notation "'funVar' x" := (Evar x funTy) (at level 20).


Notation allocPtr := (Etempvar allocIdent valPtr).
Notation limitPtr := (Etempvar limitIdent valPtr).
Notation args := (Etempvar argsIdent valPtr).
Notation gc := (Evar gcIdent gcTy).
Notation ptr := (Evar isptrIdent isptrTy).

*)



(*
Definition boxed_header: N -> N -> Z -> Prop :=
  fun t => fun a =>  fun h =>
                       (h =  (Z.shiftl (Z.of_N a) 10) + (Z.of_N t))%Z /\
                       (0 <= Z.of_N t <  Zpower.two_power_pos 8)%Z /\
                       (0 <= Z.of_N a <  Zpower.two_power_nat (Ptrofs.wordsize - 10))%Z. *)


Inductive Forall_statements_in_seq' {A}: (nat  -> A -> list basic_instruction -> Prop) ->  list A -> list basic_instruction -> nat -> Prop :=
| Fsis_last: forall (R: (nat  -> A -> list basic_instruction -> Prop)) n v s, R n v s -> Forall_statements_in_seq' R [v] s n
| Fsis_cons: forall R v vs s s' n, Forall_statements_in_seq' R vs s' (S n) ->
                                   R n v s ->  Forall_statements_in_seq' R (v::vs) (s ++ s') n.



Inductive Forall_statements_in_seq_rev {A}: (nat -> A -> list basic_instruction -> Prop) ->  list A -> list basic_instruction -> nat -> Prop :=
| Fsir_last: forall (R: (nat  -> A -> list basic_instruction -> Prop)) v s, R 0 v s -> Forall_statements_in_seq_rev R [v] s 0
| Fsir_cons: forall R v vs s s' n, Forall_statements_in_seq_rev R vs s' n ->
                                   R (S n) v s ->  Forall_statements_in_seq_rev R (v::vs) (s ++ s') (S n).


(* This is true for R, vs and S iff forall i, R i (nth vs) (nth s)
   > list cannot be empty (o.w. no statement)
   > nth on statement is taken as nth on a list of sequenced statement (;) *)
Definition Forall_statements_in_seq {A}: (nat  -> A -> list basic_instruction -> Prop) ->  list A -> list basic_instruction -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s 0.

(* like Forall_statements_in_seq, but starting from index 1 *)
Definition Forall_statements_in_seq_from_1 {A}: (nat  -> A -> list basic_instruction -> Prop) ->  list A -> list basic_instruction -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s 1.

Inductive repr_var : positive -> immediate -> Prop :=
| repr_var_V : forall s err_str i,
   (* Genv.find_symbol (Genv.globalenv p) x = Some _ -> *)
       translate_var nenv venv s err_str = Ret i ->
       repr_var s i.

(* immediate=nat: used in BI_call i *)
Inductive repr_funvar : positive -> immediate -> Prop :=
| repr_funvar_FV : forall s i,
        translate_function_var nenv fenv s = Ret i ->
        repr_funvar s i.

Inductive repr_read_var_or_funvar : positive -> basic_instruction -> Prop :=
| repr_var_or_funvar_V : forall p i,
    repr_var p i -> repr_read_var_or_funvar p (BI_get_local i)
| repr_var_or_funvar_FV : forall p i,
    repr_funvar p i -> repr_read_var_or_funvar p (BI_const (nat_to_value i)).

(* constr_alloc_ptr: pointer to linear_memory[p + 4 + 4*n] = value v *)
Inductive is_nth_projection : nat -> var -> list basic_instruction -> Prop :=
  Make_nth_proj: forall (v : var) n v',
                        repr_read_var_or_funvar v v' ->
                        is_nth_projection n v [ BI_get_global constr_alloc_ptr
                                              ; BI_const (nat_to_value ((1 + n) * 4))
                                              ; BI_binop T_i32 (Binop_i BOI_add)
                                              ; v'
                                              ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0)
                                              ].

(* Inductive repr_asgn_constr : list cps.var -> list basic_instruction -> Prop :=
  | Rconstr_asgn_cons : forall vs vs' v v' s,
        Forall_statements_in_seq is_nth_projection vs s ->
        repr_asgn_constr vs ([BI_get_global constr_alloc_ptr;
                               BI_const (nat_to_value 4);
                               BI_binop T_i32 (Binop_i BOI_add);
                               v';
                               BI_store T_i32 None 2%N 0%N;
                               BI_get_global global_mem_ptr;
                               BI_const (nat_to_value 4);
                               BI_binop T_i32 (Binop_i BOI_add);
                               BI_set_global global_mem_ptr] ++ vs'). *)

(*
    Forall_statements_in_seq (is_nth_projection_of_x x) vs s ->
    repr_asgn_constr x t vs (x ::= [val] (allocPtr +' (c_int Z.one val));
                                     allocIdent ::= allocPtr +'
                                           (c_int (Z.of_N (a + 1)) val); Field(var x, -1) :::= c_int h val;  s). *)

(* all constructors are boxed for simplicity *)
Inductive repr_asgn_constr: ctor_tag -> list var -> list basic_instruction -> Prop :=
| Rconstr_asgn: forall (t:ctor_tag) (cenv : ctor_env) (nenv : name_env) vs s,
    (* match M.get t cenv with
    | Some {| ctor_arity := ar |} => Some ar
    | _ => None
    end = Some a ->
    length vs = N.to_nat a -> *)
    Forall_statements_in_seq_from_1 is_nth_projection vs s ->
    repr_asgn_constr t vs ([ BI_get_global constr_alloc_ptr
                           ; BI_const (nat_to_value (Pos.to_nat t))
                           ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0)
                           ] ++ s).
                             (*  (x ::= [val] (allocPtr +' (c_int Z.one val));
                             allocIdent ::= allocPtr +' (c_int (Z.of_N (a + 1)) val);
                             Field(var x, -1) :::= c_int h val;
                             s). *)

(*
Inductive repr_switch_LambdaANF_Codegen: positive -> labeled_statements -> labeled_statements -> statement -> Prop :=
| Mk_switch: forall x ls ls',
    repr_switch_LambdaANF_Codegen x ls ls'
                      (isPtr isptrIdent caseIdent x;
                         Sifthenelse
                           (bvar caseIdent)
                           (Sswitch (Ebinop Oand (Field(var x, -1)) (make_cint 255 val) val) ls)
                           (
                             Sswitch (Ebinop Oshr (var x) (make_cint 1 val) val)
                                     ls')).
*)

(* args are pushed on the stack before calling a function *)
Inductive repr_fun_args_Codegen : list LambdaANF.cps.var -> list basic_instruction -> Prop :=
(* base case: no args *)
| FA_nil :
    repr_fun_args_Codegen [] []
(* arg is local var *)
| FA_cons_var : forall a a' args instr,
    repr_var a a' ->
    repr_fun_args_Codegen args instr ->
    repr_fun_args_Codegen (a :: args) ([BI_get_local a'] ++ instr)
(* arg is function -> lookup id for handling indirect calls later *)
| FA_cons_fun : forall a a' args instr,
    repr_funvar a a' ->
    repr_fun_args_Codegen args instr ->
    repr_fun_args_Codegen (a :: args) ([BI_const (nat_to_value a')] ++ instr).


(* CODEGEN RELATION: relatates LambdaANF expression and result of translate_exp *)
Inductive repr_expr_LambdaANF_Codegen: LambdaANF.cps.exp -> list basic_instruction -> Prop :=
| R_halt_e: forall v v',
    repr_var v v' ->
    repr_expr_LambdaANF_Codegen (Ehalt v) [ BI_get_local v'
                                          ; BI_set_global result_var
                                          ]
| Rproj_e: forall x x' t n v v' e  s,
    repr_expr_LambdaANF_Codegen e  s ->
    repr_var x x' ->
    repr_var v v' ->
      repr_expr_LambdaANF_Codegen (Eproj x t n v e)
           ([ BI_get_local v'
           ; BI_const (nat_to_value (((N.to_nat n) + 1) * 4))
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; BI_load T_i32 None (N_of_nat 2) (N_of_nat 0)
           ; BI_set_local x'
           ] ++ s)

| Rconstr_e:
    forall x x' t vs sgrow sinit sstore sres e e',
    (* translated assigned var *)
    repr_var x x' ->
    (* allocate memory *)
    grow_memory_if_necessary ((length vs + 1) * 4) = sgrow ->
    (* initialize pointers *)
    sinit = [ BI_get_global global_mem_ptr
            ; BI_set_global constr_alloc_ptr
            ; BI_get_global global_mem_ptr
            ; BI_const (nat_to_value ((length vs + 1) * 4))
            ; BI_binop T_i32 (Binop_i BOI_add); BI_set_global global_mem_ptr
            ] ->
    (* store tag + args *)
    repr_asgn_constr t vs sstore ->
    (* set result *)
    sres = [BI_get_global constr_alloc_ptr; BI_set_local x'] ->
    (* following expression *)
    repr_expr_LambdaANF_Codegen e e' ->
    repr_expr_LambdaANF_Codegen (Econstr x t vs e) (sgrow ++ sinit ++ sstore ++ sres ++ e')


| Rcase_e_nil : forall v, repr_expr_LambdaANF_Codegen (Ecase v []) [BI_unreachable]

| Rcase_e_cons : forall v v' cl instrs_more t e e',
        repr_var v v' ->
        repr_expr_LambdaANF_Codegen (Ecase v cl) instrs_more ->
        repr_expr_LambdaANF_Codegen e e' ->
        repr_expr_LambdaANF_Codegen (Ecase v ((t, e) :: cl))
                                    [ BI_get_local v'
                                    ; BI_load T_i32 None (N_of_nat 2) (N_of_nat 0)
                                    ; BI_const (nat_to_value (Pos.to_nat t))
                                    ; BI_relop T_i32 (Relop_i ROI_eq)
                                    ; BI_if (Tf nil nil) e' instrs_more
                                    ]

| R_app_e_direct : forall v v' t args args',
    (* args are provided properly *)
    repr_fun_args_Codegen args args' ->
    (* funvar to call *)
    repr_funvar v v' ->
    repr_expr_LambdaANF_Codegen (Eapp v t args) ((args' ++ [BI_call v']))

| R_app_e_indirect : forall v t args args' i ind,
    repr_fun_args_Codegen args args' ->
    lookup_function_var (indirection_function_name (map (fun _ : var => T_i32) args)) fenv
                        "translate call, ind function" = Ret ind ->
    lookup_local_var (translate_var_to_string nenv v) venv
                        ("ind call from var: " ++ translate_var_to_string nenv v) = Ret i ->
    repr_expr_LambdaANF_Codegen (Eapp v t args) ((args' ++ [BI_get_local i; BI_call ind])).


(* Variable mem : memory. *) (* WASM memory, created e.g. at initialization *)

Definition load_i32 m addr : option value := match load m addr (N.of_nat 0) 4 with (* offset: 0, 4 bytes *)
                                               | None => None
                                               | Some bs => Some (wasm_deserialise bs T_i32)
                                               end.

Definition store_i32 mem addr (v : value) : option memory := store mem addr (N.of_nat 0) (bits v) 4.


Definition tag_to_i32 (t : ctor_tag) := Wasm_int.Int32.repr (BinInt.Z.of_nat (Pos.to_nat t)).
Definition immediate_to_i32 (i : immediate) := Wasm_int.Int32.repr (BinInt.Z.of_nat i).

Inductive wasm_value :=
  | Val_ptr : immediate -> wasm_value
  | Val_funidx : immediate -> wasm_value.


Definition wasm_value_to_immediate (v : wasm_value) :=
    match v with
    | Val_ptr i => i
    | Val_funidx i => i
    end.

Definition wasm_value_to_i32 (v : wasm_value) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat (wasm_value_to_immediate v)).

Variable host_function : Type.
Let store_record := store_record host_function.


(* VALUE RELATION *)
(* immediate is pointer to linear memory or function id *)
Inductive repr_val_LambdaANF_Codegen:  LambdaANF.cps.val -> store_record -> wasm_value -> Prop :=
| Rconstr_v : forall t vs sr m addr, (* addr=idx in linear memory *)
    (* store_record contains memory *)
    List.nth_error sr.(s_mems) 0 = Some m ->
    (* constructor tag is set properly, see LambdaANF_to_WASM, constr alloc structure*)
    load_i32 m (N.of_nat addr) = Some (VAL_int32 (tag_to_i32 t)) ->
    (* arguments are set properly *)
    repr_val_constr_args_LambdaANF_Codegen vs sr (4 + addr) ->
    repr_val_LambdaANF_Codegen (LambdaANF.cps.Vconstr t vs) sr (Val_ptr addr)
| Rfunction_v : forall env fds f sr  tag vs e e' idx inst ftype args body,
      find_def f fds = Some (tag, vs, e) ->

      (* find runtime representation of function *)
      List.nth_error sr.(s_funcs) idx = Some (FC_func_native inst ftype args body) ->
      ftype = Tf (List.map (fun _ => T_i32) vs) [] ->
      (* TODO: calling convention: unpack values from lin. memory? *)
      body = e' ->

      repr_expr_LambdaANF_Codegen e e' ->
      (* env: why empty? *)
      repr_val_LambdaANF_Codegen (LambdaANF.cps.Vfun env fds f) sr (Val_funidx idx)

with repr_val_constr_args_LambdaANF_Codegen : (list LambdaANF.cps.val) -> store_record -> immediate -> Prop :=
     | Rnil_l : forall sr addr,
        repr_val_constr_args_LambdaANF_Codegen nil sr addr

     | Rcons_l: forall v wal vs sr m addr,
        (* store_record contains memory *)
        List.nth_error sr.(s_mems) 0 = Some m ->

        (* constr arg is ptr related to value v *)
        load_i32 m (N.of_nat addr) = Some (VAL_int32 (wasm_value_to_i32 wal)) ->
        repr_val_LambdaANF_Codegen v sr wal ->

        (* following constr args are also related *)
        repr_val_constr_args_LambdaANF_Codegen vs sr (4 + addr) ->
        repr_val_constr_args_LambdaANF_Codegen (v::vs) sr addr.



Inductive Forall_fundefs: (LambdaANF.cps.var -> fun_tag -> list LambdaANF.cps.var -> exp -> Prop) -> fundefs -> Prop :=
| Ff_cons : forall (P:(LambdaANF.cps.var -> fun_tag -> list LambdaANF.cps.var -> exp -> Prop)) f t vs e fds,
         P f t vs e ->
         Forall_fundefs P fds ->
         Forall_fundefs P (Fcons f t vs e fds)
| Ff_nil: forall P, Forall_fundefs P Fnil.


Theorem Forall_fundefs_In:
  forall P f t vs e fds,
  Forall_fundefs P fds ->
  fun_in_fundefs fds (f,t,vs,e) ->
  P f t vs e.
Proof.
  induction fds; intros.
  - inv H; inv H0; subst.
    + inv H; auto.
    +  apply IHfds; auto.
  - inv H0.
Qed.

(* END TODO move *)

(*
(* 1) finfo_env has the correct finfo
   2) fenv is consistent with the info
   3) global env holds a correct Codegen representation of the function *)
Definition correct_environments_for_function:
  genv -> fun_env -> M.t positive -> mem -> fundefs ->  LambdaANF.cps.var ->
  fun_tag -> list LambdaANF.cps.var -> exp ->  Prop
  := fun ge fenv finfo_env m fds f t vs e =>
       exists l locs finfo b,
         (*1*)
         M.get f finfo_env = Some finfo /\
         correct_fundef_info m f t vs e finfo  /\
         (*2*)
         M.get t fenv = Some (l, locs) /\
         l = N.of_nat (length vs) /\
         (* may want to check that locs are distinct and same as in finfo? *)
         (*3*)
         Genv.find_symbol (globalenv p) f = Some b /\
         (* TODO: change this to repr_val_LambdaANF_Codegen *)
         repr_val_LambdaANF_Codegen (cps.Vfun (M.empty cps.val) fds f) m (Vptr b Ptrofs.zero).


Definition correct_environments_for_functions: fundefs -> genv -> fun_env -> M.t positive -> mem ->  Prop := fun fds ge fenv finfo_env m =>
                                                                                                            Forall_fundefs (correct_environments_for_function ge fenv finfo_env m fds) fds.
 *)

Definition is_protected_id  (id:positive)  : Prop :=
  List.In id protectedIdent.

Definition is_protected_tinfo_id (id:positive) : Prop :=
    id = allocIdent \/ id = limitIdent \/ id = argsIdent.

Theorem is_protected_tinfo_weak:
  forall x, is_protected_tinfo_id x ->
            is_protected_id x.
Proof.
  intros. repeat destruct H; subst; inList. Admitted.


(* Domain of find_symbol (globalenv p) is disjoint from bound_var e /\ \sum_rho (bound_var_val x \setminus names_in_fundef x) *)
(*  *)
Definition functions_not_bound (rho:LambdaANF.eval.env) (e:exp): Prop :=
  (forall x,
    bound_var e x ->
    Genv.find_symbol (Genv.globalenv p) x = None)/\
  (forall x y v,
      M.get y rho = Some v ->
      bound_notfun_val v x ->
      Genv.find_symbol (Genv.globalenv p) x = None).



Inductive unique_bindings_val: LambdaANF.cps.val -> Prop :=
| UB_Vfun: forall rho fds f,
    unique_bindings_fundefs fds ->
    unique_bindings_val (Vfun rho fds f)
| UB_Vconstr: forall c vs,
    Forall unique_bindings_val vs ->
    unique_bindings_val (Vconstr c vs)
|UB_VInt: forall z,
    unique_bindings_val (cps.Vint z)
.


(* UB + disjoint bound and in env *)
Definition unique_bindings_env (rho:LambdaANF.eval.env) (e:exp) : Prop :=
      unique_bindings e  /\
      (forall x v,
        M.get x rho = Some v ->
    ~ bound_var e x /\ unique_bindings_val v).


Definition prefix_ctx {A:Type} rho' rho :=
  forall x v, M.get x rho' = Some v -> @M.get A x rho = Some v.


Theorem unique_bindings_env_prefix:
  forall e rho,
    unique_bindings_env rho e ->
    forall rho',
  prefix_ctx rho' rho ->
  unique_bindings_env rho' e.
Proof.
  intros.
  inv H.
  split; auto.
Qed.


(* TODO: also need UB for the functions in rho
Theorem unique_bindings_env_weaken :
  unique_bindings_env rho e ->
  rho' subseteq rho
unique_bindings_env rho e *)


Theorem functions_not_bound_subterm:
  forall rho e,
    functions_not_bound rho e ->
    forall e',
    subterm_e e' e ->
    functions_not_bound rho e'.
Proof.
  intros. split. intro; intros.
  apply H.
Admitted.

Theorem functions_not_bound_set:
    forall rho e y v,
      functions_not_bound rho e ->
      (forall x, bound_notfun_val v x -> Genv.find_symbol (globalenv p) x = None) ->
      functions_not_bound (M.set y v rho) e.
Proof.
  intros. split. apply H.
  intros. destruct (var_dec y0 y).
  - subst. rewrite M.gss in H1. inv H1. destruct H. apply H0. auto.
  - rewrite M.gso in H1 by auto. inv H. eapply H4; eauto.
Qed.

Definition protected_id_not_bound  (rho:LambdaANF.eval.env) (e:exp) : Prop :=
  (forall x y v, M.get x rho = Some v ->
                 is_protected_id  y ->
                 ~ (x = y \/ bound_var_val v y) )/\
  (forall y, is_protected_id  y ->
             ~ bound_var e y).


Theorem protected_id_not_bound_prefix:
  forall rho rho' e,
    protected_id_not_bound rho e ->
    prefix_ctx rho' rho ->
    protected_id_not_bound rho' e.
Proof.
  intros. inv H. split; intros.
  - apply H0 in H.
    apply H1; eauto.
  - eapply H2; eauto.
Qed.



Theorem find_def_bound_in_bundle:
  forall e y t xs f fds,
  bound_var e y ->
  find_def f fds = Some (t, xs, e) ->
  bound_var_fundefs fds y.
Proof.
  induction fds; intros.
  simpl in H0. destruct (cps.M.elt_eq f v). inv H0. constructor 3; auto.
  constructor 2. apply IHfds; auto.
  inv H0.
Qed.

Theorem protected_id_not_bound_closure:
  forall rho e e' f' f fds rho' t xs,
    protected_id_not_bound rho e ->
    M.get f rho = Some (Vfun rho' fds f') ->
    find_def f' fds = Some (t, xs, e') ->
   protected_id_not_bound rho e'.
Proof.
  intros.
  inv H.
  split. auto.
  intros.
  intro.
  specialize (H2 _ _ _ H0 H).
  apply H2. right.
  constructor.
  eapply find_def_bound_in_bundle; eauto.
Qed.

Theorem protected_id_closure:
  forall rho rho' f t0 ys fl f' t xs e' vs,
    protected_id_not_bound rho (Eapp f t0 ys) ->
    cps.M.get f rho = Some (Vfun (M.empty _) fl f') ->
    get_list ys rho = Some vs ->
    find_def f' fl = Some (t, xs, e') ->
    set_lists xs vs (def_funs fl fl (M.empty _) (M.empty _)) = Some rho' ->
    protected_id_not_bound rho' e'.
Proof.
  intros.
  assert (protected_id_not_bound rho e') by (eapply protected_id_not_bound_closure; eauto).
  split. intros.
  assert (decidable (List.In x xs)). apply In_decidable.  admit.
  inv H7.
  (* in vs *)
  { inv H.
    intro. inv H.
    - specialize (H7 _ _ _ H0 H6). apply H7. right.
      constructor. eapply shrink_cps_correct.name_boundvar_arg; eauto.
    - assert (List.In v vs) by (eapply set_lists_In; eauto).
      assert (Hgl := get_list_In_val _ _ _ _  H1 H). destruct Hgl.
      destruct H11. specialize (H7 _ _ _ H12 H6). apply H7. auto.
  }
  erewrite <- set_lists_not_In in H5.
  2: eauto.
  2: eauto.
  assert (decidable (name_in_fundefs fl x)). unfold decidable. assert (Hd := Decidable_name_in_fundefs fl). inv Hd. specialize (Dec x). inv Dec; auto.
      inv H7.
        (*
          2) in fl *)
      rewrite def_funs_eq in H5. 2: eauto. inv H5.
      inv H.
      specialize (H5 _ _ _ H0 H6).
      intro. inv H.

      apply H5. right. constructor.
      apply name_in_fundefs_bound_var_fundefs. auto.

      apply H5. right. constructor. inv H10. auto.

      rewrite def_funs_neq in H5. 2: eauto.
      rewrite M.gempty in H5. inv H5.

        apply H4.
Admitted.



Definition map_get_r_l: forall t l, relation (M.t t) :=
  fun t l => fun sub sub' => forall v,
               List.In v l ->
               M.get v sub = M.get v sub'.

(* lenv' is lenv after binding xs->vs with NoDup xs *)
Definition lenv_param_asgn (lenv lenv':temp_env) (xs:list positive) (vs:list Values.val): Prop :=
  forall i, (forall z, nthN xs z  = Some i ->  M.get i lenv' = nthN vs z)
            /\
            (~ List.In i xs -> M.get i lenv' = M.get i lenv).


Theorem lenv_param_refl :
  forall lenv lenv' vs,
  lenv_param_asgn lenv lenv' [] vs
  -> map_get_r _ lenv lenv'.
Proof.
  intros.
  intro.
  specialize (H v).
  destruct H.
  symmetry.
  apply H0.
  intro.
  inv H1.
Qed.

Theorem lenv_param_asgn_not_in:
  forall lenv lenv' b ofs x (L:positive -> Prop) xs vs7,
M.get x lenv = Some (Vptr b ofs) ->
  L x ->
  (forall x6 : positive, List.In x6 xs -> ~ L x6) ->
  lenv_param_asgn lenv lenv' xs vs7 ->
  M.get x lenv' = Some (Vptr b ofs).
Proof.
  intros.
  specialize (H2 x).
  destruct H2.
  rewrite H3.
  auto.
  intro.
  eapply H1; eauto.
Qed.


Theorem lenv_param_asgn_map:
  forall lenv lenv' xs vs7 l,
  lenv_param_asgn lenv lenv' xs vs7 ->
  Disjoint _ (FromList xs) (FromList l) ->
  map_get_r_l _ l lenv lenv'.
Proof.
  intros.
  intro.
  intro.
  specialize (H v); destruct H.
  rewrite H2.
  auto.
  inv H0. specialize (H3 v).
  intro.
  apply H3.
  auto.
Qed.


(* MEMORY RELATION *)

(* relates a LambdaANF evaluation environment to a Clight memory up to the free variables in e *)
(* If x is a free variable of e, then it might be in the generated code:
   1) a function (may want to handle this separately as they won't get moved by the GC) in the global environment, evaluates to a location related to f by repr_val_ptr_LambdaANF_Codegen
   2) a local variable in le related to (rho x) according to repr_val_LambdaANF_Codegen -- this happens when e.g. x := proj m, or after function initialization

All the values are in a space L which is disjoint form protected space

Note that parameters are heap allocated, and at function entry "free variables" are held in args and related according to repr_val_ptr_LambdaANF_Codegen

Now also makes sure none of the protected portion are reachable by the v7

TODO: second section needs that for any such f s.t. find_def f fl = Some (t, vs4, e),  e is closed by  var (FromList vsm4 :|: name_in_fundefs fl)
 may want something about functions in rho, i.e. that they don't need to be free to be repr_val_id, since they are the only thing that may appear free in other functions body (and not bound in the opening
may need rho' also has the Vfun
 *)


(* wasm values can be stored in memory, local or global variables *)
Definition stored_in_mem (v : wasm_value) (sr : store_record) :=
    exists m addr,
    (* store_record contains memory *)
    List.nth_error sr.(s_mems) 0 = Some m /\
    (* memory contains value at some address *)
    load_i32 m (N.of_nat addr) = Some (VAL_int32 (wasm_value_to_i32 v)).

Definition stored_in_globals (v : wasm_value) (sr : store_record) :=
  exists global i,
  List.nth_error sr.(s_globals) i = Some global /\
     global.(g_val) = VAL_int32 (wasm_value_to_i32 v).

Definition stored_in_locals (x : cps.var) (v : wasm_value) (f : frame ) :=
  exists i,
  (forall err, translate_var nenv venv x err = Ret i) /\
  List.nth_error f.(f_locs) i = Some (VAL_int32 (wasm_value_to_i32 v)).

Definition rel_mem_LambdaANF_Codegen (e : exp) (rho : LambdaANF.eval.env)
                                     (sr : store_record) (fr : frame) :=
        (* function def is related to function index *)
        (forall x rho' fds f v, exists i,
            M.get x rho = Some v ->
             (* 1) arg is subval of constructor
                2) v listed in fds -> subval *)
            subval_or_eq (Vfun rho' fds f) v ->
            (* i is index of function f *)
            translate_function_var nenv fenv f = Ret i /\
            repr_val_LambdaANF_Codegen (Vfun rho' fds f) sr (Val_funidx i) /\
            closed_val (Vfun rho' fds f))
        /\
        (* free variables are related to local var containing a memory pointer or a function index *)
        (forall x,
            occurs_free e x ->
            (exists v6 val,
               M.get x rho = Some v6 /\
               stored_in_locals x val fr /\
               repr_val_LambdaANF_Codegen v6 sr val)).

End RELATION.

Section THEOREM.

  Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show CodegenWASM.wasm_map_util.
Import Common.Common Common.compM Common.Pipeline_utils.

Import ExtLib.Structures.Monad.
Import MonadNotation.


  (* same as LambdaANF_to_Clight *)
  Variable (argsIdent : ident).
  Variable (allocIdent : ident).
  Variable (limitIdent : ident).
  Variable (gcIdent : ident).
  Variable (mainIdent : ident).
  Variable (bodyIdent : ident).
  Variable (threadInfIdent : ident).
  Variable (tinfIdent : ident).
  Variable (heapInfIdent : ident).
  Variable (numArgsIdent : ident).
  Variable (isptrIdent: ident). (* ident for the isPtr external function *)
  Variable (caseIdent:ident).
  Variable (nParam:nat).

  Variable cenv:LambdaANF.cps.ctor_env.
  Variable funenv:LambdaANF.cps.fun_env.
  Variable fenv : CodegenWASM.LambdaANF_to_WASM.fname_env.
  Variable venv : CodegenWASM.LambdaANF_to_WASM.var_env.
  Variable nenv : LambdaANF.cps_show.name_env.
  Variable finfo_env: LambdaANF_to_Clight.fun_info_env. (* map from a function name to its type info *)
  Variable p:program.


  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t ctor_rep.

Import eqtype.
Import host.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
(*Let administrative_instruction := administrative_instruction host_function.*)
Let host_state := host_state host_instance.


Let reduce_trans := @reduce_trans host_function host_instance.




 Inductive correct_crep (cenv:ctor_env): ctor_tag -> ctor_rep -> Prop :=
  (*| rep_enum :
      forall c name namei it  n,
        M.get c cenv = Some (Build_ctor_ty_info name namei it 0%N n) ->
        (* there should not be more than 2^(intsize - 1) unboxed constructors *)
        (0 <= (Z.of_N n) <   Ptrofs.half_modulus)%Z ->
      correct_crep cenv c (enum n) *)
  | rep_boxed:
      forall c name namei it a n,
        M.get c cenv = Some (Build_ctor_ty_info name namei it (Npos a%N) n) ->
        (* there should not be more than 2^8 - 1 boxed constructors *)
        (0 <= (Z.of_N n) <  Zpower.two_p 8)%Z ->
        (* arity shouldn't be higher than 2^54 - 1  *)
        (0 <= Z.of_N (Npos a) <  Zpower.two_power_nat (Ptrofs.wordsize - 10))%Z ->
      correct_crep cenv c (boxed n (Npos a)).

  (* crep <-> make_ctor_rep cenv *)
  Definition correct_crep_of_env: LambdaANF.cps.ctor_env -> M.t ctor_rep -> Prop :=
    fun cenv crep_env =>
      (forall c name namei it a n,
        M.get c cenv = Some (Build_ctor_ty_info name namei it a n) ->
        exists crep, M.get c crep_env = Some crep /\
                     correct_crep cenv c crep) /\
      (forall c crep, M.get c crep_env = Some crep ->
                     correct_crep cenv c crep).


  (* TODO: move this to cps_util *)
  Definition Forall_constructors_in_e (P: var -> ctor_tag -> list var -> Prop) (e:exp) :=
    forall x t  ys e',
      subterm_or_eq (Econstr x t ys e') e -> P x t ys.


  Definition Forall_projections_in_e (P: var -> ctor_tag -> N -> var -> Prop) (e:exp) :=
    forall x t n v e',
      subterm_or_eq (Eproj x t n v e') e -> P x t n v.

  (* Note: the fundefs in P is the whole bundle, not the rest of the list *)
  Definition Forall_functions_in_e (P: var -> fun_tag -> list var -> exp ->  fundefs -> Prop) (e:exp) :=
    forall fds e' f t xs e'',  subterm_or_eq (Efun fds e') e ->
                               fun_in_fundefs fds (f, t, xs, e'') ->
                               P f t xs e'' fds.


  Definition Forall_exp_in_caselist (P: exp -> Prop) (cl:list (ctor_tag * exp)) :=
    forall g e, List.In (g, e) cl -> P e.

  Theorem crt_incl_ct:
          forall T P e e',
          clos_trans T P e e' ->
          clos_refl_trans T P e e'.
  Proof.
    intros. induction H. constructor; auto.
    eapply rt_trans; eauto.
  Qed.

  Theorem Forall_constructors_subterm:
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

  (* all constructors in the exp exists in cenv and are applied to the right number of arguments
    May want to have "exists in cenv" also true for constructors in rho *)
  Definition correct_cenv_of_exp: LambdaANF.cps.ctor_env -> exp -> Prop :=
    fun cenv e =>
      Forall_constructors_in_e (fun x t ys =>
                                  match (M.get t cenv) with
                                  | Some (Build_ctor_ty_info _ _ _ a _) =>
                                    N.of_nat (length ys) = a
                                  | None => False
                                  end) e.

  Definition correct_cenv_of_caselist: LambdaANF.cps.ctor_env -> list (ctor_tag * exp) -> Prop :=
    fun cenv cl =>
      Forall_exp_in_caselist (correct_cenv_of_exp cenv) cl.

  Theorem correct_cenv_of_case:
    forall cenv v l,
      correct_cenv_of_exp cenv (Ecase v l) ->
      correct_cenv_of_caselist cenv l.
  Proof.
    intros; intro; intros.
    eapply Forall_constructors_subterm. apply H.
    constructor. econstructor. eauto.
  Qed.

  Lemma subterm_exists_witness : forall x t ys e v l, subterm_or_eq (Econstr x t ys e)  (Ecase v l) ->
      exists a b, In (a, b) l /\ subterm_or_eq (Econstr x t ys e) b.
  Proof.
    intros.
    apply clos_rt_rtn1 in H. inv H. inv H0. eexists. exists y. split. eassumption.
    unfold subterm_or_eq. eapply clos_rtn1_rt. assumption.
  Qed.

  Lemma subterm_witness_subterm : forall v l a e, In (a, e) l -> subterm_or_eq e (Ecase v l).
  Proof.
    intros. constructor. econstructor. eassumption.
  Qed.

  Lemma subterm_case_list : forall x t ys e   v l c e',
    subterm_or_eq (Econstr x t ys e) (Ecase v l) -> subterm_or_eq (Econstr x t ys e) (Ecase v ((c, e') :: l)).
  Proof.
    intros. apply subterm_exists_witness in H. destruct H as [a [b [H1 H2]]].
    eapply rt_trans. eassumption. eapply subterm_witness_subterm. cbn. right. eassumption.
  Qed.

  Theorem correct_cenv_case_drop_clause : forall l v c e,
    correct_cenv_of_exp cenv (Ecase v ((c, e) :: l)) ->
    correct_cenv_of_exp cenv (Ecase v l).
  Proof.
    unfold correct_cenv_of_exp. unfold Forall_constructors_in_e. intros.
    eapply H. eapply subterm_case_list. eassumption.
  Qed.

  Theorem Forall_constructors_in_constr:
  forall P x t ys e,
  Forall_constructors_in_e P (Econstr x t ys e) ->
  P x t ys.
  Proof.
    intros.
    unfold Forall_constructors_in_e in *.
    eapply H.
    apply rt_refl.
  Qed.

Open Scope list.



Definition lookup_function_var_generalize_err_string (name : string) (err : string) i :
  lookup_function_var name fenv err = Ret i -> forall err', lookup_function_var name fenv err' = Ret i.
Proof.
 unfold lookup_function_var. intros. destruct (M_string.find (elt:=nat) name fenv). auto. inv H.
Qed.

Definition lookup_local_var_generalize_err_string (name : string) (err : string) i :
  lookup_local_var name venv err = Ret i -> forall err', lookup_local_var name venv err' = Ret i.
Proof.
 unfold lookup_local_var. intros. destruct (M_string.find (elt:=nat) name venv). auto. inv H.
Qed.


Lemma pass_function_args_correct : forall l instr,
 pass_function_args nenv venv fenv l = Ret instr ->
 repr_fun_args_Codegen fenv venv nenv l instr.
Proof.
  induction l; intros.
  - cbn in H.  inv H. constructor.
  - cbn in H. destruct (translate_local_var_read nenv venv fenv a) eqn:Hvar. inv H.
    destruct (pass_function_args nenv venv fenv l) eqn:prep. inv H. inv H.
    unfold translate_local_var_read in Hvar.
    destruct (is_function_name fenv (translate_var_to_string nenv a)) eqn:Hfname.
    - destruct (lookup_function_var (translate_var_to_string nenv a) fenv
           "translate local var read: obtaining function id") eqn:fun_var; inv Hvar.
            constructor. econstructor. unfold translate_function_var.
            unfold lookup_function_var in fun_var. eapply lookup_function_var_generalize_err_string. eassumption.
        apply IHl; auto.
    - destruct (lookup_local_var (translate_var_to_string nenv a) venv
            "translate_local_var_read: normal var") eqn:var_var; inv Hvar.
            constructor.  econstructor. eassumption. apply IHl; auto.
Qed.

Lemma set_constructor_args_correct : forall l l2,
  set_constructor_args nenv venv fenv l 1 = Ret l2 ->
  Forall_statements_in_seq_from_1 (is_nth_projection fenv venv nenv) l l2.
Proof. intros.
Admitted.


Import seq.

Theorem translate_exp_correct:
    (* find_symbol_domain p map -> *)
    (* finfo_env_correct fenv map -> *)
    correct_crep_of_env cenv rep_env ->
    forall e instructions,
      correct_cenv_of_exp cenv e ->
    translate_exp nenv cenv venv fenv e = Ret instructions ->
    repr_expr_LambdaANF_Codegen fenv venv nenv e instructions.
Proof.
  intros Hcrep e.
  induction e using exp_ind'; intros instr Hcenv; intros.
  - (* Econstr *)
    simpl in H.
    { destruct (translate_exp nenv cenv venv fenv e) eqn:H_eqTranslate; inv H.
      destruct (translate_var nenv venv v "translate_exp constr") eqn:H_translate_var. inv H1. rename i into v'.
      destruct (allocate_constructor nenv cenv venv fenv t l) eqn:alloc_constr. inv H1. inv H1.

      unfold allocate_constructor in alloc_constr.
      destruct (set_constructor_args nenv venv fenv l 1) eqn:Hconstrargs. inv alloc_constr.
         remember (grow_memory_if_necessary ((length l + 1) * 4 )) as grow.
      inv alloc_constr.
         remember (grow_memory_if_necessary ((length l + 1) * 4)) as grow.

         replace ([:: BI_get_global constr_alloc_ptr, BI_set_local v' & l0]) with
         ([:: BI_get_global constr_alloc_ptr; BI_set_local v'] ++ l0) by reflexivity.

       replace ([:: BI_get_global global_mem_ptr, BI_set_global constr_alloc_ptr,
        BI_get_global global_mem_ptr, BI_const (nat_to_value ((Datatypes.length l + 1) * 4)),
        BI_binop T_i32 (Binop_i BOI_add), BI_set_global global_mem_ptr,
        BI_get_global constr_alloc_ptr, BI_const (nat_to_value (Pos.to_nat t)),
        BI_store T_i32 None 2%N 0%N
      & l2]) with ([:: BI_get_global global_mem_ptr; BI_set_global constr_alloc_ptr;
        BI_get_global global_mem_ptr; BI_const (nat_to_value ((Datatypes.length l + 1) * 4));
        BI_binop T_i32 (Binop_i BOI_add); BI_set_global global_mem_ptr] ++
        [BI_get_global constr_alloc_ptr; BI_const (nat_to_value (Pos.to_nat t));
        BI_store T_i32 None 2%N 0%N] ++ l2) by reflexivity.

         repeat rewrite <- app_assoc. Print Rconstr_e.
        eapply Rconstr_e with (sgrow := grow) (sinit := [:: BI_get_global global_mem_ptr; BI_set_global constr_alloc_ptr;
       BI_get_global global_mem_ptr;
       BI_const (nat_to_value ((Datatypes.length l + 1) * 4));
       BI_binop T_i32 (Binop_i BOI_add); BI_set_global global_mem_ptr])
       (sstore := [:: BI_get_global constr_alloc_ptr; BI_const (nat_to_value (Pos.to_nat t));
       BI_store T_i32 None 2%N 0%N] ++
   l2) ; subst; eauto.
        econstructor. eassumption. constructor; auto.

        unfold Forall_statements_in_seq_from_1.
        Print Forall_statements_in_seq'. apply set_constructor_args_correct. assumption.

        apply IHe; auto.
        assert (subterm_e e (Econstr v t l e) ). { constructor; constructor. }
        eapply Forall_constructors_subterm. eassumption. assumption.
        }
    (*
    constructor.
    2: eapply IHe; eauto.
    clear IHe H_eqTranslate.
    apply Forall_constructors_in_constr in Hcenv.
    destruct (M.get t cenv) eqn:Hccenv. destruct c.
    subst.
    eapply repr_asgn_constructorS; eauto.
    inv Hcenv.
    eapply Forall_constructors_subterm. apply Hcenv. constructor. constructor.
        *)

  - (* Ecase nil *) simpl in H. destruct (translate_var nenv venv v "translate_exp case") eqn:Hvar. inv H. inv H.
     constructor.
  - (* Ecase const *) {
    simpl in H. destruct (translate_exp nenv cenv venv fenv e) eqn:Hexp. inv H.
      destruct ((fix translate_case_branch_expressions
           (arms : list (ctor_tag * exp)) :
             error (list (ctor_tag * list basic_instruction)) :=
           match arms with
           | [] => Ret []
           | (t, e) :: tl =>
               match translate_exp nenv cenv venv fenv e with
               | Err t0 =>
                   fun
                     _ : list basic_instruction ->
                         error
                           (list
                              (ctor_tag * list basic_instruction))
                   => Err t0
               | Ret a =>
                   fun
                     m2 : list basic_instruction ->
                          error
                            (list
                               (ctor_tag * list basic_instruction))
                   => m2 a
               end
                 (fun e' : list basic_instruction =>
                  match translate_case_branch_expressions tl with
                  | Err t0 =>
                      fun
                        _ : list
                              (ctor_tag * list basic_instruction) ->
                            error
                              (list
                                 (ctor_tag *
                                  list basic_instruction)) =>
                      Err t0
                  | Ret a =>
                      fun
                        m2 : list
                               (ctor_tag * list basic_instruction) ->
                             error
                               (list
                                  (ctor_tag *
                                   list basic_instruction)) =>
                      m2 a
                  end
                    (fun
                       arms' : list
                                 (ctor_tag *
                                  list basic_instruction) =>
                     Ret ((t, e') :: arms')))
           end) l) eqn:Hprep. inv H.
           destruct (translate_var nenv venv v "translate_exp case") eqn:Hvar. inv H. inv H.
           constructor. econstructor. eassumption. apply IHe0.
           eapply correct_cenv_case_drop_clause. eassumption.
         cbn. rewrite Hprep. rewrite Hvar. reflexivity.
            apply IHe; auto. eapply Forall_constructors_subterm; eauto. constructor. econstructor. cbn. eauto. }
   - (* Eproj *)
      { simpl in H.
      destruct (translate_exp nenv cenv venv fenv e) eqn:He. inv H.
      destruct (translate_var nenv venv v0 "translate_exp proj y") eqn:Hy. inv H.
      destruct (translate_var nenv venv v "translate_exp proj x") eqn:Hx. inv H.
      injection H => instr'. subst. clear H. constructor. apply IHe; auto.
      unfold correct_cenv_of_exp in Hcenv.
      eapply Forall_constructors_subterm. eassumption.
      unfold subterm_e. constructor. constructor.
      econstructor; eauto. econstructor; eauto. }
  - (* Eletapp *) (* non-tail call, we require CPS *)
    inv H.
  - (* Efun *)
    inv H.
  - (* Eapp *)
    simpl in H. unfold translate_call in H.
    destruct (pass_function_args nenv venv fenv l) eqn:Hargs. inv H.
    destruct (is_function_name fenv (translate_var_to_string nenv v)) eqn:Hind. inv H.
    (* direct call*)
    - { destruct (lookup_function_var (translate_var_to_string nenv v) fenv "direct function call") eqn:Hvar. inv H1. inv H1.
    constructor. apply pass_function_args_correct. assumption.
    econstructor. unfold translate_function_var. unfold translate_var_to_string. eapply lookup_function_var_generalize_err_string. eassumption. }
   (* indirect call *)
   - { destruct (lookup_local_var (translate_var_to_string nenv v) venv
        ("ind call from var: " ++ translate_var_to_string nenv v)) eqn:Hlvar. inv H.
         destruct (lookup_function_var (indirection_function_name (List.map (fun _ : var => T_i32) l))
        fenv ("didn't find ind. function for: " ++ translate_var_to_string nenv v)) eqn:Hlvar2. inv H. injection H => Heq. subst. clear H. constructor; auto.
                 apply pass_function_args_correct. assumption. eapply lookup_function_var_generalize_err_string. eassumption. }
  - (* Eprim *)
    inv H. inv H.
  - (* Ehalt *)
    simpl in H. destruct (translate_var nenv venv v "translate_exp halt") eqn:Hvar. inv H.
    injection H => instr'. subst. constructor. econstructor. eauto.
Qed.

From Wasm Require Import opsem.
(*
Definition program_inv := fun (x : nat) => I.
(* The full the domain of map is exactly the symbols of globalenv *)
Definition find_symbol_domain {A} (map:M.t A):=
   forall (x:positive), (exists V1, M.get x map = Some V1) <-> (exists b, Genv.find_symbol (Genv.globalenv p) x = Some b).

Definition finfo_env_correct :=
   forall (x:positive) i t, M.get x finfo_env = Some (i , t) -> (exists finfo, M.get t fenv = Some finfo).
*)
(*       M.get tinfIdent lenv = Some (Vptr tinf_b tinf_ofs) /\
      deref_loc (Tarray uval maxArgs noattr) m tinf_b (Ptrofs.add tinf_ofs (Ptrofs.repr 12)) (Vptr args_b args_ofs) /\ *)
(*
                                  Mem.load int_chunk m args_b (Ptrofs.unsigned (Ptrofs.add args_ofs (Ptrofs.repr int_size))) = Some Codegenv /\
                                  repr_val_L_LambdaANF_Codegen_id fenv finfo_env p rep_env v m L Codegenv.

*)

Definition result_val_LambdaANF_Codegen
 (val : LambdaANF.cps.val) (inst : instance) (sr : store_record) : Prop :=
    exists res_i32 wasmval,

      (* global var *result_var* contains correct return value *)
      sglob_val sr inst result_var = Some (VAL_int32 res_i32) /\
      wasm_value_to_i32 wasmval = res_i32 /\
      repr_val_LambdaANF_Codegen fenv venv nenv  _ val sr wasmval.


Import ssrfun ssrbool eqtype seq.

Import interpreter_sound binary_format_parser binary_format_printer host
                         datatypes_properties check_toks instantiation
                         operations opsem interpreter_sound interpreter_func interpreter_func_sound properties common.


Import eqtype.
Import Lia.
Import Relations.Relation_Operators.
Import ssreflect seq.

Lemma set_global_var_updated: forall sr fr value s',
  supdate_glob (host_function:=host_function) sr (f_inst fr) result_var value = Some s' ->
  sglob_val (host_function:=host_function) s' (f_inst fr) result_var = Some value.
Proof.
  intros. unfold supdate_glob in H. cbn in H. unfold sglob_val, sglob; cbn. destruct (inst_globs (f_inst fr)) eqn:Hgl. inv H.
  destruct l eqn:Hl. inv H. unfold g_val. subst. cbn in *. unfold supdate_glob_s in H.
  destruct (nth_error (s_globals sr) g0) eqn:Hntherr.
Admitted.


Lemma val_relation_depends_only_on_mem_and_funcs : forall v sr sr' value,
    sr.(s_mems) = sr'.(s_mems) ->
    sr.(s_funcs) = sr'.(s_funcs) ->
    repr_val_LambdaANF_Codegen fenv venv nenv host_function v sr value ->
    repr_val_LambdaANF_Codegen fenv venv nenv host_function v sr' value.
Proof.
  intros. induction H1. (* need custom induction principle ? *)
Admitted.


Lemma update_glob_keeps_memory_intact : forall sr sr' fr value,
  supdate_glob (host_function:=host_function) sr (f_inst fr) result_var
  (VAL_int32 (wasm_value_to_i32 value)) = Some sr' -> sr.(s_mems) = sr'.(s_mems).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s in H. cbn in H. destruct (inst_globs (f_inst fr)). inv H.
  destruct l. inv H. destruct l. inv H. cbn in H.
  destruct (nth_error (s_globals sr) g1). cbn in H. inv H. reflexivity. inv H.
Qed.

Lemma update_glob_keeps_funcs_intact : forall sr sr' fr value,
  supdate_glob (host_function:=host_function) sr (f_inst fr) result_var
  (VAL_int32 (wasm_value_to_i32 value)) = Some sr' -> sr.(s_funcs) = sr'.(s_funcs).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s in H. cbn in H. destruct (inst_globs (f_inst fr)). inv H.
  destruct l. inv H. destruct l. inv H. cbn in H. destruct (nth_error (s_globals sr) g1). inv H.  reflexivity.
  inv H.
Qed.

(* TODO: probably needs to be weaker *)
Definition global_var_writable var := forall (s : store_record) val inst,
  (exists s', supdate_glob s inst var val = Some s') /\
  (exists g, sglob_val (host_function:=host_function) s inst var = Some (VAL_int32 g)).

Definition INV_result_var_readwritable := global_var_writable result_var.

Definition INV_global_mem_ptr_readwritable := global_var_writable global_mem_ptr.

Definition INV_constr_alloc_ptr_readwritable := global_var_writable constr_alloc_ptr.

(*
Lemma glob_writable_implies_readable : forall (s : store_record) inst var,
  global_var_writable var -> exists g, nth_error (inst_globs inst) var = Some g.
Proof.
  intros. unfold global_var_writable in H. edestruct H.
  unfold sglob_val. unfold sglob. unfold supdate_glob in H.
  unfold sglob_ind in *.
  destruct ( (nth_error (inst_globs inst) var)) eqn:Hglob; eauto.
  unfold supdate_glob in H0. unfold sglob_ind in H0. erewrite Hglob in H0.
  cbn in H0. inv H0. Unshelve. eauto. constructor. exists 0%Z. unfold Wasm_int.Int32.modulus.
  unfold two_power_nat. lia.
Qed.
 *)

Definition INV_local_vars_exist := forall x x' fr,
  repr_var venv nenv x x' -> exists val, nth_error (f_locs fr) x' = Some (VAL_int32 val).


Definition INV_linear_memory_exists := forall sr fr,
  smem_ind (host_function:=host_function) sr (f_inst fr) =
Some 0 /\ exists m, nth_error (s_mems sr) 0 = Some m.


Definition INV_local_ptr_in_linear_memory := forall y v' x fr Hm,
  repr_var venv nenv y v'
  -> nth_error (f_locs fr) v' = Some (VAL_int32 x) ->
  exists bytes, load Hm (Wasm_int.N_of_uint i32m x) 0%N (t_length T_i32) = Some bytes.

Definition INV_global_mem_ptr_in_linear_memory := forall sr inst x,
  nth_error (inst_globs inst) global_mem_ptr = Some x ->
  exists r, nth_error (@s_globals host_function sr) x = Some r.

(*
Definition INV_constr_alloc_fn_present := forall (t : ctor_tag) (e e1 : cps.exp) x vs sr i inst ty locals body err_str,
  subterm_or_eq (Econstr x t vs e1) e ->
  lookup_function_var (constr_alloc_function_name t) fenv err_str = Ret i ->
  List.nth_error (sr.(s_funcs) : list (function_closure host_function)) i = Some (FC_func_native inst ty locals body) /\
*)


Import ssreflect.

Ltac separate_instr :=
  cbn;
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end.

(* applies r_elimr on the first const + following instr *)
Ltac elimr_nary_instr n :=
  let H := fresh "H" in
  match n with
  | 0 => lazymatch goal with
         | |- reduce _ _ _ ([::AI_basic ?instr] ++ ?l3) _ _ _ ?l4 => apply r_elimr
          end
  | 1 => lazymatch goal with
         | |- reduce _ _ _ ([::AI_basic (BI_const ?c1)] ++
                            [::AI_basic ?instr] ++ ?l3) _ _ _ ?l4 =>
            assert ([:: AI_basic (BI_const c1)] ++ [:: AI_basic instr] ++ l3
                  = [:: AI_basic (BI_const c1);
                        AI_basic instr] ++ l3) as H by reflexivity; rewrite H; apply r_elimr; clear H
          end
  | 2 => lazymatch goal with
         | |- reduce _ _ _ ([::AI_basic (BI_const ?c1)] ++
                            [::AI_basic (BI_const ?c2)] ++
                            [::AI_basic ?instr] ++ ?l3) _ _ _ ?l4 =>
            assert ([:: AI_basic (BI_const c1)] ++ [:: AI_basic (BI_const c2)] ++ [:: AI_basic instr] ++ l3
                  = [:: AI_basic (BI_const c1);
                        AI_basic (BI_const c2);
                        AI_basic instr] ++ l3) as H by reflexivity; rewrite H; apply r_elimr; clear H
          end
  end.



Lemma steps_inside_label : forall instructions state sr sr' fr fr',
 clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction)
 (reduce_tuple (host_instance:=host_instance))
 (state, sr, fr, instructions)
 (state, sr', fr', []) ->

  clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction) (reduce_tuple (host_instance:=host_instance))
  (state, sr, fr, [:: AI_label 0 [::] instructions])
  (state, sr', fr', [::]).
Proof.
  induction instructions; intros.
  - constructor. eapply r_label with (k:=0) (lh := LH_base [] []). admit. apply /lfilledP.  cbn. cbn. unfold lfilled, lfill. cbn. unfold eqseq. cbn. eauto.
Admitted.


Ltac dostep :=
  eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s] ++ ?[t])); first  apply rt_step.

(* only returns single list of instructions *)
Ltac dostep' :=
   eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s])); first  apply rt_step.

Ltac dostep_label :=
   eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s])); first apply steps_inside_label.


(*
Example label_red : forall sr fr state c,
  reduce_trans (state, sr, fr, [:: AI_label 0 [::] [:: AI_basic (BI_const c)]]) (state, sr, fr, [:: AI_basic (BI_const c)]).
Proof.
  intros. constructor. cbn. apply r_label with (k:= 1)(es:=[])(es' := [])(lh := LH_base [] []).
  all: cbn.
 *)

Print caseConsistent.

Theorem caseConsistent_findtag_In_cenv:
  forall cenv t e l,
    caseConsistent cenv l t ->
    findtag l t = Some e ->
    exists (a aty:BasicAst.name) (ty:ind_tag) (n:N) (i:N), M.get t cenv = Some (Build_ctor_ty_info a aty ty n i).
Proof.
  destruct l; intros.
  - inv H0.
  - inv H. destruct info.
    exists ctor_name, ctor_ind_name, ctor_ind_tag,ctor_arity,ctor_ordinal; auto.
Qed.

(* H0 : nthN vs n = Some v
Hev : bstep_e (M.empty (seq cps.val -> option cps.val)) cenv
        (map_util.M.set x v rho) e ov c
IHHev : forall (instructions : seq basic_instruction)
          (f : frame) (hs : host_state) (sr : store_record),
        INV_result_var_writable ->
        INV_linear_memory_exists ->
        INV_local_ptr_in_linear_memory ->
        INV_local_vars_exist ->
        repr_expr_LambdaANF_Codegen fenv venv nenv e instructions ->
        rel_mem_LambdaANF_Codegen fenv venv nenv host_function e
          (map_util.M.set x v rho) sr f ->
        exists (sr' : store_record) (f' : frame),
          reduce_trans (hs, sr, f, [seq AI_basic i | i <- instructions])
            (hs, sr', f', [::]) /\ result_val_LambdaANF_Codegen ov (f_inst f) sr'
fr : frame
state : host_state
sr : store_record
INVres : INV_result_var_writable
INVlinmem : INV_linear_memory_exists
INVptrInMem : INV_local_ptr_in_linear_memory
INVlocals : forall (x : positive) (x' : immediate) (fr : frame),
            repr_var venv nenv x x' ->
            exists val : i32, nth_error (f_locs fr) x' = Some (VAL_int32 val)
x', y' : immediate
e' : seq basic_instruction
Hrel_m : rel_mem_LambdaANF_Codegen fenv venv nenv host_function
           (Eproj x t n y e) rho sr fr
H7 : repr_expr_LambdaANF_Codegen fenv venv nenv e e'
H8 : repr_var venv nenv x x'
H9 : repr_var venv nenv y y'
Hrho : rho ! y = Some (Vconstr t vs)
addr : nat
Hrepr : repr_val_LambdaANF_Codegen fenv venv nenv host_function
          (Vconstr t vs) sr (Val_ptr addr)
Hlocal : stored_in_locals venv nenv y (Val_ptr addr) fr
Hfun : forall (x : positive) (rho' : M.t cps.val) (fds : fundefs)
         (f : var) (v : cps.val),
       exists i : immediate,
         rho ! x = Some v ->
         subval_or_eq (Vfun rho' fds f) v ->
         translate_function_var nenv fenv f = Ret i /\
         repr_val_LambdaANF_Codegen fenv venv nenv host_function
           (Vfun rho' fds f) sr (Val_funidx i) /\ closed_val (Vfun rho' fds f)
Hvar : forall x0 : var,
       occurs_free (Eproj x t n y e) x0 ->
       exists (v6 : cps.val) (val : wasm_value),
         rho ! x0 = Some v6 /\
         stored_in_locals venv nenv x0 val fr /\
         repr_val_LambdaANF_Codegen fenv venv nenv host_function v6 sr val
m : memory
H2 : nth_error (s_mems sr) 0 = Some m
H3 : load_i32 m (N.of_nat addr) = Some (VAL_int32 (tag_to_i32 t))
H6 : repr_val_constr_args_LambdaANF_Codegen fenv venv nenv host_function vs sr
       (4 + addr)
Hvy : repr_var venv nenv y y'
H : nth_error (f_locs fr) y' = Some (VAL_int32 (nat_to_i32 addr))*)

Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Structures.OrderedTypeEx.

Lemma extract_constr_arg : forall n vs v sr addr m,
  nthN vs n = Some v ->
  nth_error (s_mems sr) 0 = Some m ->
  repr_val_constr_args_LambdaANF_Codegen fenv venv nenv host_function vs sr addr ->
  exists bs wal, load m (N.of_nat addr + 4 * n) 0%N 4 = Some bs /\
             VAL_int32 (wasm_value_to_i32 wal) = wasm_deserialise bs T_i32 /\
             repr_val_LambdaANF_Codegen fenv venv nenv host_function v sr wal.
Proof.
  intros. generalize dependent v. generalize dependent n. generalize dependent m.
  induction H1; intros.
  - inv H.
  - assert (n = N.of_nat (N.to_nat n)) by lia. rewrite H5 in H4. clear H5. generalize dependent v0.
    induction (N.to_nat n); intros.
    + inv H4. rewrite H in H3. inv H3. rename m0 into m. rewrite N.add_comm. cbn.
      unfold load_i32 in H0. destruct (load m (N.of_nat addr) (N.of_nat 0) 4) eqn:Hl; try inv H0.
       exists b. exists wal. repeat split.
       destruct n; cbn; auto.
        admit. admit. assumption. (* minus modulo *)
    + simpl in H4. destruct (Pos.of_succ_nat n0). cbn in H4.
      edestruct IHrepr_val_constr_args_LambdaANF_Codegen. eassumption.
      eassumption. destruct H5 as [wal' [Hl [Heq Hval]]].
      (*
     inv H4. rewrite H in H3. inv H3. rename m0 into m. cbn. rewrite N.add_comm. cbn.
        unfold load_i32 in H0. destruct (load m (N.of_nat addr) (N.of_nat 0) 4) eqn:Hl; try inv H0. exists b. exists wal. repeat split; auto. admit. (* same as above *)
      *


  induction n; intros.
  - (* n=0 *)
    destruct vs; inv H. inv H1.
    unfold load_i32 in H4. destruct (load m0 (N.of_nat addr) (N.of_nat 0) 4) eqn:Hl; try by inv H4. rewrite H0 in H3. inv H3. rename m0 into m.
    cbn in Hl. cbn. rewrite N.add_comm. exists b. exists wal.
    repeat split; auto. f_equal.
    unfold wasm_deserialise in H4. symmetry. injection H4 => H4'.
    unfold wasm_value_to_i32.
    unfold Wasm_int.Int32.repr. simpl. Check ({|
  Wasm_int.Int32.intval := Wasm_int.Int32.Z_mod_modulus (decode_int b);
  Wasm_int.Int32.intrange := Wasm_int.Int32.Z_mod_modulus_range' (decode_int b)
|}). Print Wasm_int.Int32.int. unfold Wasm_int.Int32.repr. (* rewrite <- H1.
     inv H4. unfold wasm_value_to_immediate in H1.
     unfold wasm_value_to_i32, wasm_value_to_immediate, decode_int. f_equal. destruct wal. unfold rev_if_be.
     unfold int_of_bytes. unfold int_ cbn. *) admit.
  - (* IH *)

  - inv H1. rewrite H0 in H4. inv H4.
    destruct n.
    + inv H.
    +
    have IH := IHvs n v wal.


  intros. generalize dependent v. generalize dependent n. generalize dependent m. generalize dpen
  induction vs; intros; inv H1.
  - inv H.
  -
  induction H1; intros.
  - inv H.
  - cbn. destruct n.
    + injection H4 => H4'. subst.
      rewrite H0 in H. injection H => H'. subst m0. clear H.
      unfold load_i32 in H1.
      destruct (load m (N.of_nat addr) (N.of_nat 0) 4) eqn:Heq.
      exists b. split; intros.
      assert (N.of_nat addr + 0 = N.of_nat addr)%N by lia. rewrite H. clear H.
      assumption. split. f_equal.
      injection H1 => H1'. *)
Admitted.

(* TODO RENAME *)
Lemma arith_addr_helper : forall n addr, Wasm_int.N_of_uint i32m
     (Wasm_int.Int32.iadd (wasm_value_to_i32 (Val_ptr addr))
        (nat_to_i32 ((N.to_nat n + 1) * 4))) = (N.of_nat (4 + addr) + 4 * n)%N .
Proof.
  intros. unfold wasm_value_to_i32, wasm_value_to_immediate, nat_to_i32.
  assert ((Z.of_nat
           (N.to_nat n + 1 +
            (N.to_nat n + 1 + (N.to_nat n + 1 + (N.to_nat n + 1 + 0))))) = Z.of_nat (4 * (1 + N.to_nat n))) by lia.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
admit. Admitted. (* TODO: wrong, assert that n < Int32.max *)

Lemma repr_bs_LambdaANF_Codegen_related_case : True. constructor. Qed.

(*
H : rho ! y = Some (Vconstr t vl)
H1 : findtag ((t0, e0) :: cl0) t = Some e
Hev : bstep_e (M.empty (seq cps.val -> option cps.val)) cenv rho e v c
IHHev : forall (instructions : seq basic_instruction) (f : frame) (hs : host_state)
          (sr : store_record),
        INV_result_var_writable ->
        INV_linear_memory_exists ->
        INV_local_ptr_in_linear_memory ->
        INV_local_vars_exist ->
        repr_expr_LambdaANF_Codegen fenv venv nenv e instructions ->
        rel_mem_LambdaANF_Codegen fenv venv nenv host_function e rho sr f ->
        exists (sr' : store_record) (f' : frame),
          reduce_trans (hs, sr, f, [seq AI_basic i | i <- instructions]) (hs, sr', f', [::]) /\
          result_val_LambdaANF_Codegen v (f_inst f) sr'
INVres : INV_result_var_writable
INVlinmem : INV_linear_memory_exists
INVptrInMem : INV_local_ptr_in_linear_memory
INVlocals : INV_local_vars_exist
Hrel_m : rel_mem_LambdaANF_Codegen fenv venv nenv host_function (Ecase y ((t0, e0) :: cl0)) rho
           sr fr
v' : immediate
instrs_more, e' : seq basic_instruction
H4 : repr_var venv nenv y v'
H5 : repr_expr_LambdaANF_Codegen fenv venv nenv (Ecase y cl0) instrs_more
H7 : repr_expr_LambdaANF_Codegen fenv venv nenv e0 e'
______________________________________(1/1)
exists (sr' : store_record) (f' : frame),
  reduce_trans
    (state, sr, fr,
    [seq AI_basic i
       | i <- [:: BI_get_local v'; BI_load T_i32 None (N.of_nat 2) (N.of_nat 0);
                  BI_const (nat_to_value (Pos.to_nat t0)); BI_relop T_i32 (Relop_i ROI_eq);
                  BI_if (Tf [::] [::]) e' instrs_more]]) (state, sr', f', [::]) /\
  result_val_LambdaANF_Codegen v (f_inst fr) sr'


*)



(* MAIN THEOREM, corresponds to 4.3.2 in Olivier's thesis *)
Theorem repr_bs_LambdaANF_Codegen_related:

  (*
  forall (p : program) (rep_env : M.t ctor_rep) (cenv : ctor_env)
         (finfo_env : M.t (positive * fun_tag)) (ienv : n_ind_env), *)
  (*  program_inv p -> (* isPtr function is defined/correct /\ thread info is correct /\ gc invariant *)
    find_symbol_domain p finfo_env -> (* finfo_env [LambdaANF] contains precisely the same things as global env [Clight] *)
    finfo_env_correct fenv finfo_env -> (* everything in finfo_env is in the function environment *) *)
    forall (rho : eval.env) (v : cps.val) (e : exp) (n : nat), (* rho is environment containing outer fundefs. e is body of LambdaANF program *)
      bstep_e (M.empty _) cenv rho e v n ->  (* e n-steps to v *) (* for linking: environment won't be empty *)
      (* correct_envs cenv ienv rep_env rho e -> (* inductive type/constructor environments are correct/pertain to e*) *)
      (* protected_id_not_bound_id rho e ->
      unique_bindings_env rho e -> *)
      (* functions_not_bound p rho e -> (* function names in p/rho not bound in e *) *)
      forall (instructions : list basic_instruction) (f : frame) (hs : host_state) (sr : store_record) (*(k : cont) (max_alloc : Z) (fu : function) *),

        (* invariants *)
        INV_result_var_readwritable ->
        INV_global_mem_ptr_readwritable ->
        INV_constr_alloc_ptr_readwritable ->

        INV_linear_memory_exists ->
        INV_local_ptr_in_linear_memory ->
        INV_global_mem_ptr_in_linear_memory ->
        INV_local_vars_exist ->

        repr_expr_LambdaANF_Codegen fenv venv nenv e instructions -> (* translate_body e returns stm *)
        rel_mem_LambdaANF_Codegen fenv venv nenv _ e rho sr f ->
        (* " relates a LambdaANF evaluation environment [rho] to a Clight memory [m/lenv] up to the free variables in e " *)
        (* also says fundefs in e are correct in m *)
        (* NOTE: this is only place pertaining to outside of the body, and can likely incorporate free variables here *)
       (* correct_alloc e max_alloc ->  (* max_alloc correct *)
        correct_tinfo p max_alloc lenv m -> (* thread_info correct *) *)
        exists (sr' : store_record) (f' : frame),
          reduce_trans (hs, sr, f, map AI_basic instructions) (hs, sr', f', []) /\
          (* memory m/lenv becomes m'/lenv' after executing stm *)
          result_val_LambdaANF_Codegen v f.(f_inst) sr'. (* value v is related to memory m'/lenv' *)
Proof.
  intros rho v e n Hev.
  induction Hev; intros Hc_env fr state sr INVres INVgmp INVcap INVlinmem INVptrInMem INVglobalptrInMem INVlocals Hrepr_e Hrel_m; inv Hrepr_e.
  - (* Econstr *)
    { remember (grow_memory_if_necessary ((Datatypes.length ys + 1) * 4)) as grow.
      cbn. repeat rewrite map_cat. cbn. rewrite map_cat. cbn.
      subst. unfold grow_memory_if_necessary.

      eexists. eexists. split.

      (* increase memory if necessary *)
      have Hw := INVgmp. edestruct Hw. destruct H1. cbn.
      unfold INV_global_mem_ptr_in_linear_memory in INVglobalptrInMem.
      (* load global_mem_ptr *)
      dostep. separate_instr. elimr_nary_instr 0.
      apply r_get_global. eassumption.
      (* add required bytes *)
      dostep. separate_instr. elimr_nary_instr 2. constructor.
      apply rs_binop_success. reflexivity.
      dostep. separate_instr. elimr_nary_instr 2. constructor.
      apply rs_binop_success.
      admit. (* addition correct *)
      dostep. apply r_eliml; auto.
      elimr_nary_instr 0. eapply r_current_memory.


      admit. }
  - (* rename v' into y'.
    { remember (Ecase y cl) as exp. generalize dependent Heqexp. generalize dependent e. generalize dependent t. induction Hrepr_e; intros; inv Heqexp; first inv H1.
    inv Hrepr_e.

  induction Hrepr_e. *)
  - (* Eproj ctor_tag t, let x := proj_n y in e *)
    rename s into e'. rename v' into y'.

    (* y is constr value with correct tag, arity *)
    assert (Hy : occurs_free (Eproj x t n y e) y) by constructor.
    have Hrel_m' := Hrel_m.
    destruct Hrel_m' as [Hfun Hvar].
    apply Hvar in Hy. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
    rewrite Hrho in H. inv H.
    have Hrepr' := Hrepr. inv Hrepr'.

    inv Hlocal. destruct H.

    have Hextr := extract_constr_arg n vs v _ _ _ H0 H2 H6.
    destruct Hextr as [bs [wal [Hload [Heq Hbsval]]]].

     assert (Hrm: rel_mem_LambdaANF_Codegen fenv venv nenv host_function e (map_util.M.set x v rho) sr
  {|
    f_locs := set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32);
    f_inst := f_inst fr
  |}). {
  split; intros. admit. (* x not a fundef *)

  destruct (var_dec x x1).
  (* x = x1 *)
  subst x1.
  exists v. exists (Val_ptr ((4 + addr) + 4 * N.to_nat n)). split.
  rewrite map_util.M.gsspec.
  apply peq_true.
  split. exists x'. split.
  inv H8. unfold translate_var in H5. unfold translate_var. eapply lookup_local_var_generalize_err_string. eassumption.
  rewrite <- Heq. admit. (* nth_error set_nth correct *)
  admit.

  (* x <> x1 *)
  assert (occurs_free (Eproj x t n y e) x1). { constructor; assumption. }
  apply Hvar in H5. destruct H5 as [v6 [wal' [Henv [Hloc Hval]]]].
  exists v6. exists wal'. repeat split.
  rewrite map_util.M.gsspec.
  rewrite peq_false. assumption. intro. subst. contradiction.
  cbn.
  admit. (* different vars -> different wasm local vars *)
  assumption.
  }


   have IH := IHHev e' (Build_frame (set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32)) fr.(f_inst)) state sr INVres INVgmp INVcap INVlinmem INVptrInMem INVglobalptrInMem INVlocals H7 Hrm. destruct IH as [sr' [f' [Hred Hval]]].

    eexists. eexists. cbn. split.
    { (* take steps *)
    have Hvy := H9. inv H9.

    unfold INV_local_vars_exist in INVlocals.
    destruct (INVlocals _ _ fr Hvy).
    rewrite H in H4. injection H4 => H4'. subst. clear H4.
    rewrite H1 in H5. injection H5 => H5'. subst. clear H5.

    (* get_local y' *)
    dostep. separate_instr. elimr_nary_instr 0.
    apply r_get_local. apply H1.

    (* add offset n *)
    dostep. separate_instr. elimr_nary_instr 2.
    constructor. apply rs_binop_success. cbn. reflexivity.

    inv Hrepr.

    dostep. separate_instr. elimr_nary_instr 1.
    eapply r_load_success.


    unfold INV_linear_memory_exists in INVlinmem.
    specialize INVlinmem with sr fr. destruct INVlinmem as [Hmem1 [m' Hmem2]].
    eassumption. apply H2.

    rewrite arith_addr_helper. apply Hload.

    (* save result in x' *)
    have Hx := H8. inv H8.

    cbn.
    (* dostep' with fr *)
    eapply rt_trans with (y := (?[hs], ?[sr], {|
           f_locs :=
             set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32);
           f_inst := f_inst fr
         |}, ?[s])); first  apply rt_step.

    cbn. separate_instr. elimr_nary_instr 1.
    apply r_set_local with (vd := (wasm_deserialise bs T_i32)). reflexivity.

    have Hloc := INVlocals x x' fr Hx. destruct Hloc.
    apply /ssrnat.leP.
    assert (x' < length (f_locs fr)). { apply nth_error_Some. congruence. } lia.
    reflexivity.
    cbn.
    apply Hred.
    }
    apply Hval.
(*     transitivity (f_locs (Build_frame (set_nth (VAL_int32 (Wasm_int.Int32.repr (decode_int x0)))
  (f_locs fr) x' (VAL_int32 (Wasm_int.Int32.repr (decode_int x0)))) fr.(f_inst))). reflexivity. reflexivity.

    cbn. _ _ _ _.  INVlocals INVres INVlinmem INVlocals.

    (* constructor *)
    eapply can_load_constr_args in H10. destruct H10 as [bs [Hb1 [Hb2 Hb3]]].


    assert ((N.of_nat (addr + 4 * (N.to_nat n + 1))) =  (Wasm_int.N_of_uint i32m
     (Wasm_int.Int32.iadd (wasm_value_to_i32 (Val_ptr addr))
        (nat_to_i32
           (N.to_nat n + 1 +
            (N.to_nat n + 1 +
             (N.to_nat n + 1 + (N.to_nat n + 1 + 0)))))))) as Harith. { cbn. admit. }
             rewrite <- Harith. apply Hb1.


    unfold INV_local_vars_exist in INVlocals.
    have H' := INVlocals _ _ _ H8. specialize H' with fr.
    apply /ssrnat.leP. lia.
    admit. }

    cbn.

    have IH := IHHev s _ state sr INVres INVlinmem INVlocals H7. admit. admit. admit. } *)

  - (* Ecase_nil *)
    inv H1. (* absurd *)
  - (* Ecase_cons *) {
    (*
    remember ([:: BI_get_local v'; BI_load T_i32 None (N.of_nat 2) (N.of_nat 0);
                BI_const (nat_to_value (Pos.to_nat t0));
                BI_relop T_i32 (Relop_i ROI_eq);
                BI_if (Tf [::] [::]) e' instrs_more]) as code. induction Hrepr_e; inv Heqcode. *)

    (* y is constr value with tag *)
    assert (Hy : occurs_free (Ecase y ((t0, e0) :: cl0)) y) by constructor.
    have Hrel_m' := Hrel_m.
    destruct Hrel_m' as [Hfun Hvar].
    apply Hvar in Hy. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
    rewrite Hrho in H. inv H.
    have Hrepr' := Hrepr. inv Hrepr'.
    inv Hlocal. rename x into y'. destruct H.

    have Hx := H1. unfold findtag in Hx.
    cbn in Hx. destruct (M.elt_eq t0 t); first injection Hx => Hx'.
    (* t0 = t *)
    subst. clear Hx.
    { (* have Hrel_m' := Hrel_m.
      destruct Hrel_m' as [Hrel_m_fn Hrel_m_ptr]. *)

      assert (Hw: rel_mem_LambdaANF_Codegen fenv venv nenv host_function e rho sr fr). admit.

      have IH := IHHev e' fr state sr INVres INVgmp INVcap INVlinmem INVptrInMem INVglobalptrInMem INVlocals H7 Hw.
      destruct IH as [sr' [f' [Hred Hres]]].

      have Hconsist := caseConsistent_findtag_In_cenv _ _ _ _ H0 H1.
      destruct Hconsist as [a [aty [ty [n [i Hconstr]]]]].

       have H' := INVlocals _ _ fr H4. destruct H' as [? H'].

      (* execute wasm instructions *)
      eexists. eexists. cbn. split.

      dostep. separate_instr.
      unfold rel_mem_LambdaANF_Codegen in Hrel_m.
      eapply r_elimr. apply r_get_local. apply H'.

      destruct (INVlinmem sr fr) as [Hm1 [m' Hm2]].
      (* ptr in mem *)
      (* unfold INV_local_ptr_in_linear_memory in INVptrInMem. *)
      have HMem := INVptrInMem _ _ _ _ m' H4 H'. destruct HMem.

      dostep. cbn. separate_instr. elimr_nary_instr 1.
      eapply r_load_success; try eassumption.

      destruct (Wasm_int.Int32.eq (Wasm_int.Int32.repr (decode_int x0))
            (nat_to_i32 (Pos.to_nat t))) eqn:Hbool; cbn.

      { (* ctag comparison true *)
      dostep. cbn. separate_instr. elimr_nary_instr 2.
      constructor. apply rs_relop.

      dostep'. cbn. constructor. eapply rs_if_true. by rewrite Hbool.

      dostep'. cbn. constructor. eapply rs_block with (vs := []); cbn; auto.

      cbn. unfold to_e_list.
      dostep_label.
      apply Hred.
      apply rt_refl.
      }
      { (* ctag comparison false *)
      dostep'. cbn. separate_instr. elimr_nary_instr 2.
      constructor. apply rs_relop. cbn.

      dostep'. cbn. constructor. eapply rs_if_false. by rewrite Hbool.

      dostep'. cbn. constructor. eapply rs_block with (vs := []); cbn; auto.
      cbn. unfold to_e_list.

      dostep_label. 2: apply rt_refl.
  admit. } admit. } admit. }
  - (* Eapp_direct *)
  (*   rewrite map_cat.
    assert (occurs_free (Eapp f t ys) f) by constructor.

    eexists. eexists. split. rewrite map_cat. cbn.
    Check r_eliml. cbn.
    dostep'. cbn. apply r_eliml. admit. (* args' const *)
    apply r_call. admit. admit. admit. *)
 admit.
  - (* Eapp_indirect *) admit.
  - (* Ehalt *)
    cbn. destruct Hrel_m. destruct (H2 x) as [v6 [wal [Henv [Hloc Hrepr]]]]. constructor.
    rewrite Henv in H. inv H.

    unfold INV_result_var_readwritable, global_var_writable in INVres.
    specialize INVres with sr (VAL_int32 (wasm_value_to_i32 wal)) (f_inst fr).
    destruct INVres as [[s' Hs] [g Hg]].

    exists s'. eexists fr.

    destruct H1.
    destruct Hloc as [ilocal [H3 Hilocal]]. split. erewrite H3 in H. injection H => H'. subst. clear H.
    (* execute wasm instructions *)
    dostep. separate_instr. apply r_elimr. eapply r_get_local. eassumption.
    dostep'. apply r_set_global. eassumption.
    apply rt_refl.

    exists (wasm_value_to_i32 wal). exists wal.
    repeat split. eapply set_global_var_updated. eassumption.
    apply val_relation_depends_only_on_mem_and_funcs with sr...
    eapply update_glob_keeps_memory_intact. eassumption.
    eapply update_glob_keeps_funcs_intact. eassumption. assumption.
Admitted.




(*
  - (* Econstr *)

    assert (Hx_not:  ~ is_protected_id_thm  x). {
          intro. inv Hp_id. eapply H2; eauto.
    }


    (* get the tempenv and mem after assigning the constructor *)
    assert (exists lenv' m',
               ( clos_trans state (traceless_step2 (globalenv p))
                                     (State fu s (Kseq s' k) empty_env lenv m)
                                     (State fu Sskip (Kseq s' k) empty_env lenv' m') )
               /\  rel_mem_LambdaANF_Codegen_id fenv finfo_env p rep_env e (M.set x (Vconstr t vs) rho) m' lenv'
               /\ correct_tinfo p (Z.of_nat (max_allocs e)) lenv' m' /\
                   same_args_ptr lenv lenv').
    {
      inv H6.
      - (* boxed *)

        assert (Ha_l : a = N.of_nat (length ys) /\ ys <> []). {
          assert (subterm_or_eq (Econstr x t ys e) (Econstr x t ys e)) by constructor 2.
          inv Hc_env. destruct H5 as [H5' H5]. destruct H5 as [H5 H6].
          apply H5 in H3.   destruct (M.get t cenv) eqn:Hmc. destruct c0. inv H6.
          apply H9 in H0. inv H0. rewrite H10 in Hmc. inv Hmc.
          split; auto. destruct ys. inv H2. intro. inv H0. inv H3.
        }


        (* 1 -> get the alloc info, steps through the assignment of the header *)
        assert (Hc_tinfo' := Hc_tinfo).
        unfold correct_tinfo in Hc_tinfo.
        destruct Hc_tinfo as [alloc_b [alloc_ofs [limit_ofs [args_b [args_ofs [tinf_b [tinf_ofs [Hget_alloc [Halign_alloc [Hrange_alloc [Hget_limit [Hbound_limit [Hget_args [Hdj_args [Hbound_args [Hrange_args [Htinf1 [Htinf2 [Htinf3 [Hinf_limit [Htinf_deref Hglobals]]]]]]]]]]]]]]]]]]]]].

        assert (~ is_protected_id_thm x).
        { intro. inv Hp_id. eapply H5; eauto. }

        assert (Hx_loc_eq : (Ptrofs.add (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr Z.one))) (Ptrofs.mul (Ptrofs.repr int_size) (Ptrofs.repr (-1)))) = alloc_ofs). {
          rewrite Ptrofs.add_assoc.
          rewrite Ptrofs.mul_mone.
          rewrite Ptrofs.mul_one.
          rewrite Ptrofs.add_neg_zero.
          apply Ptrofs.add_zero.
        }


        assert ( {m2 : mem |  Mem.store int_chunk m alloc_b
                                      (Ptrofs.unsigned alloc_ofs) (make_vint h) = Some m2}). {
          apply Mem.valid_access_store.
          split.
          intro.
          intro. apply Hrange_alloc.
          unfold int_size in *.
          simpl size_chunk in *.
          inv H4.
          split; auto.
          eapply OrdersEx.Z_as_OT.lt_le_trans. eauto.
          inv Hbound_limit.
          inv Hc_alloc. simpl max_allocs. destruct ys. exfalso; inv Ha_l; auto. simpl max_allocs in H4.
          rewrite Nat2Z.inj_succ in H4. chunk_red; lia.
          auto.
        }
        destruct X as [m2 Hm2].

        assert (Hstep_m2 : clos_trans state (traceless_step2 (globalenv p))
                            (State fu
         (Ssequence
            (Ssequence
               (Ssequence
                  (Sset x
                     (Ecast
                        (add (Etempvar allocIdent (Tpointer val {| attr_volatile := false; attr_alignas := None |}))
                           (c_int' Z.one val)) val))
                  (Sset allocIdent
                     (add (Etempvar allocIdent (Tpointer val {| attr_volatile := false; attr_alignas := None |}))
                        (c_int' (Z.of_N (a + 1)) val))))
               (Sassign
                  (Ederef
                     (add (Ecast (Etempvar x val) (Tpointer val {| attr_volatile := false; attr_alignas := None |}))
                          (c_int' (-1)%Z val)) val) (c_int' h val))) s0) (Kseq s' k) empty_env lenv m)
                           (State fu s0 (Kseq s' k) empty_env
       (Maps.PTree.set allocIdent
          (Vptr alloc_b (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr (Z.of_N (a + 1))))))
          (Maps.PTree.set x
             (Vptr alloc_b (Ptrofs.add alloc_ofs (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv p) val)) (Ptrofs.repr Z.one)))) lenv)) m2)).
        {
          eapply t_trans. constructor. constructor.
          eapply t_trans. constructor. constructor.
          eapply t_trans. constructor. constructor.
          chunk_red; archi_red.
          (* branch ptr64 *)

          {
            eapply t_trans. constructor. constructor. econstructor.
            econstructor. constructor. eauto. constructor. constructor.
            constructor.
            eapply t_trans. constructor. constructor.

            eapply t_trans. constructor. constructor.
            econstructor. constructor. rewrite M.gso.
            eauto. intro. apply H3. rewrite <- H4. inList.
            constructor. constructor.
            eapply t_trans. constructor. constructor.
            eapply t_trans. constructor. econstructor. constructor. simpl. econstructor.
            econstructor. constructor. rewrite M.gso. rewrite M.gss. reflexivity.
            intro. apply H3. rewrite  H4. inList.
            constructor. econstructor. constructor. constructor. constructor. simpl.
            econstructor. econstructor.  simpl.  unfold Ptrofs.of_int64. rewrite ptrofs_of_int64. rewrite ptrofs_of_int64.
            rewrite Hx_loc_eq. eauto.
            constructor. unfold Ptrofs.of_int64. do 2 (rewrite ptrofs_of_int64).
            constructor.
          }
*)


Definition extract_const g := match g.(modglob_init) with (* guarantee non-divergence during instantiation *)
| [:: BI_const c] => Ret c
| _ => Err "only constants allowed during instantiation"%bs
end : error value.

Definition extract_i32 instr :=  match instr with
   | [:: BI_const (VAL_int32 i)] => Ret i
   | _ => Err "expected const i32"%bs
end : error i32.

(* error monad from certicoq *)
Definition interp_instantiate (s : store_record) (m : module) (v_imps : list v_ext)
  : error (store_record * instance * list module_export) :=
  match module_type_checker m with
  | None => Err "module_type_checker failed"%bs
  | Some (t_imps, t_exps) =>
    if seq.all2 (external_type_checker _ s) v_imps t_imps then
      let inst_c := {|
            inst_types := nil;
            inst_funcs := nil;
            inst_tab := nil;
            inst_memory := nil;
            inst_globs := List.map (fun '(Mk_globalidx i) => i) (ext_globs v_imps);
          |} in
      (* init global vars *)
      g_inits <- sequence (List.map extract_const m.(mod_globals));;

      let '(s', inst, v_exps) := interp_alloc_module _ s m v_imps g_inits in

      e_offs <- sequence (List.map (fun e => extract_i32 e.(modelem_offset)) m.(mod_elem));;
      d_offs <- sequence (List.map (fun d => extract_i32 d.(moddata_offset)) m.(mod_data));;

      if check_bounds_elem _ inst s' m e_offs &&
         check_bounds_data _ inst s' m d_offs then
        match m.(mod_start) with
        | Some _ => Err "start function not supported"%bs
        | None =>
          let s'' := init_tabs _ s' inst (List.map nat_of_int e_offs) m.(mod_elem) in
          let s_end := init_mems _ s' inst (List.map N_of_int d_offs) m.(mod_data) in
          Ret (s_end, inst, v_exps)
        end
      else Err "bounds check failed"%bs
    else Err "external_type_checker failed"%bs
  end.

Definition empty_store_record : store_record := {|
    s_funcs := nil;
    s_tables := nil;
    s_mems := nil;
    s_globals := nil;
  |}.

Definition interp_instantiate_wrapper (m : module)
  : error (store_record * instance * list module_export) :=
  interp_instantiate empty_store_record m nil.


(* MAIN THEOREM, corresponds to 4.3.1 in Olivier's thesis *)

Corollary LambdaANF_Codegen_related :
  forall (rho : eval.env) (v : cps.val) (e : exp) (n : nat), (* rho is environment containing outer fundefs. e is body of LambdaANF program *)

  forall module sr hs inst exports mainidx function,

  (* evaluation of LambdaANF expression *)
  bstep_e (M.empty _) cenv rho e v n ->

  (* compilation function *)
  LambdaANF_to_WASM nenv cenv e = Ret module ->

  (* TODO, this could be a theorem? *)
  interp_instantiate_wrapper module = Ret (sr, inst, exports) ->

  List.nth_error sr.(s_funcs) mainidx = Some function ->
  (* codegen relation with e = let fundefs in mainexpr *)

    exists (sr' : store_record),
       reduce_trans (hs, sr,  (Build_frame [] inst), [ AI_basic (BI_call mainidx) ])
                    (hs, sr', (Build_frame [] inst), [])    /\

       result_val_LambdaANF_Codegen v inst sr'.
Proof.
  intros. eexists. split.
  eapply rt_trans with (y := (?[hs], ?[sr], ?[f], ?[t])).
  apply rt_step. eapply r_call.
Admitted.


End THEOREM.
