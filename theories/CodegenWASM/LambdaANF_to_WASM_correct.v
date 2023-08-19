
(*
  Proof of correctness of the WASM code generation phase of CertiCoq
  (this file is based on the proof for Clight code generation, it still contains some relicts that have not beed removed yet.)

  > Relates expressions to Wasm instructions (codegen relation, syntactic)
  > Relates LambdaANF values to Wasm values (value relation)
  > Relates values to location in memory (memory relation, syntactic)
  > Relates LambdaANF states to Wasm states according to execution semantics
 *)
Unset Universe Checking.


From mathcomp Require Import eqtype.

From compcert Require Import Coqlib.

Require Import LambdaANF.cps LambdaANF.eval LambdaANF.cps_util LambdaANF.List_util LambdaANF.Ensembles_util LambdaANF.identifiers LambdaANF.tactics LambdaANF.shrink_cps_corresp.


Require Import Coq.ZArith.BinInt.
Require Import Lia.
Require Export Int31.



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

From Wasm Require Import datatypes datatypes_properties operations host interpreter_sound type_preservation
                         binary_format_printer check_toks instantiation memory_list
                         opsem interpreter_func interpreter_func_sound properties common.

Require Import Libraries.maps_util.

Open Scope list.

Import ListNotations.


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
  -  specialize (IHclos_trans2 t vs Logic.eq_refl).
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
  Variable cenv:LambdaANF.cps.ctor_env.
  Variable funenv:LambdaANF.cps.fun_env.
  Variable fenv : CodegenWASM.LambdaANF_to_WASM.fname_env.
  Variable lenv : CodegenWASM.LambdaANF_to_WASM.localvar_env.
  Variable nenv : LambdaANF.cps_show.name_env.
  Variable finfo_env: LambdaANF_to_Clight.fun_info_env. (* map from a function name to its type info *)

  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t ctor_rep.



Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show.
Import Common.Common Common.compM Common.Pipeline_utils.

Import ExtLib.Structures.Monad.
Import MonadNotation.


(* all boxed -> list can be empty *)
Inductive Forall_statements_in_seq' {A}: (nat  -> A -> list basic_instruction -> Prop) ->  list A -> list basic_instruction -> nat -> Prop :=
| Fsis_nil : forall (R: (nat  -> A -> list basic_instruction -> Prop)) n, Forall_statements_in_seq' R [] [] n
| Fsis_cons : forall R v vs s s' n, Forall_statements_in_seq' R vs s' (S n) ->
                                   R n v s ->  Forall_statements_in_seq' R (v::vs) (s ++ s') n.


(* This is true for R, vs and S iff forall i, R i (nth vs) (nth s)
   > nth on statement is taken as nth on a list of sequenced statement (;) *)
Definition Forall_statements_in_seq {A}: (nat  -> A -> list basic_instruction -> Prop) ->  list A -> list basic_instruction -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s 0.

(* like Forall_statements_in_seq, but starting from index 1 *)
Definition Forall_statements_in_seq_from_1 {A}: (nat  -> A -> list basic_instruction -> Prop) ->  list A -> list basic_instruction -> Prop :=
  fun P vs s =>  Forall_statements_in_seq' P vs s 1.

Inductive repr_var : positive -> immediate -> Prop :=
| repr_var_V : forall s err_str i,
   (* Genv.find_symbol (Genv.globalenv p) x = Some _ -> *)
       translate_var nenv lenv s err_str = Ret i ->
       repr_var s i.

(* immediate=nat: used in BI_call i *)
Inductive repr_funvar : positive -> immediate -> Prop :=
| repr_funvar_FV : forall s i errMsg,
        translate_function_var nenv fenv s errMsg = Ret i ->
        repr_funvar s i.

Inductive repr_read_var_or_funvar : positive -> basic_instruction -> Prop :=
| repr_var_or_funvar_V : forall p i,
    repr_var p i -> repr_read_var_or_funvar p (BI_get_local i)
| repr_var_or_funvar_FV : forall p i,
    repr_funvar p i -> repr_read_var_or_funvar p (BI_const (nat_to_value i)).

(* constr_alloc_ptr: pointer to linear_memory[p + 4 + 4*n] = value v *)
Inductive set_nth_constr_arg : nat -> var -> list basic_instruction -> Prop :=
  Make_nth_proj: forall (v : var) n instr,
                        repr_read_var_or_funvar v instr ->
                        set_nth_constr_arg n v [ BI_get_global constr_alloc_ptr
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
    forall x x' t vs sgrow sargs sres e e',
    (* translated assigned var *)
    repr_var x x' ->
    (* allocate memory *)
    grow_memory_if_necessary page_size = sgrow ->
    (* store args *)
    Forall_statements_in_seq set_nth_constr_arg vs sargs ->
    (* set result *)
    sres = [BI_get_global constr_alloc_ptr; BI_set_local x'] ->
    (* following expression *)
    repr_expr_LambdaANF_Codegen e e' ->

    repr_expr_LambdaANF_Codegen (Econstr x t vs e) (sgrow ++
                                    [ BI_get_global result_out_of_mem
                                    ; BI_const (nat_to_value 1)
                                    ; BI_relop T_i32 (Relop_i ROI_eq)
                                    ; BI_if (Tf nil nil)
                                            (* grow mem failed *) []
                                            (* grow mem success *)
                                            ([ BI_get_global global_mem_ptr
                                             ; BI_set_global constr_alloc_ptr
                                             ; BI_get_global constr_alloc_ptr
                                             ; BI_const (nat_to_value (Pos.to_nat t))
                                             ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0)
                                             ; BI_get_global global_mem_ptr
                                             ; BI_const (nat_to_value 4)
                                             ; BI_binop T_i32 (Binop_i BOI_add)
                                             ; BI_set_global global_mem_ptr
                                             ] ++ sargs ++ sres ++ e')
                                     ])

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

| R_app_e : forall v instr t args args',
    (* args are provided properly *)
    repr_fun_args_Codegen args args' ->
    (* instr reduces to const containing funidx to call *)
    repr_read_var_or_funvar v instr ->
    repr_expr_LambdaANF_Codegen (Eapp v t args) ((args' ++ [instr] ++ [BI_call_indirect (length args)])).

(* Variable mem : memory. *) (* WASM memory, created e.g. at initialization *)

Definition load_i32 m addr : option value := match load m addr 0%N 4 with (* offset: 0, 4 bytes *)
                                             | None => None
                                             | Some bs => Some (wasm_deserialise bs T_i32)
                                             end.

Definition store_i32 mem addr (v : value) : option memory := store mem addr 0%N (bits v) 4.


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

Variable host_function : eqType.
Let store_record := store_record host_function.


(* VALUE RELATION *)
(* immediate is pointer to linear memory or function id *)
Inductive repr_val_LambdaANF_Codegen:  LambdaANF.cps.val -> store_record -> frame -> wasm_value -> Prop :=
| Rconstr_v : forall v t vs (sr : store_record) fr gmp m (addr : nat),
    (* only depends on memory before v_gmp (simple memory model: gmp is increased whenever new mem is needed) *)
    sglob_val (host_function:=host_function) sr (f_inst fr) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
    (-1 < Z.of_nat gmp < Wasm_int.Int32.modulus)%Z ->
    (* addr in bounds of linear memory (later INV: gmp + 4 < length of memory) *)
    (addr + 4 <= gmp) ->
    (* store_record contains memory *)
    List.nth_error sr.(s_mems) 0 = Some m ->
    (* constructor tag is set properly, see LambdaANF_to_WASM, constr alloc structure*)
    v = tag_to_i32 t ->
    load_i32 m (N.of_nat addr) = Some (VAL_int32 v) ->
    (* arguments are set properly *)
    repr_val_constr_args_LambdaANF_Codegen vs sr fr (4 + addr) ->
    repr_val_LambdaANF_Codegen (LambdaANF.cps.Vconstr t vs) sr fr (Val_ptr addr)
| Rfunction_v : forall env fds f sr fr tag vs e e' idx inst ftype args body,
      find_def f fds = Some (tag, vs, e) ->

      (* find runtime representation of function *)
      List.nth_error sr.(s_funcs) idx = Some (FC_func_native inst ftype args body) ->
      ftype = Tf (List.map (fun _ => T_i32) vs) [] ->
      body = e' ->
      repr_expr_LambdaANF_Codegen e e' ->
      (* env: why empty? *)
      repr_val_LambdaANF_Codegen (LambdaANF.cps.Vfun env fds f) sr fr (Val_funidx idx)

with repr_val_constr_args_LambdaANF_Codegen : (list LambdaANF.cps.val) -> store_record -> frame -> immediate -> Prop :=
     | Rnil_l : forall sr fr addr,
        repr_val_constr_args_LambdaANF_Codegen nil sr fr (addr : nat)

     | Rcons_l: forall v wal vs sr fr m addr gmp,
        (* store_record contains memory *)
        List.nth_error sr.(s_mems) 0 = Some m ->

        sglob_val (host_function:=host_function) sr (f_inst fr) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
        (-1 < Z.of_nat gmp < Wasm_int.Int32.modulus)%Z ->
        (addr + 4 <= gmp) ->

        (* constr arg is ptr related to value v *)
        load_i32 m (N.of_nat addr) = Some (VAL_int32 (wasm_value_to_i32 wal)) ->
        repr_val_LambdaANF_Codegen v sr fr wal ->

        (* following constr args are also related *)
        repr_val_constr_args_LambdaANF_Codegen vs sr fr (4 + addr) ->
        repr_val_constr_args_LambdaANF_Codegen (v::vs) sr fr addr.

Scheme repr_val_LambdaANF_Codegen_mut := Induction for repr_val_LambdaANF_Codegen Sort Prop
  with repr_val_constr_args_LambdaANF_Codegen_mut := Induction for repr_val_constr_args_LambdaANF_Codegen Sort Prop.

(*
Check repr_val_LambdaANF_Codegen_ind.
Check repr_val_LambdaANF_Codegen_mut. *)

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

(* ORIGINAL pasted from C backend TODO update

If x is a free variable of e, then it might be in the generated code:
   1) a function in the global environment, evaluates to a location related to f by repr_val_ptr_LambdaANF_Codegen
   2) a local variable in le related to (rho x) according to repr_val_LambdaANF_Codegen

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
  (forall err, translate_var nenv lenv x err = Ret i) /\
  List.nth_error f.(f_locs) i = Some (VAL_int32 (wasm_value_to_i32 v)).

Definition rel_mem_LambdaANF_Codegen (e : exp) (rho : LambdaANF.eval.env)
                                     (sr : store_record) (fr : frame) :=
        (* function def is related to function index *)
        (forall x rho' fds f v errMsg,
            M.get x rho = Some v ->
             (* 1) arg is subval of constructor
                2) v listed in fds -> subval *)
            subval_or_eq (Vfun rho' fds f) v ->
            (* i is index of function f *)
            exists i, translate_function_var nenv fenv f errMsg = Ret i /\
            repr_val_LambdaANF_Codegen (Vfun rho' fds f) sr fr (Val_funidx i) /\
            closed_val (Vfun rho' fds f))
        /\
        (* free variables are related to local var containing a memory pointer or a function index *)
        (forall x,
            occurs_free e x ->
            (exists v6 val,
               M.get x rho = Some v6 /\
               stored_in_locals x val fr /\
               repr_val_LambdaANF_Codegen v6 sr fr val)).

End RELATION.

Section THEOREM.

  Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show.
Import Common.Common Common.compM Common.Pipeline_utils.

Import ExtLib.Structures.Monad.
Import MonadNotation.


  (* same as LambdaANF_to_Clight *)

  Variable cenv:LambdaANF.cps.ctor_env.
  Variable funenv:LambdaANF.cps.fun_env.
  Variable fenv : CodegenWASM.LambdaANF_to_WASM.fname_env.
  Variable lenv : CodegenWASM.LambdaANF_to_WASM.localvar_env.
  Variable nenv : LambdaANF.cps_show.name_env.
  Variable finfo_env: LambdaANF_to_Clight.fun_info_env. (* map from a function name to its type info *)


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
(* Let reduce := @reduce host_function host_instance. *)




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

Lemma pass_function_args_correct : forall l instr,
 pass_function_args nenv lenv fenv l = Ret instr ->
 repr_fun_args_Codegen fenv lenv nenv l instr.
Proof.
  induction l; intros.
  - cbn in H.  inv H. constructor.
  - cbn in H. destruct (instr_local_var_read nenv lenv fenv a) eqn:Hvar. inv H.
    destruct (pass_function_args nenv lenv fenv l) eqn:prep. inv H. inv H.
    unfold instr_local_var_read in Hvar.
    destruct (is_function_var fenv a) eqn:Hfname.
    - destruct (translate_function_var nenv fenv a _) eqn:fun_var; inv Hvar.
            constructor. econstructor. eassumption.
        apply IHl; auto.
    - destruct (translate_var  nenv lenv a _) eqn:var_var; inv Hvar.
            constructor.  econstructor. eassumption. apply IHl; auto.
Qed.

Lemma set_nth_constr_arg_correct : forall l instr n,
  set_constructor_args nenv lenv fenv l n = Ret instr ->
  Forall_statements_in_seq' (set_nth_constr_arg fenv lenv nenv) l instr n.
Proof.
  induction l; intros.
  - inv H. econstructor; auto.
  - cbn in H. destruct (instr_local_var_read nenv lenv fenv a) eqn:Hvar. inv H.
  destruct (set_constructor_args nenv lenv fenv l (S n)) eqn:Harg. inv H. inv H.
  replace ((BI_get_global constr_alloc_ptr
   :: BI_const
        (nat_to_value (S (n + S (n + S (n + S (n + 0))))))
      :: BI_binop T_i32 (Binop_i BOI_add)
         :: b :: BI_store T_i32 None 2%N 0%N
               :: BI_get_global global_mem_ptr
                  :: BI_const (nat_to_value 4)
                     :: BI_binop T_i32 (Binop_i BOI_add)
                        :: BI_set_global global_mem_ptr :: l0)) with
      (([ BI_get_global constr_alloc_ptr
        ; BI_const (nat_to_value (S (n + S (n + S (n + S (n + 0))))))
        ; BI_binop T_i32 (Binop_i BOI_add)
        ; b
        ; BI_store T_i32 None 2%N 0%N
        ; BI_get_global global_mem_ptr
        ; BI_const (nat_to_value 4)
        ; BI_binop T_i32 (Binop_i BOI_add)
        ; BI_set_global global_mem_ptr] ++ l0)) by reflexivity.
   constructor; auto.

  replace ((nat_to_value (S (n + S (n + S (n + S (n + 0))))))) with ((nat_to_value ((1 + n) * 4))). constructor.
  unfold instr_local_var_read in Hvar.
  destruct (is_function_var fenv a) eqn:Hfn.
  - destruct (translate_function_var nenv fenv a _) eqn:Hvar'. inv Hvar. inv Hvar.
    constructor. econstructor. eassumption.
  - destruct (translate_var nenv lenv a _) eqn:Hloc. inv Hvar. inv Hvar.
    constructor. econstructor. unfold translate_var. eassumption. f_equal. lia.
Qed.

Import seq.

Theorem translate_exp_correct:
    (* find_symbol_domain p map -> *)
    (* finfo_env_correct fenv map -> *)
    (* correct_crep_of_env cenv rep_env -> *)
    forall e instructions,
      correct_cenv_of_exp cenv e ->
    translate_exp nenv cenv lenv fenv e = Ret instructions ->
    repr_expr_LambdaANF_Codegen fenv lenv nenv e instructions.
Proof.
  intros (* Hcrep *) e.
  induction e using exp_ind'; intros instr Hcenv; intros.
  - (* Econstr *)
    simpl in H.
    { destruct (translate_exp nenv cenv lenv fenv e) eqn:H_eqTranslate; inv H.
      destruct (translate_var nenv lenv v "translate_exp constr") eqn:H_translate_var. inv H1.
      destruct (store_constructor nenv cenv lenv fenv t l) eqn:store_constr.
      inv H1. inv H1. cbn.
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite <-(cat1s x l) end
  end.
  rename i into v'.
  replace   ([:: BI_get_global global_mem_ptr] ++
   [:: BI_const (N_to_value 65536)] ++
   [:: BI_binop T_i32 (Binop_i BOI_add)] ++
   [:: BI_const (Z_to_value 65536)] ++
   [:: BI_binop T_i32 (Binop_i (BOI_div SX_S))] ++
   [:: BI_current_memory] ++
   [:: BI_relop T_i32 (Relop_i (ROI_ge SX_S))] ++
   [:: BI_if (Tf [::] [::])
         ([:: BI_const (nat_to_value 1)] ++
          [:: BI_grow_memory] ++
          [:: BI_const (Z_to_value (-1))] ++
          [:: BI_relop T_i32 (Relop_i ROI_eq)] ++
          [:: BI_if (Tf [::] [::])
                ([:: BI_const (nat_to_value 1)] ++
                 [:: BI_set_global result_out_of_mem]) [::]])
         [::]] ++
   [:: BI_get_global result_out_of_mem] ++
   [:: BI_const (nat_to_value 1)] ++
   [:: BI_relop T_i32 (Relop_i ROI_eq)] ++
   [:: BI_if (Tf [::] [::]) [::]
         (l1 ++
          ([:: BI_get_global constr_alloc_ptr] ++
           [:: BI_set_local v'] ++ l0)%SEQ)%list]) with
   (([:: BI_get_global global_mem_ptr] ++
   [:: BI_const (N_to_value 65536)] ++
   [:: BI_binop T_i32 (Binop_i BOI_add)] ++
   [:: BI_const (Z_to_value 65536)] ++
   [:: BI_binop T_i32 (Binop_i (BOI_div SX_S))] ++
   [:: BI_current_memory] ++
   [:: BI_relop T_i32 (Relop_i (ROI_ge SX_S))] ++
   [:: BI_if (Tf [::] [::])
         ([:: BI_const (nat_to_value 1)] ++
          [:: BI_grow_memory] ++
          [:: BI_const (Z_to_value (-1))] ++
          [:: BI_relop T_i32 (Relop_i ROI_eq)] ++
          [:: BI_if (Tf [::] [::])
                ([:: BI_const (nat_to_value 1)] ++
                 [:: BI_set_global result_out_of_mem]) []])
         []]) ++
   [:: BI_get_global result_out_of_mem] ++
   [:: BI_const (nat_to_value 1)] ++
   [:: BI_relop T_i32 (Relop_i ROI_eq)] ++
   [:: BI_if (Tf [::] [::]) [::]
         (l1 ++
          ([:: BI_get_global constr_alloc_ptr] ++
           [:: BI_set_local v'] ++ l0)%SEQ)%list]) by reflexivity.
  remember ([:: BI_get_global global_mem_ptr] ++
   [:: BI_const (N_to_value 65536)] ++
   [:: BI_binop T_i32 (Binop_i BOI_add)] ++
   [:: BI_const (Z_to_value 65536)] ++
   [:: BI_binop T_i32 (Binop_i (BOI_div SX_S))] ++
   [:: BI_current_memory] ++
   [:: BI_relop T_i32 (Relop_i (ROI_ge SX_S))] ++
   [:: BI_if (Tf [::] [::])
         ([:: BI_const (nat_to_value 1)] ++
          [:: BI_grow_memory] ++
          [:: BI_const (Z_to_value (-1))] ++
          [:: BI_relop T_i32 (Relop_i ROI_eq)] ++
          [:: BI_if (Tf [::] [::])
                ([:: BI_const (nat_to_value 1)] ++
                 [:: BI_set_global result_out_of_mem]) []])
         []]) as grow_instr.
      unfold store_constructor in store_constr.
      destruct (set_constructor_args nenv lenv fenv l 0) eqn:Hconstrargs. inv store_constr.
         remember (grow_memory_if_necessary page_size) as grow.
      inversion store_constr.

         replace ([:: BI_get_global constr_alloc_ptr, BI_set_local v' & l0]) with
         ([:: BI_get_global constr_alloc_ptr; BI_set_local v'] ++ l0) by reflexivity.

       replace ([:: BI_get_global global_mem_ptr, BI_set_global constr_alloc_ptr,
        BI_get_global global_mem_ptr, BI_const (N_to_value page_size),
        BI_binop T_i32 (Binop_i BOI_add), BI_set_global global_mem_ptr,
        BI_get_global constr_alloc_ptr, BI_const (nat_to_value (Pos.to_nat t)),
        BI_store T_i32 None 2%N 0%N
      & l2]) with ([:: BI_get_global global_mem_ptr; BI_set_global constr_alloc_ptr;
        BI_get_global global_mem_ptr; BI_const (N_to_value page_size);
        BI_binop T_i32 (Binop_i BOI_add); BI_set_global global_mem_ptr] ++
        [BI_get_global constr_alloc_ptr; BI_const (nat_to_value (Pos.to_nat t));
        BI_store T_i32 None 2%N 0%N] ++ l2) by reflexivity.

        replace ([:: BI_get_global constr_alloc_ptr] ++ [:: BI_set_local v'] ++ l0) with
                ([BI_get_global constr_alloc_ptr; BI_set_local v'] ++ l0) by reflexivity.
        remember ([BI_get_global constr_alloc_ptr; BI_set_local v']) as sres.

        replace ([:: BI_get_global global_mem_ptr,
              BI_set_global constr_alloc_ptr,
              BI_get_global constr_alloc_ptr,
              BI_const (nat_to_value (Pos.to_nat t)),
              BI_store T_i32 None 2%N 0%N,
              BI_get_global global_mem_ptr,
              BI_const (nat_to_value 4),
              BI_binop T_i32 (Binop_i BOI_add),
              BI_set_global global_mem_ptr
            & l2]) with ([ BI_get_global global_mem_ptr;
              BI_set_global constr_alloc_ptr ] ++ [
              BI_get_global constr_alloc_ptr; BI_const (nat_to_value (Pos.to_nat t));
              BI_store T_i32 None 2%N 0%N;
              BI_get_global global_mem_ptr;
              BI_const (nat_to_value 4);
              BI_binop T_i32 (Binop_i BOI_add);
              BI_set_global global_mem_ptr
            ] ++ l2) by reflexivity.
        repeat rewrite <- app_assoc.
        eapply Rconstr_e with (e' := l0) (sres := sres); eauto.
        econstructor. eassumption. apply set_nth_constr_arg_correct. assumption.

        apply IHe; auto.
        assert (subterm_e e (Econstr v t l e) ). { constructor; constructor. }
        eapply Forall_constructors_subterm. eassumption. assumption.
        }

  - (* Ecase nil *) simpl in H. destruct (translate_var nenv lenv v "translate_exp case") eqn:Hvar. inv H. inv H.
     constructor.
  - (* Ecase const *) {
    simpl in H. destruct (translate_exp nenv cenv lenv fenv e) eqn:Hexp. inv H.
    destruct (_ l) eqn:Hprep. inv H.
    destruct (translate_var nenv lenv v "translate_exp case") eqn:Hvar. inv H. inv H.
    constructor. econstructor. eassumption. apply IHe0.
    eapply correct_cenv_case_drop_clause. eassumption.
    cbn. rewrite Hprep. rewrite Hvar. reflexivity.
    apply IHe; auto. eapply Forall_constructors_subterm; eauto. constructor. econstructor. cbn.
    left; eauto. }
   - (* Eproj *)
      { simpl in H.
      destruct (translate_exp nenv cenv lenv fenv e) eqn:He. inv H.
      destruct (translate_var nenv lenv v0 "translate_exp proj y") eqn:Hy. inv H.
      destruct (translate_var nenv lenv v "translate_exp proj x") eqn:Hx. inv H.
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
    destruct (pass_function_args nenv lenv fenv l) eqn:Hargs. inv H.
    destruct (instr_local_var_read nenv lenv fenv v) eqn:Hloc. inv H. inv H. constructor.
    apply pass_function_args_correct. assumption.
    unfold instr_local_var_read in Hloc.
    destruct (is_function_var fenv v) eqn:Hfname.
    - destruct (translate_function_var nenv fenv v _) eqn:fun_var; inv Hloc.
      constructor. econstructor. eassumption.
    - destruct (translate_var  nenv lenv v _) eqn:var_var; inv Hloc.
      constructor. econstructor. eassumption.
  - (* Eprim *)
    inv H. inv H.
  - (* Ehalt *)
    simpl in H. destruct (translate_var nenv lenv v "translate_exp halt") eqn:Hvar. inv H.
    injection H => instr'. subst. constructor. econstructor. eauto.
Qed.

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
 (val : LambdaANF.cps.val) (sr : store_record) (fr : frame) : Prop :=

   (exists res_i32 wasmval,
      (* global var *result_var* contains correct return value *)
      sglob_val sr (f_inst fr) result_var = Some (VAL_int32 res_i32) /\
      wasm_value_to_i32 wasmval = res_i32 /\
      repr_val_LambdaANF_Codegen fenv lenv nenv  _ val sr fr wasmval)
    \/ (sglob_val sr (f_inst fr) result_out_of_mem = Some (nat_to_value 1)).

Import ssrfun ssrbool eqtype seq.

Import interpreter_sound binary_format_parser binary_format_printer host
                         datatypes_properties check_toks instantiation
                         operations opsem interpreter_sound interpreter_func interpreter_func_sound properties common.


Import eqtype.
Import Lia.
Import Relations.Relation_Operators.
Import ssreflect seq.


Lemma val_relation_depends_on_finst : forall v sr fr fr' value,
    f_inst fr = f_inst fr' ->
    repr_val_LambdaANF_Codegen fenv lenv nenv host_function v sr fr value ->
    repr_val_LambdaANF_Codegen fenv lenv nenv host_function v sr fr' value.
Proof.
  intros. inv H0.
  (* constructor value *)
  { have indPrinciple := repr_val_constr_args_LambdaANF_Codegen_mut fenv lenv nenv host_function
    (fun (v : cps.val) (s : datatypes.store_record host_function) (f : frame) (w : wasm_value)
                       (H: repr_val_LambdaANF_Codegen fenv lenv nenv host_function v s f w) =>
         (forall f',
                f_inst f = f_inst f' ->
                repr_val_LambdaANF_Codegen fenv lenv nenv host_function v s f' w)
    )
    (fun (l : seq cps.val) (s : datatypes.store_record host_function) (f : frame) (i : immediate)
                       (H: repr_val_constr_args_LambdaANF_Codegen fenv lenv nenv host_function l s f i) =>
         (forall f',
                f_inst f = f_inst f' ->
                repr_val_constr_args_LambdaANF_Codegen fenv lenv nenv host_function l s f' i)
    ). eapply indPrinciple in H7; intros; clear indPrinciple; try eassumption.
    { econstructor; eauto. congruence. }
    { econstructor; eauto. congruence. }
    { econstructor; eauto. }
    { econstructor; eauto. }
    { econstructor; eauto. congruence. }
  }
  (* function *)
  { econstructor; eauto. }
Qed.

Lemma val_relation_depends_on_mem_smaller_than_gmp_and_funcs : forall v sr sr' m m' fr fr' gmp gmp' value,
    f_inst fr = f_inst fr' ->
    sr.(s_funcs) = sr'.(s_funcs) ->
    nth_error sr.(s_mems)  0 = Some m ->
    nth_error sr'.(s_mems) 0 = Some m' ->
    (* memories agree on values < gmp *)
    sglob_val sr  (f_inst fr) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
    (Z.of_nat gmp + 4 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
    sglob_val sr' (f_inst fr') global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp')) ->
    (Z.of_nat gmp' + 4 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
    gmp' >= gmp ->
    (forall a, (a + 4 <= N.of_nat gmp)%N -> load_i32 m a = load_i32 m' a) ->

    repr_val_LambdaANF_Codegen fenv lenv nenv host_function v sr fr value ->
    repr_val_LambdaANF_Codegen fenv lenv nenv host_function v sr' fr' value.
Proof.
  intros. inv H9.
  (* constructor value *)
  { have indPrinciple := repr_val_constr_args_LambdaANF_Codegen_mut fenv lenv nenv host_function
    (fun (v : cps.val) (s : datatypes.store_record host_function) (f : frame) (w : wasm_value)
                       (H: repr_val_LambdaANF_Codegen fenv lenv nenv host_function v s f w) =>
         (forall a s' f' m m',
                f_inst f = f_inst f' ->
                s_funcs s = s_funcs s' ->
                nth_error s.(s_mems) 0 = Some m ->
                nth_error s'.(s_mems) 0 = Some m' ->
                (* memories agree on values < gmp *)
                sglob_val s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
                (Z.of_nat gmp + 4 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
                sglob_val s' (f_inst f') global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp')) ->
                (Z.of_nat gmp' + 4 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
                gmp' >= gmp ->
                (forall a, (a + 4<= N.of_nat gmp)%N -> load_i32 m a = load_i32 m' a) ->
                    repr_val_LambdaANF_Codegen fenv lenv nenv host_function v s' f' w)
    )
    (fun (l : seq cps.val) (s : datatypes.store_record host_function) (f : frame) (i : immediate)
                       (H: repr_val_constr_args_LambdaANF_Codegen fenv lenv nenv host_function l s f i) =>
         (forall a s' f' m m',
                f_inst f = f_inst f' ->
                s_funcs s = s_funcs s' ->
                nth_error s.(s_mems) 0 = Some m ->
                nth_error s'.(s_mems) 0 = Some m' ->
                (* memories agree on values < gmp *)
                sglob_val s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
                (Z.of_nat gmp + 4 <= Z.of_N (mem_length m) < Wasm_int.Int32.modulus)%Z ->
                sglob_val s' (f_inst f') global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp')) ->
                (Z.of_nat gmp' + 4 <= Z.of_N (mem_length m') < Wasm_int.Int32.modulus)%Z ->
                gmp' >= gmp ->
                (forall a, (a + 4 <= N.of_nat gmp)%N -> load_i32 m a = load_i32 m' a) ->
                   repr_val_constr_args_LambdaANF_Codegen fenv lenv nenv host_function l s' f' i)
    ). eapply indPrinciple in H16; intros; clear indPrinciple; try eassumption; try lia.
    { assert (gmp = gmp0). { assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp0) by congruence.
                             inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H14; try lia.
                             rewrite Wasm_int.Int32.Z_mod_modulus_id in H14; lia. } subst gmp0.
      assert (m = m0) by congruence; subst m0.
      econstructor. eassumption. lia. lia. eassumption. reflexivity. rewrite <- H8. assumption. lia. eassumption. }
    { assert (gmp = gmp0). { assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp0) by congruence.
                             inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H27; try lia.
                             rewrite Wasm_int.Int32.Z_mod_modulus_id in H27; lia. } subst gmp0.
      assert (gmp = gmp1). { assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp1) by congruence.
                             inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H27; try lia.
                             rewrite Wasm_int.Int32.Z_mod_modulus_id in H27; lia. } subst gmp1.
      assert (m = m0) by congruence. subst m0.
      assert (m1 = m2) by congruence. subst m2. subst.
      econstructor; eauto. lia. rewrite <- H25; auto; try lia. }
    { econstructor; eauto. erewrite <- e1. congruence. }
    { econstructor. }
    { assert (gmp = gmp0). {
         assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp0) by congruence.
              inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H28; try lia.
              rewrite Wasm_int.Int32.Z_mod_modulus_id in H28; lia. } subst gmp0.
      econstructor; eauto. lia. assert (gmp1 = gmp). {
         assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp1) by congruence.
              inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H28; try lia.
              rewrite Wasm_int.Int32.Z_mod_modulus_id in H28; lia. } subst. lia.
      rewrite <- H26. assert (m1 = m2) by congruence. subst m2. eassumption.
      assert (gmp1 = gmp). {
                 assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp1) by congruence.
                 inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H28; try lia.
                 rewrite Wasm_int.Int32.Z_mod_modulus_id in H28; lia. } subst gmp1. lia.
      eapply H9; eauto; lia. }
    { assert (m = m0) by congruence. subst m0. lia. }
    { assert (m = m0) by congruence; subst m0. apply H8. lia. }
  }
  (* function *)
  { econstructor; eauto. rewrite <- H0. eassumption. }
Qed.

(* TODO: remove duplicate *)
Lemma update_glob_keeps_memory_intact : forall sr sr' fr v j,
  supdate_glob (host_function:=host_function) sr (f_inst fr) j v = Some sr' ->
    sr.(s_mems) = sr'.(s_mems).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H. cbn in H.
  destruct (nth_error (inst_globs (f_inst fr)) j). 2: inv H. cbn in H.
  destruct (nth_error (s_globals sr) g). inv H. reflexivity. inv H.
Qed.

Lemma update_glob_keeps_funcs_intact : forall sr sr' fr v j,
  supdate_glob (host_function:=host_function) sr (f_inst fr) j v = Some sr' ->
    sr.(s_funcs) = sr'.(s_funcs).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H. cbn in H.
  destruct (nth_error (inst_globs (f_inst fr)) j). 2: inv H. cbn in H.
  destruct (nth_error (s_globals sr) g). inv H. reflexivity. inv H.
Qed.

Definition globals_all_mut_i32 s := forall g g0, nth_error (@s_globals host_function s) g = Some g0 -> exists i, g0 = {| g_mut := MUT_mut; g_val := VAL_int32 i |}.

Definition global_var_w var (s : store_record) (f : frame) :=
  forall val, (exists s', @supdate_glob host_function s (f_inst f) var (VAL_int32 val) = Some s').

Definition global_var_r var (s : store_record) (f : frame) :=
   exists v, sglob_val (host_function:=host_function) s (f_inst f) var = Some (VAL_int32 v).

Definition INV_result_var_writable := global_var_w result_var.
Definition INV_result_var_out_of_mem_writable := global_var_w result_out_of_mem.
Definition INV_global_mem_ptr_writable := global_var_w global_mem_ptr.
Definition INV_constr_alloc_ptr_writable := global_var_w constr_alloc_ptr.
Definition INV_globals_all_mut_i32 := globals_all_mut_i32.

(* indicates all good *)
Definition INV_result_var_out_of_mem_is_zero s f :=
  sglob_val (host_function:=host_function) s (f_inst f) result_out_of_mem = Some (VAL_int32 (nat_to_i32 0)).

Definition INV_linear_memory sr fr :=
      smem_ind (host_function:=host_function) sr (f_inst fr) = Some 0
   /\ exists m, nth_error (s_mems sr) 0 = Some m
   /\ exists size, mem_size m = size
   /\ mem_max_opt m = Some max_mem_pages
   /\ (size <= max_mem_pages)%N.

Definition INV_global_mem_ptr_in_linear_memory s f := forall gmp_v m,
  nth_error (s_mems s) 0 = Some m ->
  sglob_val (host_function:=host_function) s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp_v)) ->
  (-1 < Z.of_nat gmp_v < Wasm_int.Int32.modulus)%Z ->
  (* enough space to store an i32 *)
  (N.of_nat gmp_v + 4 <= mem_length m)%N.

Definition INV_constr_alloc_ptr_in_linear_memory s f := forall addr t m,
  sglob_val (host_function:=host_function) s (f_inst f) constr_alloc_ptr = Some (VAL_int32 addr)
  -> exists m', store m (Wasm_int.N_of_uint i32m addr) 0%N (bits (nat_to_value (Pos.to_nat t))) (t_length T_i32) = Some m'.

Definition INV_locals_all_i32 f :=
  forall i v, nth_error (f_locs f) i = Some v -> exists v', v = (VAL_int32 v').

Definition INV_num_functions_upper_bound sr :=
  (Z.of_nat (length (@s_funcs host_function sr)) < Wasm_int.Int32.modulus)%Z.

(* invariants that need to hold throughout the execution of the Wasm program,
   doesn't hold anymore when memory runs out -> just abort  *)
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
 /\ INV_num_functions_upper_bound s.


Lemma set_nth_nth_error_same : forall {X:Type} (l:seq X) e e' i vd,
    List.nth_error l i = Some e ->
    List.nth_error (set_nth vd l i e') i = Some e'.
Proof.
  intros. generalize dependent e'. generalize dependent l. generalize dependent vd. generalize dependent e. induction i; intros.
  - inv H. destruct l.
    inv H1. inv H1. reflexivity.
  - cbn in H. destruct l. inv H. eapply IHi in H. cbn. eassumption.
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

Lemma exists_i32 : exists (v : i32), True.
Proof. exists (nat_to_i32 1). constructor. Qed.

(* TODO consistent naming of lemmas *)
Lemma global_var_write_read_same : forall sr sr' i val fr,
  supdate_glob (host_function:=host_function) sr  (f_inst fr) i (VAL_int32 val) = Some sr' ->
     sglob_val (host_function:=host_function) sr' (f_inst fr) i = Some (VAL_int32 val).
Proof.
  unfold supdate_glob, supdate_glob_s, sglob_val, sglob, sglob_ind. cbn. intros.
  destruct (nth_error (inst_globs (f_inst fr)) i) eqn:H1. 2: inv H. cbn in H.
  destruct (nth_error (s_globals sr) g) eqn:H2. 2: inv H. inv H. cbn.
  rewrite nth_error_update_list_hit; auto.
  apply /ssrnat.leP. apply lt_le_S. apply nth_error_Some. congruence.
Qed.

Lemma global_var_write_read_other : forall i j sr sr' fr num val,
  i <> j ->
  sglob_val (host_function:=host_function) sr (f_inst fr) i = Some (VAL_int32 val) ->
  supdate_glob (host_function:=host_function) sr (f_inst fr) j
             (VAL_int32 num) = Some sr' ->
  sglob_val (host_function:=host_function) sr' (f_inst fr) i = Some (VAL_int32 val).
Proof.
  intros ? ? ? ? ? ? ? Hneq Hr Hw.
    unfold supdate_glob, sglob_ind, supdate_glob_s in *.
    destruct (nth_error (inst_globs (f_inst fr)) j) eqn:Heqn. 2: inv Hw. cbn in Hw.
    destruct (nth_error (s_globals sr) g) eqn:Heqn'. 2: inv Hw. inv Hw.
    unfold sglob_val, sglob, sglob_ind in *.
    destruct (nth_error (inst_globs (f_inst fr)) i) eqn:Heqn''.  2: inv Hr.
    cbn. cbn in Hr.
    assert (g <> g1). { admit. (* should follow from i<>j*) }
    rewrite nth_error_update_list_others; auto.
     assert (g < length (s_globals sr)) as Hl. { apply nth_error_Some. intro. congruence. }
     apply /ssrnat.leP. lia.
Admitted.

Lemma update_global_var_preserves_memory : forall sr sr' f j num,
  supdate_glob (host_function:=host_function) sr (f_inst f) j
             (VAL_int32 num) = Some sr' ->
  nth_error (s_mems sr) 0 = nth_error (s_mems sr') 0.
Proof.
  intros. unfold supdate_glob, supdate_glob_s, sglob_ind in H.
  destruct (nth_error (inst_globs (f_inst f)) j). 2: inv H. cbn in H.
  destruct ((nth_error (s_globals sr) g)). 2: inv H. inv H. reflexivity.
Qed.

Lemma update_global_preserves_globals_all_mut_i32 : forall sr sr' i f num,
  globals_all_mut_i32 sr ->
  supdate_glob (host_function:=host_function) sr (f_inst f) i
             (VAL_int32 num) = Some sr' ->
  globals_all_mut_i32 sr'.
Proof.
  intros. unfold globals_all_mut_i32 in *. intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H0.
  destruct (nth_error (inst_globs (f_inst f)) i) eqn:Heqn. 2: inv H0. cbn in H0.
  destruct (nth_error (s_globals sr) g1) eqn:Heqn'. 2: inv H0. inv H0. cbn in H1.
  destruct (Nat.lt_total g g1) as [Heq | [Heq | Heq]].
  - (* g < g1 *)
    rewrite nth_error_update_list_others in H1. eauto. lia. apply /ssrnat.leP.
    assert (g1 < length (s_globals sr)). { apply nth_error_Some. intro. congruence. } lia.
  - (* g = g1 *)
    subst. rewrite nth_error_update_list_hit in H1. inv H1.
    assert (g_mut g2 = MUT_mut). { apply H in Heqn'. destruct Heqn'. subst. reflexivity. }
    subst. rewrite H0. eauto. apply /ssrnat.leP.
    assert (g1 < length (s_globals sr)). { apply nth_error_Some. intro. congruence. } lia.
  - (* g1 < g *)
    rewrite nth_error_update_list_others in H1. eauto. lia. apply /ssrnat.leP.
    assert (g1 < length (s_globals sr)). { apply nth_error_Some. intro. congruence. } lia.
Qed.

Lemma update_list_at_preserves_nth_error_option {A} : forall l i j v v',
  nth_error l j = Some v ->
  i < length l ->
  exists v'', @nth_error A (update_list_at l i v') j = Some v''.
Proof.
  intros.
  destruct (Nat.lt_total i j) as [Heq | [Heq | Heq]].
  - (* i < j*)
    eexists. rewrite nth_error_update_list_others. eassumption. lia.
    apply /ssrnat.leP. lia.
  - (* i = j *)
    subst. rewrite nth_error_update_list_hit. eauto. apply /ssrnat.leP. lia.
  - (* i > j *)
    eexists. rewrite nth_error_update_list_others. eassumption. lia.
    apply /ssrnat.leP. lia.
Qed.


Lemma update_global_preserves_global_var_w : forall i j sr sr' f num,
  global_var_w i sr f ->
  supdate_glob (host_function:=host_function) sr (f_inst f) j
             (VAL_int32 num) = Some sr' ->
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
       (update_list_at (s_globals sr) g1 {| g_mut := g_mut g2; g_val := VAL_int32 num |}) g) eqn:Heqn''''. cbn. intro. eauto.
        exfalso. cbn in HG.
     assert (g1 < length (s_globals sr)) as Hl. { apply nth_error_Some. intro. congruence. }
     have Ht := update_list_at_preserves_nth_error_option _ _ _ _ _ Heqn' Hl. specialize Ht with ({| g_mut := g_mut g2; g_val := VAL_int32 num |}). destruct Ht. rewrite H in Heqn''''. discriminate. }
     cbn in HG. edestruct HG. eauto. inv H0.
     Unshelve. auto.
Qed.

Lemma update_global_preserves_result_var_out_of_mem_is_zero : forall i sr sr' f num,
  INV_result_var_out_of_mem_is_zero sr f ->
  result_out_of_mem <> i ->
  supdate_glob (host_function:=host_function) sr (f_inst f) i
             (VAL_int32 num) = Some sr' ->
  INV_result_var_out_of_mem_is_zero sr' f.
Proof.
  unfold INV_result_var_out_of_mem_is_zero. intros.
  have H' := global_var_write_read_other _ _ _ _ _ _ _ H0 H H1. assumption.
Qed.

Lemma update_global_preserves_linear_memory : forall j sr sr' f  num,
  INV_linear_memory sr f ->
  supdate_glob (host_function:=host_function) sr (f_inst f) j
             (VAL_int32 num) = Some sr' ->
  INV_linear_memory sr' f.
Proof.
  intros.
  unfold supdate_glob, sglob_ind, supdate_glob_s in H0.
  destruct (nth_error (inst_globs (f_inst f))) eqn:Heqn. 2: inv H0. cbn in H0. destruct (nth_error (s_globals sr) g). 2: inv H0. cbn in H0. inv H0.
  assumption.
Qed.

Lemma update_global_preserves_num_functions_upper_bound : forall j sr sr' f  num,
  INV_num_functions_upper_bound sr ->
  supdate_glob (host_function:=host_function) sr (f_inst f) j
             (VAL_int32 num) = Some sr' ->
  INV_num_functions_upper_bound sr'.
Proof.
  unfold INV_num_functions_upper_bound. intros.
  assert (s_funcs sr = s_funcs sr') as Hfuncs. {
   unfold supdate_glob, supdate_glob_s in H0.
   destruct (sglob_ind (host_function:=host_function) sr (f_inst f) j). 2:inv H0. cbn in H0.
   destruct (nth_error (s_globals sr) n). 2: inv H0. inv H0. reflexivity. }
   rewrite Hfuncs in H. apply H.
Qed.

(* TODO: false, additional restriction on num required *)
Lemma update_global_preserves_global_mem_ptr_in_linear_memory : forall j sr sr' f  num,
  INV_global_mem_ptr_in_linear_memory sr f ->
  supdate_glob (host_function:=host_function) sr (f_inst f) j
             (VAL_int32 num) = Some sr' ->
  INV_global_mem_ptr_in_linear_memory sr' f.
Proof. Admitted.

(* TODO: false, additional restriction on num required *)
Lemma update_global_preserves_constr_alloc_ptr_in_linear_memory : forall j sr sr' f  num,
  INV_constr_alloc_ptr_in_linear_memory sr f ->
  supdate_glob (host_function:=host_function) sr (f_inst f) j
             (VAL_int32 num) = Some sr' ->
  INV_constr_alloc_ptr_in_linear_memory sr' f.
Proof. Admitted.

Corollary update_global_preserves_INV : forall sr sr' i f num,
  INV sr f ->
  result_out_of_mem <> i ->
  supdate_glob (host_function:=host_function) sr (f_inst f) i
             (VAL_int32 num) = Some sr' ->
  INV sr' f.
Proof with eassumption.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_result_var_out_of_mem_is_zero...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_globals_all_mut_i32...
  split. eapply update_global_preserves_linear_memory...
  split. eapply update_global_preserves_global_mem_ptr_in_linear_memory...
  split. assumption. eapply update_global_preserves_num_functions_upper_bound...
Qed.

Corollary update_local_preserves_INV : forall sr f f' x' v,
  INV sr f ->
  x' < length (f_locs f) ->
  f' = {| f_locs := set_nth (VAL_int32 v) (f_locs f) x' (VAL_int32 v)
        ; f_inst := f_inst f
        |} ->
  INV sr f'.
Proof with eauto.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]]. subst.
  repeat (split; auto). unfold INV_locals_all_i32 in *. cbn. intros.
  destruct (Nat.eq_dec x' i).
  (* i=x' *) subst. apply nth_error_Some in H0. apply notNone_Some in H0. destruct H0.
  erewrite set_nth_nth_error_same in H1; eauto. inv H1. eauto.
  (* i<>x' *) rewrite set_nth_nth_error_other in H1; auto. apply H9 in H1. assumption.
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

Lemma update_mem_preserves_global_var_w : forall i s f s' m,
   global_var_w i s f ->
   upd_s_mem (host_function:=host_function) s
                (update_list_at (s_mems s) 0 m) = s' ->
   global_var_w i s' f.
Proof.
  destruct exists_i32 as [x _].
  intros. unfold upd_s_mem in H0. subst. edestruct H. unfold global_var_w. intro.
  unfold supdate_glob, sglob_ind, supdate_glob_s in *. cbn in *.
  destruct (nth_error (inst_globs (f_inst f)) i). 2: inv H0. cbn in *.
  destruct (nth_error (s_globals s) g). 2: inv H0. cbn in *. eexists. reflexivity.
  Unshelve. assumption.
Qed.

Lemma update_mem_preserves_result_var_out_of_mem_is_zero : forall s f s' m,
   INV_result_var_out_of_mem_is_zero s f ->
   upd_s_mem (host_function:=host_function) s
                (update_list_at (s_mems s) 0 m) = s' ->
   INV_result_var_out_of_mem_is_zero s' f.
Proof.
  unfold INV_result_var_out_of_mem_is_zero, sglob_val, sglob, sglob_ind, nat_to_i32. intros. subst. cbn in *.
  destruct (inst_globs (f_inst f)). inv H.
  destruct l. inv H. destruct l. inv H. destruct l. inv H. assumption.
Qed.

Lemma update_mem_preserves_all_mut_i32 : forall s s' m,
   globals_all_mut_i32 s  ->
   upd_s_mem (host_function:=host_function) s
                (update_list_at (s_mems s) 0 m) = s' ->
   globals_all_mut_i32 s'.
Proof.
  unfold globals_all_mut_i32. intros.
  unfold upd_s_mem in H0. assert (s_globals s = s_globals s') as Hglob. {
   subst. destruct s. reflexivity. }
  rewrite Hglob in H. apply H in H1. destruct H1 as [i Hi]. eauto.
Qed.

Lemma update_mem_preserves_linear_memory : forall s s' f m,
   INV_linear_memory s f  ->
   mem_max_opt m = Some max_mem_pages ->
   (exists size, mem_size m = size /\ size <= max_mem_pages)%N ->
   upd_s_mem (host_function:=host_function) s
                (update_list_at (s_mems s) 0 m) = s' ->
   INV_linear_memory s' f.
Proof.
  unfold INV_linear_memory. intros s s' f m [H [m' [H1 [size [H2 [H3 H4]]]]]] H' [size' [H6 H7]].
  split. assumption. exists m. split. subst.
  cbn. unfold update_list_at. cbn. by rewrite take0.
   exists size'. repeat split; auto.
Qed.

Lemma update_mem_preserves_global_mem_ptr_in_linear_memory : forall s s' f m m',
   INV_global_mem_ptr_in_linear_memory s f ->
   INV_global_mem_ptr_writable s f ->
   INV_globals_all_mut_i32 s ->
   nth_error (s_mems s) 0  = Some m ->
   (mem_length m' >= mem_length m)%N ->
   upd_s_mem (host_function:=host_function) s
                (update_list_at (s_mems s) 0 m') = s' ->
   INV_global_mem_ptr_in_linear_memory s' f.
Proof.
  unfold INV_global_mem_ptr_in_linear_memory. intros ? ? ? ? ? H Hinv Hinv' ? ? ? ? ? ? ? ?.
  subst. cbn in H3. unfold update_list_at in H3. rewrite take0 in H3. inv H3.
  eapply update_mem_preserves_global_var_w in Hinv; eauto.
  apply global_var_w_implies_global_var_r in Hinv. 2: now eapply update_mem_preserves_all_mut_i32.
  assert (N.of_nat gmp_v + 4 <= mem_length m)%N. { apply H; auto. } lia.
  Unshelve. assumption.
Qed.

Lemma update_mem_preserves_global_constr_alloc_ptr_in_linear_memory : forall s s' f m m',
   INV_constr_alloc_ptr_in_linear_memory s f  ->
   INV_constr_alloc_ptr_writable s f ->
   INV_globals_all_mut_i32 s ->
   nth_error (s_mems s) 0  = Some m ->
   (mem_length m' >= mem_length m)%N ->
   upd_s_mem (host_function:=host_function) s
                (update_list_at (s_mems s) 0 m') = s' ->
   INV_constr_alloc_ptr_in_linear_memory s' f.
Proof.
  unfold INV_constr_alloc_ptr_in_linear_memory. intros ? ? ? ? ? H Hinv Hinv' ? ? ? ? ? ? ?.
  eapply update_mem_preserves_global_var_w in Hinv; eauto.
  apply global_var_w_implies_global_var_r in Hinv.
  unfold global_var_r in Hinv. destruct Hinv as [v Hv]. rewrite H3 in Hv. inv Hv.
  eapply H in H3; eauto. now eapply update_mem_preserves_all_mut_i32.
Qed.

Lemma update_mem_preserves_num_functions_upper_bound : forall s s' m,
   INV_num_functions_upper_bound s  ->
   upd_s_mem (host_function:=host_function) s
                (update_list_at (s_mems s) 0 m) = s' ->
   INV_num_functions_upper_bound s'.
Proof.
  unfold INV_num_functions_upper_bound. intros. subst. cbn. assumption.
Qed.

Corollary update_mem_preserves_INV : forall s s' f m m',
  INV s f ->
  nth_error (s_mems s) 0  = Some m ->
  (mem_length m' >= mem_length m)%N ->
  mem_max_opt m' = Some max_mem_pages ->
  (exists size, mem_size m' = size /\ size <= max_mem_pages)%N ->
  upd_s_mem (host_function:=host_function) s
                (update_list_at (s_mems s) 0 m') = s' ->
  INV s' f.
Proof with eassumption.
 intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
 split. eapply update_mem_preserves_global_var_w...
 split. eapply update_mem_preserves_global_var_w...
 split. eapply update_mem_preserves_result_var_out_of_mem_is_zero...
 split. eapply update_mem_preserves_global_var_w...
 split. eapply update_mem_preserves_global_var_w...
 split. eapply update_mem_preserves_all_mut_i32...
 split. eapply update_mem_preserves_linear_memory...
 split. eapply update_mem_preserves_global_mem_ptr_in_linear_memory...
 split. assumption.
 eapply update_mem_preserves_num_functions_upper_bound...
Qed.

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

Lemma administrative_instruction_eqb_refl : forall x, administrative_instruction_eqb x x = true.
Proof.
  intros. unfold administrative_instruction_eqb.
  destruct administrative_instruction_eq_dec. reflexivity. contradiction.
Qed.

Lemma reduce_trans_label : forall instructions hs hs' sr sr' fr fr',
 clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction)
 (reduce_tuple (host_instance:=host_instance))
 (hs,  sr, fr, instructions)
 (hs', sr', fr', []) ->

  clos_refl_trans
  (host.host_state host_instance * datatypes.store_record host_function * frame *
   seq administrative_instruction) (reduce_tuple (host_instance:=host_instance))
  (hs,  sr, fr, [:: AI_label 0 [::] instructions])
  (hs', sr', fr', [::]).
Proof.
  intros.
  apply clos_rt_rt1n in H.
  remember (hs, sr, fr, instructions) as x. remember (hs', sr', fr', [::]) as x'.
  generalize dependent state. generalize dependent sr. generalize dependent fr. generalize dependent fr'. generalize dependent sr'. revert instructions hs hs'.
  induction H; intros; subst.
  - inv Heqx. constructor. constructor. now apply rs_label_const.
  - destruct y as [[[? ?] ?] ?].
    assert ((s, s0, f, l) = (s, s0, f, l)) as H' by reflexivity.
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[instr])). eapply rt_step.
    eapply r_label with (es:=instructions) (k:=1) (lh:= (LH_rec [] 0 [] (LH_base [] []) []) ). apply H.
    cbn. rewrite app_nil_r. now rewrite administrative_instruction_eqb_refl.
    cbn. rewrite app_nil_r. assert (eqseq [:: AI_label 0 [::] l] [:: AI_label 0 [::] l]). {
       cbn. now rewrite administrative_instruction_eqb_refl. } eassumption.
    eapply IHclos_refl_trans_1n; eauto.
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
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[instr])). eapply rt_step. eapply r_local. apply H.
    now eapply IHclos_refl_trans_1n.
Qed.

Ltac dostep_no_separate :=
  eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s] ++ ?[t])); first apply rt_step.

Ltac dostep :=
  eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s] ++ ?[t])); first apply rt_step; separate_instr.

(* only returns single list of instructions *)
Ltac dostep' :=
   eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s])); first  apply rt_step.

(* Print caseConsistent. *)
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

Lemma reduce_preserves_finst : forall hs hs' s s' f f' es es',
  reduce (host_instance:=host_instance) hs  s  f  es
                                        hs' s' f' es' -> f_inst f = f_inst f'.
Proof.
  intros. induction H; auto.
Qed.

Lemma reduce_trans_preserves_finst : forall s f es s' f' es' hs hs',
    reduce_trans (hs, s, f, es) (hs', s', f', es') -> f_inst f = f_inst f'.
Proof.
  intros. apply clos_rt_rt1n in H. remember (hs, s, f, es) as x. remember (hs', s', f', es') as x'.
  generalize dependent hs'. generalize dependent hs. revert s s' f f' es es'.
  induction H; intros; subst.
  - congruence.
  - destruct y as [[[hs0 s0] f0] es0].
    apply reduce_preserves_finst in H. rewrite H.
    now eapply IHclos_refl_trans_1n.
Qed.

Lemma app_trans: forall s f es s' f' es' les hs hs',
    reduce_trans (hs, s, f, es) (hs', s', f', es') ->
    reduce_trans (hs, s, f, (es ++ les)) (hs', s', f', (es' ++ les)).
Proof.
  intros. apply clos_rt_rt1n in H. remember (hs, s, f, es) as x. remember (hs', s', f', es') as x'.
  generalize dependent hs. generalize dependent hs'. revert s s' f f' es es'.
  induction H; intros; subst.
  - inv Heqx. apply rt_refl.
  - destruct y as [[[hs0 s0] f0] es0].
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[l])). apply rt_step.
    eapply r_label with (k:=0) (lh:=LH_base [] les). apply H. cbn. now apply /eqseqP.
    cbn. now apply /eqseqP.
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

Lemma decode_int_bounds : forall b m addr,
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

Lemma value_bounds : forall wal v sr fr,
  INV_num_functions_upper_bound sr ->
  repr_val_LambdaANF_Codegen fenv lenv nenv host_function v sr fr wal ->
 (-1 < Z.of_nat (wasm_value_to_immediate wal) < Wasm_int.Int32.modulus)%Z.
Proof.
  intros ? ? ? ? Hinv H.
  inv H.
  - (* constr. value *) cbn. lia.
  - (* function value *) cbn.
    assert (idx < length (s_funcs sr)). { apply nth_error_Some. congruence. }
    unfold INV_num_functions_upper_bound in Hinv. lia.
Qed.

Lemma extract_constr_arg : forall n vs v sr fr addr m,
  INV_num_functions_upper_bound sr ->
  nthN vs n = Some v ->
  nth_error (s_mems sr) 0 = Some m ->
  (* addr points to the first arg after the constructor tag *)
  repr_val_constr_args_LambdaANF_Codegen fenv lenv nenv host_function vs sr fr addr ->
  exists bs wal, load m (N.of_nat addr + 4 * n) 0%N 4 = Some bs /\
             VAL_int32 (wasm_value_to_i32 wal) = wasm_deserialise bs T_i32 /\
             repr_val_LambdaANF_Codegen fenv lenv nenv host_function v sr fr wal.
Proof.
  intros n vs v sr fr addr m Hinv H H1 H2. generalize dependent v. generalize dependent n. generalize dependent m.
  induction H2; intros. 1: inv H.
  assert (n = N.of_nat (N.to_nat n)) by lia. rewrite H8 in H7. generalize dependent v0.
  induction (N.to_nat n); intros.
  - (* n = 0 *)
    inv H7. assert (m = m0) by congruence. subst m0. rewrite N.add_comm.
    unfold load_i32 in H3. destruct (load m (N.of_nat addr) 0%N 4) eqn:Hl; inv H3.
    exists b. exists wal. repeat split. rewrite <- Hl. reflexivity. unfold wasm_value_to_i32.
    have H'' := value_bounds wal.
    unfold wasm_deserialise. f_equal. f_equal.
    have H' := decode_int_bounds _ _ _ Hl.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H8; try lia.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H8; auto.
    eapply value_bounds; eauto. assumption.
  - (* n = S n0 *)
    rewrite Nnat.Nat2N.inj_succ in H8. cbn in H7.
    replace (match
         match Pos.of_succ_nat n0 with
         | (p~1)%positive => Pos.IsPos p~0
         | (p~0)%positive => Pos.IsPos (Pos.pred_double p)
         | 1%positive => Pos.IsNul
         end
       with
       | Pos.IsPos p => N.pos p
       | _ => 0
       end)%N with (N.of_nat n0)%N in H7. 2: {
         destruct (N.succ (N.of_nat n0)) eqn:Heqn. lia. destruct (Pos.of_succ_nat n0) eqn:Har; lia. }
    edestruct IHrepr_val_constr_args_LambdaANF_Codegen. assumption. eassumption. eassumption.
    destruct H9 as [wal' [Hl [Heq Hval]]]. exists x. exists wal'.
    split. rewrite -Hl. f_equal. lia. split; eauto.
Qed.

Lemma N_div_ge0 : forall a b, (b > 0)%N -> (a >= 0)%N -> (a / b >= 0)%N.
Proof.
  intros. assert (Z.of_N a / Z.of_N b >= 0)%Z. apply Z_div_ge0; lia. lia.
Qed.

Import Nnat Znat.
Export numerics.

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
Lemma mem_store_preserves_length (m m': memory) (n: N) (off: static_offset) (bs: bytes) :
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
                               length (ml_data dat) = length (ml_data (mem_data m)) ->
                               length (ml_data dat') = length (ml_data (mem_data m))).
  - intros Hi.
    assert (length bs <= length bs) ; first lia.
    destruct (let '(_, acc_end) := fold_left _ _ _ in acc_end) eqn:Hfl ; try by inversion H.
    apply (Hi _ (mem_data m) m0) in H0 => //=.
    + destruct m' ; inversion H ; subst; cbn; congruence.
    + rewrite PeanoNat.Nat.sub_diag. rewrite drop0. exact Hfl.
  - induction j ; intros ; subst i.
    + rewrite Nat.sub_0_r in H1.
      rewrite drop_size in H1.
      simpl in H1. inversion H1. by rewrite - H4.
    + assert (j <= length bs) ; first lia.
      destruct (drop (length bs - S j) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S j) bs) = 0) ; first by rewrite Hdrop. clear H Hlen IHj H1 H2 H3 H4. exfalso.
      assert (size (drop (Datatypes.length bs - S j) bs) = 0). {rewrite Hdrop. reflexivity. } rewrite size_drop in H.
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
           replace (S (Datatypes.length bs - S j)) with (Datatypes.length bs - S j + 1) by lia. rewrite drop0. assumption.
        ++ erewrite <- mem_update_length; eauto.
Qed.

Lemma mem_store_preserves_max_pages : forall m m' v x l,
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
  destruct ((mem_size m + sgrow <=? page_limit)%N) eqn:Hari. 2: inv H.
  destruct (mem_max_opt m) eqn:Hmaxpages; cbn in H.
  (* mem_max_opt = Some n0 *)
  destruct (mem_size m + sgrow <=? n)%N. 2: inv H. inv H.
  unfold mem_length. unfold memory_list.mem_length.
  rewrite app_length. rewrite Nat2N.inj_add.
  rewrite N.add_comm. rewrite repeat_length. lia. inv H.
  unfold mem_length, memory_list.mem_length. cbn. rewrite app_length.
  rewrite repeat_length. lia.
Qed.

Lemma mem_grow_increases_size : forall m m' sgrow,
  mem_grow m sgrow = Some m' ->
  mem_size m' = (sgrow + mem_size m)%N.
Proof.
  intros. unfold mem_grow in H.
  destruct ((mem_size m + sgrow <=? page_limit)%N) eqn:Hari. 2: inv H.
  destruct (mem_max_opt m) eqn:Hmaxpages; cbn in H.
  (* mem_max_opt = Some n0 *)
  destruct (mem_size m + sgrow <=? n)%N. 2: inv H. inv H.
  unfold mem_size. unfold mem_length. unfold memory_list.mem_length.
  rewrite app_length. rewrite Nat2N.inj_add.
  rewrite N.add_comm. unfold page_size. rewrite <- N.div_add_l. 2: intro; lia.
  remember (N.of_nat (Datatypes.length (memory_list.ml_data (mem_data m)))) as len.
  rewrite repeat_length. rewrite N2Nat.id.
  replace (sgrow * (64 * 1024))%N with (sgrow * 65536)%N; reflexivity.
  (* mem_max_opt = None *)
  inv H. unfold mem_size. unfold mem_length. unfold memory_list.mem_length.
  rewrite app_length. rewrite Nat2N.inj_add.
  rewrite N.add_comm. unfold page_size. rewrite <- N.div_add_l. 2: intro; lia.
  remember (N.of_nat (Datatypes.length (memory_list.ml_data (mem_data m)))) as len.
  rewrite repeat_length. cbn. lia.
Qed.

Lemma mem_grow_preserves_max_pages : forall n m m',
  mem_grow m 1 = Some m' ->
  mem_max_opt m = Some n ->
  mem_max_opt m' = Some n.
Proof.
  intros. unfold mem_grow in H.
  destruct ((mem_size m + 1 <=? page_limit)%N). 2: inv H. cbn in H.
  rewrite H0 in H.
  destruct ((mem_size m + 1 <=? n)%N). 2: inv H. inv H. reflexivity.
Qed.

Lemma mem_lookup_in_lower : forall a l1 l2 init,
  (a < N.of_nat (length l1))%N ->
  mem_lookup a {| ml_init := init; ml_data := l1 ++ l2 |} =
  mem_lookup a {| ml_init := init; ml_data := l1 |}.
Proof.
  intros. unfold mem_lookup. cbn.
  rewrite nth_error_app1; auto. lia.
Qed.

Lemma mem_grow_preserves_original_values : forall a m m' maxlim,
  (mem_max_opt m = Some maxlim)%N ->
  (maxlim <= page_limit)%N ->
  (mem_size m + 1 <= maxlim)%N ->
  mem_grow m 1 = Some m' ->
  (a + 4 <= mem_length m)%N ->
  load_i32 m a = load_i32 m' a.
Proof.
  intros ? ? ? ? Hlim1 Hlim2 Hlim3 Hgrow Ha.
  have Hg := Hgrow. apply mem_grow_increases_length in Hg.
  unfold mem_grow in Hgrow.
  assert (Hlim4: (mem_size m + 1 <= page_limit)%N) by lia. apply N.leb_le in Hlim4, Hlim3.
  rewrite Hlim4 in Hgrow. rewrite Hlim1 in Hgrow. rewrite Hlim3 in Hgrow. inv Hgrow.

  unfold load_i32, load, memory_list.mem_grow, read_bytes, those. cbn.
  apply N.leb_le in Ha. rewrite Ha. apply N.leb_le in Ha.
  assert (Hlen: (a + 4 <=?
     mem_length {| mem_data := {| ml_init := ml_init (mem_data m);
                                  ml_data := ml_data (mem_data m) ++ repeat (ml_init (mem_data m)) (Pos.to_nat 65536) |};
                   mem_max_opt := Some maxlim |})%N). {
     unfold mem_length, memory_list.mem_length. cbn. rewrite app_length. rewrite repeat_length.
     unfold mem_length, memory_list.mem_length in Ha. apply N.leb_le. lia. }
  rewrite Hlen.
  unfold mem_length, memory_list.mem_length in Ha.
  repeat rewrite mem_lookup_in_lower; try lia. reflexivity.
Qed.

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
  intros. replace (a + 1) with (ssrnat.addn a 1) by (rewrite ssrnat.plusE; auto).
  rewrite update_list_at_is_set_nth. unfold update_list_at. now rewrite drop_is_skipn.
  apply /ssrnat.leP. cbn. rewrite -length_is_size. lia.
Qed.

Lemma memory_grow_success : forall m sr fr,
  INV_linear_memory sr fr ->
  nth_error (s_mems sr) 0 = Some m ->
  (mem_size m + 1 <=? max_mem_pages)%N ->
  exists m', mem_grow m 1 = Some m'.
Proof.
  intros m sr fr Hinv H Hsize. eexists. unfold mem_grow.
  assert ((mem_size m + 1 <=? page_limit)%N) as H'. { unfold max_mem_pages in H. unfold page_limit. apply N.leb_le. apply N.leb_le in Hsize. unfold max_mem_pages in Hsize. lia. }
  rewrite H'. clear H'.
  unfold INV_linear_memory in Hinv. destruct Hinv as [H1 [m' [H2 [H3 [H4 [H5 H6]]]]]].
  rewrite H2 in H. inv H. rewrite H5. cbn. rewrite Hsize. reflexivity.
Qed.

Ltac simpl_modulus_in H := unfold Wasm_int.Int32.modulus, Wasm_int.Int32.half_modulus, two_power_nat in H; cbn in H.
Ltac simpl_modulus := unfold Wasm_int.Int32.modulus, Wasm_int.Int32.half_modulus, two_power_nat.

Definition max_constr_alloc_size := (max_constr_args * 4 + 4)%Z. (* in bytes *)

Lemma signed_upper_bound : forall x, (Wasm_int.Int32.signed (Wasm_int.Int32.repr x) < Wasm_int.Int32.half_modulus)%Z.
Proof.
  intros x.
  unfold Wasm_int.Int32.signed. destruct (zlt _ _); auto.
  unfold Wasm_int.Int32.unsigned in *. clear g.
  have H' := Wasm_int.Int32.Z_mod_modulus_range x. simpl_modulus_in H'. simpl_modulus. cbn. lia.
Qed.

Lemma mem_length_upper_bound : forall m, (mem_size m <= max_mem_pages)%N
  -> (mem_length m <= (max_mem_pages + 1) * page_size)%N.
Proof.
  intros.
  unfold mem_size, page_size, max_mem_pages in H. unfold page_size. cbn in *.
  remember (mem_length m) as n. clear Heqn m.
  assert (Z.of_N n / 65536 <= 5000)%Z as Hn by lia. clear H.
  assert (Hs: (65536 > 0)%Z) by lia.
  destruct (Zdiv_eucl_exist Hs (Z.of_N n)) as [[z z0] [H1 H2]].
  rewrite H1 in Hn.
  rewrite Z.add_comm in Hn.
  rewrite Z.mul_comm in Hn.
  rewrite Z.div_add in Hn; try lia.
  rewrite Zdiv_small in Hn; lia.
Qed.

Lemma i32_exists_nat : forall (x : i32), exists n, x = nat_to_i32 n /\ (-1 < Z.of_nat n <  Wasm_int.Int32.modulus)%Z.
Proof.
  intros [val H]. exists (Z.to_nat val). split; try lia.
  destruct (nat_to_i32 (Z.to_nat val)) eqn:He. inv He. revert intrange.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
  rewrite Z2Nat.id; try lia. intros.
  destruct H as [low high].
  destruct intrange as [low' high'].
  rewrite (Wasm_int.Int32.Z_lt_irrelevant low low').
  rewrite (Wasm_int.Int32.Z_lt_irrelevant high high'). reflexivity.
Qed.

(* there is quite a bit of copy paste in this lemma: TODO reorganize/automate *)
Lemma memory_grow_reduce : forall grow state s f,
  grow = grow_memory_if_necessary page_size ->
  INV s f ->
  exists s', reduce_trans
   (state, s, f, [seq AI_basic i | i <- grow])
   (state, s', f, [])
  (* enough memory to alloc. constructor *)
  /\ ((INV s' f /\
        (forall m v_gmp, nth_error (s_mems s') 0 = Some m ->
           sglob_val (host_function:=host_function) s' (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 v_gmp)) ->
           (Z.of_nat v_gmp < Wasm_int.Int32.modulus)%Z ->
           (Z.of_nat v_gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z) /\
        (forall wal val, repr_val_LambdaANF_Codegen fenv lenv nenv host_function val s f wal ->
                         repr_val_LambdaANF_Codegen fenv lenv nenv host_function val s' f wal))
      \/ (sglob_val (host_function:=host_function) s' (f_inst f) result_out_of_mem = Some (VAL_int32 (nat_to_i32 1)))).
Proof with eauto.
  destruct exists_i32 as [my_i32 _].
  (* grow memory if necessary *)
  intros grow state sr fr H Hinv. subst.
  unfold grow_memory_if_necessary. cbn.
  have I := Hinv. destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM [? ?]]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].

  assert (global_var_r global_mem_ptr sr fr) as H2. { apply global_var_w_implies_global_var_r; auto. } destruct H2 as [g Hgmp_r]. destruct (i32_exists_nat g) as [gmp [HgmpEq HgmpBound]]. subst g.
  have H' := HgmpInM _ _ Hm2 Hgmp_r HgmpBound.
  destruct ((~~ Wasm_int.Int32.lt
                     (Wasm_int.Int32.repr
                        (  Wasm_int.Int32.signed
                           (Wasm_int.Int32.iadd (nat_to_i32 gmp)
                              (nat_to_i32 (N.to_nat page_size))) ÷ 65536))
                     (Wasm_int.Int32.repr (Z.of_nat (ssrnat.nat_of_bin (mem_size m)))))) eqn:HneedMoreMem.
  2: rename HneedMoreMem into HenoughMem.
  (* need to grow memory *)
  { destruct (N.leb_spec (size + 1) max_mem_pages); unfold max_mem_pages in *.
    (* grow memory success *)
    assert (mem_size m + 1 <= page_limit)%N. { unfold page_limit. lia. }
    assert (Hsize: (mem_size m + 1 <=? max_mem_pages)%N). { subst. apply N.leb_le. now unfold max_mem_pages. }

    have Hgrow := memory_grow_success _ _ _ INVlinmem Hm2 Hsize.
    destruct Hgrow.
    { eexists. split.
      (* load global_mem_ptr *)
      dostep. separate_instr. elimr_nary_instr 0. apply r_get_global. eassumption.
      (* add required bytes *)
      dostep. separate_instr. elimr_nary_instr 2. constructor.
      apply rs_binop_success. reflexivity.
      dostep. separate_instr. elimr_nary_instr 2. constructor.
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
        simpl_modulus_in H''. cbn. lia. cbn in H4. lia. }
      dostep. apply r_eliml; auto.
      elimr_nary_instr 0. eapply r_current_memory...

      dostep. separate_instr. elimr_nary_instr 2.
      constructor. apply rs_relop.

      dostep'. separate_instr.
      constructor. subst.
      rewrite HneedMoreMem. apply rs_if_true. intro H3'. inv H3'.

      dostep'. separate_instr. constructor. apply rs_block with (vs:=[])(n:= 0); auto.
      cbn.
      apply reduce_trans_label.
      dostep'. separate_instr. elimr_nary_instr 1. eapply r_grow_memory_success; eauto.
      dostep'. separate_instr. elimr_nary_instr 2. constructor. apply rs_relop. cbn.
      dostep'. constructor. apply rs_if_false.

      assert (size >= 0)%N. { subst. cbn. auto. lia. }
      { unfold Wasm_int.Int32.eq. cbn. rewrite zeq_false. reflexivity. intro.
        subst. cbn in *. unfold page_limit in *.
        rewrite Z_nat_bin in H5.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in H5. lia. simpl_modulus. cbn. lia. }
      dostep'. separate_instr. constructor. apply rs_block with (vs:= [])(n:=0); eauto.
      apply reduce_trans_label. cbn. apply rt_refl.
      intros.
      left. split.
      { (* invariant *) eapply update_mem_preserves_INV. 6: reflexivity. assumption. eassumption.
        erewrite mem_grow_increases_length; eauto. lia.
      eapply mem_grow_preserves_max_pages... exists (mem_size m + 1)%N. split.
      eapply mem_grow_increases_size in H3; auto. rewrite N.add_comm. apply H3. now apply N.leb_le. }
      { (* enough memory available *)
        rename x into m''. split. intros. subst. destruct (update_list_at (s_mems sr) 0 m'') eqn:Hm'. inv H4.
        inv H4. assert (m0 = m''). { unfold update_list_at in Hm'.  rewrite take0 in Hm'. now inv Hm'. } subst m0.
        rename m'' into m'.
        assert (mem_length m' = (page_size + mem_length m)%N) as Hlength'. {
                        eapply mem_grow_increases_length in H3; eauto. }
        assert (v_gmp = gmp). {
          assert (Hgl: sglob_val (upd_s_mem sr (m' :: l)) (f_inst fr) global_mem_ptr
                = sglob_val sr (f_inst fr) global_mem_ptr) by reflexivity.
          rewrite Hgl in H5. rewrite H5 in Hgmp_r. inv Hgmp_r.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H7; lia. } subst v_gmp.
        rewrite Hlength'. apply mem_length_upper_bound in Hm5; cbn in Hm5.
        unfold page_size. lia.
        (* preserved value relation *)
        intros. eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H4.
        reflexivity. reflexivity. eassumption.
        cbn. unfold update_list_at. rewrite take0. cbn. reflexivity. eassumption.
        subst. apply mem_length_upper_bound in Hm5; cbn in Hm5. simpl_modulus; cbn; lia.
        rewrite <- Hgmp_r. reflexivity.
        subst. apply mem_length_upper_bound in Hm5; cbn in Hm5.
        apply mem_grow_increases_length in H3. simpl_modulus; cbn; lia. lia.
        intros. eapply mem_grow_preserves_original_values; eauto; unfold page_limit; lia. } }
       (* growing memory fails *)
      edestruct INVresM_w as [sr'' HresM].

      eexists. split.
      (* load global_mem_ptr *)
      dostep. separate_instr. elimr_nary_instr 0. apply r_get_global. eassumption.
      (* add required bytes *)
      dostep. elimr_nary_instr 2. constructor.
      apply rs_binop_success. reflexivity.
      dostep. elimr_nary_instr 2. constructor.
      apply rs_binop_success. cbn. unfold is_left.
      rewrite zeq_false. reflexivity.
      { (*TODO code duplication *)
        intro HA. unfold Wasm_int.Int32.unsigned, Wasm_int.Int32.iadd, Wasm_int.Int32.add,
                      Wasm_int.Int32.unsigned in HA;
        cbn in HA.
        assert ((Wasm_int.Int32.signed
          (Wasm_int.Int32.repr
             (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z). (* arbitrary number *)
        apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
        have H'' := signed_upper_bound (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size).
        cbn. simpl_modulus_in H''. lia. cbn in H2. lia. }
      dostep. apply r_eliml; auto.
      elimr_nary_instr 0. eapply r_current_memory...

      dostep. elimr_nary_instr 2. constructor. apply rs_relop.

      dostep'. separate_instr. constructor. subst. rewrite HneedMoreMem. apply rs_if_true. discriminate.
      dostep'. constructor. apply rs_block with (vs:=[])(n:= 0); auto.
      apply reduce_trans_label.
      dostep. elimr_nary_instr 1. eapply r_grow_memory_failure; try eassumption.
      dostep. elimr_nary_instr 2. constructor. apply rs_relop. cbn.
      dostep'. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
      dostep'. constructor. eapply rs_block with (vs:=[]); auto.
      apply reduce_trans_label. cbn.
      constructor. apply r_set_global. eassumption.
      (* correct resulting environment *)
      right. intros. eapply global_var_write_read_same. eassumption.
      }
    (* enough space already *)
    {
      eexists. split.
      edestruct INVgmp_w as [sr' Hgmp].
      (* load global_mem_ptr *)
      dostep. separate_instr. elimr_nary_instr 0. apply r_get_global. eassumption.
      (* add required bytes *)
      dostep. separate_instr. elimr_nary_instr 2. constructor.
      apply rs_binop_success. reflexivity.
      dostep. separate_instr. elimr_nary_instr 2. constructor.
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
        simpl_modulus_in H''. cbn. lia. cbn in H1. lia. }
      dostep. apply r_eliml; auto.
      elimr_nary_instr 0. eapply r_current_memory...

      dostep. separate_instr. elimr_nary_instr 2.
      constructor. apply rs_relop.

      dostep'. separate_instr.
      constructor. subst.
      rewrite HenoughMem. apply rs_if_false. reflexivity.

      dostep'. constructor. apply rs_block with (vs:=[])(n:= 0); auto. cbn.
      apply reduce_trans_label. apply rt_refl. left. split. assumption.

      (* enough space *)
      { split; auto. intros. unfold max_mem_pages in *.
        rewrite H2 in Hgmp_r. inv Hgmp_r.
        repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H5; try lia. apply Nat2Z.inj in H5. subst gmp.
        assert (m = m0). { cbn in Hm2. rewrite H1 in Hm2. now inv Hm2. } subst m0.
        unfold Wasm_int.Int32.lt in HenoughMem.
        destruct (zlt _ _) as [Ha|Ha]. 2: inv HenoughMem. clear HenoughMem.
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in Ha. cbn in Ha.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: { unfold  Wasm_int.Int32.modulus,
         two_power_nat. cbn. apply mem_length_upper_bound in Hm5; cbn in Hm5. lia. }
        rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: { simpl_modulus. cbn. lia. }
        remember ( (Wasm_int.Int32.signed
                (Wasm_int.Int32.repr
                   (Z.of_nat v_gmp + Z.of_nat (Pos.to_nat 65536))) ÷ 65536))%Z as y.
        unfold Wasm_int.Int32.signed, Wasm_int.Int32.unsigned in Heqy.
        rewrite Z_nat_bin in Ha.
        have Hlength := mem_length_upper_bound _ Hm5. unfold page_size, max_mem_pages in Hlength. cbn in Hlength.
        (* currently can only use half of memory, TODO: relax*)
        rewrite zlt_true in Heqy. 2: { cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. lia. simpl_modulus. cbn. lia. }
        { unfold Wasm_int.Int32.signed in Heqy. cbn in Heqy.
          rewrite Wasm_int.Int32.Z_mod_modulus_id in Heqy. 2: { simpl_modulus. cbn. lia. }
          cbn in Heqy. replace (Z.of_nat (Pos.to_nat 65536)) with 65536%Z in Heqy by lia.
          rewrite (Z.quot_add (Z.of_nat v_gmp) 1 65536) in Heqy; try lia.
          subst y. unfold Wasm_int.Int32.signed in Ha. cbn in Ha.
          rewrite zlt_true in Ha. 2: { assert ((Z.of_nat v_gmp ÷ 65536 < 6000)%Z) as H''. { apply Z.quot_lt_upper_bound; lia. } rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. simpl_modulus. cbn.
          assert (Z.of_nat v_gmp ÷ 65536  >= 0)%Z.
          rewrite Zquot.Zquot_Zdiv_pos; try lia.
          apply Z_div_ge0; lia. lia. }
          rewrite zlt_true in Ha. 2: { rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. simpl_modulus. cbn. lia. }
          rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: {
          assert ((Z.of_nat v_gmp ÷ 65536 < 6000)%Z) as H''. { apply Z.quot_lt_upper_bound; lia. }
          simpl_modulus. cbn.
          assert (Z.of_nat v_gmp ÷ 65536  >= 0)%Z. { rewrite Zquot.Zquot_Zdiv_pos; try lia. apply Z_div_ge0; lia. }
          lia. }
          rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: { simpl_modulus. cbn. lia. }
          cbn in Ha. rewrite N2Z.inj_div in Ha.
          rewrite Zquot.Zquot_Zdiv_pos in Ha; try lia.
          remember (Z.of_nat v_gmp) as q.
          remember (Z.of_N (mem_length m)) as r.
          (* the following can probably be done in an easier way, TODO*)
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
     }}
   } Unshelve. all: auto.
(* Qed. hangs here *)
Admitted.


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
    apply (H _ (mem_data m)) in H0 as [datf' Hdatf'].
    + rewrite PeanoNat.Nat.sub_diag in Hdatf'.
      rewrite drop0 in Hdatf'.
      rewrite Hdatf'.
      by eexists _.
    + unfold mem_length, memory_list.mem_length.
      by rewrite Nat2N.id.
  - induction i ; intros ; subst j.
    + rewrite <- minus_n_O.
      repeat rewrite length_is_size. rewrite drop_size.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop.
        rewrite length_is_size in H2. rewrite size_drop in H2.
        rewrite -length_is_size in H2. rewrite ssrnat.subnE in H2. unfold ssrnat.subn_rec in H2. lia.
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

Lemma load_store : forall m addr v b1 b2 b3 b4,
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

Lemma store_load : forall m m' addr v,
length v = 4 ->
store m addr 0%N v 4 = Some m' ->
load_i32 m' addr = Some (wasm_deserialise v T_i32).
Proof.
  intros. assert (mem_length m = mem_length m'). { rewrite <- H in H0. now eapply mem_store_preserves_length. }
   unfold store in H. unfold store in H0.
  destruct ((addr + 0 + N.of_nat 4 <=? mem_length m)%N) eqn:Heq. 2: inv H0.
  unfold load_i32. unfold load. cbn. cbn in Heq. unfold store in H0.
  assert (Hbytes: exists b1 b2 b3 b4, v = [b1; b2; b3; b4]). {
    destruct v. inv H. destruct v. inv H.
    destruct v. inv H. destruct v. inv H. destruct v.
    exists b, b0, b1, b2. reflexivity. inv H. }
  destruct Hbytes as [b1 [b2 [b3 [b4 Hb]]]]. subst v. clear H. rewrite N.add_0_r. rewrite N.add_0_r in Heq, H0.
  unfold write_bytes in H0. cbn in H0. rewrite N.add_0_r in H0.
  destruct (mem_update addr b1 (mem_data m)) eqn:Hupd1. 2: inv H0.
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
  destruct (addr     <? N.of_nat (Datatypes.length (ml_data (mem_data m))))%N eqn:Hl1. 2: inv Hupd1.
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
  assert (He: exists e, nth_error (ml_data (mem_data m)) (N.to_nat addr) = Some e). { apply notNone_Some. intro Hcontra.
  apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b1 (ml_data (mem_data m)) (N.to_nat addr) b1)
  (N.to_nat (addr + 1)) = Some e). { apply notNone_Some.
   intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b2
     (set_nth b1 (ml_data (mem_data m)) (N.to_nat (addr)) b1)
     (N.to_nat (addr + 1)) b2)
  (N.to_nat (addr + 2)) = Some e). {
    apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b3
     (set_nth b2
        (set_nth b1 (ml_data (mem_data m)) (N.to_nat addr)
           b1) (N.to_nat (addr + 1)) b2)
     (N.to_nat (addr + 2)) b3)
  (N.to_nat (addr + 3)) = Some e). { apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same; try lia; auto. eassumption.
Qed.


Lemma enough_space_to_load m k :
  (k + 4 <= mem_length m)%N -> exists v, load_i32 m k = Some v.
Proof.
  intros. unfold load_i32, load.
  assert ((k + (0 + N.of_nat 4) <=? mem_length m)%N). { apply N.leb_le. lia. } rewrite H0.
  unfold read_bytes, those, mem_lookup. cbn.
  apply N.leb_le in H0. unfold mem_length, memory_list.mem_length in H0.
  assert (Hex1 : exists v, nth_error (ml_data (mem_data m)) (N.to_nat (k + 0 + 0)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex1 as [x1 Hex1]. rewrite Hex1.
  assert (Hex2: exists v, nth_error (ml_data (mem_data m)) (N.to_nat (k + 0 + 1)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex2 as [x2 Hex2]. rewrite Hex2.
  assert (Hex3: exists v, nth_error (ml_data (mem_data m)) (N.to_nat (k + 0 + 2)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex3 as [x3 Hex3]. rewrite Hex3.
  assert (Hex4: exists v, nth_error (ml_data (mem_data m)) (N.to_nat (k + 0 + 3)) = Some v).
  { apply notNone_Some. intro. apply nth_error_None in H1. lia. }
  destruct Hex4 as [x4 Hex4]. rewrite Hex4.
   eauto.
Qed.


Ltac solve_arith_load_store := repeat (try rewrite length_is_size; try rewrite size_set_nth;
                                       try rewrite maxn_nat_max;
                                       try rewrite Nat2N.inj_max;
                                       try apply N.ltb_lt; try apply N.leb_le;
                                       try (apply N.max_lt_iff; right); try (apply Nat.max_lt_iff; right);
                                       rewrite -length_is_size; try lia).

Lemma load_store_load : forall m m' a1 a2 v w,
  length w = 4 ->
  (a1 + 4 <= a2)%N ->
  load_i32 m a1 = Some v ->
  store m a2 0%N w 4 = Some m' ->
  load_i32 m' a1 = Some v.
Proof.
  intros ? ? ? ? ? ? Hlw Harith Hload Hstore.
  cbn in Harith.
  unfold store in Hstore. destruct (a2 + 0 + N.of_nat 4 <=?
        mem_length m)%N eqn:Ha. 2: inv Hstore.
  apply N.leb_le in Ha. cbn in Ha. unfold mem_length, memory_list.mem_length in Ha.
  destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw. destruct w. 2: inv Hlw. clear Hlw.
  unfold write_bytes in Hstore. cbn in Hstore. unfold mem_update in Hstore. cbn in Hstore.
  destruct (a2 + 0 + 0 <? N.of_nat (Datatypes.length (ml_data (mem_data m))))%N eqn:Ha1. 2: discriminate.
  cbn in Hstore. rewrite take_drop_is_set_nth in Hstore; try lia.
  rewrite take_drop_is_set_nth in Hstore. 2: solve_arith_load_store.
  assert ((a2 + 0 + 1 <? N.of_nat (Datatypes.length (set_nth b (ml_data (mem_data m))
                    (N.to_nat (a2 + 0 + 0)) b)))%N) as Ha2. { solve_arith_load_store. }
 rewrite Ha2 in Hstore. cbn in Hstore. repeat rewrite take_drop_is_set_nth in Hstore. 2: solve_arith_load_store.
assert ((a2 + 0 + 2 <?
                N.of_nat
                  (Datatypes.length
                     (set_nth b0
                        (set_nth b (ml_data (mem_data m))
                          (N.to_nat (a2 + 0 + 0)) b)
                        (N.to_nat (a2 + 0 + 1)) b0)))%N) as Ha3. { solve_arith_load_store. }
  rewrite Ha3 in Hstore.
  repeat rewrite take_drop_is_set_nth in Hstore. 2: solve_arith_load_store.
  assert ((a2 + 0 + 3 <?
           N.of_nat (Datatypes.length
                       (set_nth b1
                          (set_nth b0
                             (set_nth b (ml_data (mem_data m))
                                (N.to_nat (a2 + 0 + 0)) b)
                             (N.to_nat (a2 + 0 + 1)) b0)
                          (N.to_nat (a2 + 0 + 2)) b1)))%N) as Ha4. { solve_arith_load_store. }
  rewrite Ha4 in Hstore. inv Hstore.

  unfold load_i32, load in *. cbn. unfold mem_length, memory_list.mem_length in *. cbn in *.
  destruct ((a1 + 4 <=? N.of_nat (Datatypes.length (ml_data (mem_data m))))%N) eqn:Hr1. 2: discriminate.
  cbn in Ha4. unfold read_bytes, those, mem_lookup in Hload. cbn in Hload.

  destruct (nth_error (ml_data (mem_data m))
              (N.to_nat (a1 + 0 + 0))) eqn:Hl1. 2: discriminate.
  destruct (nth_error (ml_data (mem_data m))
                (N.to_nat (a1 + 0 + 1))) eqn:Hl2. 2: discriminate.
  destruct (nth_error (ml_data (mem_data m))
                (N.to_nat (a1 + 0 + 2))) eqn:Hl3. 2: discriminate.
  destruct (nth_error (ml_data (mem_data m))
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
                   (set_nth b (ml_data (mem_data m))
                      (N.to_nat (a2 + 0 + 0)) b) (N.to_nat (a2 + 0 + 1)) b0) (N.to_nat (a2 + 0 + 2)) b1)
             (N.to_nat (a2 + 0 + 3)) b2)))%N) as Hdf. { solve_arith_load_store. }  rewrite Hdf. cbn.

  unfold read_bytes, those, mem_lookup. cbn.
  repeat rewrite set_nth_nth_error_other; try by lia.
  rewrite Hl1 Hl2 Hl3 Hl4. reflexivity. all: solve_arith_load_store.
Qed.

(* taken from iriswasm *)
Lemma deserialise_bits v t :
  types_agree t v -> wasm_deserialise (bits v) t = v.
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

Lemma store_constr_args_reduce : forall ys offset vs sargs state rho s f m v_cap,
  INV s f ->
  nth_error (s_mems s) 0 = Some m ->
  sglob_val (host_function:=host_function) s (f_inst f) constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap)) ->
  ((N.of_nat v_cap) + page_size < mem_length m)%N ->
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  (-1 < Z.of_nat (length ys + offset) < 2 * max_constr_args)%Z ->
  sglob_val (host_function:=host_function) s (f_inst f)
                 global_mem_ptr = Some (VAL_int32 (nat_to_i32 (4 + (4*offset) + v_cap))) ->
  Forall_statements_in_seq' (set_nth_constr_arg fenv lenv nenv) ys sargs offset ->
  get_list ys rho = Some vs ->
  (* memory relation: ys are available as locals in frame f *)
  (forall y, In y ys -> (exists v6 val, M.get y rho = Some v6
                                     /\ stored_in_locals lenv nenv y val f
                                     /\ repr_val_LambdaANF_Codegen fenv lenv nenv _ v6 s f val)) ->
  exists s', reduce_trans
                  (state, s, f, [seq AI_basic i | i <- sargs])
                  (state, s', f, [])
            /\ INV s' f
            (* constructor args val *)
            /\ sglob_val (host_function:=host_function) s' (f_inst f)
                 constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap))
            /\ (0 <= Z.of_nat v_cap < Wasm_int.Int32.modulus)%Z
            /\ repr_val_constr_args_LambdaANF_Codegen fenv lenv nenv _ vs s' f (4 + (4*offset) + v_cap)
            /\ sglob_val (host_function:=host_function) s' (f_inst f)
                 global_mem_ptr = Some (VAL_int32 (nat_to_i32 ((4 + (4*offset) + v_cap) + 4 * (length ys))))
            /\ s_funcs s = s_funcs s'
            (* previous mem including tag unchanged *)
            /\ exists m', nth_error (s_mems s') 0 = Some m'
                       /\ mem_length m = mem_length m'
                       /\ forall a, N.to_nat a <= v_cap + 4 * offset -> load_i32 m a = load_i32 m' a.
Proof.
  induction ys; intros offset vs sargs state rho s f m v_cap Hinv Hm Hcap Hlen Hargs Hoffset Hgmp H Hvs HmemR.
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
    destruct Hinv_linmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. assert (m = m') by congruence. subst m' size.
    apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
    split. simpl_modulus. cbn. lia. split. econstructor.
    split. rewrite Hgmp. do 3! f_equal. cbn. lia.
    split. reflexivity.
    exists m. auto.
  }
  { inv H. inv H6. rename s' into instr_args. rename a into y.
    (* rewrite map_cat. inv H0. cbn. *)
    inv H. rename i into y'.
    { (* store var *)
      destruct vs. { cbn in Hvs. destruct (rho ! y). 2: inv Hvs. destruct (get_list ys rho); inv Hvs. }
      assert (Hgetlist: get_list ys rho = Some vs). {
          cbn in Hvs. destruct (rho ! y). 2: inv Hvs. destruct (get_list ys rho); inv Hvs; auto. }
      assert (Hrhoy: rho ! y = Some v). { cbn in Hvs. destruct (rho ! y). 2: inv Hvs.
        destruct (get_list ys rho); inv Hvs; auto. }
      clear Hvs. rename Hgetlist into Hvs.
      (* invariants *)
      have I := Hinv. destruct I as [_ [_ [_ [Hinv_gmp [Hinv_cap [Hinv_muti32 [Hinv_linmem _]]]]]]].
      eapply global_var_w_implies_global_var_r in Hinv_cap; auto. destruct Hinv_cap as [cap ?].
      eapply global_var_w_implies_global_var_r in Hinv_gmp; auto. destruct Hinv_gmp as [gmp ?].

      assert (Htmp: In y (y :: ys)) by (cbn; auto).
      destruct (HmemR _ Htmp) as [val [wal [Hrho [[y0' [Htv Hly']] Hy_val]]]].
      assert (val = v) by congruence. subst v. clear Hrhoy.
      assert (y' = y0'). { inv H0. congruence. } subst y0'.
      clear Htmp.

      destruct Hinv_linmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst size. cbn.

      assert (m = m') by congruence. subst m'. clear Hmem2.

      destruct (i32_exists_nat cap) as [x1 [Hx ?]]. subst cap. rename x1 into cap.
      destruct (i32_exists_nat gmp) as [x1 [Hx' ?]]. subst gmp. rename x1 into gmp.
      assert (exists m0, store m
        (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (nat_to_i32 v_cap) (nat_to_i32 (S (S (S (S (offset * 4)))))))) 0%N
          (bits (VAL_int32 (wasm_value_to_i32 wal))) (t_length T_i32) = Some m0) as Hm0. {
          intros.  edestruct enough_space_to_store as [m3 Hstore]. 2: { exists m3.
          replace (t_length T_i32) with (Datatypes.length (bits (VAL_int32 (wasm_value_to_i32 wal)))) by auto. apply Hstore. } rewrite N.add_0_r.
       replace (N.of_nat (Datatypes.length (bits (VAL_int32 (wasm_value_to_i32 wal))))) with 4%N by reflexivity.
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
      assert (Hmaxargs : (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z). {
      cbn in Hargs. lia. } clear Hargs.

      assert (Hoff: (Datatypes.length (y :: ys) + offset) = Datatypes.length ys + (S offset)). { cbn. lia. }
      rewrite Hoff in Hoffset. clear Hoff.

      destruct Hm0 as [m0 Hm0].
      remember (upd_s_mem (host_function:=host_function) s
                       (update_list_at (s_mems s) 0 m0)) as s'.
      assert (Hinv' : INV s' f). {
        eapply update_mem_preserves_INV. 6: subst; reflexivity. assumption. eassumption.
        apply mem_store_preserves_length in Hm0. lia.
        apply mem_store_preserves_max_pages in Hm0. congruence.
        eexists. split. reflexivity.
        apply mem_store_preserves_length in Hm0. unfold mem_size in Hmem5. now rewrite Hm0 in Hmem5. }
      have I := Hinv'. destruct I as [_ [_ [_ [Hgmp_w _]]]].
      destruct (Hgmp_w (Wasm_int.Int32.iadd (nat_to_i32 gmp) (nat_to_i32 4))) as [s_before_IH ?].

      assert (Hinv_before_IH : INV s_before_IH f). { eapply update_global_preserves_INV; try eassumption. unfold result_out_of_mem, global_mem_ptr. lia. }

      assert (Hmem_before_IH : nth_error (s_mems s_before_IH) 0 = Some m0). { subst s'.
        erewrite <- update_glob_keeps_memory_intact; try eassumption. cbn.
      unfold update_list_at. now rewrite take0. }

      assert (Hcap_before_IH: sglob_val (host_function:=host_function) s_before_IH
       (f_inst f) constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap))). { subst.
       eapply  global_var_write_read_other; try apply H5.
       unfold constr_alloc_ptr, global_mem_ptr. lia. cbn. rewrite -Hcap. reflexivity. }

      assert (Hlen_m0: (N.of_nat v_cap + page_size < mem_length m0)%N). {
        apply mem_store_preserves_length in Hm0. unfold mem_length, memory_list.mem_length in *. congruence. }

      assert (HrelM_before_IH: (forall y : var,
      In y ys ->
      exists (v6 : cps.val) (val : wasm_value),
        rho ! y = Some v6 /\
        stored_in_locals lenv nenv y val f /\
        repr_val_LambdaANF_Codegen fenv lenv nenv host_function v6 s_before_IH f val)). {
        intros. assert (Htmp : In y0 (y :: ys)) by (right; assumption).
        destruct (HmemR _ Htmp) as [val' [wal' [? [? ?]]]].
        subst s'. exists val', wal'. repeat split; try assumption.

        { edestruct i32_exists_nat as [? [Hn ?]]. erewrite Hn in H5.
          rewrite H1 in Hgmp. remember (4 + 4 * offset + v_cap) as n. inv Hgmp.
          unfold page_size in Hlen_m0; cbn in Hlen_m0.
          apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
          have Hm0' := Hm0. apply mem_store_preserves_length in Hm0'. cbn in Hoffset. simpl_modulus_in H4; cbn in H4.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H12; simpl_modulus; cbn; try lia.
          apply Nat2Z.inj in H12. subst gmp.

          unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add, nat_to_i32 in Hn. remember (4 + 4 * offset + v_cap) as n. inv Hn.
          repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id in H12; try lia). 2: simpl_modulus; cbn; lia.
          2: { rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia. }
          assert (x = (4 + 4 * offset + v_cap) + 4) by lia. subst x. clear H12.
          eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H9; subst.
          reflexivity. apply update_glob_keeps_funcs_intact in H5. rewrite -H5. reflexivity.
          eassumption. eassumption. eassumption. have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [INVgmp_M _]]]]]]]]. have H' := INVgmp_M _ _ Hm H1 H4. simpl_modulus. cbn. lia.
          eapply global_var_write_read_same in H5. eassumption. simpl_modulus. cbn. lia.

          lia. intros.
          assert (Hex: exists v, load_i32 m a = Some v). { apply enough_space_to_load. lia. } destruct Hex.
          rewrite H12. symmetry. erewrite load_store_load; try apply Hm0; auto.
          unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add. remember (S (S (S (S (offset * 4))))) as n.
          cbn. subst.
          repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id); try lia. }
        }

      assert (Hgmp_before_IH: sglob_val (host_function:=host_function) s_before_IH (f_inst f) global_mem_ptr =
     Some (VAL_int32 (nat_to_i32 (4 + 4 * S offset + v_cap)))). { subst.
     apply global_var_write_read_same in H5. rewrite H5. f_equal. f_equal.
     unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add. cbn.
     rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. unfold nat_to_i32. f_equal.
     rewrite Hgmp in H1. remember (4 + 4 * offset + v_cap) as n. inv H1.
     rewrite Wasm_int.Int32.Z_mod_modulus_id in H7.
     rewrite Wasm_int.Int32.Z_mod_modulus_id in H7; try lia.
     cbn in Hoffset. unfold page_size in Hlen_m0. cbn in Hlen_m0.
     unfold max_constr_args in Hmaxargs.
     apply mem_store_preserves_length in Hm0.
     apply mem_length_upper_bound in Hmem5. cbn in Hmem5. simpl_modulus. cbn. lia. }

      have IH := IHys _ _ _ state _ _ _ _ _ Hinv_before_IH Hmem_before_IH Hcap_before_IH Hlen_m0 Hmaxargs Hoffset Hgmp_before_IH H3 Hvs HrelM_before_IH.
      clear IHys Hmem_before_IH Hinv_before_IH HrelM_before_IH Hcap_before_IH.
      destruct IH as [sr [Hred [Hinv'' [Hv1 [? [Hv2 [? [? [m1 [Hm1 [? ?]]]]]]]]]]].
      assert (sglob_val (host_function:=host_function) s (f_inst f) constr_alloc_ptr
            = sglob_val (host_function:=host_function) (upd_s_mem (host_function:=host_function) s
                       (update_list_at (s_mems s) 0 m0)) (f_inst f) constr_alloc_ptr) as Hglob_cap by reflexivity.
      have HlenBound := mem_length_upper_bound _ Hmem5. cbn in HlenBound.
      assert (cap = v_cap). { rewrite H in Hcap. inv Hcap.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in H12; try lia. rewrite Wasm_int.Int32.Z_mod_modulus_id in H12; lia. } subst v_cap.

      eexists. split.
      (* reduce *)
      dostep. elimr_nary_instr 0. apply r_get_global. rewrite Hglob_cap. eassumption.
      dostep. elimr_nary_instr 2. constructor. constructor. reflexivity.
      dostep. apply r_eliml. auto. elimr_nary_instr 0. apply r_get_local. eassumption.

      dostep. elimr_nary_instr 2. eapply r_store_success; try eassumption; auto.
      dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
      dostep. elimr_nary_instr 2. constructor. apply rs_binop_success. reflexivity.
      dostep. elimr_nary_instr 1. apply r_set_global. subst. eassumption.
      apply Hred.
      split. assumption. split. auto. split. simpl_modulus. cbn. lia. split.
      econstructor. apply Hm1. eassumption. { simpl_modulus.
        apply mem_length_upper_bound in Hmem5. cbn in Hmem5, Hoffset. cbn. lia. } cbn. lia.
      (* load val *)
      rewrite -H10; try lia.
      apply store_load in Hm0.
      assert ((N.of_nat (S (S (S (S (offset + (offset + (offset + (offset + 0))) + cap)))))) =
              (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (nat_to_i32 cap)
                          (nat_to_i32 (S (S (S (S (offset * 4))))))))) as Har. {
        remember (S (S (S (S (offset * 4))))) as o. cbn.
        assert (Z.of_nat offset < 2 * max_constr_args)%Z as HarOffset by lia. cbn in HarOffset.
        repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
      }
      rewrite deserialise_bits in Hm0. rewrite Har. eassumption.
      auto. reflexivity.

      { rewrite H1 in Hgmp. remember (4 + 4 * offset + cap) as n. inv Hgmp.
        repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id in H12; try lia).
        2: { unfold page_size in Hlen_m0; cbn in Hlen_m0. cbn in Hoffset. simpl_modulus. cbn. lia. }
        apply Nat2Z.inj in H12. subst gmp.

        eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply Hy_val; try eassumption; auto.
        subst. apply update_glob_keeps_funcs_intact in H5. cbn in H5. congruence.
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [Hgmp_M _]]]]]]]].
        have H' := Hgmp_M _ _ Hm H1 H4. apply mem_length_upper_bound in Hmem5. cbn in Hmem5. simpl_modulus. cbn. lia. (* TODO refactor: duplication usage of mem_length_upper_bound etc *)
        simpl_modulus. cbn in Hoffset. unfold max_constr_args in Hmaxargs.
        unfold page_size in Hlen_m0; cbn in Hlen_m0.
        apply mem_store_preserves_length in Hm0. cbn. lia. lia.

        intros. rewrite <- H10; try lia. symmetry.
        assert (exists v, load_i32 m a = Some v). { apply enough_space_to_load.
        unfold page_size in Hlen; cbn in Hlen. cbn in Hoffset. lia. } destruct H12.
        erewrite load_store_load; try apply Hm0; eauto.
        remember (S (S (S (S (offset * 4))))) as n. cbn in Hoffset. cbn.
        repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia.
      }

      replace ((4 + S (S (S (S (offset + (offset + (offset + (offset + 0))) + cap)))))) with
      (4 + 4 * S offset + cap) by lia. apply Hv2.
      split. subst. auto. rewrite H7. f_equal. f_equal. f_equal. cbn. lia.
      split. { subst. apply update_glob_keeps_funcs_intact in H5. cbn in H5. congruence. }
      exists m1. split. assumption. split. apply mem_store_preserves_length in Hm0. congruence.
      intros. rewrite -H10; try lia.
      { assert (exists v, load_i32 m a = Some v). {
          have Hm0' := Hm0.
          apply enough_space_to_load. unfold store in Hm0'.
          destruct ((Wasm_int.N_of_uint i32m
           (Wasm_int.Int32.iadd (nat_to_i32 cap)
              (nat_to_i32 (S (S (S (S (offset * 4))))))) + 0 +
         N.of_nat (t_length T_i32) <=? mem_length m)%N) eqn:Har. 2: inv Hm0'.
         cbn in Hoffset. apply mem_store_preserves_length in Hm0.
         unfold page_size in Hlen_m0. lia. } destruct H12.
         assert (Har: (a + 4 <=
      Wasm_int.N_of_uint i32m
        (Wasm_int.Int32.iadd (nat_to_i32 cap)
           (nat_to_i32 (S (S (S (S (offset * 4))))))))%N). {
       unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
       remember ((S (S (S (S (offset * 4)))))) as o. cbn.
       cbn in Hoffset.
       repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia.  }
        have Ht := load_store_load _ _ _ _ _ _ _ Har H12 Hm0. clear Har. rewrite Ht; auto. } }
    { (* store fn index *)
      (* invariants *)
      admit.
    }
Admitted.

Lemma store_constr_reduce : forall state s f rho ys (vs : list cps.val) t sargs,
  INV s f ->
  (* enough memory available *)
  (forall m gmp_v, nth_error (s_mems s) 0 = Some m ->
             sglob_val s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp_v)) ->
             (-1 < Z.of_nat gmp_v < Wasm_int.Int32.modulus)%Z ->
             Z.of_nat gmp_v + Z.of_N page_size < Z.of_N (mem_length m))%Z ->
  (* memory relation: ys available as local vars *)
  (forall y : var,
         In y ys ->
         exists (v6 : cps.val) (val : wasm_value),
           rho ! y = Some v6 /\
           stored_in_locals lenv nenv y val f /\
           repr_val_LambdaANF_Codegen fenv lenv nenv host_function v6 s f val) ->
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  Forall_statements_in_seq (set_nth_constr_arg fenv lenv nenv) ys sargs ->
  get_list ys rho = Some vs ->

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
      [seq AI_basic i | i <- sargs])
    (state, s', f, []) /\ INV s' f
      (* cap points to value *)
      /\ (exists cap_v wasmval, sglob_val s' (f_inst f) constr_alloc_ptr = Some (VAL_int32 cap_v)
          /\ wasm_value_to_i32 wasmval = cap_v
          /\ repr_val_LambdaANF_Codegen fenv lenv nenv  _ (Vconstr t vs) s' f wasmval).
Proof.
  intros ? ? ? ? ? ? ? ? Hinv HenoughM HmemR Hmaxargs Hsetargs Hrho.

  have I := Hinv. destruct I as [_ [_ [_ [INVgmp_w [INVcap_w [INVmuti32 _]]]]]].
  have INVgmp_r := global_var_w_implies_global_var_r _ _ _ INVmuti32 INVgmp_w.
  destruct INVgmp_r as [gmp_v Hgmp]. clear INVmuti32 INVgmp_w.
  edestruct i32_exists_nat as [x [Hx ?]]. erewrite Hx in Hgmp. subst gmp_v. rename x into gmp_v.
  (* invariants after set_global cap *)
  destruct (INVcap_w (nat_to_i32 gmp_v)) as [s' ?]. clear INVcap_w.
  (* INV after set_global cap *)
  assert (INV s' f) as Hinv'. {
    eapply update_global_preserves_INV. 3: eassumption.
    assumption. unfold result_out_of_mem, constr_alloc_ptr. lia. }

   have I := Hinv'. destruct I as [_ [_ [_ [_ [INVcap_w'' [INVmuti32'' [INVlinmem'' _ ]]]]]]].

  (* invariants mem *)
  edestruct INVlinmem'' as [Hmem1'' [m [Hmem2'' [size'' [Hmem3'' [Hmem4'' Hmem5'']]]]]].

  assert (exists mem, store m (Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v)) 0%N (bits (nat_to_value (Pos.to_nat t)))
  (t_length T_i32) = Some mem) as Htest. { apply enough_space_to_store. cbn.
  assert ((Datatypes.length (serialise_i32 (nat_to_i32 (Pos.to_nat t)))) = 4) as Hl. { unfold serialise_i32, encode_int, bytes_of_int, rev_if_be. destruct (Archi.big_endian); reflexivity. } rewrite Hl. clear Hl. cbn.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. subst size''.
  destruct Hinv' as [_ [_ [_ [_ [_ [_ [Hlinmem [INVgmp_M _]]]]]]]].
    destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst.

  assert (Hgmp_r : sglob_val (host_function:=host_function) s' (f_inst f) global_mem_ptr =
            Some (VAL_int32 (nat_to_i32 gmp_v))). { eapply global_var_write_read_other; try eassumption.
             unfold global_mem_ptr, constr_alloc_ptr. lia. }
  have Htest := INVgmp_M _ _ Hmem2 Hgmp_r. assert (m' = m) by congruence. subst m'. lia. }
  destruct Htest as [m' Hstore]. subst.

  remember (upd_s_mem s' (update_list_at s'.(s_mems) 0 m')) as s_tag.
  assert (Hinv_tag : INV s_tag f). { subst.
    assert (mem_length m = mem_length m'). { apply mem_store_preserves_length in Hstore. congruence. }
    assert (mem_max_opt m = mem_max_opt m'). { apply mem_store_preserves_max_pages in Hstore. congruence. }
    eapply update_mem_preserves_INV. apply Hinv'. eassumption. erewrite <- H1. lia.
    congruence. exists (mem_size m); split; auto. unfold mem_size. congruence.  reflexivity. }

  have I := Hinv_tag. destruct I as [_ [_ [_ [Hgmp_w _]]]].
  destruct (Hgmp_w (Wasm_int.Int32.iadd (nat_to_i32 gmp_v) (nat_to_i32 4))) as [s_before_args ?].
  edestruct i32_exists_nat as [gmp [HgmpEq HgmpBound]].
  erewrite HgmpEq in H1.
  assert (gmp = gmp_v + 4). {
    inv HgmpEq. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H3; try lia.
    unfold store in Hstore.
    destruct ((Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v) + 0 + N.of_nat (t_length T_i32)
                                 <=? mem_length m)%N) eqn:Har. 2: inv Hstore.
    apply N.leb_le in Har. cbn in Har.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in Har; try lia.
    apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
    simpl_modulus. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. } subst gmp.

 (* INV after set_global gmp *)
  assert (Hinv_before_args : INV s_before_args f). { eapply update_global_preserves_INV. 3: eassumption. assumption. unfold result_out_of_mem, global_mem_ptr. lia. }

  assert (Hmem: nth_error (s_mems s_before_args) 0 = Some m'). { subst s_tag. cbn.
    apply update_glob_keeps_memory_intact in H1. rewrite -H1. cbn.  unfold update_list_at.
   now rewrite take0. }
  assert (Hglob_cap: sglob_val (host_function:=host_function) s_before_args
          (f_inst f) constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 gmp_v))). {
    subst.
    replace (sglob_val (host_function:=host_function)
               (upd_s_mem (host_function:=host_function) s' (update_list_at (s_mems s') 0 m')) (f_inst f) constr_alloc_ptr)
    with (sglob_val (host_function:=host_function) s' (f_inst f) constr_alloc_ptr) by reflexivity.
    apply global_var_write_read_same in H0.
    eapply global_var_write_read_other in H1. eassumption. unfold constr_alloc_ptr, global_mem_ptr. lia.
    rewrite -H0. reflexivity. }
  assert (HenoughM': (N.of_nat gmp_v + page_size < mem_length m')%N). {
    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
    destruct Hlinmem as [Hmem1 [m'' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
    have Htest := HenoughM _ _ Hmem2 Hgmp H.
    assert (mem_length m' = mem_length m''). {
    apply mem_store_preserves_length in Hstore.
    apply update_global_var_preserves_memory in H1, H0. subst.
    assert (m = m'') by congruence. subst m''. congruence. } lia. }

  assert (HlenBound: (-1 < Z.of_nat (Datatypes.length ys + 0) < 2 * max_constr_args)%Z). { rewrite plus_0_r.
    cbn. unfold max_constr_args in Hmaxargs. lia. }

  assert (HrelM': forall y : var,
In y ys ->
exists (v6 : cps.val) (val : wasm_value),
  rho ! y = Some v6 /\
  stored_in_locals lenv nenv y val f /\
  repr_val_LambdaANF_Codegen fenv lenv nenv host_function v6 s_before_args f val). {
    intros y Hy. apply HmemR in Hy. destruct Hy as [val [wal [Hrho' [Hylocal Hval]]]].
    exists val, wal. repeat (split; auto).

    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply Hval.
    reflexivity.
    { subst. apply update_glob_keeps_funcs_intact in H0, H1. cbn. subst. assert (s_funcs
       (upd_s_mem (host_function:=host_function) s'
          (update_list_at (s_mems s') 0 m')) = s_funcs s') by reflexivity. congruence. }
    { erewrite update_glob_keeps_memory_intact. 2: eassumption. eassumption. }
    { apply update_glob_keeps_memory_intact in H1. subst. rewrite <- H1. cbn.
      unfold update_list_at. rewrite take0. cbn. reflexivity. }
    { eassumption. }
    { apply mem_store_preserves_length in Hstore.
      subst. apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''.
      simpl_modulus. simpl_modulus_in HenoughM'. cbn. lia. }
    { subst. eapply global_var_write_read_same. eassumption. }
    { cbn in HlenBound. rewrite Nat.add_0_r in HlenBound.
      simpl_modulus_in HenoughM'. cbn in HenoughM'.  simpl_modulus. cbn. subst. apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''. apply mem_store_preserves_length in Hstore.
       lia. }
    { lia. }
    { intros.
      assert (Hv: exists v, load_i32 m a = Some v). { apply enough_space_to_load. subst.
        simpl_modulus_in HenoughM'. apply mem_store_preserves_length in Hstore. lia. }
      destruct Hv as [? Hv].
      assert (load_i32 m' a = Some x). { eapply load_store_load ; try apply Hstore; eauto. cbn.
       rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. } congruence. }
  }

  assert (Hgmp_before_args : sglob_val (host_function:=host_function) s_before_args
          (f_inst f) global_mem_ptr =
        Some (VAL_int32 (nat_to_i32 (4 + gmp_v)))). { apply global_var_write_read_same in H1. rewrite H1. do 3! f_equal. lia. }

  have Hargs := store_constr_args_reduce _ _ _ _ state _ _ _ _ _ Hinv_before_args Hmem Hglob_cap HenoughM' Hmaxargs HlenBound Hgmp_before_args Hsetargs Hrho HrelM'.
  destruct Hargs as [s_final [Hred [Hinv_final [Hcap_v [? [Hargs_val [Hglobsame [Hfuncs [m'' [Hm' [Hmemlen Hmemsame]]]]]]]]]]].
  {
  cbn in Hargs_val. clear Hsetargs Hrho HenoughM' HlenBound.

  exists s_final. split.
  (* steps *)
  dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
  dostep. elimr_nary_instr 1. apply r_set_global. eassumption. cbn.
  dostep. elimr_nary_instr 0. apply r_get_global. eapply global_var_write_read_same. eassumption.
  (* write tag *)
  dostep. elimr_nary_instr 2. eapply r_store_success. 4: eassumption.
  reflexivity. eassumption. assumption.

  dostep. elimr_nary_instr 0. apply r_get_global. replace (sglob_val (host_function:=host_function)
  (upd_s_mem (host_function:=host_function) s'
     (update_list_at (s_mems s') 0 m'))) with (sglob_val (host_function:=host_function)
  s') by reflexivity.
  eapply global_var_write_read_other with (j:= constr_alloc_ptr). unfold global_mem_ptr, constr_alloc_ptr. lia.
  2: eassumption. eassumption. cbn.

  dostep. elimr_nary_instr 2. constructor. apply rs_binop_success. reflexivity.
  dostep. elimr_nary_instr 1. apply r_set_global. subst. rewrite HgmpEq. eassumption.
  cbn. apply Hred. split. assumption.
  (* constr value in memory *)
  eexists. eexists. split. eassumption.
  split.
  assert (wasm_value_to_i32 (Val_ptr gmp_v) = nat_to_i32 gmp_v) by reflexivity. eassumption.
  econstructor; eauto. { assert (Hm: nth_error (s_mems s) 0 = Some m). erewrite update_glob_keeps_memory_intact; eassumption. have H' := HenoughM _ _ Hm Hgmp H.
  apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''. unfold page_size in H'. cbn in H'.
  unfold max_constr_args in Hmaxargs. simpl_modulus. cbn. lia. } lia.
  apply store_load in Hstore; auto.
  rewrite deserialise_bits in  Hstore; auto.
  assert ((Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v)) = (N.of_nat gmp_v)) as Heq. {
  unfold nat_to_i32. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
  rewrite Heq in Hstore.
  rewrite -Hmemsame. eassumption. lia. }
Qed.


Inductive const_val_list : list cps.val -> store_record -> frame -> list nat -> Prop :=
  | CV_nil  : forall s f, const_val_list [] s f []
  | CV_cons : forall s f v vs n w ns,
       repr_val_LambdaANF_Codegen fenv lenv nenv _ v s f w ->
       n = wasm_value_to_immediate w ->
       const_val_list vs s f ns ->
       const_val_list (v::vs) s f (n::ns).

Lemma fun_args_reduce : forall state fr sr (ys : seq cps.var) rho vs f t args_instr,
  INV sr fr ->
  get_list ys rho = Some vs ->
  rel_mem_LambdaANF_Codegen fenv lenv nenv
           host_function (Eapp f t ys) rho sr fr ->
  repr_fun_args_Codegen fenv lenv nenv ys args_instr ->
  exists args,
    reduce_trans (state, sr, fr, map AI_basic args_instr)
                 (state, sr, fr, (map (fun a => AI_basic (BI_const (nat_to_value a))) args))
    /\ const_val_list vs sr fr args.
Proof.
  intros ? ? ? ? ? ? ? ? ? Hinv Hgetlist HrelM Hargs.
  generalize dependent f. generalize dependent rho. generalize dependent sr.
  revert vs t fr state. induction Hargs; intros.
  { inv Hgetlist. exists []. cbn. split. apply rt_refl. constructor. }
  { destruct vs.
    - cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist.
    - assert (HrelM': rel_mem_LambdaANF_Codegen fenv lenv nenv host_function
          (Eapp f t args) rho sr fr). {
            destruct HrelM as [HM1 HM2]. split. assumption.
            intros. assert (Hocc : (occurs_free (Eapp f t (a :: args)) x)). {
            inv H0. constructor. constructor. right. assumption. }
             destruct (HM2 _ Hocc) as [val [wal [Hrho' [Hlocals Hval]]]].
            exists val, wal. eauto. }
      assert (Hgetlist': get_list args rho = Some vs). {
        cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
      assert (Ha: rho ! a = Some v). { cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
    have IH := IHHargs _ _ _ state _ Hinv _ Hgetlist' _  HrelM'.
    destruct IH as [args' [Hred HconstL]].
    unfold rel_mem_LambdaANF_Codegen in HrelM.

    destruct HrelM as [_ Hvar].
    assert (Hocc: occurs_free (Eapp f t (a :: args)) a). { constructor. cbn. auto. }
    destruct (Hvar _ Hocc) as [val [wal [Hrho' [Hlocs Hval]]]].
    assert (v = val) by congruence. subst val.
    destruct Hlocs as [a'' [Ha'' HlVar]]. destruct H. rewrite Ha'' in H. inv H.

    exists (wasm_value_to_immediate wal :: args'). cbn. split.
    dostep. elimr_nary_instr 0. apply r_get_local. eassumption.
    apply app_trans_const; auto.
    econstructor; eauto. }
    { destruct vs.
    - cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist.
    - assert (HrelM': rel_mem_LambdaANF_Codegen fenv lenv nenv host_function
          (Eapp f t args) rho sr fr). {
            destruct HrelM as [HM1 HM2]. split. assumption.
            intros. assert (Hocc : (occurs_free (Eapp f t (a :: args)) x)). {
            inv H0. constructor. constructor. right. assumption. }
             destruct (HM2 _ Hocc) as [val [wal [Hrho' [Hlocals Hval]]]].
            exists val, wal. eauto. }
      assert (Hgetlist': get_list args rho = Some vs). {
        cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
      assert (Ha: rho ! a = Some v). { cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
    have IH := IHHargs _ _ _ state _ Hinv _ Hgetlist' _ HrelM'.
    destruct IH as [args' [Hred HconstL]].

    exists (a' :: args'). split. cbn. apply app_trans_const with (lconst := [AI_basic (BI_const (nat_to_value a'))]); auto.
    econstructor; auto. destruct H. destruct HrelM as [HM1 HM2].

    (* assert (Hsubval : subval_or_eq (Vfun rho fl f')). *)
    Print name_in_fundefs.
Admitted.


(* MAIN THEOREM, corresponds to 4.3.2 in Olivier's thesis *)
Theorem repr_bs_LambdaANF_Codegen_related:

  (*
  forall (rep_env : M.t ctor_rep) (cenv : ctor_env)
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
      forall (hs : host_state) (sr : store_record) (f : frame) (instructions : list basic_instruction) (*(k : cont) (max_alloc : Z) (fu : function) *),

        (* invariants *)
        INV sr f ->

        (forall loc loc', repr_var lenv nenv loc loc' -> loc' < length (f_locs f)) ->

        (* translate_body e returns stm *)
        repr_expr_LambdaANF_Codegen fenv lenv nenv e instructions ->

        (* relates a LambdaANF evaluation environment [rho] to a WASM environment [store/frame] (free variables in e) *)
        rel_mem_LambdaANF_Codegen fenv lenv nenv _ e rho sr f ->
        exists (sr' : store_record) (f' : frame),
          reduce_trans (hs, sr, f, map AI_basic instructions) (hs, sr', f', []) /\
          (* memory m/lenv becomes m'/lenv' after executing stm *)
          result_val_LambdaANF_Codegen v sr' f'. (* value v is related to memory m'/lenv' *)
Proof with eauto.
  intros rho v e n Hev.
  induction Hev; intros state sr fr instructions Hinv Hlocals Hrepr_e Hrel_m.
  - (* Econstr *)
    (*  TODO. refuse to compile otherwise *)
    assert (Hmaxargs: (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z) by admit.

    inversion Hrepr_e. subst t0 x0 vs0 e0 sgrow. rename H5 into Hx', H10 into Hexp.
    { remember (grow_memory_if_necessary page_size) as grow.
      cbn. repeat rewrite map_cat. cbn.

      (* prepare calling memory_grow_reduce *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
      destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
      have Hgrowmem := memory_grow_reduce _ state sr fr Heqgrow Hinv.
      destruct Hgrowmem as [s' [Hred [[Hinv' [Henoughmem HpreservedVals]] | HoutofM]]].
      have I := Hinv'. destruct I as [_ [_ [HresM0 [Hgmp [_ [Hmuti32 [Hlinmem' _]]]]]]].
      destruct Hlinmem' as [Hmem1' [m' [Hmem2' [size' [Hmem3' _]]]]].

      (* invariants after reducing grow *)
      have INVgmp_r' := global_var_w_implies_global_var_r _ _ _ Hmuti32 Hgmp.
      destruct INVgmp_r' as [n Hgmp'].
      edestruct i32_exists_nat as [gmp_v' [Hn ?]]. erewrite Hn in Hgmp'. clear Hn n.
      have HenoughM := Henoughmem _ _ Hmem2' Hgmp'. clear Henoughmem.

      { assert (HrelM : (forall y : var,
           In y ys ->
           exists (v6 : cps.val) (val : wasm_value),
             rho ! y = Some v6 /\
             stored_in_locals lenv nenv y val fr /\
             repr_val_LambdaANF_Codegen fenv lenv nenv host_function v6 s' fr val)). {
              destruct Hrel_m as [_ Hvar]. intros.
        assert (Hocc: occurs_free (Econstr x t ys e) y) by (constructor; auto).
        apply Hvar in Hocc. destruct Hocc as [val [wal [Hrho [Hloc Hval]]]].
        exists val, wal. repeat split; auto. }

      have Hconstr := store_constr_reduce state _ _ _ _ _ _ _ Hinv' _  HrelM Hmaxargs _ H.
      edestruct Hconstr as [s_v [Hred_v [Hinv_v [cap_v [wal [? [? Hvalue]]]]]]].
      { intros. assert (m' = m0) by congruence. subst m0.
        assert (gmp_v = gmp_v'). { rewrite Hgmp' in H3. inv H3.
          rewrite Wasm_int.Int32.Z_mod_modulus_id in H6; try lia.
          rewrite Wasm_int.Int32.Z_mod_modulus_id in H6; try lia. } subst gmp_v'. lia. }
     eassumption.
     { clear Hconstr. subst cap_v.
      have Hl := Hlocals _ _ Hx'. apply nth_error_Some in Hl.
      apply notNone_Some in Hl. destruct Hl as [? Hlx].

      remember ({|f_locs := set_nth (VAL_int32 (wasm_value_to_i32 wal)) (f_locs fr) x' (VAL_int32 (wasm_value_to_i32 wal));
      f_inst := f_inst fr|}) as f_before_IH.

      assert (Hinv_before_IH: INV s_v f_before_IH). {
        eapply update_local_preserves_INV; try eassumption.
        apply nth_error_Some. congruence. }
      (* prepare IH *)

      (* memory relation *)
      assert (Hrel_m_v : rel_mem_LambdaANF_Codegen fenv lenv nenv host_function e rho' s_v f_before_IH). { clear IHHev Hinv Hmem1 Hmem2 Hmem3 Hmem4 Hmem1' Hmem2' Hmem3'. clear Hred Hinv' Hred_v H8.
         destruct Hrel_m as [HrelmFun HrelmVar]. admit. }
       (*   assert (Hocc: occurs_free (Econstr x t ys e) x). { apply Free_Econstr1. }
         apply HrelmVar in Hocc. destruct Hocc as [v' [w' [Hrho' [Hlocals Hval]]]].
         split.
         - (* fun *) intros x1 r fds f val Hrho' Hfunsub.
            (* have Hrel_f := HrelmFun _ _ _ _ _ Hrho'. *)
         - (* var *) intros x1 Hfree.
            destruct (var_dec x x1).
            subst x1.
            (* x1 = x *)

            (* x1 <> x*)

             exists v', w'. cbn.
           } *)
      assert (Hlocals_before_IH: forall (loc : positive) (loc' : immediate),
      repr_var lenv nenv loc loc' ->  loc' < length (f_locs f_before_IH)). {
        intros ? ? Hr. subst. cbn. rewrite length_is_size. rewrite size_set_nth.
        rewrite maxn_nat_max. rewrite -length_is_size.
        assert (x' < length (f_locs fr)). { apply nth_error_Some. congruence. }
        apply Hlocals in Hr. lia. }

      have IH := IHHev state _ _ _ Hinv_before_IH Hlocals_before_IH Hexp Hrel_m_v.
      destruct IH as [s_final [f_final [Hred_IH Hval]]].

      exists s_final. exists f_final. split.
      (* steps *)
      eapply rt_trans. apply app_trans. apply Hred. cbn.

      dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
      dostep. elimr_nary_instr 2. constructor. apply rs_relop. cbn.
      dostep'. constructor. apply rs_if_false. reflexivity.
      dostep'. constructor. eapply rs_block with (vs := []); auto.
      apply reduce_trans_label. unfold to_e_list. cbn.
      repeat rewrite map_cat. cbn. repeat rewrite map_cat.
      separate_instr. cbn.
      assert (Heq: [:: AI_basic (BI_get_global global_mem_ptr),
      AI_basic (BI_set_global constr_alloc_ptr),
      AI_basic (BI_get_global constr_alloc_ptr),
      AI_basic (BI_const (nat_to_value (Pos.to_nat t))),
      AI_basic (BI_store T_i32 None 2%N 0%N),
      AI_basic (BI_get_global global_mem_ptr),
      AI_basic (BI_const (nat_to_value 4)),
      AI_basic (BI_binop T_i32 (Binop_i BOI_add)),
      AI_basic (BI_set_global global_mem_ptr)
    & [seq AI_basic i | i <- sargs] ++
      [seq AI_basic i | i <- sres] ++ [seq AI_basic i | i <- e']] =
  ([:: AI_basic (BI_get_global global_mem_ptr)] ++
  [:: AI_basic (BI_set_global constr_alloc_ptr)] ++
  [:: AI_basic (BI_get_global constr_alloc_ptr)] ++
  [:: AI_basic (BI_const (nat_to_value (Pos.to_nat t)))] ++
  [:: AI_basic (BI_store T_i32 None 2%N 0%N)] ++
  [:: AI_basic (BI_get_global global_mem_ptr)] ++
  [:: AI_basic (BI_const (nat_to_value 4))] ++
  [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add))] ++
  [:: AI_basic (BI_set_global global_mem_ptr)] ++
  [seq AI_basic i | i <- sargs]) ++
  [seq AI_basic i | i <- sres] ++ [seq AI_basic i | i <- e']). { rewrite <- app_assoc. reflexivity. }
    rewrite Heq.
    clear Heq. replace ([::]) with ([::] ++ [::]: list administrative_instruction) by reflexivity.
    eapply rt_trans. apply app_trans. apply Hred_v. clear Hred_v. subst sres. cbn.
    separate_instr.
    replace ([:: AI_basic (BI_get_global constr_alloc_ptr)] ++
    [:: AI_basic (BI_set_local x')] ++ [seq AI_basic i | i <- e']) with (([:: AI_basic (BI_get_global constr_alloc_ptr)] ++
    [:: AI_basic (BI_set_local x')]) ++ [seq AI_basic i | i <- e']) by reflexivity. eapply rt_trans. apply app_trans.
    dostep. elimr_nary_instr 0. apply r_get_global. eassumption.

    assert (f_inst f_before_IH = f_inst fr) as Hfinst. { subst. reflexivity. }
    dostep'. eapply r_set_local. eassumption.
    apply /ssrnat.leP. apply nth_error_Some. congruence. subst. reflexivity. apply rt_refl. cbn.
    apply Hred_IH. assumption. } }
    { (* grow mem failed *)
    eexists. eexists. split. eapply rt_trans. apply app_trans. apply Hred.
    dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
    dostep. elimr_nary_instr 2. constructor. apply rs_relop.
    dostep'. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
    dostep'. constructor. eapply rs_block with (vs:=[]); auto.
    dostep'. constructor. apply rs_label_const; auto. apply rt_refl.
    right. assumption. }}
  - (* Eproj ctor_tag t, let x := proj_n y in e *)
    inv Hrepr_e.
    rename s into e', v' into y', H8 into Hx', H9 into Hy'.

    (* y is constr value with correct tag, arity *)
    assert (Hy : occurs_free (Eproj x t n y e) y) by constructor.
    have Hrel_m' := Hrel_m.
    destruct Hrel_m' as [Hfun Hvar].
    apply Hvar in Hy. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
    rewrite Hrho in H. inv H.
    have Hrepr' := Hrepr. inv Hrepr'.

    inv Hlocal. destruct H.

    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hinv_bound]]]]]]]]].
    have Hextr := extract_constr_arg n vs v _ _ _ _ Hinv_bound H0 H5 H12.
    destruct Hextr as [bs [wal [Hload [Heq Hbsval]]]].

    assert (Hrm: rel_mem_LambdaANF_Codegen fenv lenv nenv host_function e (map_util.M.set x v rho) sr
     {| f_locs := set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32);
        f_inst := f_inst fr
      |}). {
      split; intros. admit. (* x not a fundef *)

      destruct (var_dec x x1).
      { (* x = x1 *)
        subst x1.
        exists v. exists wal. split.
        rewrite map_util.M.gsspec.
        apply peq_true.
        split; auto. exists x'. split. inv Hx'. intro.
        unfold translate_var in H9. unfold translate_var.
        destruct (lenv ! x); auto. inv H9. cbn.
        unfold wasm_deserialise in Heq. rewrite -Heq.
        have Hl := Hlocals _ _ Hx'. apply nth_error_Some in Hl.
        apply notNone_Some in Hl. destruct Hl.
        eapply set_nth_nth_error_same. eassumption.
        eapply val_relation_depends_on_finst; try eassumption; auto. }

      { (* x <> x1 *)
        assert (Hocc: occurs_free (Eproj x t n y e) x1). { constructor; assumption. }
        apply Hvar in Hocc. destruct Hocc as [v6 [wal' [Henv [Hloc Hval]]]].
        exists v6. exists wal'. repeat split; auto.
        rewrite map_util.M.gsspec.
        rewrite peq_false. assumption. auto.
        destruct Hloc as [x1' [? ?]].
        unfold stored_in_locals. cbn.
        assert (x1' <> x'). admit. (* different vars -> different wasm local vars *)
        exists x1'. split; auto.
        rewrite set_nth_nth_error_other; auto. eapply Hlocals. eassumption.
        eapply val_relation_depends_on_finst; try eassumption; auto. }
   }

  assert (INV sr
         {|
           f_locs :=
             set_nth (wasm_deserialise bs T_i32)
               (f_locs fr) x' (wasm_deserialise bs T_i32);
           f_inst := f_inst fr
         |}) as Hinv'. { cbn. eapply update_local_preserves_INV. 3: reflexivity. assumption.
                         apply nth_error_Some. intros. apply nth_error_Some. eapply Hlocals.
                         eassumption. }

   assert (Hlocals' :  (forall (loc : positive) (loc' : immediate),
      repr_var lenv nenv loc loc' -> loc' < length (set_nth (wasm_deserialise bs T_i32) (f_locs fr) x'
             (wasm_deserialise bs T_i32)))).
         { intros. apply Hlocals in H6, Hx'. rewrite length_is_size size_set_nth -length_is_size.
          rewrite maxn_nat_max. lia. }

    have IH := IHHev state sr (Build_frame (set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32)) (f_inst fr)) e' Hinv' Hlocals' H7 Hrm. destruct IH as [sr' [f' [Hred Hval]]].

    exists sr'. exists f'. cbn. split.
    { (* take steps *)
    have Htmp := Hy'. inv Htmp.

    have I := Hinv'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
    have Hly := Hlocals _ _ Hy'.
    have Hlx := Hlocals _ _ Hx'.
    rewrite H in H6. injection H6 => H6'. subst. clear H6.

    (* get_local y' *)
    dostep. elimr_nary_instr 0.
    apply r_get_local. apply H1.

    (* 2: admit. (* x <> y -> x' <> y' *)
    2: { have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [Hlocals _]]]]]]]].
        destruct (Hlocals _ _ H8). eapply nth_error_Some. congruence. }
    rewrite H1 in H11. injection H11 => H11'. subst. clear H11. *)

    (* add offset n *)
    dostep. elimr_nary_instr 2.
    constructor. apply rs_binop_success. cbn. reflexivity.

    inv Hrepr.

    dostep. elimr_nary_instr 1.
    eapply r_load_success.

    destruct Hlinmem as [Hmem1 [m' Hmem2]].
    eassumption. apply H5.

    assert (Har: Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (wasm_value_to_i32 (Val_ptr addr))
        (nat_to_i32 ((N.to_nat n + 1) * 4))) = (N.of_nat (4 + addr) + 4 * n)%N). {
        replace (4 + addr) with (addr + 4) by lia. replace (4*n)%N with (n*4)%N by lia. cbn.
     unfold load in Hload.
     destruct ((N.of_nat (4 + addr) + 4 * n + (0 + N.of_nat 4) <=? mem_length m)%N) eqn:Heqn. 2: inv Hload.
     apply N.leb_le in Heqn.
     destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. assert (m' = m) by congruence. subst.
     apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
     repeat (rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia). }
    rewrite Har. apply Hload.

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
    apply /ssrnat.leP. apply Hlocals in Hx'. assumption.
    reflexivity. cbn. apply Hred.
    }
    apply Hval.

  - (* Ecase *)
    { generalize dependent y. generalize dependent instructions. induction cl; intros; subst. inv H1. destruct a. rename c0 into t0.

      assert (caseConsistent cenv cl t). { inv H0. assumption. }
      cbn in H1. destruct (M.elt_eq t0 t). subst.

      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].

      (* t0 = t *)
      { inv H1. clear IHcl.
        inv Hrepr_e. rename v' into y', H7 into Hy'.

        assert (Hy : occurs_free (Ecase y ((t, e) :: cl)) y) by constructor.
        have Hrel_m' := Hrel_m.
        destruct Hrel_m' as [Hfun Hvar].
        apply Hvar in Hy. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
        rewrite Hrho in H. inv H.
        have Hrepr' := Hrepr. inv Hrepr'.
        destruct Hlocal as [i [Hl1 Hl2]]. inv Hy'. rewrite Hl1 in H. inv H.

      assert (Hrel: rel_mem_LambdaANF_Codegen fenv lenv nenv host_function e rho sr fr).
      { unfold rel_mem_LambdaANF_Codegen. split; intros... }

      have IH := IHHev state _ _ _ Hinv Hlocals H9 Hrel. destruct IH as [sr' [fr' [Hstep Hval]]].

    exists sr'. exists fr'.
    split. {
    (* steps *)
    dostep. elimr_nary_instr 0.
    apply r_get_local. eassumption.

    unfold load_i32 in H10.
    destruct (load m (N.of_nat addr) (N.of_nat 0) 4) eqn:Hload.

    dostep. elimr_nary_instr 1. eapply r_load_success. apply Hlinmem. eassumption.
    assert (N.of_nat addr = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))). { cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
    rewrite <- H. apply Hload.

    remember (VAL_int32 (tag_to_i32 t)) as tag.

    dostep. elimr_nary_instr 2. constructor. apply rs_relop. cbn.

    dostep'. constructor. apply rs_if_true.
    cbn. unfold nat_to_i32. unfold tag_to_i32.
    unfold Wasm_int.Int32.eq.
    cbn in Hload. rewrite Hload in H10. subst. injection H10 => H10'.
    destruct (zeq (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (decode_int b)))
      (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (Pos.to_nat t))))) eqn:Heq. discriminate. contradiction.

       dostep'. constructor. eapply rs_block with (vs := []); auto. unfold to_e_list. cbn.
      eapply reduce_trans_label. apply Hstep. unfold load_i32 in H10. rewrite Hload in H10. inv H10. }
       assumption. }

      (* t0 <> t *)

      inv H0.
      inv Hrepr_e.

      assert (Hrel: rel_mem_LambdaANF_Codegen fenv lenv nenv host_function (Ecase y cl) rho sr fr).
      { unfold rel_mem_LambdaANF_Codegen. split; intros.
        destruct Hrel_m. eauto. apply Hrel_m. apply Free_Ecase3. assumption.
      }

      have IH := IHcl H10 H1 _ _ H H12 Hrel.
      destruct IH as [sr' [f' [Hred Hval]]].

      (* t <> t0 *)

       assert (Hy : occurs_free (Ecase y ((t0, e0) :: cl)) y) by constructor.
    have Hrel_m' := Hrel_m.
    destruct Hrel_m' as [Hfun Hvar].
    apply Hvar in Hy. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
    rewrite Hrho in H. inv H.

    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
    have Hl := Hlocals _ _ H11. apply nth_error_Some in Hl. apply notNone_Some in Hl.
    destruct Hl as [x H].
    have Htmp := H11. inv Htmp. rename v' into y'.
    have Hrepr' := Hrepr. inv Hrepr'.
    inv Hlocal. destruct H3.
    rewrite H3 in H0. inv H0. rewrite H4 in H. inv H.

    eexists. eexists. cbn.
    split.

    (* execute instructions *)
    dostep. elimr_nary_instr 0.
    apply r_get_local. eassumption.

     assert (Harith: (N.of_nat addr) = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))). cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. cbn.
    rewrite Harith in H17.
     unfold load_i32 in H8.
    destruct (load m (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))
         (N.of_nat 0) 4) eqn:Hload.
     { dostep. elimr_nary_instr 1.
       eapply r_load_success.
       apply Hlinmem. eassumption.
       apply Hload. unfold load_i32 in H17. rewrite Hload in H17.
       assert (wasm_deserialise b T_i32 = VAL_int32 (tag_to_i32 t)). {
       inv H15. unfold wasm_deserialise. f_equal. unfold tag_to_i32. cbn.
       cbn in Hload.
       rewrite Wasm_int.Int32.Z_mod_modulus_id in Hload; try lia.
       replace (Z.to_N (Z.of_nat addr)) with (N.of_nat addr) in Hload by lia.
       apply decode_int_bounds in Hload. inv H17.
       rewrite Wasm_int.Int32.Z_mod_modulus_id in H15; auto. rewrite H15.
       rewrite Wasm_int.Int32.Z_mod_modulus_id; auto.
       admit. (* t < i32 max *) } rewrite H.

       dostep. elimr_nary_instr 2.
       constructor. apply rs_relop.
       assert ((wasm_bool
                 (app_relop (Relop_i ROI_eq) (VAL_int32 (tag_to_i32 t))
                    (nat_to_value (Pos.to_nat t0)))) = nat_to_i32 0). {
                    unfold nat_to_value, nat_to_i32, tag_to_i32.
      unfold wasm_bool. cbn. unfold Wasm_int.Int32.eq. cbn. rewrite zeq_false; auto.
      rewrite Wasm_int.Int32.Z_mod_modulus_id. 2: admit. (* t < i32 max *)
      rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. admit. (* t0 < i32 max *)
       }
      rewrite H0.
      dostep'. separate_instr. constructor. apply rs_if_false. reflexivity.

      dostep'. constructor. eapply rs_block with (vs := []); eauto. cbn.
      eapply reduce_trans_label. unfold to_e_list. apply Hred.
     } unfold load_i32 in H17. rewrite Hload in H17. inv H17. assumption. }
  - (* Eapp *)
    inv Hrepr_e. rename args' into args_instr. inv H8.
    + (* indirect call*)
      repeat rewrite map_cat. cbn. admit.
    + (* direct call *) admit.
  - (* Eletapp *)   inv Hrepr_e. (* absurd, we require CPS *)
  - (* Efun *)      inv Hrepr_e. (* absurd, fn defs only on topmost level *)
  - (* Eprim_val *) inv Hrepr_e. (* absurd, primitives not supported *)
  - (* Eprim *)     inv Hrepr_e. (* absurd, primitives not supported *)
  - (* Ehalt *)
    cbn. destruct Hrel_m. destruct (H1 x) as [v6 [wal [Henv [Hloc Hrepr]]]]. constructor.
    rewrite Henv in H. inv H. inv Hrepr_e.

    have I := Hinv. destruct I as [INVres [_ [_ [Hgmp_r [_ [Hmuti32 [Hlinmem [HgmpInMem _]]]]]]]].
    apply global_var_w_implies_global_var_r in Hgmp_r; auto. destruct Hgmp_r.
    edestruct i32_exists_nat as [x' [Hx' ?]]. erewrite Hx' in H. subst.

    destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst.
    apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
    have HinM := HgmpInMem _ _ Hmem2 H.

    unfold INV_result_var_writable, global_var_w in INVres.
    specialize INVres with (wasm_value_to_i32 wal).
    destruct INVres as [s' Hs].

    exists s'. eexists fr. cbn.

    destruct H2.
    destruct Hloc as [ilocal [H4 Hilocal]]. split. erewrite H4 in H2. injection H2 => H'. subst. clear H2.
    (* execute wasm instructions *)
    dostep. separate_instr. apply r_elimr. eapply r_get_local. eassumption.
    dostep'. apply r_set_global. eassumption.
    apply rt_refl.
    unfold result_val_LambdaANF_Codegen. left.
    exists (wasm_value_to_i32 wal). exists wal.
    repeat split. eapply global_var_write_read_same. eassumption.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply Hrepr; eauto.
    eapply update_glob_keeps_funcs_intact; try eassumption.
    erewrite <- update_glob_keeps_memory_intact; try eassumption.
    simpl_modulus. cbn. lia.
    eapply global_var_write_read_other; try eassumption.
    unfold global_mem_ptr, result_var. lia.
    simpl_modulus. cbn. lia.
Admitted.

End THEOREM.

(* Definition extract_const g := match g.(modglob_init) with (* guarantee non-divergence during instantiation *)
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

Definition interp_instantiate_wrapper (m : module)
  : error (store_record * instance * list module_export) :=
  interp_instantiate empty_store_record m nil.
 *)

Import host.
Import eqtype.
Import Lia.
Import Relations.Relation_Operators.
Import ssreflect seq.
Variable cenv:LambdaANF.cps.ctor_env.
Variable funenv:LambdaANF.cps.fun_env.
Variable nenv : LambdaANF.cps_show.name_env.
Variable finfo_env: LambdaANF_to_Clight.fun_info_env. (* map from a function name to its type info *)
 (* This should be a definition rather than a parameter, computed once and for all from cenv *)
Variable rep_env: M.t ctor_rep.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
(*Let administrative_instruction := administrative_instruction host_function.*)
Let host_state := host_state host_instance.

Let reduce_trans := @reduce_trans host_function host_instance.


From compcert Require Import Maps.

Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show.
Import Common.Common Common.compM Common.Pipeline_utils.

Import ExtLib.Structures.Monad.
Import MonadNotation.


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

Definition empty_store_record : store_record := {|
    s_funcs := nil;
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

Lemma add_funcs_effect : forall s' s'' l l1 l2 f,
    fold_left
          (fun '(s, ys) (x : module_func) =>
           (add_func host_function s
              (FC_func_native (f_inst f)
                 (nth match modfunc_type x with
                      | Mk_typeidx n => n
                      end (inst_types (f_inst f)) (Tf [] []))
                 (modfunc_locals x) (modfunc_body x)),
           (Mk_funcidx (Datatypes.length (s_funcs s)) :: ys)%SEQ)) l
          (s', l1) = (s'', l2) -> (s_globals s' = s_globals s'') /\ (s_mems s' = s_mems s'') /\
                                  (s_tables s' = s_tables s'') /\
        (s_funcs s'' = (s_funcs s') ++
        (map (fun a =>
               FC_func_native (f_inst f)
                  (nth match modfunc_type a with
                    | Mk_typeidx n => n
                    end (inst_types (f_inst f)) (Tf [] []))
                    (modfunc_locals a) (modfunc_body a)) l ))%list.
Proof.
  intros. generalize dependent l1. revert s' s'' f l2.
  induction l; intros.
  - inv H. cbn. rewrite app_nil_r. auto.
  - cbn in H. apply IHl in H.
    destruct H as [H1 [H2 [H3 H4]]]. rewrite -H1 -H2 -H3 H4.
    rewrite -app_assoc. auto.
Qed.


(* TODO: generalize table initialization *)
Lemma add_tab_effect : forall l s s' f,
  fold_left
            (fun (s : datatypes.store_record host_function) '(e_ind, e) =>
             let
             '{| table_data := tab_e; table_max_opt := maxo |} :=
              nth
                (nth match modelem_table e with
                     | Mk_tableidx i => i
                     end (inst_tab (f_inst f)) 0) (datatypes.s_tables s)
                dummy_table in
              {|
                s_funcs := datatypes.s_funcs s;
                s_tables :=
                  insert_at
                    {|
                      table_data :=
                        (firstn e_ind tab_e ++
                         map
                           (fun i : funcidx =>
                            nth_error (inst_funcs (f_inst f))
                              match i with
                              | Mk_funcidx j => j
                              end) (modelem_init e) ++
                         skipn
                           (ssrnat.addn_rec e_ind
                              (Datatypes.length
                                 (map
                                    (fun i : funcidx =>
                                     nth_error (inst_funcs (f_inst f))
                                       match i with
                                       | Mk_funcidx j => j
                                       end) (modelem_init e)))) tab_e)%list;
                      table_max_opt := maxo
                    |}
                    (nth match modelem_table e with
                         | Mk_tableidx i => i
                         end (inst_tab (f_inst f)) 0) (datatypes.s_tables s);
                s_mems := datatypes.s_mems s;
                s_globals := datatypes.s_globals s
              |}) l s = s' ->
                s_globals s = s_globals s' /\ s_mems s = s_mems s' /\ s_funcs s = s_funcs s'.
Proof.
  induction l; intros.
  - cbn in H. inv H. auto.
  - cbn in H. apply IHl in H. cbn in H. destruct H as [H1 [H2 H3]].
    rewrite -H1 -H2 -H3. cbn.
    destruct a. destruct (nth
      (nth match modelem_table m with
           | Mk_tableidx i => i
           end (inst_tab (f_inst f)) 0) (s_tables s) dummy_table). cbn. auto.
Qed.

Lemma reduce_const_false : forall state s f c,
  ~ exists y,
  (reduce_tuple (host_instance:=host_instance))
  (state, s, f, [AI_basic (BI_const c)]) y.
Proof.
  (* intros ? ? ? ? [c' Hcontra]. cbn in Hcontra.
  remember [AI_basic (BI_const c)] as instr.
  remember [AI_basic (BI_const c')] as instr'. revert Heqinstr Heqinstr'.
   induction Hcontra; intros; try (by inv Heqinstr); subst.
  { inv H. }
  { destruct vcs; inv Heqinstr. destruct vcs; inv H2. }
  { destruct vcs; inv Heqinstr. destruct vcs; inv H2. }
  { unfold is_true, lfilled in H0, H.
    destruct (lfill k lh es) eqn:Heqn. 2: inv H.
    destruct (lfill k lh es') eqn:Heqn'. 2: inv H0.
    apply eqseq_true in H0, H. subst l l0.
    destruct lh.
    { destruct k; cbn in Heqn, Heqn'. 2: inv Heqn.
      destruct (const_list l). 2: inv Heqn.
      destruct l. 2: { inv Heqn. destruct l, es, l0; inv H1. inv Heqn'.
      destruct es'; inv H1. admit. (* reduces [] *)  }
      destruct es. 2: { destruct es', es, l0; inv Heqn; inv Heqn'. destruct es'; inv H1. auto. }
      destruct l0. inv Heqn. destruct l0; inv Heqn. destruct es'; inv Heqn'. 2: destruct es'; inv H1. admit. }
    { destruct k; cbn in Heqn, Heqn'. inv Heqn.
      destruct (const_list l). 2: inv Heqn.
      destruct (lfill k lh es'). 2: inv Heqn'.
      destruct (lfill k lh es). 2: inv Heqn.
      destruct l; inv Heqn. destruct l; inv H1. } *)
Admitted.

Lemma reduce_trans_const_eq : forall state s f c c',
   opsem.reduce_trans (host_instance:=host_instance)
                    (state, s, f, [AI_basic (BI_const c)])
                    (state, s, f, [AI_basic (BI_const c')]) -> c = c'.
Proof.
  intros.
  remember (state, s, f, [AI_basic (BI_const c)]) as x.
  remember (state, s, f, [AI_basic (BI_const c')]) as x'.
  generalize dependent c. generalize dependent c'. revert f s state.
  apply clos_rt_rt1n in H. induction H; intros; subst; try inv Heqx; auto.
  apply clos_rt1n_rt in H0.
  exfalso. eapply reduce_const_false. eauto.
Qed.


Lemma reduce_forall_elem_effect : forall fns l f s state,
  Forall2 (fun (e : module_element) (c : Wasm_int.Int32.T) =>
                  opsem.reduce_trans (host_instance:=host_instance)
                    (state, s, {| f_locs := []; f_inst := f_inst f |},
                    to_e_list (modelem_offset e))
                    (state, s, {| f_locs := []; f_inst := f_inst f |},
                    [AI_basic (BI_const (VAL_int32 c))]))
                 (map
                    (fun f : wasm_function =>
                     {|
                       modelem_table := Mk_tableidx 0;
                       modelem_offset :=
                         [BI_const (nat_to_value (LambdaANF_to_WASM.fidx f))];
                       modelem_init := [Mk_funcidx (LambdaANF_to_WASM.fidx f)]
                     |}) fns) l -> l = map (fun f => nat_to_i32 (LambdaANF_to_WASM.fidx f)) fns.
Proof.
  induction fns; intros.
  - now inv H.
  - cbn in H. inv H. cbn in H2. apply reduce_trans_const_eq in H2. cbn. inv H2.
    erewrite (IHfns l'); eauto.
Qed.

Fixpoint fds_length (fds : fundefs) : nat :=
  match fds with
  | Fnil => 0
  | Fcons _ _ _ _ fds' => 1 + fds_length fds'
  end.

Lemma fds_length_length :
  forall fenv f0 fns,
  (fix iter (fds : fundefs) : error (seq.seq wasm_function) :=
               match fds with
               | Fcons x _ xs e fds' =>
                   match translate_function nenv cenv fenv x xs e with
                   | Err t => fun _ : wasm_function -> error (seq.seq wasm_function) => Err t
                   | Ret a => fun m2 : wasm_function -> error (seq.seq wasm_function) => m2 a
                   end
                     (fun fn : wasm_function =>
                      match iter fds' with
                      | Err t =>
                          fun _ : seq.seq wasm_function -> error (seq.seq wasm_function) => Err t
                      | Ret a =>
                          fun m2 : seq.seq wasm_function -> error (seq.seq wasm_function) => m2 a
                      end (fun following : seq.seq wasm_function => Ret (fn :: following)%SEQ))
               | Fnil => Ret []
               end) f0 = Ret fns -> fds_length f0 = length fns.
Proof.
  intro fenv. induction f0; intros. 2: { now inv H. }
  destruct (translate_function nenv cenv fenv v l e). inv H.
  destruct (_ f0). inv H. destruct fns; inv H. cbn. now rewrite -IHf0.
Qed.

Lemma module_instantiate_INV : forall e (fds : fundefs) module fenv main_lenv sr f exports,
  (Z.of_nat (match e with | Efun fds _ => fds_length fds | _ => 0 end) + 2 < max_num_functions)%Z ->
  LambdaANF_to_WASM nenv cenv e = Ret (module, fenv, main_lenv) ->
  (* for INV_locals_all_i32, the initial context has no local vars for simplicity *)
  (f_locs f) = [] ->
  instantiate host_function host_instance empty_store_record module [] (sr, (f_inst f), exports, None) ->
  INV _ sr f.
Proof.
  intros e fds module fenv lenv s f exports HfdsLength Hcompile Hflocs Hinst.
  unfold instantiate in Hinst.
  unfold LambdaANF_to_WASM in Hcompile.
  destruct (create_fname_mapping nenv e) eqn:Hmapping. inv Hcompile. simpl in Hcompile.
  destruct (generate_constr_pp_function cenv nenv f0 e) eqn:HgenPP. inv Hcompile.
  destruct (match e with | Efun fds _ => _ | _ => Ret [] end) eqn:HtransFns. inv Hcompile.
  destruct (translate_exp nenv cenv _ _ _) eqn:Hexpr. inv Hcompile.
  destruct (translate_function_var nenv f0 main_function_var "main function") eqn:HmainFname. inv Hcompile.
  inv Hcompile. unfold INV. cbn in Hinst. unfold is_true in *.
  destruct Hinst as [t_imps [t_exps [state [s' [ g_inits [e_offs [d_offs
      [Hmodule [Himports [HallocModule [HinstGlobals [HinstElem
         [HinstData [HboundsElem [HboundsData [_ Hinst]]]]]]]]]]]]]]]].
  rename l into fns.
  (* module typing *) clear Hmodule.
  (* globals red. to const *)
  unfold instantiate_globals in HinstGlobals. cbn in HinstGlobals.
  inv HinstGlobals. inv H3. inv H5. inv H6. inv H7.
  (* data offsets of mem init. red. to const, empty list *) inv HinstData.
  (* elem vals red. to const *)
  unfold instantiate_elem in HinstElem. cbn in HinstElem. rewrite map_app in HinstElem. cbn in HinstElem.
  apply Forall2_app_inv_l in HinstElem. destruct HinstElem as [l1' [l2' [HinstElemFns [HinstElem ?]]]].
  subst e_offs. inv HinstElem. inv H7. inv H9. cbn in Hinst. rewrite map_cat in Hinst.
  rewrite map_app in Hinst. cbn in Hinst. unfold init_tabs, init_tab in Hinst. cbn in Hinst.
  unfold store_record_eqb in Hinst. destruct (store_record_eq_dec) eqn:Heqn; cbn in Hinst. 2: inv Hinst.
  apply reduce_trans_const_eq in H1, H2, H3, H4. subst y y0 y1 y2.
  unfold alloc_module, alloc_funcs, alloc_globs, add_mem, alloc_Xs in HallocModule.
  cbn in HallocModule. repeat rewrite map_app in HallocModule. cbn in HallocModule.
  destruct (fold_left _ _) eqn:HaddTab.
  destruct (add_tab_effect _ _ _ _ HaddTab) as [HT0 [HT1 HT2]]. cbn in HT0, HT1, HT2.
   subst s_globals s_mems s_funcs.
  destruct (fold_left _ ((map _ fns) ++ _ )) eqn:HaddF.
  unfold add_glob in HallocModule. cbn in HallocModule.
  unfold store_record_eqb in HallocModule.
  destruct (store_record_eq_dec s'); cbn in HallocModule. 2: inv HallocModule.
  repeat (apply andb_prop in HallocModule;
           destruct HallocModule as [HallocModule ?F]).
  apply eqseq_true in F0,F1,F2,F3,F, HallocModule.
  apply add_funcs_effect in HaddF. cbn in HaddF. destruct HaddF as [Hs01 [Hs02 [Hs03 Hs04]]].
  rewrite <- Hs01 in e1, F0. rewrite <- Hs02 in e1, F1.
  rewrite <- Hs03 in e1, F2. rewrite Hs04 in e1, F3. cbn in F0, F1, F2, F3.
  clear Hs01 Hs02 Hs03 Hs04 s0.
  cbn in Hinst. unfold init_tabs, init_mems, init_mem in Hinst. cbn in Hinst.
  clear HboundsData HboundsElem. (* clear for now *)
  subst.

  (* INV globals *)
  unfold INV_result_var_writable, INV_result_var_out_of_mem_writable, INV_global_mem_ptr_writable,
  INV_constr_alloc_ptr_writable. unfold global_var_w, supdate_glob, supdate_glob_s. cbn.
  rewrite F0.
  split. (* res_var_w *) eexists. reflexivity.
  split. (* res_var_M_w *) eexists. reflexivity.
  split. (* res_var_M_0 *) unfold INV_result_var_out_of_mem_is_zero. unfold sglob_val, sglob.
  cbn. rewrite F0. reflexivity.
  split. (* gmp_w *) eexists. reflexivity.
  split. (* cap_w *) eexists. reflexivity.
  (* globals mut i32 *)
  split. unfold INV_globals_all_mut_i32, globals_all_mut_i32. intros. cbn. cbn in H. subst.
  { destruct g. inv H. eexists. reflexivity.
    destruct g. inv H. eexists. reflexivity.
    destruct g. inv H. eexists. reflexivity.
    destruct g. inv H. eexists. reflexivity.
    destruct g; inv H. }
  split. (* linmem *)
  { unfold INV_linear_memory. unfold smem_ind. cbn. rewrite F1.
    split; auto. eexists; auto. split. reflexivity. unfold mem_mk. cbn. unfold mem_size, mem_length, memory_list.mem_length. cbn. eexists. split. reflexivity.
    split; auto. unfold max_mem_pages. rewrite repeat_length. cbn.
    replace (N.of_nat (Pos.to_nat 65536)) with 65536%N by lia. cbn. lia. }
   split. (* gmp in linmem *)
   { unfold INV_global_mem_ptr_in_linear_memory.
   unfold sglob_val, sglob. cbn. intros. rewrite F0 in H0. inv H0. inv H. cbn.
   unfold mem_mk, mem_length, memory_list.mem_length. cbn. rewrite repeat_length.
   rewrite Wasm_int.Int32.Z_mod_modulus_id in H3; try lia. }
   split. (* all locals i32 *)
   { unfold INV_locals_all_i32. intros. rewrite Hflocs in H. rewrite nth_error_nil in H. inv H. }
   (* num functions upper bound *)
   { unfold INV_num_functions_upper_bound.
     rewrite map_length. cbn. rewrite app_length. rewrite map_length. cbn.
     destruct e; try (inv HtransFns; simpl_modulus; cbn; lia).
     erewrite <- fds_length_length; eauto.
     unfold max_num_functions in HfdsLength. simpl_modulus. cbn. lia. }
Qed.

Lemma local_var_mapping_list_aux : forall l loc loc' err_str n,
  translate_var nenv (create_local_variable_mapping' n l (M.empty _)) loc err_str = Ret loc' ->
  loc' < length l + n.
Proof.
  intros ? ? ? ? ? H.
  unfold translate_var in H.
  destruct (create_local_variable_mapping' n l (M.empty nat)) ! loc eqn:Heqn; inv H.
  generalize dependent loc. revert loc' err_str n.
  induction l; intros. inv Heqn.
  destruct (var_dec loc a).
  (* loc = a *) subst. cbn in Heqn. rewrite Maps.PTree.gss in Heqn. inv Heqn. cbn. lia.
  (* loc <> a *) cbn in Heqn. rewrite Maps.PTree.gso in Heqn; auto. cbn.
  replace (S (Datatypes.length l + n)) with (Datatypes.length l + (S n)) by lia.
  eapply IHl; eauto.
Qed.

Lemma local_var_mapping_list : forall l loc loc' err_str,
  translate_var nenv (create_local_variable_mapping l) loc err_str = Ret loc' ->
  loc' < length l.
Proof.
  intros. apply local_var_mapping_list_aux in H. lia.
Qed.

(* MAIN THEOREM, corresponds to 4.3.1 in Olivier's thesis *)
Corollary LambdaANF_Codegen_related :
  forall (rho : eval.env) (v : cps.val) (e : exp) (n : nat), (* rho is environment containing outer fundefs. e is body of LambdaANF program *)
  forall (hs : host_state) module fenv lenv mainidx errMsg,
    forall (sr : store_record) (fr : frame) exports,

  (* evaluation of LambdaANF expression *)
  bstep_e (M.empty _) cenv rho e v n ->
  (* compilation function *)
  LambdaANF_to_WASM nenv cenv e = Ret (module, fenv, lenv) ->
  translate_function_var nenv fenv main_function_var errMsg = Ret mainidx ->
  (* constructors welformed *)
  correct_cenv_of_exp cenv e ->
  (* expression must be closed *)
  (~ exists x, occurs_free e x) ->
  (* TODO: imports *)
  instantiate _ host_instance empty_store_record module [] ((sr, (f_inst fr), exports), None) ->
  (* *)
  exists (sr' : store_record),
       reduce_trans (hs, sr,  (Build_frame [] (f_inst fr)), [ AI_basic (BI_call mainidx) ])
                    (hs, sr', (Build_frame [] (f_inst fr)), [])    /\

       result_val_LambdaANF_Codegen fenv lenv nenv _ v sr' fr.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? Hstep LANF2WASM Hmainidx Hcenv Hfreevars Hinst.
  remember ({| f_locs := []; f_inst := f_inst fr |}) as f.
  assert (Hinv : INV _ sr f). { subst. eapply module_instantiate_INV; eauto. apply Fnil.
                                          admit. (* TODO: enforce fds + 2 < max_num_functions *) }
  remember (Build_frame (repeat (nat_to_value 0) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.
  assert (Hinv_before_IH: INV _ sr f_before_IH). { subst.
    destruct Hinv as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    unfold INV. repeat (split; try assumption).
    unfold INV_locals_all_i32. cbn. intros. exists (nat_to_i32 0).
    assert (i < (length (repeat (nat_to_value 0) (Datatypes.length (collect_local_variables e))))). { now apply nth_error_Some. }
    rewrite nth_error_repeat in H9. inv H9. reflexivity. rewrite repeat_length in H10. assumption. }

  unfold LambdaANF_to_WASM in LANF2WASM.
  destruct (create_fname_mapping nenv e) eqn:Hmapping. inv LANF2WASM. simpl in LANF2WASM. rename f0 into fname_mapping.
  destruct (generate_constr_pp_function cenv nenv fname_mapping e) eqn:Hppconst. inv LANF2WASM.
  destruct (match e with
       | Efun fds _ => _ fds
       | _ => Ret []
       end) eqn:Hfuns. inv LANF2WASM. rename l into fns.
       destruct (translate_exp nenv cenv _ fname_mapping
       (match e with
          | Efun _ exp => exp
          | _ => e end)) eqn:Hexpr. inv LANF2WASM. rename l into wasm_main_instr.
  destruct (translate_function_var nenv fname_mapping main_function_var "main function") eqn:Hfmain.
  inv LANF2WASM. inv LANF2WASM.
  remember (match e with
           | Efun _ exp => exp
           | _ => e end) as mainexpr.

    remember (Build_frame (repeat (nat_to_value 0) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.
   assert (Hlocals: (forall (loc : positive) (loc' : immediate),
           repr_var (create_local_variable_mapping (collect_local_variables e)) nenv loc loc' ->
           loc' < length (f_locs f_before_IH))). { intros ? ? Hl. subst. cbn. rewrite repeat_length.
           inv Hl.  eapply local_var_mapping_list. eassumption. }

  have Heqdec := inductive_eq_dec e. destruct Heqdec.
  { (* top exp is Efun _ _ *)
    destruct e0 as [fds' [e' He]]. subst e.

    have HMAIN := repr_bs_LambdaANF_Codegen_related cenv funenv fenv _ nenv finfo_env rep_env _ host_instance _ _ _ _ Hstep hs _ _ wasm_main_instr Hinv_before_IH Hlocals.

    exists sr. subst. admit. }

  { (* top exp is not Efun _ _ *)
    assert (mainexpr = e). { destruct e; auto. exfalso. eauto. } subst mainexpr.
    assert (fns = []). { destruct e; inv Hfuns; auto. exfalso. eauto. }
    rewrite H in Hexpr.

    eapply translate_exp_correct in Hexpr; auto.

    assert (Hrelm : rel_mem_LambdaANF_Codegen fenv (create_local_variable_mapping (collect_local_variables e)) nenv
            host_function e rho sr f_before_IH). {
      split.
      { intros. inv Hfuns. admit.
        (* absurd, no functions *)
      }
      { intros. exfalso. eauto. }}
    rewrite -> H in *.
    have HMAIN := repr_bs_LambdaANF_Codegen_related cenv funenv fenv _ nenv finfo_env rep_env _ host_instance rho _ _ _ Hstep hs _ _ wasm_main_instr Hinv_before_IH Hlocals Hexpr Hrelm.
    destruct HMAIN as [s' [f' [Hred Hval]]]. subst. cbn.
    exists sr. admit. }
Admitted.

(*
Goal True.
idtac "Assumptions:".
Abort.
Print Assumptions LambdaANF_Codegen_related.
 *)
