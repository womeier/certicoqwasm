(*
  Proof of correctness of the WASM code generation phase of CertiCoq
  (this file is based on the proof for Clight code generation, it still contains some relicts that have not beed removed yet.)

  > Relates expressions to Wasm instructions (codegen relation, syntactic)
  > Relates LambdaANF values to Wasm values (value relation)
  > Relates values to location in memory (memory relation, syntactic)
  > Relates LambdaANF states to Wasm states according to execution semantics
 *)
Unset Universe Checking.

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
  Variable cenv:LambdaANF.cps.ctor_env.
  Variable funenv:LambdaANF.cps.fun_env.
  Variable fenv : CodegenWASM.LambdaANF_to_WASM.fname_env.
  Variable venv : CodegenWASM.LambdaANF_to_WASM.var_env.
  Variable nenv : LambdaANF.cps_show.name_env.
  Variable finfo_env: LambdaANF_to_Clight.fun_info_env. (* map from a function name to its type info *)
  (* TODO: cleanup, program not required *)
  Variable p:program.

  (* This should be a definition rather than a parameter, computed once and for all from cenv *)
  Variable rep_env: M.t ctor_rep.



Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show CodegenWASM.wasm_map_util.
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
Inductive set_nth_constr_arg : nat -> var -> list basic_instruction -> Prop :=
  Make_nth_proj: forall (v : var) n instr,
                        repr_read_var_or_funvar v instr ->
                        set_nth_constr_arg n v [ BI_get_global constr_alloc_ptr
                                              ; BI_const (nat_to_value ((1 + n) * 4))
                                              ; BI_binop T_i32 (Binop_i BOI_add)
                                              ; instr
                                              ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0)
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
    forall x x' t vs sgrow sinit sargs sres e e',
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
                                            [] (* grow mem failed *)
                                            (sinit ++
                                             [ BI_get_global constr_alloc_ptr
                                             ; BI_const (nat_to_value (Pos.to_nat t))
                                             ; BI_store T_i32 None (N_of_nat 2) (N_of_nat 0)
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
| Rconstr_v : forall v t vs sr m addr,
    (* addr in bounds of linear memory *)
    (0 <= Z.of_nat addr < Wasm_int.Int32.modulus)%Z ->
    (* store_record contains memory *)
    List.nth_error sr.(s_mems) 0 = Some m ->
    (* constructor tag is set properly, see LambdaANF_to_WASM, constr alloc structure*)
    v = tag_to_i32 t ->
    load_i32 m (N.of_nat addr) = Some (VAL_int32 v) ->
    (* arguments are set properly *)
    repr_val_constr_args_LambdaANF_Codegen vs sr (4 + addr) ->
    repr_val_LambdaANF_Codegen (LambdaANF.cps.Vconstr t vs) sr (Val_ptr addr)
| Rfunction_v : forall env fds f sr  tag vs e e' idx inst ftype args body,
      find_def f fds = Some (tag, vs, e) ->

      (* find runtime representation of function *)
      List.nth_error sr.(s_funcs) idx = Some (FC_func_native inst ftype args body) ->
      ftype = Tf (List.map (fun _ => T_i32) vs) [] ->
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
  (forall err, translate_var nenv venv x err = Ret i) /\
  List.nth_error f.(f_locs) i = Some (VAL_int32 (wasm_value_to_i32 v)).

Definition rel_mem_LambdaANF_Codegen (e : exp) (rho : LambdaANF.eval.env)
                                     (sr : store_record) (fr : frame) :=
        (* function def is related to function index *)
        (forall x rho' fds f v,
            M.get x rho = Some v ->
             (* 1) arg is subval of constructor
                2) v listed in fds -> subval *)
            subval_or_eq (Vfun rho' fds f) v ->
            (* i is index of function f *)
            exists i, translate_function_var nenv fenv f = Ret i /\
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

Lemma set_nth_constr_arg_correct : forall l instr n,
  set_constructor_args nenv venv fenv l n = Ret instr ->
  Forall_statements_in_seq' (set_nth_constr_arg fenv venv nenv) l instr n.
Proof.
  induction l; intros.
  - inv H. econstructor; auto.
  - cbn in H. destruct (translate_local_var_read nenv venv fenv a) eqn:Hvar. inv H.
  destruct (set_constructor_args nenv venv fenv l (S n)) eqn:Harg. inv H. inv H.
  replace ((BI_get_global constr_alloc_ptr
   :: BI_const
        (nat_to_value (S (n + S (n + S (n + S (n + 0))))))
      :: BI_binop T_i32 (Binop_i BOI_add)
         :: b :: BI_store T_i32 None 2%N 0%N :: l0)) with
      (([ BI_get_global constr_alloc_ptr
        ; BI_const (nat_to_value (S (n + S (n + S (n + S (n + 0))))))
        ; BI_binop T_i32 (Binop_i BOI_add)
        ; b
        ; BI_store T_i32 None 2%N 0%N] ++ l0)) by reflexivity.
   constructor; auto.

  replace ((nat_to_value (S (n + S (n + S (n + S (n + 0))))))) with ((nat_to_value ((1 + n) * 4))). constructor.
  unfold translate_local_var_read in Hvar.
  destruct (is_function_name fenv (translate_var_to_string nenv a)) eqn:Hfn.
  destruct (lookup_function_var (translate_var_to_string nenv a) fenv
         "translate local var read: obtaining function id") eqn:Hvar'. inv Hvar. inv Hvar.
         constructor. constructor. unfold translate_function_var.
  eapply lookup_function_var_generalize_err_string in Hvar'. rewrite Hvar'; auto.

  destruct (lookup_local_var (translate_var_to_string nenv a) venv
         "translate_local_var_read: normal var") eqn:Hloc. inv Hvar. inv Hvar.
         constructor. econstructor. unfold translate_var. eassumption.
    f_equal. lia.
Qed.

Import seq.

Theorem translate_exp_correct:
    (* find_symbol_domain p map -> *)
    (* finfo_env_correct fenv map -> *)
    (* correct_crep_of_env cenv rep_env -> *)
    forall e instructions,
      correct_cenv_of_exp cenv e ->
    translate_exp nenv cenv venv fenv e = Ret instructions ->
    repr_expr_LambdaANF_Codegen fenv venv nenv e instructions.
Proof.
  intros (* Hcrep *) e.
  induction e using exp_ind'; intros instr Hcenv; intros.
  - (* Econstr *)
    simpl in H.
    { destruct (translate_exp nenv cenv venv fenv e) eqn:H_eqTranslate; inv H.
      destruct (translate_var nenv venv v "translate_exp constr") eqn:H_translate_var. inv H1.
      destruct (store_constructor nenv cenv venv fenv t l) eqn:store_constr.
      inv H1. inv H1. cbn.
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite <-(cat1s x l) end
  end.
  rename i into v'.
  replace ([:: BI_get_global global_mem_ptr] ++
   [:: BI_const (nat_to_value ((Datatypes.length l + 1) * 4))] ++
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
         []] ++
   [:: BI_get_global result_out_of_mem] ++
   [:: BI_const (nat_to_value 1)] ++
   [:: BI_relop T_i32 (Relop_i ROI_eq)] ++
   [:: BI_if (Tf [::] [::]) [::]
         (l1 ++
          ([:: BI_get_global constr_alloc_ptr] ++
           [:: BI_set_local v'] ++ l0)%SEQ)%list]) with
   (([:: BI_get_global global_mem_ptr] ++
   [:: BI_const (nat_to_value ((Datatypes.length l + 1) * 4))] ++
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
   [:: BI_const (nat_to_value ((Datatypes.length l + 1) * 4))] ++
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
      destruct (set_constructor_args nenv venv fenv l 0) eqn:Hconstrargs. inv store_constr.
         remember (grow_memory_if_necessary ((length l + 1) * 4 )) as grow.
      inversion store_constr.

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

        replace ([:: BI_get_global constr_alloc_ptr] ++ [:: BI_set_local v'] ++ l0) with
                ([BI_get_global constr_alloc_ptr; BI_set_local v'] ++ l0) by reflexivity.

        repeat rewrite <- app_assoc.
        eapply Rconstr_e; eauto.
        econstructor. eassumption. apply set_nth_constr_arg_correct. assumption.

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
    destruct (_ l) eqn:Hprep. inv H.
    destruct (translate_var nenv venv v "translate_exp case") eqn:Hvar. inv H. inv H.
    constructor. econstructor. eassumption. apply IHe0.
    eapply correct_cenv_case_drop_clause. eassumption.
    cbn. rewrite Hprep. rewrite Hvar. reflexivity.
    apply IHe; auto. eapply Forall_constructors_subterm; eauto. constructor. econstructor. cbn.
    left; eauto. }
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

Import opsem.
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

   (exists res_i32 wasmval,
      (* global var *result_var* contains correct return value *)
      sglob_val sr inst result_var = Some (VAL_int32 res_i32) /\
      wasm_value_to_i32 wasmval = res_i32 /\
      repr_val_LambdaANF_Codegen fenv venv nenv  _ val sr wasmval)
    \/ (sglob_val sr inst result_out_of_mem = Some (nat_to_value 1)).

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
  intros.
  unfold supdate_glob, supdate_glob_s in H. cbn in H.
  unfold sglob_val, sglob; cbn. destruct (inst_globs (f_inst fr)) eqn:Hgl. inv H.
  destruct l eqn:Hl. inv H.
  destruct l0 eqn:Hl0. inv H. subst. cbn in H. cbn.
  destruct (nth_error (s_globals sr) g1) eqn:Hntherr. 2: inv H. inv H. cbn.
  rewrite nth_error_update_list_hit. reflexivity.
  apply /ssrnat.leP. assert (g1 < length (s_globals sr)). { apply nth_error_Some. intro. congruence. } lia.
Qed.

Lemma val_relation_depends_only_on_mem_and_funcs : forall v sr sr' value,
    sr.(s_mems) = sr'.(s_mems) ->
    sr.(s_funcs) = sr'.(s_funcs) ->
    repr_val_LambdaANF_Codegen fenv venv nenv host_function v sr value ->
    repr_val_LambdaANF_Codegen fenv venv nenv host_function v sr' value.
Proof.
  intros. inv H1.
  (* constructor value *)
  { remember (4 + addr) as a.  generalize dependent addr.
    have indPrinciple := repr_val_constr_args_LambdaANF_Codegen_mut fenv venv nenv _
      (fun (v : cps.val) (s : datatypes.store_record host_function) (w : wasm_value)
           (H : repr_val_LambdaANF_Codegen fenv venv nenv host_function v s w) => forall s',
                s_mems s = s_mems s' -> s_funcs s = s_funcs s' ->
                   repr_val_LambdaANF_Codegen fenv venv nenv host_function v s' w)
      (fun (l : seq cps.val) (s : datatypes.store_record host_function) (i : immediate)
           (H: repr_val_constr_args_LambdaANF_Codegen fenv venv nenv host_function l s i) => forall s',
               s_mems s = s_mems s' -> s_funcs s = s_funcs s' ->
                   repr_val_constr_args_LambdaANF_Codegen fenv venv nenv host_function l s' i).
    eapply indPrinciple in H6; clear indPrinciple; intros; eauto.
    { econstructor; eauto. congruence. subst. eassumption. }
    { econstructor; eauto. congruence. }
    { econstructor; eauto. rewrite <- H2. eassumption. }
    { econstructor. }
    { econstructor; eauto. congruence. }
  }
  (* function *)
  { econstructor; eauto. rewrite -H0. eassumption. }
Qed.

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

Definition INV_local_vars_exist fr := forall x x',
  repr_var venv nenv x x' -> exists val, nth_error (f_locs fr) x' = Some (VAL_int32 val).

Definition INV_linear_memory sr fr :=
      smem_ind (host_function:=host_function) sr (f_inst fr) = Some 0
   /\ exists m, nth_error (s_mems sr) 0 = Some m
   /\ exists size, mem_size m = size
   /\ mem_max_opt m = Some max_mem_pages
   /\ (size <= max_mem_pages)%N.

Definition INV_local_ptr_in_linear_memory (sr : store_record) fr := forall y y' x m,
  (* TODO holds for function indices? *)
  repr_var venv nenv y y' ->
  nth_error (f_locs fr) y' = Some (VAL_int32 x) ->
  nth_error (s_mems sr) 0 = Some m ->
  exists bytes, load m (Wasm_int.N_of_uint i32m x) 0%N (t_length T_i32) = Some bytes.

Definition INV_global_mem_ptr_in_linear_memory s f := forall addr m,
  sglob_val (host_function:=host_function) s (f_inst f) global_mem_ptr = Some (VAL_int32 addr) ->
  exists bytes, load m (Wasm_int.N_of_uint i32m addr) 0%N (t_length T_i32) = Some bytes.

Definition INV_constr_alloc_ptr_in_linear_memory s f := forall addr t m,
  sglob_val (host_function:=host_function) s (f_inst f) constr_alloc_ptr = Some (VAL_int32 addr)
  -> exists m', store m (Wasm_int.N_of_uint i32m addr) 0%N (bits (nat_to_value (Pos.to_nat t))) (t_length T_i32) = Some m'.

Definition INV_num_functions_upper_bound sr :=
  (Z.of_nat (length (@s_funcs host_function sr)) < Wasm_int.Int32.modulus)%Z.

(* invariants that need to hold throughout the execution of the Wasm program *)
Definition INV (s : store_record) (f : frame) :=
    INV_result_var_writable s f
 /\ INV_result_var_out_of_mem_writable s f
 /\ INV_global_mem_ptr_writable s f
 /\ INV_constr_alloc_ptr_writable s f
 /\ INV_globals_all_mut_i32 s
 /\ INV_linear_memory s f
 /\ INV_local_vars_exist f
 /\ INV_local_ptr_in_linear_memory s f
 /\ INV_global_mem_ptr_in_linear_memory s f
 /\ INV_constr_alloc_ptr_in_linear_memory s f
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

Lemma update_global_preserves_local_ptr_in_linear_memory : forall j sr sr' f  num,
  INV_local_ptr_in_linear_memory sr f ->
  supdate_glob (host_function:=host_function) sr (f_inst f) j
             (VAL_int32 num) = Some sr' ->
  INV_local_ptr_in_linear_memory sr' f.
Proof.
  unfold INV_local_ptr_in_linear_memory. intros.
  assert (s_mems sr = s_mems sr') as Hmem. {
   unfold supdate_glob, supdate_glob_s in H0.
   destruct (sglob_ind (host_function:=host_function) sr (f_inst f) j). 2:inv H0. cbn in H0.
   destruct (nth_error (s_globals sr) n). 2: inv H0. inv H0. reflexivity. }
   rewrite Hmem in H. clear Hmem. eapply H; eauto.
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
  supdate_glob (host_function:=host_function) sr (f_inst f) i
             (VAL_int32 num) = Some sr' ->
  INV sr' f.
Proof with eauto.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_globals_all_mut_i32...
  split. eapply update_global_preserves_linear_memory...
  split. assumption.
  split. eapply update_global_preserves_local_ptr_in_linear_memory...
  split. eapply update_global_preserves_global_mem_ptr_in_linear_memory...
  split. eapply update_global_preserves_constr_alloc_ptr_in_linear_memory...
  eapply update_global_preserves_num_functions_upper_bound...
Qed.

Lemma update_local_preserves_local_var_exists : forall f f' x' v,
  INV_local_vars_exist f ->
  x' < length (f_locs f) ->
  f' = {| f_locs := set_nth (VAL_int32 v) (f_locs f) x' (VAL_int32 v)
        ; f_inst := f_inst f
        |} ->
  INV_local_vars_exist f'.
Proof.
  unfold INV_local_vars_exist. intros. rename x' into y'. rename x'0 into x'. subst.
  cbn. destruct (H _ _ H2).
  destruct (dec_eq_nat x' y').
  (* x' = y' *)
  subst. eexists. eapply set_nth_nth_error_same; eauto.
  (* x' <> y' *)
  rewrite set_nth_nth_error_other; eauto.
Qed.

Lemma update_local_preserves_local_ptr_in_memory : forall sr f f' x' v,
  INV_local_ptr_in_linear_memory sr f ->
  x' < length (f_locs f) ->
  f' = {| f_locs := set_nth (VAL_int32 v) (f_locs f) x' (VAL_int32 v)
        ; f_inst := f_inst f
        |} ->
  INV_local_ptr_in_linear_memory sr f'.
Proof.
  unfold INV_local_ptr_in_linear_memory. intros. subst. cbn in H3.
  destruct (dec_eq_nat x' y').
  (* x' = y' *)
  subst. eexists.
  (* x' <> y' *)
Admitted.

Corollary update_local_preserves_INV : forall sr f f' x' v,
  INV sr f ->
  x' < length (f_locs f) ->
  f' = {| f_locs := set_nth (VAL_int32 v) (f_locs f) x' (VAL_int32 v)
        ; f_inst := f_inst f
        |} ->
  INV sr f'.
Proof with eauto.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]. subst. cbn.
  repeat (split; auto).
  eapply update_local_preserves_local_var_exists...
  eapply update_local_preserves_local_ptr_in_memory...
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

Lemma update_mem_preserves_local_ptr_in_linear_memory : forall s s' f m m',
   INV_local_ptr_in_linear_memory s f ->
   nth_error (s_mems s) 0  = Some m ->
   (mem_length m' >= mem_length m)%N ->
   upd_s_mem (host_function:=host_function) s
                (update_list_at (s_mems s) 0 m') = s' ->
   INV_local_ptr_in_linear_memory s' f.
Proof.
  unfold INV_local_ptr_in_linear_memory. intros. subst.
  cbn in H5. unfold update_list_at in H5. rewrite take0 in H5. inv H5.
  have H' := H _ _ _ _ H3 H4 H0. destruct H' as [bs Hload]. eauto.
  unfold load in Hload. cbn in Hload. unfold load. cbn.
  destruct ((Z.to_N (Wasm_int.Int32.unsigned x) + 4 <=?
           mem_length m)%N) eqn:Harith. 2: inv Hload. apply N.leb_le in Harith.
  assert ((Z.to_N (Wasm_int.Int32.unsigned x) + 4 <=? mem_length m0)%N) as Harith'. { apply N.leb_le. lia. } rewrite Harith'. clear Harith'. unfold read_bytes, those. rewrite N.add_0_r. cbn.
  unfold mem_lookup. cbn. rewrite N.add_0_r. unfold mem_length, memory_list.mem_length in Harith, H1.
  assert (Hb1: exists b1, nth_error (ml_data (mem_data m0))
        (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned x))) = Some b1). {
   apply notNone_Some. intro. apply nth_error_None in H2; auto. lia. }
  destruct Hb1 as [b1 Hb1]. rewrite Hb1. clear Hb1.
  assert (Hb2: exists b2, nth_error (ml_data (mem_data m0))
        (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned x) + 1)) = Some b2). {
   apply notNone_Some. intro. apply nth_error_None in H2; auto. lia. }
  destruct Hb2 as [b2 Hb2]. rewrite Hb2. clear Hb2.
 assert (Hb3: exists b3, nth_error (ml_data (mem_data m0))
        (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned x) + 2)) = Some b3). {
   apply notNone_Some. intro. apply nth_error_None in H2; auto. lia. }
  destruct Hb3 as [b3 Hb3]. rewrite Hb3. clear Hb3.
  assert (Hb4: exists b4, nth_error (ml_data (mem_data m0))
        (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned x) + 3)) = Some b4). {
   apply notNone_Some. intro. apply nth_error_None in H2; auto. lia. }
  destruct Hb4 as [b4 Hb4]. rewrite Hb4. clear Hb4. eauto.
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
  unfold INV_global_mem_ptr_in_linear_memory. intros ? ? ? ? ? H Hinv Hinv' ? ? ? ? ? ?.
  eapply update_mem_preserves_global_var_w in Hinv; eauto.
  apply global_var_w_implies_global_var_r in Hinv.
  unfold global_var_r in Hinv. destruct Hinv as [v Hv]. rewrite H3 in Hv. inv Hv.
  eapply H in H3; eauto. now eapply update_mem_preserves_all_mut_i32.
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
Proof with eauto.
 intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]].
 split. eapply update_mem_preserves_global_var_w...
 split. eapply update_mem_preserves_global_var_w...
 split. eapply update_mem_preserves_global_var_w...
 split. eapply update_mem_preserves_global_var_w...
 split. eapply update_mem_preserves_all_mut_i32...
 split. eapply update_mem_preserves_linear_memory...
 split. assumption.
 split. eapply update_mem_preserves_local_ptr_in_linear_memory...
 split. eapply update_mem_preserves_global_mem_ptr_in_linear_memory...
 split. eapply update_mem_preserves_global_constr_alloc_ptr_in_linear_memory...
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

Lemma decode_int_bounds : forall b m addr,
  load m (N.of_nat addr) (N.of_nat 0) 4 = Some b ->
  (-1 < decode_int b < Wasm_int.Int32.modulus)%Z.
Proof.
  intros.
  (* length b = 4 bytes *)
  unfold load, those in H.
  destruct (N.of_nat addr + (N.of_nat 0 + N.of_nat 4) <=? mem_length m)%N. 2: inv H.
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

Lemma value_bounds : forall wal v sr,
  INV_num_functions_upper_bound sr ->
  repr_val_LambdaANF_Codegen fenv venv nenv host_function v sr wal ->
 (-1 < Z.of_nat (wasm_value_to_immediate wal) < Wasm_int.Int32.modulus)%Z.
Proof.
  intros ? ? ? Hinv H.
  inv H.
  - (* constr. value *) cbn. lia.
  - (* function value *) cbn.
    assert (idx < length (s_funcs sr)). { apply nth_error_Some. congruence. }
    unfold INV_num_functions_upper_bound in Hinv. lia.
Qed.

Lemma extract_constr_arg : forall n vs v sr addr m,
  INV_num_functions_upper_bound sr ->
  nthN vs n = Some v ->
  nth_error (s_mems sr) 0 = Some m ->
  (* addr points to the first arg after the constructor tag *)
  repr_val_constr_args_LambdaANF_Codegen fenv venv nenv host_function vs sr addr ->
  exists bs wal, load m (N.of_nat addr + 4 * n) 0%N 4 = Some bs /\
             VAL_int32 (wasm_value_to_i32 wal) = wasm_deserialise bs T_i32 /\
             repr_val_LambdaANF_Codegen fenv venv nenv host_function v sr wal.
Proof.
  intros n vs v sr addr m Hinv H H1 H2. generalize dependent v. generalize dependent n. generalize dependent m.
  induction H2; intros. 1: inv H.
  assert (n = N.of_nat (N.to_nat n)) by lia. rewrite H5 in H4. generalize dependent v0.
  induction (N.to_nat n); intros.
  - (* n = 0 *)
    inv H4. rewrite H in H3. inv H3. rename m0 into m. rewrite N.add_comm.
    unfold load_i32 in H0. destruct (load m (N.of_nat addr) (N.of_nat 0) 4) eqn:Hl; try inv H0.
     exists b. exists wal. repeat split. rewrite <- Hl. reflexivity. unfold wasm_value_to_i32.
    have H'' := value_bounds wal.
    unfold wasm_deserialise. f_equal. f_equal.
    have H' := decode_int_bounds _ _ _ Hl.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H4; try lia.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in H4; auto.
    eapply value_bounds; eauto. assumption.
  - (* n = S n0 *)
    rewrite Nnat.Nat2N.inj_succ in H4. cbn in H4.
    destruct (N.succ (N.of_nat n0)) eqn:Heqn. inv H4. lia. rewrite <- Heqn in H4. cbn in H4.
    assert ((N.succ (N.of_nat n0) - 1) = N.of_nat n0)%N by lia. rewrite H6 in H4.
    edestruct IHrepr_val_constr_args_LambdaANF_Codegen. assumption. eassumption. eassumption.
    destruct H7 as [wal' [Hl [Heq Hval]]]. exists x. exists wal'.
    split. rewrite -Hl. f_equal. lia. split; eauto.
Qed.

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
  clear p.
  destruct n => //=.
  replace (ssrnat.nat_of_pos p) with (Pos.to_nat p); first by rewrite positive_nat_N.
  induction p => //=.
  - rewrite Pos2Nat.inj_xI.
    f_equal.
    rewrite IHp0.
    rewrite ssrnat.NatTrec.doubleE.
    rewrite - ssrnat.mul2n.
    by lias.
  - rewrite Pos2Nat.inj_xO.
    rewrite IHp0.
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
  length m.(mem_data).(ml_data) = length m'.(mem_data).(ml_data).
Proof.
  intros.
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
    + destruct m' ; inversion H ; by subst.
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

Lemma mem_grow_increases_length : forall m m' n sgrow,
  mem_length m = n ->
  mem_grow m sgrow = Some m' ->
  mem_length m' = ((sgrow * 65536) + n)%N.
Proof.
  intros. unfold mem_grow in H0.
  destruct ((mem_size m + sgrow <=? page_limit)%N) eqn:Hari. 2: inv H0.
  destruct (mem_max_opt m) eqn:Hmaxpages; cbn in H0.
  (* mem_max_opt = Some n0 *)
  destruct (mem_size m + sgrow <=? n0)%N. 2: inv H0. inv H0.
  unfold mem_length. unfold memory_list.mem_length.
  rewrite app_length. rewrite Nat2N.inj_add.
  rewrite N.add_comm. rewrite repeat_length. lia. inv H0.
  unfold mem_length, memory_list.mem_length. cbn. rewrite app_length.
  rewrite repeat_length. lia.
Qed.

Lemma mem_grow_increases_size : forall m m' n sgrow,
  mem_size m = n ->
  mem_grow m sgrow = Some m' ->
  mem_size m' = (sgrow + n)%N.
Proof.
  intros. unfold mem_grow in H0.
  destruct ((mem_size m + sgrow <=? page_limit)%N) eqn:Hari. 2: inv H0.
  destruct (mem_max_opt m) eqn:Hmaxpages; cbn in H0.
  (* mem_max_opt = Some n0 *)
  destruct (mem_size m + sgrow <=? n0)%N. 2: inv H0. inv H0.
  unfold mem_size. unfold mem_length. unfold memory_list.mem_length.
  rewrite app_length. rewrite Nat2N.inj_add.
  rewrite N.add_comm. unfold page_size. rewrite <- N.div_add_l. 2: intro; lia.
  remember (N.of_nat (Datatypes.length (memory_list.ml_data (mem_data m)))) as len.
  rewrite repeat_length. rewrite N2Nat.id.
  replace (sgrow * (64 * 1024))%N with (sgrow * 65536)%N; reflexivity.
  (* mem_max_opt = None *)
  inv H0. unfold mem_size. unfold mem_length. unfold memory_list.mem_length.
  rewrite app_length. rewrite Nat2N.inj_add.
  rewrite N.add_comm. unfold page_size. rewrite <- N.div_add_l. 2: intro; lia.
  remember (N.of_nat (Datatypes.length (memory_list.ml_data (mem_data m)))) as len.
  rewrite repeat_length. rewrite N2Nat.id.
  replace (sgrow * (64 * 1024))%N with (sgrow * 65536)%N; reflexivity.
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

Lemma global_var_write_read : forall sr sr' i val fr,
  supdate_glob (host_function:=host_function) sr  (f_inst fr) i (VAL_int32 val) = Some sr' ->
     sglob_val (host_function:=host_function) sr' (f_inst fr) i = Some (VAL_int32 val).
Proof.
  unfold supdate_glob, supdate_glob_s, sglob_val, sglob, sglob_ind. cbn. intros.
  destruct (nth_error (inst_globs (f_inst fr)) i) eqn:H1. 2: inv H. cbn in H.
  destruct (nth_error (s_globals sr) g) eqn:H2. 2: inv H. inv H. cbn.
  rewrite nth_error_update_list_hit; auto.
  apply /ssrnat.leP. apply lt_le_S. apply nth_error_Some. congruence.
Qed.


Definition max_constr_alloc_size := (max_constr_args * 4 + 4)%Z. (* in bytes *)

Lemma memory_grow_reduce : forall  (ys : list cps.var)  grow state s f,
  grow = grow_memory_if_necessary ((Datatypes.length ys + 1) * 4) ->
  INV s f ->
  exists s' f', reduce_trans
   (state, s, f, [seq AI_basic i | i <- grow])
   (state, s', f', [])
  /\ INV s' f'
  (* enough memory to alloc. constructor *)
  /\ (forall m v_gmp, nth_error (s_mems s') 0 = Some m ->
      sglob_val (host_function:=host_function) s' (f_inst f') global_mem_ptr = Some (VAL_int32 (nat_to_i32 v_gmp)) ->
      (Z.of_nat v_gmp + max_constr_alloc_size < Z.of_N (mem_length m))%Z
  \/ (sglob_val (host_function:=host_function) s' (f_inst f') result_out_of_mem = Some (VAL_int32 (nat_to_i32 1)))).
Proof with eauto.
  (* grow memory if necessary *)
  intros ys grow state sr fr H Hinv. subst.
  unfold grow_memory_if_necessary. cbn.
  have I := Hinv. destruct I as [_ [INVresM_w [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [? [? [INVglobalptrInMem [INVcapInMem _]]]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].

  assert (global_var_r global_mem_ptr sr fr) as H2. { apply global_var_w_implies_global_var_r; auto. } destruct H2. cbn.
  destruct ((~~ Wasm_int.Int32.lt
                     (Wasm_int.Int32.repr
                        (  Wasm_int.Int32.signed
                           (Wasm_int.Int32.iadd x
                              (nat_to_i32 ((Datatypes.length ys + 1) * 4))) ÷ 65536))
                     (Wasm_int.Int32.repr (Z.of_nat (ssrnat.nat_of_bin (mem_size m)))))) eqn:HneedMoreMem.
  (* grow memory *)
  {
  destruct (N.leb_spec (size + 1) max_mem_pages); unfold max_mem_pages in *.
  (* grow memory success *)
  assert (mem_size m + 1 <= page_limit)%N. { unfold page_limit. lia. }
  assert (Hsize: (mem_size m + 1 <=? max_mem_pages)%N). { subst. apply N.leb_le. now unfold max_mem_pages. }

  have Hgrow := memory_grow_success _ _ _ INVlinmem Hm2 Hsize.
  destruct Hgrow.
  { eexists. eexists. split.
    edestruct INVgmp_w as [sr' Hgmp].
    unfold INV_global_mem_ptr_in_linear_memory in INVglobalptrInMem.
    (* load global_mem_ptr *)
    dostep. separate_instr. elimr_nary_instr 0. apply r_get_global. eassumption.
    (* add required bytes *)
    dostep. separate_instr. elimr_nary_instr 2. constructor.
    apply rs_binop_success. reflexivity.
    dostep. separate_instr. elimr_nary_instr 2. constructor.
    apply rs_binop_success. cbn. unfold is_left.
    rewrite zeq_false. reflexivity.
    intro. zify.  (* unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in H5. *) admit. (* addition correct *)
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
      rewrite Z_nat_bin in H6.
      rewrite Wasm_int.Int32.Z_mod_modulus_id in H6. lia.
       unfold Wasm_int.Int32.modulus, Wasm_int.Int32.wordsize, Wordsize_32.wordsize, two_power_nat. cbn. lia. }
    dostep'. separate_instr. constructor. apply rs_block with (vs:= [])(n:=0); eauto.
    apply reduce_trans_label. cbn. apply rt_refl.
    split.
    { (* invariant *) eapply update_mem_preserves_INV. 6: reflexivity. assumption. eassumption.
      erewrite mem_grow_increases_length; eauto. lia.
    eapply mem_grow_preserves_max_pages... exists (mem_size m + 1)%N. split.
    eapply mem_grow_increases_size in H4; auto. rewrite N.add_comm. apply H4. now apply N.leb_le. }
    { (* enough memory available *)
      rename x0 into m''. intros. subst. destruct (update_list_at (s_mems sr) 0 m'') eqn:Hm'. inv Hm'. inv H5. inv H5. assert (m0 = m''). { unfold update_list_at in Hm'.  rewrite take0 in Hm'. now inv Hm'. } subst m0. rename m'' into m'.
       assert (mem_size m' = (1 + mem_size m)%N) as Hsize'. { eapply mem_grow_increases_size; eauto. } assert (sglob_val (host_function:=host_function) sr (f_inst fr) global_mem_ptr =
                 sglob_val (host_function:=host_function)(upd_s_mem (host_function:=host_function)
                 sr (m' :: l)) (f_inst fr) global_mem_ptr) as H_preserves_global by auto.
        rewrite H_preserves_global in H1. rewrite H1 in H6. inv H6.
        unfold Wasm_int.Int32.lt in HneedMoreMem.
        destruct (zlt _ _) as [|Hc]. inv HneedMoreMem. clear HneedMoreMem. cbn in Hc.
        unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in Hc. cbn in Hc.
        rewrite Wasm_int.Int32.Z_mod_modulus_id in Hc. 2: admit. (* v_gmp < i32.max *)
        rewrite Wasm_int.Int32.Z_mod_modulus_id in Hc. 2: admit. (* length ys * 4 + 4 < i32.max *)
        cbn in Hc. left.
        assert (Z.of_nat v_gmp < Z.of_N (mem_length m))%Z as Hlength. admit. (* from invariant *)
        unfold mem_size in Hsize'. (* Search (?a + ?b / ?c). *)
(*
        erewrite Wasm_int.Int32.signed_repr_signed in Hc.
        have H'' := Wasm_int.Int32.signed _.
        erewrite Wasm_int.Int32.repr_inv in Hc. admit.

        unfold Wasm_int.Int32.signed. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. cbn.
        rewrite zlt_true. rewrite Z_nat_bin. subst. unfold Wasm_int.Int32.modulus, two_power_nat. cbn. lia.
        rewrite Z_nat_bin. lia.
        rewrite Z_nat_bin. unfold Wasm_int.Int32.modulus, two_power_nat. cbn. lia. *)
        admit.
     } }
     (* growing memory fails *)
    edestruct INVresM_w as [sr'' HresM].

    eexists. eexists. split.
    unfold INV_global_mem_ptr_in_linear_memory in INVglobalptrInMem.
    (* load global_mem_ptr *)
    dostep. separate_instr. elimr_nary_instr 0. apply r_get_global. eassumption.
    (* add required bytes *)
    dostep. elimr_nary_instr 2. constructor.
    apply rs_binop_success. reflexivity.
    dostep. elimr_nary_instr 2. constructor.
    apply rs_binop_success. cbn. unfold is_left.
    rewrite zeq_false. reflexivity.
    intro. zify.  (* unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in H5. *) admit. (* addition correct *)
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
    (* INV *)
    split. eapply update_global_preserves_INV; try eassumption.
    (* correct resulting environment *)
    intros. right. eapply global_var_write_read. eassumption.
    }
    (* enough space already *)
    {
    eexists. eexists. split.
    edestruct INVgmp_w as [sr' Hgmp].
    unfold INV_global_mem_ptr_in_linear_memory in INVglobalptrInMem.
    (* load global_mem_ptr *)
    dostep. separate_instr. elimr_nary_instr 0. apply r_get_global. eassumption.
    (* add required bytes *)
    dostep. separate_instr. elimr_nary_instr 2. constructor.
    apply rs_binop_success. reflexivity.
    dostep. separate_instr. elimr_nary_instr 2. constructor.
    apply rs_binop_success. cbn. unfold is_left.
    rewrite zeq_false. reflexivity.
    intro. zify. admit. (* addition correct *)
    dostep. apply r_eliml; auto.
    elimr_nary_instr 0. eapply r_current_memory...

    dostep. separate_instr. elimr_nary_instr 2.
    constructor. apply rs_relop.

    dostep'. separate_instr.
    constructor. subst.
    rewrite HneedMoreMem. apply rs_if_false. reflexivity.

    dostep'. constructor. apply rs_block with (vs:=[])(n:= 0); auto. cbn.
    apply reduce_trans_label. apply rt_refl. split. assumption.

    (* enough space *)
    { intros. left. unfold max_mem_pages in *.
      rewrite H1 in H3. inv H3.
      unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in HneedMoreMem. cbn in HneedMoreMem.
      cbn in Hm2. rewrite H2 in Hm2. inv Hm2.
      unfold Wasm_int.Int32.lt in HneedMoreMem.
      destruct (zlt _ _) as [Ha|Ha]. 2: inv HneedMoreMem. clear HneedMoreMem.
      rewrite Z_nat_bin in Ha.
      rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: admit.
      rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: admit.
      rewrite -Nat2Z.inj_add in Ha.
      Check (Wasm_int.Int32.repr
           (Wasm_int.Int32.signed
              (Wasm_int.Int32.repr (Z.of_nat (v_gmp + (Datatypes.length ys + 1) * 4))) ÷ 65536))%Z.
     (*  Search "÷".
      unfold Wasm_int.Int32.repr in Ha. cbn in Ha. (Wasm_int.Int32.repr (Z.of_N (mem_size m)))) as z. unfold Wasm_int.Int32.signed in Heqz. cbn in Heqz. rewrite zlt_true in Heqz. rewrite Wasm_int.Int32.Z_mod_modulus_id in Heqz. subst. *)
     admit. (*  unfold Wasm_int.Int32.modulus, two_power_nat. cbn. lia.
      rewrite Wasm_int.Int32.Z_mod_modulus_id. lia.
      unfold Wasm_int.Int32.modulus, two_power_nat. cbn. lia. *)
     }
  }
  Unshelve. all: auto.
Admitted.


(* TODO: automate with zify *)
Lemma load_store : forall m addr v b1 b2 b3 b4,
load_i32 m (Wasm_int.N_of_uint i32m addr) = Some v ->
exists m', store m (Wasm_int.N_of_uint i32m addr) 0%N [b1;b2;b3;b4] 4 = Some m'.
Proof.
  intros. unfold load_i32 in H.
  destruct (load m (Wasm_int.N_of_uint i32m addr) (N.of_nat 0) 4) eqn:Heqn; inv H.
  unfold load in Heqn.
  destruct ((Wasm_int.N_of_uint i32m addr + (N.of_nat 0 + N.of_nat 4) <=? mem_length m)%N) eqn:Harith. 2: inv Heqn.
  unfold read_bytes, those in Heqn. cbn in Heqn.
  repeat rewrite N.add_0_r in Heqn. clear Heqn.
  unfold store, write_bytes. rewrite N.add_0_r. cbn in Harith. rewrite Harith.
  unfold fold_lefti. cbn. apply N.leb_le in Harith.
  unfold mem_update. unfold mem_length, memory_list.mem_length in Harith.
  rewrite take_drop_is_set_nth; try lia. rewrite N.add_0_r.
  assert ((Z.to_N (Wasm_int.Int32.unsigned addr) <?
             N.of_nat (Datatypes.length (ml_data (mem_data m))))%N) as Ha. apply N.ltb_lt. lia.
  rewrite Ha. clear Ha. cbn.
  rewrite length_is_size. rewrite size_set_nth.
  assert ((Z.to_N (Wasm_int.Int32.unsigned addr) + 1 <?
           N.of_nat
             (ssrnat.maxn (S (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr))))
                (size (ml_data (mem_data m)))))%N) as Ha. {
  rewrite maxn_nat_max. rewrite Nat2N.inj_max. apply N.ltb_lt.
  apply N.max_lt_iff. right. rewrite -length_is_size. lia. } rewrite Ha. clear Ha.
  cbn. rewrite take_drop_is_set_nth. 2: { remember (Z.to_N (Wasm_int.Int32.unsigned addr)) as a. rewrite length_is_size size_set_nth. rewrite -length_is_size. rewrite maxn_nat_max. lia. }
  assert ((Z.to_N (Wasm_int.Int32.unsigned addr) + 2 <?
         N.of_nat
           (Datatypes.length
              (set_nth b2
                 (set_nth b1 (ml_data (mem_data m))
                    (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr))) b1)
                 (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr) + 1)) b2)))%N) as Ha.
  { rewrite length_is_size size_set_nth maxn_nat_max Nat2N.inj_max.
    rewrite size_set_nth maxn_nat_max Nat2N.inj_max. apply N.ltb_lt. apply N.max_lt_iff. right.
    apply N.max_lt_iff. right. rewrite -length_is_size. lia. } rewrite Ha. clear Ha. cbn.
  rewrite take_drop_is_set_nth. 2: { rewrite length_is_size size_set_nth maxn_nat_max.
  rewrite size_set_nth maxn_nat_max. rewrite -length_is_size. lia. }
  intros. rewrite length_is_size.
  assert ((Z.to_N (Wasm_int.Int32.unsigned addr) + 3 <?
       N.of_nat
         (size
            (set_nth b3
               (set_nth b2
                  (set_nth b1 (ml_data (mem_data m))
                     (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr))) b1)
                  (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr) + 1)) b2)
               (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr) + 2)) b3)))%N) as Ha.
   { repeat rewrite size_set_nth maxn_nat_max. apply N.ltb_lt.
     repeat (rewrite Nat2N.inj_max; rewrite N.max_lt_iff; right). rewrite -length_is_size. lia. } rewrite Ha. eauto.
Qed.

Lemma load_store_load : forall m m' a1 a2 v,
length v = 4 ->
((Wasm_int.N_of_uint i32m a1) + 4 <= (Wasm_int.N_of_uint i32m a2))%N ->
load_i32 m (Wasm_int.N_of_uint i32m a1) = Some (wasm_deserialise v T_i32) ->
store m (Wasm_int.N_of_uint i32m a2) 0%N v 4 = Some m' ->
load_i32 m' (Wasm_int.N_of_uint i32m a1) = Some (wasm_deserialise v T_i32).
Proof.
  intros.
  replace (Wasm_int.N_of_uint i32m a1) with (N.of_nat (N.to_nat (Wasm_int.N_of_uint i32m a1))) in H0 by lia.
  replace (Wasm_int.N_of_uint i32m a2) with (N.of_nat (N.to_nat (Wasm_int.N_of_uint i32m a2))) in H0 by lia.
  remember (N.to_nat (Wasm_int.N_of_uint i32m a2)) as a2'. generalize dependent a2. generalize dependent a1.
  generalize dependent v. revert m m'.
  induction a2'; intros; try lia.
(*
  eapply IHa2'. 4 : {
  assert (Ha: a2' = N.to_nat (Wasm_int.N_of_uint i32m (Wasm_int.Int32.isub a2 Wasm_int.Int32.one))). { admit. } eassumption. } all: eauto. admit.
  destruct v. inv H. destruct v. inv H. destruct v. inv H. destruct v. inv H. destruct v. 2: inv H. clear H. cbn in H1.
  unfold store in H2. *)
Admitted.

Lemma store_load : forall m m' addr v,
length v = 4 ->
store m (Wasm_int.N_of_uint i32m addr) 0%N v 4 = Some m' ->
load_i32 m' (Wasm_int.N_of_uint i32m addr) = Some (wasm_deserialise v T_i32).
Proof.
  intros. assert (mem_length m = mem_length m'). { rewrite <- H in H0. apply mem_store_preserves_length in H0. unfold mem_length, memory_list.mem_length. f_equal. assumption. }
   unfold store in H. unfold store in H0.
  destruct ((Wasm_int.N_of_uint i32m addr + 0 + N.of_nat 4 <=? mem_length m)%N) eqn:Heq. 2: inv H0.
  unfold load_i32. unfold load. cbn. cbn in Heq. unfold store in H0.
  assert (Hbytes: exists b1 b2 b3 b4, v = [b1; b2; b3; b4]). {
    destruct v. inv H. destruct v. inv H.
    destruct v. inv H. destruct v. inv H. destruct v.
    exists b, b0, b1, b2. reflexivity. inv H. }
  destruct Hbytes as [b1 [b2 [b3 [b4 Hb]]]]. subst v. clear H. rewrite N.add_0_r. rewrite N.add_0_r in Heq, H0.
  unfold write_bytes in H0. cbn in H0. rewrite N.add_0_r in H0.
  destruct (mem_update (Z.to_N (Wasm_int.Int32.unsigned addr))%N b1
               (mem_data m)) eqn:Hupd1. 2: inv H0.
  destruct (mem_update (Z.to_N (Wasm_int.Int32.unsigned addr) + 1)%N b2 m0) eqn:Hupd2. 2: inv H0.
  destruct (mem_update (Z.to_N (Wasm_int.Int32.unsigned addr) + 2)%N b3 m1) eqn:Hupd3. 2: inv H0.
  destruct (mem_update (Z.to_N (Wasm_int.Int32.unsigned addr) + 3)%N b4 m2) eqn:Hupd4. 2: inv H0.
  inv H0. cbn. unfold mem_length, memory_list.mem_length. cbn.
  have Hu1 := mem_update_length _ _ _ _ Hupd1.
  have Hu2 := mem_update_length _ _ _ _ Hupd2.
  have Hu3 := mem_update_length _ _ _ _ Hupd3.
  have Hu4 := mem_update_length _ _ _ _ Hupd4. rewrite -Hu4 -Hu3 -Hu2 -Hu1.
  cbn. rewrite Heq.
  apply N.leb_le in Heq.
  unfold mem_update in Hupd1, Hupd2, Hupd3, Hupd4.
  destruct ((Z.to_N (Wasm_int.Int32.unsigned addr) <?
           N.of_nat (Datatypes.length (ml_data (mem_data m))))%N) eqn:Hl1. 2: inv Hupd1.
  destruct ((Z.to_N (Wasm_int.Int32.unsigned addr) + 1 <?
           N.of_nat (Datatypes.length (ml_data m0)))%N) eqn:Hl2. 2: inv Hupd2.
  destruct ((Z.to_N (Wasm_int.Int32.unsigned addr) + 2 <?
           N.of_nat (Datatypes.length (ml_data m1)))%N) eqn:Hl3. 2: inv Hupd3.
  destruct ((Z.to_N (Wasm_int.Int32.unsigned addr) + 3 <?
           N.of_nat (Datatypes.length (ml_data m2)))%N) eqn:Hl4. 2: inv Hupd4.
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
  assert (He: exists e, nth_error (ml_data (mem_data m)) (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr))) = Some e). { apply notNone_Some. intro Hcontra.
  apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b1 (ml_data (mem_data m)) (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr))) b1)
  (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr) + 1)) = Some e). { apply notNone_Some.
   intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b2
     (set_nth b1 (ml_data (mem_data m)) (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr))) b1)
     (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr) + 1)) b2)
  (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr) + 2)) = Some e). {
    apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same. 2: eassumption. cbn.
  repeat (rewrite set_nth_nth_error_other; [ | lia | try lia]).
  assert (He: exists e, nth_error
  (set_nth b3
     (set_nth b2
        (set_nth b1 (ml_data (mem_data m)) (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr)))
           b1) (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr) + 1)) b2)
     (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr) + 2)) b3)
  (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned addr) + 3)) = Some e). { apply notNone_Some. intro Hcontra. apply nth_error_Some in Hcontra; lia. } destruct He.
  erewrite set_nth_nth_error_same; try lia; auto. eassumption.
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

Lemma store_constr_args_reduce : forall ys vs sargs state rho s f offset,
  INV s f ->
  (* TODO: enough memory available *)
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  Forall_statements_in_seq' (set_nth_constr_arg fenv venv nenv) ys sargs offset ->
  get_list ys rho = Some vs ->
  exists s' f', reduce_trans
                  (state, s, f, [seq AI_basic i | i <- sargs])
                  (state, s', f', [])
            /\ INV s' f'
            (* constructor args val *)
            /\ exists v_cap, sglob_val (host_function:=host_function) s' (f_inst f')
               constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap))
               /\ (0 <= Z.of_nat v_cap < Wasm_int.Int32.modulus)%Z
               /\ repr_val_constr_args_LambdaANF_Codegen fenv venv nenv _ vs s' (4 + (4*offset) + v_cap)
               (* previous mem including tag unchanged *)
               /\ sglob_val (host_function:=host_function) s  (f_inst f ) constr_alloc_ptr
                = Some (VAL_int32 (nat_to_i32 v_cap))
               /\ exists m m', nth_error (s_mems s ) 0 = Some m
                            /\ nth_error (s_mems s') 0 = Some m'
                            /\ forall a, ((* tag *) a = v_cap \/ (* previous mem *) a + 4 < v_cap)
                                         -> load_i32 m (N.of_nat a) = load_i32 m' (N.of_nat a).

Proof.
  induction ys; intros vs sargs state rho s f offset Hinv Hargs H Hvs.
  { inv Hvs. inv H. exists s. exists f. split. apply rt_refl. split. assumption.
    have I := Hinv. destruct I as [_ [_ [_ [Hcap_w [Hmut _]]]]].
    apply global_var_w_implies_global_var_r in Hcap_w; auto.
    destruct Hcap_w as [v Hv].
    edestruct i32_exists_nat as [x [Hx ?]]. erewrite Hx in Hv. clear Hx v.
    eexists. split. eassumption. split. lia.
    split. constructor.
    split. assumption.
    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [Hinv_linmem _]]]]]].
    destruct Hinv_linmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
    exists m, m. auto.
  }
  { inv H. inv H6. subst.
    (* rewrite map_cat. inv H0. cbn. *)
    inv H.
    { (* store var *)
      destruct vs. { cbn in Hvs. destruct (rho ! a). 2: inv Hvs. destruct (get_list ys rho); inv Hvs. }
      assert (Hgetlist: get_list ys rho = Some vs). {
          cbn in Hvs. destruct (rho ! a). 2: inv Hvs. destruct (get_list ys rho); inv Hvs; auto. }
      clear Hvs. rename Hgetlist into Hvs.
      (* invariants *)
      have I := Hinv. destruct I as [_ [_ [_ [Hinv_cap [Hinv_muti32 [Hinv_linmem [Hinv_locals _]]]]]]].
      eapply global_var_w_implies_global_var_r in Hinv_cap; auto. destruct Hinv_cap.
      destruct (Hinv_locals _ _ H0).
      destruct Hinv_linmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. cbn.

      destruct (i32_exists_nat x) as [x1 [Hx ?]].
      assert (exists m0, forall v_cap, store m'
        (Wasm_int.N_of_uint i32m (Wasm_int.Int32.iadd (nat_to_i32 v_cap) (nat_to_i32 (S (S (S (S (offset * 4)))))))) 0%N
          (bits (VAL_int32 x0)) (t_length T_i32) = Some m0) as Hm0. { admit. }
      destruct Hm0 as [m0 Hm0].


      (* prepare IH *)
      assert (Hmaxargs : (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z). {
      cbn in Hargs. lia. } clear Hargs.
      have IH := IHys _ _ state _ _ _ _ _ Hmaxargs H3 Hvs. clear IHys.
      edestruct IH as [sr [fr [Hred [Hinv' [v_cap [Hv1 [? [Hv2 [? [m1 [m2 [Hm1 [Hm2 ?]]]]]]]]]]]]].
      2: {
      assert (sglob_val (host_function:=host_function) s (f_inst f) constr_alloc_ptr
            = sglob_val (host_function:=host_function) (upd_s_mem (host_function:=host_function) s
                       (update_list_at (s_mems s) 0 m0)) (f_inst f) constr_alloc_ptr) as Hglob_cap by reflexivity.

      eexists. eexists. split.
      (* reduce *)
      separate_instr. dostep. elimr_nary_instr 0. apply r_get_global. rewrite Hglob_cap. eassumption.
      separate_instr. dostep. elimr_nary_instr 2. constructor. constructor. reflexivity.
      separate_instr. dostep. apply r_eliml. auto. elimr_nary_instr 0. apply r_get_local. eassumption.

      separate_instr. dostep. elimr_nary_instr 2. eapply r_store_success. 4: { rewrite Hx.
        apply Hm0. }
      auto. eassumption. eassumption. apply Hred.
      split. assumption. exists v_cap. split; eauto. split. lia.
      split. econstructor.
      admit. (* mem exists *)
      admit. (* load val *)
      admit. (* v ~ wal *)
      assert ((4 + 4 * S offset + v_cap) = (4 + S (S (S (S (offset + (offset + (offset + (offset + 0)))
                                           + v_cap)))))) as Harith by lia.
      rewrite -Harith. assumption.
      split. rewrite <- H5. reflexivity. exists m', m2.
      split. assumption. split. assumption. (* m0 -> m1, *) admit. }

      (* INV from before applying IH *)
      eapply update_mem_preserves_INV. 6: reflexivity. all: eauto.

      have H' := mem_store_preserves_length _ _ _ _ _ (Hm0 x1). unfold mem_length, memory_list.mem_length. lia.
      erewrite <-mem_store_preserves_max_pages; eauto.
      exists size; split; auto. rewrite -Hmem3. unfold mem_size, mem_length, memory_list.mem_length.
      have H' := mem_store_preserves_length _ _ _ _ _ (Hm0 x1). congruence.
    }
    { (* store fn index *)
      (* invariants *)
      admit.
    }
    (*
      (* set args + finish *)
      induction H9.

      (* no constr args *)
      { rename num'0 into resptr. cbn.
        remember ({| f_locs := set_nth (VAL_int32 resptr) (f_locs f') x' (VAL_int32 resptr)
                ; f_inst := f_inst f' |}) as fr'.

          (* IH *)
        assert (Hrel: rel_mem_LambdaANF_Codegen fenv venv nenv host_function e (map_util.M.set x (Vconstr t vs) rho) (upd_s_mem (host_function:=host_function) s2 (update_list_at (s_mems s2) n m_tag)) fr'). {
         inv H.
         have Hrel_m' := Hrel_m. destruct Hrel_m' as [Hfun Hvar].
         unfold rel_mem_LambdaANF_Codegen; split; intros.
         (* functions *)
         { destruct (var_dec x x0); try subst x0.
           (* x = x1 *)
           rewrite map_util.M.gsspec in H. rewrite peq_true in H. inv H.
           admit. (* subval_or_eq (Vfun rho' fds f) (Vconstr t [::]) absurd *)
           rewrite map_util.M.gsspec in H. rewrite peq_false in H. 2: intuition.
           have Hf' := Hfun _ _ _ _ _ H H1. destruct Hf' as [idx [Hf1 [Hf2 Hf3]]].
           exists idx. repeat split; intros; auto. econstructor; eauto.
(*
         have Htest := Hvar.
         (* free variables *)
         eexists. eexists. destruct (var_dec x x1); repeat split; intros; subst.

         (* x = x1 *)
         rename x1 into x.
         rewrite map_util.M.gsspec. rewrite peq_true. reflexivity.
         econstructor.
         assert (occurs_free e split; intros.
        } *)
        have IH := IHHev e' _ state _ INVres INVgmp INVcap INVlinmem INVptrInMem INVglobalptrInMem INVcapInMem INVlocals H11 Hrel.

        destruct IH as [srfinal [frfinal [Hredfinal Hvalfinal]]]. clear IHHev.

        exists srfinal.
        exists frfinal. split. cbn.

        dostep. elimr_nary_instr 0. apply r_get_global. eassumption.

        dostep. elimr_nary_instr 1.
        eapply r_set_local.
        assert (f_inst fr' = f_inst f') as Hfi. { rewrite Heqfr'. reflexivity. } apply Hfi.
        have Hloc := INVlocals x x' fr' H5. destruct Hloc.
        apply /ssrnat.leP.
        assert (x' < length (f_locs fr')). { apply nth_error_Some. congruence. }
        rewrite <- Hlocs. assert (length (f_locs fr') = length (f_locs fr)).
         rewrite Heqfr'. cbn. admit. (* update var doesn't change #vars *) lia.
        cbn. rewrite Heqfr'. reflexivity.
        cbn.
        apply Hredfinal. (*assumption. *) admit.
        }

(* exists (wasm_value_to_i32 wal). exists wal.
        repeat split. eapply set_global_var_updated. eassumption.
        apply val_relation_depends_only_on_mem_and_funcs with sr...
        eapply update_glob_keeps_memory_intact. eassumption.
        eapply update_glob_keeps_funcs_intact. eassumption.

      }
      {}
      }
      destruct Hex as [sr_tag [fr_tag [Htrans Hrest]]].
      destruct Hrest as [sr_final [fr_final [Htransf Hresf]]].
      eexists. eexists. split.
      eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[l])). apply Htrans. apply Htransf.
      assumption. *) *)
Admitted.

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

Lemma store_constr_reduce : forall state s f rho ys (vs : list cps.val) t sargs,
  INV s f ->
  (* TODO: enough memory available *)
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  Forall_statements_in_seq (set_nth_constr_arg fenv venv nenv) ys sargs ->
  get_list ys rho = Some vs ->

  exists s' f', reduce_trans
    (state, s, f,
      [:: AI_basic (BI_get_global global_mem_ptr)] ++
      [:: AI_basic (BI_set_global constr_alloc_ptr)] ++
      [:: AI_basic (BI_get_global global_mem_ptr)] ++
      [:: AI_basic (BI_const (nat_to_value ((Datatypes.length ys + 1) * 4)))] ++
      [:: AI_basic (BI_binop T_i32 (Binop_i BOI_add))] ++
      [:: AI_basic (BI_set_global global_mem_ptr)] ++
      [:: AI_basic (BI_get_global constr_alloc_ptr)] ++
      [:: AI_basic (BI_const (nat_to_value (Pos.to_nat t)))] ++
      [:: AI_basic (BI_store T_i32 None 2%N 0%N)] ++
      [seq AI_basic i | i <- sargs])
    (state, s', f', []) /\ INV s' f'
      (* cap points to value *)
      /\ (exists cap_v wasmval, sglob_val s' (f_inst f') constr_alloc_ptr = Some (VAL_int32 cap_v)
          /\ wasm_value_to_i32 wasmval = cap_v
          /\ repr_val_LambdaANF_Codegen fenv venv nenv  _ (Vconstr t vs) s' wasmval).
Proof.
  intros ? ? ? ? ? ? ? ? Hinv Hmaxargs Hsetargs Hrho.

  have I := Hinv. destruct I as [_ [_ [INVgmp_w [INVcap_w [INVmuti32 _]]]]].
  have INVgmp_r := global_var_w_implies_global_var_r _ _ _ INVmuti32 INVgmp_w.
  destruct INVgmp_r as [gmp_v Hgmp]. clear INVmuti32 INVgmp_w.

  (* invariants after set_global cap *)
  edestruct INVcap_w as [s' ?]. clear INVcap_w.
  assert (INV s' f) as Hinv'. { eapply update_global_preserves_INV; eassumption. }
  have I' := Hinv'. destruct I' as [_ [_ [INVgmp_w' [INVcap_w' [INVmuti32' _]]]]].
  have INVgmp_r' := global_var_w_implies_global_var_r _ _ _ INVmuti32' INVgmp_w'.
  destruct INVgmp_r' as [gmp_v' ?]. clear INVmuti32'.

  edestruct INVgmp_w' as [s'' ?]. clear INVgmp_w'.

 (* invariants after set_global gmp *)
  assert (INV s'' f) as Hinv''. { eapply update_global_preserves_INV; eassumption. }
  have I'' := Hinv''. destruct I'' as [_ [_ [_ [INVcap_w'' [INVmuti32'' [INVlinmem'' [_ [_ [_ [INVcapInMem'' _]]]]]]]]]].
  have INVcap_r'' := global_var_w_implies_global_var_r _ _ _ INVmuti32'' INVcap_w''.
  destruct INVcap_r''. clear INVmuti32''.
  (* invariants mem *)
  edestruct INVlinmem'' as [Hmem1'' [m'' [Hmem2'' [size'' [Hmem3'' [Hmem4'' Hmem5'']]]]]].
  edestruct INVcapInMem'' as [m''' Hstore''']. eassumption.

  have Hargs := store_constr_args_reduce _ _ _ state _ _ _ _ _ Hmaxargs Hsetargs Hrho.
  edestruct Hargs as [s_final [f_final [Hred [Hinv_final [v_cap [Hcap_v [? [Hargs_val [Hcap_v' [m [m' [Hm [Hm' Hmemsame]]]]]]]]]]]]].
  2: {
  cbn in Hargs_val. clear Hargs. clear Hsetargs Hrho.
  rewrite Hcap_v' in H2. inv H2.

  eexists. eexists. split.
  (* steps *)
  (* get global, increase, set global *)
  dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
  dostep. elimr_nary_instr 1. apply r_set_global. eassumption.
  dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
  dostep. elimr_nary_instr 2. constructor. apply rs_binop_success. reflexivity.
  dostep. elimr_nary_instr 1. apply r_set_global. eassumption.
  dostep. elimr_nary_instr 0. apply r_get_global. 2: { (* eassumption. *)
  (* write tag *)
  dostep. elimr_nary_instr 2. eapply r_store_success. 4: eassumption.
  reflexivity. eassumption. eassumption.
  apply Hred. } assumption.
  split. assumption.
  (* constr value in memory *)
  eexists. eexists. split. eassumption.
  split. 2: econstructor. reflexivity.
  lia. apply store_load in Hstore'''.
  eassumption. reflexivity. reflexivity.
  rewrite <- Hmemsame; try lia.
  apply store_load in Hstore'''.
  assert (m = m'''). { cbn in Hm. unfold update_list_at in Hm. rewrite take0 in Hm. now inv Hm. }
  subst m'''.  rewrite deserialise_bits in  Hstore'''; auto.
  assert ((Wasm_int.N_of_uint i32m (nat_to_i32 v_cap) = N.of_nat v_cap)) as Harith. { cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
  rewrite Harith in Hstore'''. assumption. reflexivity. assumption.
  }
  { (* INV before stepping through sargs *)
    eapply update_mem_preserves_INV. 6: reflexivity. assumption.
    eassumption. apply mem_store_preserves_length in Hstore'''.
    unfold mem_length, memory_list.mem_length. lia.
    apply mem_store_preserves_max_pages in Hstore'''. congruence.
    exists size''. split; auto.
    unfold mem_size, mem_length, memory_list.mem_length in *.
    apply mem_store_preserves_length in Hstore'''. congruence.
   }
Qed.



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
        INV sr f ->

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
          result_val_LambdaANF_Codegen v f'.(f_inst) sr'. (* value v is related to memory m'/lenv' *)
Proof with eauto.
  intros rho v e n Hev.
  induction Hev; intros instructions fr state sr Hinv Hrepr_e Hrel_m.
  - (* Econstr *)
    inversion Hrepr_e. subst t0 x0 vs0 e0 sgrow. rename H5 into Hx. rename H11 into Hexp.
    { remember (grow_memory_if_necessary ((Datatypes.length ys + 1) * 4)) as grow.
      cbn. repeat rewrite map_cat. cbn.

      (* prepare calling memory_grow_reduce *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [Hlinmem _]]]]]].
      destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
      have Hgrowmem := memory_grow_reduce _ _ state sr fr Heqgrow Hinv.
      destruct Hgrowmem as [s' [f' [Hred [Hinv' Henoughmem]]]].
      have I := Hinv'. destruct I as [_ [_ [Hgmp [_ [Hmuti32 [Hlinmem' _]]]]]].
      destruct Hlinmem' as [Hmem1' [m' [Hmem2' [size' [Hmem3' _]]]]].
      apply global_var_w_implies_global_var_r in Hgmp; auto. destruct Hgmp as [val Hgmp].

      (* invariants after reducing grow *)
      have I' := Hinv'. destruct I' as [_ [INVresmem_w' [INVgmp_w' [INVcap_w' [INVmuti32' _]]]]].
      have INVgmp_r' := global_var_w_implies_global_var_r _ _ _ INVmuti32' INVgmp_w'.
      have INVresmem_r' := global_var_w_implies_global_var_r _ _ _ INVmuti32' INVresmem_w'.
      destruct INVgmp_r' as [n Hgmp']. destruct INVresmem_r' as [resmem_v' Hresmem'].
      edestruct i32_exists_nat as [gmp_v' [Hn ?]]. erewrite Hn in Hgmp'. clear Hn n.
      have HenoughM := Henoughmem _ _ Hmem2' Hgmp'. clear Henoughmem.

      destruct HenoughM as [HenoughM | HoutofM].
      { (* enough memory *)
      assert (Hmaxargs: (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z) by admit.

      have Hconstr := store_constr_reduce state _ _ _ _ _ _ _ _ Hmaxargs H9 H.
      edestruct Hconstr as [s_v [f_v [Hred_v [Hinv_v [cap_v [wal [? [? Hvalue]]]]]]]]. 2:{ clear Hconstr. subst cap_v.

    (* prepare IH *) (* TODO not s_v but updated with global var *)
    assert (Hrel_m_v : rel_mem_LambdaANF_Codegen fenv venv nenv host_function e rho'
       s_v f_v). admit.
    have IH := IHHev _ _ state _ Hinv_v Hexp Hrel_m_v.
    destruct IH as [s_final [f_final [Hred_IH Hval]]].

    eexists. eexists. split.
    (* steps *)
    eapply rt_trans. apply app_trans. apply Hred. cbn.

      admit. eassumption. } eassumption. }
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
    rename s into e'. rename v' into y'.

    (* y is constr value with correct tag, arity *)
    assert (Hy : occurs_free (Eproj x t n y e) y) by constructor.
    have Hrel_m' := Hrel_m.
    destruct Hrel_m' as [Hfun Hvar].
    apply Hvar in Hy. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
    rewrite Hrho in H. inv H.
    have Hrepr' := Hrepr. inv Hrepr'.

    inv Hlocal. destruct H.

    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hinv_bound]]]]]]]]]].
    have Hextr := extract_constr_arg n vs v _ _ _ Hinv_bound H0 H3 H11.
    destruct Hextr as [bs [wal [Hload [Heq Hbsval]]]].

     assert (Hrm: rel_mem_LambdaANF_Codegen fenv venv nenv host_function e (map_util.M.set x v rho) sr
  {|
    f_locs := set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32);
    f_inst := f_inst fr
  |}).
  {
  split; intros. admit. (* x not a fundef *)

  destruct (var_dec x x1).
  (* x = x1 *)
  subst x1.
  exists v. exists (Val_ptr (addr + 4 + (4 * N.to_nat n))). split.
  rewrite map_util.M.gsspec.
  apply peq_true.
  split. exists x'. split.
  inv H8. unfold translate_var in H5. unfold translate_var. eapply lookup_local_var_generalize_err_string. eassumption.
  assert ((wasm_deserialise bs T_i32) = (VAL_int32 (wasm_value_to_i32 (Val_ptr (addr + 4 + (4 * N.to_nat n)))))). admit. rewrite H6.

  have I := Hinv. destruct I as [_ [_ [_ [_ [_ [Hlinmem [Hl _]]]]]]].
  destruct (Hl x x'). assumption.
  eapply set_nth_nth_error_same. eassumption. admit.

  (* x <> x1 *)
  assert (occurs_free (Eproj x t n y e) x1). { constructor; assumption. }
  apply Hvar in H6. destruct H6 as [v6 [wal' [Henv [Hloc Hval]]]].
  exists v6. exists wal'. repeat split.
  rewrite map_util.M.gsspec.
  rewrite peq_false. assumption. intro. subst. contradiction.
  cbn.
  admit. (* different vars -> different wasm local vars *)
  assumption.
  }
  assert (INV sr
         {|
           f_locs :=
             set_nth (wasm_deserialise bs T_i32)
               (f_locs fr) x' (wasm_deserialise bs T_i32);
           f_inst := f_inst fr
         |}) as Hinv'. { cbn. eapply update_local_preserves_INV...
         have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hl _]]]]]]].
         destruct (Hl _ _ H8). apply nth_error_Some. intro. congruence. }

   have IH := IHHev e' (Build_frame (set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32)) (f_inst fr)) state sr Hinv' H7 Hrm. destruct IH as [sr' [f' [Hred Hval]]].

    eexists. eexists. cbn. split.
    { (* take steps *)
    have Hvy := H9. inv H9.

    have I := Hinv'. destruct I as [_ [_ [_ [_ [_ [Hlinmem [Hl ]]]]]]].
    destruct (Hl _ _ Hvy).
    rewrite H in H4. injection H4 => H4'. subst. clear H4.

    rewrite set_nth_nth_error_other in H9. 2: admit. 2: admit. cbn.
    rewrite H1 in H9. injection H9 => H9'. subst. clear H9.

    (* get_local y' *)
    dostep. elimr_nary_instr 0.
    apply r_get_local. apply H1.

    (* add offset n *)
    dostep. elimr_nary_instr 2.
    constructor. apply rs_binop_success. cbn. reflexivity.

    inv Hrepr.

    dostep. elimr_nary_instr 1.
    eapply r_load_success.

    destruct Hlinmem as [Hmem1 [m' Hmem2]].
    eassumption. apply H3.

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


    have Hloc := Hl x x' Hx. destruct Hloc. clear Hl.
    apply /ssrnat.leP.
    assert (x' < length (f_locs fr)). { apply nth_error_Some. intro.
    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hl _]]]]]]]. edestruct Hl; eauto. congruence. } lia.
    reflexivity.
    cbn.
    apply Hred.
    }
    apply Hval.

  - (* Ecase *)
    { generalize dependent y. generalize dependent instructions. induction cl; intros; subst. inv H1. destruct a. rename c0 into t0.

      assert (caseConsistent cenv cl t). { inv H0. assumption. }
      cbn in H1. destruct (M.elt_eq t0 t). subst.

      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [Hlinmem [Hl _]]]]]]].

      (* t0 = t *)
      { inv H1. clear IHcl.
        inv Hrepr_e.

        assert (Hy : occurs_free (Ecase y ((t, e) :: cl)) y) by constructor.
        have Hrel_m' := Hrel_m.
        destruct Hrel_m' as [Hfun Hvar].
        apply Hvar in Hy. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
        rewrite Hrho in H. inv H.
        destruct (Hl _ _ H7) as [x H].
        have H' := H7. inv H'. rename v' into y'.
        have Hrepr' := Hrepr. inv Hrepr'.
        inv Hlocal. destruct H3.
        rewrite H3 in H1. inv H1. rewrite H4 in H. inv H.

      assert (Hrel: rel_mem_LambdaANF_Codegen fenv venv nenv host_function e rho sr fr).
      { unfold rel_mem_LambdaANF_Codegen. split; intros... }

      have IH := IHHev _ _ state _ Hinv H9  Hrel. destruct IH as [sr' [f' [Hstep Hval]]].

    eexists. eexists.
    split. {
    (* steps *)
    dostep. elimr_nary_instr 0.
    apply r_get_local. eassumption.

    unfold load_i32 in H6.
    destruct (load m (N.of_nat addr) (N.of_nat 0) 4) eqn:Hload.

    dostep. elimr_nary_instr 1.
    eapply r_load_success.

    apply Hlinmem. eassumption.

    assert (N.of_nat addr = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))). admit. (* arithmetic fact *)
    rewrite <- H. apply Hload.

    remember (VAL_int32 (tag_to_i32 t)) as tag.

    dostep. elimr_nary_instr 2.
    constructor. apply rs_relop. cbn.

    dostep'. constructor. apply rs_if_true.
    cbn. unfold nat_to_i32. unfold tag_to_i32.
    unfold Wasm_int.Int32.eq.
    cbn in Hload. unfold load_i32 in H11.
    rewrite Hload in H11. subst. injection H11 => H11'.
    destruct (zeq (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (decode_int b)))
      (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (Pos.to_nat t))))) eqn:Heq. discriminate. contradiction.

       dostep'. constructor. eapply rs_block with (vs := []); auto. unfold to_e_list. cbn.
      eapply reduce_trans_label. apply Hstep. unfold load_i32 in H11. rewrite Hload in H11. inv H11. }
       assumption. }

      (* t0 <> t *)

      inv H0.
      inv Hrepr_e.

      assert (Hrel: rel_mem_LambdaANF_Codegen fenv venv nenv host_function (Ecase y cl) rho sr fr).
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

    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [Hlinmem [Hl _]]]]]]].
    destruct (Hl _ _ H11) as [x H]. clear Hl.
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
    rewrite Harith in H15.
     unfold load_i32 in H8.
    destruct (load m (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))
         (N.of_nat 0) 4) eqn:Hload.
     { dostep. elimr_nary_instr 1.
       eapply r_load_success.
       apply Hlinmem. eassumption.
       apply Hload. unfold load_i32 in H15. rewrite Hload in H15.
       assert (wasm_deserialise b T_i32 = VAL_int32 (tag_to_i32 t)). {
       inv H15. unfold wasm_deserialise. f_equal. unfold tag_to_i32. cbn. cbn in Hload.
       rewrite Wasm_int.Int32.Z_mod_modulus_id in Hload; try lia.
       replace (Z.to_N (Z.of_nat addr)) with (N.of_nat addr) in Hload by lia.
       apply decode_int_bounds in Hload.
       rewrite Wasm_int.Int32.Z_mod_modulus_id in H0; auto. rewrite H0.
       rewrite Wasm_int.Int32.Z_mod_modulus_id; auto.
       admit. } rewrite H.

       dostep. elimr_nary_instr 2.
       constructor. apply rs_relop.
       assert ((wasm_bool
                 (app_relop (Relop_i ROI_eq) (VAL_int32 (tag_to_i32 t))
                    (nat_to_value (Pos.to_nat t0)))) = nat_to_i32 0). {
                    unfold nat_to_value, nat_to_i32, tag_to_i32.
      unfold wasm_bool. cbn. unfold Wasm_int.Int32.eq. cbn. rewrite zeq_false; auto. admit.
       } (* by t <> t0 *)
      rewrite H0.
      dostep'. separate_instr. constructor. apply rs_if_false. reflexivity.

      dostep'. constructor. eapply rs_block with (vs := []); eauto. cbn.
      eapply reduce_trans_label. unfold to_e_list. apply Hred.
     } unfold load_i32 in H15. rewrite Hload in H15. inv H15. assumption. }

(*
    { (* remember ([:: BI_get_local v'; BI_load T_i32 None (N.of_nat 2) (N.of_nat 0);
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
  admit. } admit. } admit. } *)
  - (* Eapp *)
    inv Hrepr_e.
    + (* direct call *)
      { unfold rel_mem_LambdaANF_Codegen in Hrel_m. destruct Hrel_m.
        edestruct H3 as [j [Hfvar [Hval Hclosed]]]. eassumption.
         constructor. constructor. eapply find_def_name_in_fundefs. eassumption.
        (* apply rt_refl. *) inv Hval.
        rewrite H1 in H11. inv H11. rename e0 into e.
        rewrite map_cat. cbn.

        eexists. eexists. split. dostep. apply r_eliml. admit. apply r_call. assert (j = v') by admit. subst.  admit. admit. admit.

      }
     (*
      assert (exists sr', exists f', exists args'',
        reduce_trans (state, sr, fr, [seq AI_basic i | i <- args'])%list
                     (state, sr', f', [seq AI_basic i | i <- args''])%list) /\ .  *) admit.
    + (* indirect call *) admit.
  (*   rewrite map_cat.
    assert (occurs_free (Eapp f t ys) f) by constructor.

    eexists. eexists. split. rewrite map_cat. cbn.
    Check r_eliml. cbn.
    dostep'. cbn. apply r_eliml. admit. (* args' const *)
    apply r_call. admit. admit. admit. *)
  - (* Eletapp *)   inv Hrepr_e. (* absurd, we require CPS *)
  - (* Efun *)      inv Hrepr_e. (* absurd, fn defs only on topmost level *)
  - (* Eprim_val *) inv Hrepr_e. (* absurd, primitives not supported *)
  - (* Eprim *)     inv Hrepr_e. (* absurd, primitives not supported *)
  - (* Ehalt *)
    cbn. destruct Hrel_m. destruct (H2 x) as [v6 [wal [Henv [Hloc Hrepr]]]]. constructor.
    rewrite Henv in H. inv H.

    destruct Hinv as [INVres _]. unfold INV_result_var_writable, global_var_w in INVres.
    specialize INVres with (wasm_value_to_i32 wal).
    destruct INVres as [s' Hs].

    exists s'. eexists fr.

    destruct H1.
    destruct Hloc as [ilocal [H3 Hilocal]]. split. erewrite H3 in H. injection H => H'. subst. clear H.
    (* execute wasm instructions *)
    dostep. separate_instr. apply r_elimr. eapply r_get_local. eassumption.
    dostep'. apply r_set_global. eassumption.
    apply rt_refl.
    unfold result_val_LambdaANF_Codegen. left.
    exists (wasm_value_to_i32 wal). exists wal.
    repeat split. eapply set_global_var_updated. eassumption.
    apply val_relation_depends_only_on_mem_and_funcs with sr...
    eapply update_glob_keeps_memory_intact. eassumption.
    eapply update_glob_keeps_funcs_intact. eassumption.
Admitted.

End THEOREM.
(*
Lemma funargs_reduce_to_const : forall sr fr state, repr_fun_args_Codegen fenv venv nenv ys args' -> reduce_trans (state, sr, fr, [seq AI_basic i | i <- args']) (state, sr, fr, args) /\ vs_co *)

(*
  - (* Econstr *)

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
Variable p:program. (* TODO remove program relict from Codegen *)
 (* This should be a definition rather than a parameter, computed once and for all from cenv *)
Variable rep_env: M.t ctor_rep.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
(*Let administrative_instruction := administrative_instruction host_function.*)
Let host_state := host_state host_instance.

Let reduce_trans := @reduce_trans host_function host_instance.

Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show CodegenWASM.wasm_map_util.
Import Common.Common Common.compM Common.Pipeline_utils.

Import ExtLib.Structures.Monad.
Import MonadNotation.

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

Lemma module_instantiatable : forall e module fenv venv,
LambdaANF_to_WASM nenv cenv e = Ret (module, fenv, venv) ->
  exists sr f exports, instantiate host_function host_instance empty_store_record module []
       (sr, (f_inst f), exports, None)
       /\ INV venv nenv _ sr f.
Proof.
  intros. eexists. eexists. intros. unfold LambdaANF_to_WASM in H.
  destruct (create_fname_mapping nenv e) eqn:Hmapping. inv H. simpl in H. rename f into fname_mapping.
  destruct (generate_constr_pp_function cenv fname_mapping
       (collect_constr_tags e)) eqn:Hppconst. inv H.
  destruct (collect_function_signatures nenv e) eqn:Hfsigs. inv H. rename l into sigs.
  destruct (generate_indirection_functions sigs fname_mapping) eqn:Hind. inv H. rename l into indfns.
  destruct (match e with
       | Efun fds _ =>
           (fix iter (fds0 : fundefs) : error (seq.seq wasm_function) :=
              match fds0 with
              | Fcons x _ xs e0 fds' =>
                  match
                    translate_function nenv cenv fname_mapping
                      (create_local_variable_mapping nenv fname_mapping e) x xs e0
                  with
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
              end) fds
       | _ => Ret []
       end) eqn:Hfuns. inv H. rename l into fns.
       destruct ( translate_exp nenv cenv (create_local_variable_mapping nenv fname_mapping e) fname_mapping
       (match e with
          | Efun _ exp => exp
          | _ => e end)) eqn:Hexpr. inv H. rename l into wasm_main_instr.
  destruct (lookup_function_var main_function_name fname_mapping
         "main function") eqn:Hfmain. inv H. inv H.
   eexists. split. repeat esplit.
   (* function types *) { cbn. repeat rewrite map_app; cbn. apply Forall2_app. admit. admit. }
   (* module glob typing *) {
      apply Forall2_cons. cbn. repeat split; auto. cbn. constructor.
      apply Forall2_cons. cbn. repeat split; auto. cbn. constructor.
      apply Forall2_cons. cbn. repeat split; auto. cbn. constructor.
      apply Forall2_cons. cbn. repeat split; auto. cbn. constructor.
      apply Forall2_nil. }
   (* module elem typing *) { apply Forall_nil. }
   (* module data typing *) { apply Forall_nil. }
   (* module import typing *) {
      apply Forall2_cons. cbn. unfold is_true.
      assert (match ET_func (Tf [T_i32] []) with
              | ET_func tf => function_type_eqb tf (Tf [T_i32] [])
              | _ => false
              end = true) by reflexivity. eassumption.
      apply Forall2_cons. cbn.
      assert (match ET_func (Tf [T_i32] []) with
              | ET_func tf => function_type_eqb tf (Tf [T_i32] [])
              | _ => false
              end = true) by reflexivity. eassumption.
      apply Forall2_nil. }
   (* module export typing *) {
      apply Forall2_app. (* exporting functions *) repeat rewrite map_app. apply Forall2_app. admit. admit.
      apply Forall2_cons. cbn. unfold is_true. admit.
      apply Forall2_cons. cbn. unfold is_true. admit.
      apply Forall2_cons. cbn. unfold is_true. admit.
      apply Forall2_nil. }
   (* external typing *) { admit. }
   (* alloc_module is true *) { admit. }
   (* instantiate globals *) { admit. }
   (* instantiate elem *) { apply Forall2_nil. }
   (* instantiate data *) { apply Forall2_nil. }
   (* check_bounds elem *) { reflexivity. }
   (* check_bounds data *) { reflexivity. }
   (* check_start *) { cbn. admit. }
   (* INV *) { admit. }
   Unshelve. apply empty_store_record.
Admitted.


(* MAIN THEOREM, corresponds to 4.3.1 in Olivier's thesis *)

Corollary LambdaANF_Codegen_related :
  forall (rho : eval.env) (v : cps.val) (e : exp) (n : nat), (* rho is environment containing outer fundefs. e is body of LambdaANF program *)

  forall (hs : host_state) module fenv venv exports mainidx function,

  (* evaluation of LambdaANF expression *)
  bstep_e (M.empty _) cenv rho e v n ->

  (* compilation function *)
  LambdaANF_to_WASM nenv cenv e = Ret (module, fenv, venv) ->

  (* constructors welformed *)
  correct_cenv_of_exp cenv e ->

  (* expression must be closed *)
  (~ exists x, occurs_free e x) ->

  (* TODO: imports *)
  exists sr inst,
  instantiate _ host_instance empty_store_record module [] ((sr, inst, exports), None) /\
  List.nth_error sr.(s_funcs) mainidx = Some function /\

  (* *)
  exists (sr' : store_record),
       reduce_trans (hs, sr,  (Build_frame [] inst), [ AI_basic (BI_call mainidx) ])
                    (hs, sr', (Build_frame [] inst), [])    /\

       result_val_LambdaANF_Codegen fenv venv nenv _ v inst sr'.
Proof.
  intros. eexists. eexists. intros. have HL2WASM := H0. unfold LambdaANF_to_WASM in H0.
  destruct (create_fname_mapping nenv e) eqn:Hmapping. inv H0. simpl in H0. rename f into fname_mapping.
  destruct (generate_constr_pp_function cenv fname_mapping
       (collect_constr_tags e)) eqn:Hppconst. inv H0.
  destruct (collect_function_signatures nenv e) eqn:Hfsigs. inv H0. rename l into sigs.
  destruct (generate_indirection_functions sigs fname_mapping) eqn:Hind. inv H0. rename l into indfns.
  destruct (match e with
       | Efun fds _ =>
           (fix iter (fds0 : fundefs) : error (seq.seq wasm_function) :=
              match fds0 with
              | Fcons x _ xs e0 fds' =>
                  match
                    translate_function nenv cenv fname_mapping
                      (create_local_variable_mapping nenv fname_mapping e) x xs e0
                  with
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
              end) fds
       | _ => Ret []
       end) eqn:Hfuns. inv H0. rename l into fns.
       destruct ( translate_exp nenv cenv (create_local_variable_mapping nenv fname_mapping e) fname_mapping
       (match e with
          | Efun _ exp => exp
          | _ => e end)) eqn:Hexpr. inv H0. rename l into wasm_main_instr.
  destruct (lookup_function_var main_function_name fname_mapping
         "main function") eqn:Hfmain. inv H0. inv H0.
       remember (match e with
          | Efun _ exp => exp
          | _ => e end) as mainexpr.

  remember (create_local_variable_mapping nenv fenv e) as venv.
  have Hinstantiate := module_instantiatable _ _ _ _ HL2WASM.
  destruct Hinstantiate as [sr [inst [exports' [Hinst HINV2]]]].

  have Heqdec := inductive_eq_dec e. destruct Heqdec.
  destruct e0 as [fds' [e' He]]. subst.
  (* top exp is Efun _ _ *)
  exfalso. inv H. (* TODO *)
  remember (Efun fds' e') as e.
  remember (create_local_variable_mapping nenv fenv e) as venv.

  have HMAIN := repr_bs_LambdaANF_Codegen_related cenv funenv fenv venv nenv finfo_env _ rep_env _ host_instance _ _ _ _ H7 wasm_main_instr.
  edestruct HMAIN.
  (* program, relict, should be removed *) admit.
  (* INVariants *) admit.
  eapply translate_exp_correct. eapply Forall_constructors_subterm in H1. eassumption. subst. constructor. apply dsubterm_fds2. assumption. split; intros. admit. admit. admit.

  (* top exp is not Efun _ _ *)
  exfalso. assert (mainexpr = e). { destruct e; auto. exfalso. eauto. } subst mainexpr.
  assert (fns = []). { destruct e; inv Hfuns; auto. exfalso. eauto. } subst.
  unfold collect_function_signatures in Hfsigs.
  assert (sigs = []). { destruct e; inv Hfsigs; auto. exfalso. eauto. } subst. inv Hind. clear Hfsigs Hfuns.
  rewrite H0 in Hexpr.

  remember (create_local_variable_mapping nenv fenv e) as venv.
  have HMAIN := repr_bs_LambdaANF_Codegen_related cenv funenv fenv venv nenv finfo_env _ rep_env _ host_instance rho _ _ _ H wasm_main_instr.
  edestruct HMAIN.
  (* program, relict, should be removed *) admit.
  (* INVariants  rw *) admit.
  eapply translate_exp_correct. eassumption. assumption. split; intros.
  (* absurd: no functions -> rho ! x = None *)
  admit. admit. admit.
Admitted.

(*
Goal True.
idtac "Assumptions:".
Abort.
Print Assumptions LambdaANF_Codegen_related.
 *)
