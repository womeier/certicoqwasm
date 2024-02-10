(* Proof of correctness of the WASM code generation phase of CertiCoq,
   this file is based on the proof for the Clight backend.

 > Codegen relation: relates expressions to Wasm instructions
 > Value relation:   relates LambdaANF values to Wasm values
 > Environment relation: relates values to location in linear memory,
   function values to function indices, called "memory relation" for Clight)

 > Main statement: relates LambdaANF states to Wasm states according
                   to operational semantics

  TODO: consider reusing functions from certicoq for collecting variables
  TODO: consider using Ensemble like the Clight backend

 *)
From mathcomp Require Import eqtype.

From compcert Require Import Coqlib.

Require Import LambdaANF.cps LambdaANF.eval LambdaANF.cps_util LambdaANF.List_util
               LambdaANF.Ensembles_util LambdaANF.identifiers
               LambdaANF.shrink_cps_corresp.

Require Import Coq.ZArith.BinInt.
Require Import Lia.
Require Export Int31.

Require Import Coq.Arith.Arith Coq.NArith.BinNat ExtLib.Data.String
               ExtLib.Data.List Coq.Program.Program Coq.Sets.Ensembles
               Coq.Logic.Decidable Coq.Lists.ListDec
               Coq.Relations.Relations Relations.Relation_Operators.

Require Import compcert.lib.Integers compcert.common.Memory.

Require Import CodegenWASM.LambdaANF_to_WASM.

From Wasm Require Import datatypes datatypes_properties operations host
                         type_preservation instantiation_spec memory_list
                         opsem interpreter_func properties common.

Require Import Libraries.maps_util.
From Coq Require Import List.

Open Scope list.

Import ListNotations.

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
    + rewrite M.gso in H0 by auto.
      constructor 2.
      inv H. exfalso; apply n; reflexivity.
      eapply IHxs; eauto.
Qed.


(**** Representation relation for LambdaANF values, expressions and functions ****)
Section RELATION.
Variable cenv:LambdaANF.cps.ctor_env.
Variable funenv:LambdaANF.cps.fun_env.
Variable fenv : CodegenWASM.LambdaANF_to_WASM.fname_env.
Variable nenv : LambdaANF.cps_show.name_env.

Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show.
Import Common.compM Common.Pipeline_utils.

Import ExtLib.Structures.Monad.
Import MonadNotation.


(* all boxed -> list can be empty *)
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

(* immediate=nat: used in BI_call i *)
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
Inductive repr_fun_args_Codegen {lenv} : list LambdaANF.cps.var ->
                                         list basic_instruction -> Prop :=
(* base case: no args *)
| FA_nil :
    repr_fun_args_Codegen [] []
(* arg is local var *)
| FA_cons_var : forall a a' args instr,
    repr_var (lenv:=lenv) a a' ->
    repr_fun_args_Codegen args instr ->
    repr_fun_args_Codegen (a :: args) ([BI_get_local a'] ++ instr)
(* arg is function -> lookup id for handling indirect calls later *)
| FA_cons_fun : forall a a' args instr,
    repr_funvar a a' ->
    repr_fun_args_Codegen args instr ->
    repr_fun_args_Codegen (a :: args) ([BI_const (nat_to_value a')] ++ instr).


Inductive repr_asgn_constr_Codegen {lenv} : immediate -> ctor_tag -> list var -> list basic_instruction -> list basic_instruction ->  Prop :=
| Rconstr_asgn_boxed :
  forall x' t vs sgrow sargs sres scont arity,
    get_ctor_arity cenv t = Ret arity ->
    arity > 0 ->
    (* allocate memory *)
    grow_memory_if_necessary page_size = sgrow ->
    (* store args *)
    Forall_statements_in_seq (set_nth_constr_arg (lenv:=lenv)) vs sargs ->
    (* set result *)
    sres = [BI_get_global constr_alloc_ptr; BI_set_local x'] ->

    repr_asgn_constr_Codegen x' t vs scont
      (sgrow ++
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
            ] ++ sargs ++ sres ++ scont)
       ])

| Rconstr_asgn_unboxed :
  forall x' t scont,
    get_ctor_arity cenv t = Ret 0 ->
    repr_asgn_constr_Codegen x' t [] scont
      ([ BI_const (nat_to_value (Pos.to_nat t))
         ; BI_const (nat_to_value 1)
         ; BI_binop T_i32 (Binop_i BOI_shl)
         ; BI_const (nat_to_value 1)
         ; BI_binop T_i32 (Binop_i BOI_add)
         ; BI_set_local x' ] ++ scont ).


(* CODEGEN RELATION: relatates LambdaANF expression and result of translate_exp *)
Inductive repr_expr_LambdaANF_Codegen {lenv} : LambdaANF.cps.exp -> list basic_instruction -> Prop :=
| R_halt_e: forall x x',
    repr_var (lenv:=lenv) x x' ->
    repr_expr_LambdaANF_Codegen (Ehalt x) [ BI_get_local x'
                                          ; BI_set_global result_var
                                          ]
| Rproj_e: forall x x' t n y y' e e',
    repr_expr_LambdaANF_Codegen e e' ->
    repr_var (lenv:=lenv) x x' ->
    repr_var (lenv:=lenv) y y' ->
      repr_expr_LambdaANF_Codegen (Eproj x t n y e)
           ([ BI_get_local y'
           ; BI_const (nat_to_value (((N.to_nat n) + 1) * 4))
           ; BI_binop T_i32 (Binop_i BOI_add)
           ; BI_load T_i32 None (N_of_nat 2) (N_of_nat 0)
           ; BI_set_local x'
           ] ++ e')

| Rconstr_e: forall x x' t vs e instrs e',
    repr_expr_LambdaANF_Codegen e e' ->
    repr_var (lenv:=lenv) x x' ->
    repr_asgn_constr_Codegen (lenv:=lenv) x' t vs e' instrs ->
    repr_expr_LambdaANF_Codegen (Econstr x t vs e) instrs


| Rcase_e_nil : forall v, repr_expr_LambdaANF_Codegen (Ecase v []) [BI_unreachable]

| Rcase_e_cons_unboxed : forall y y' cl instrs_more t e e',
        repr_var (lenv:=lenv) y y' ->
        repr_expr_LambdaANF_Codegen (Ecase y cl) instrs_more ->
        repr_expr_LambdaANF_Codegen e e' ->
        get_ctor_arity cenv t = Ret 0 ->
        repr_expr_LambdaANF_Codegen (Ecase y ((t, e) :: cl))
          [ BI_get_local y'
          ; BI_const (nat_to_value 1) ; BI_binop T_i32 (Binop_i (BOI_shr SX_S))
          ; BI_const (nat_to_value (Pos.to_nat t))
          ; BI_relop T_i32 (Relop_i ROI_eq)
          ; BI_if (Tf nil nil) e' instrs_more
          ]

| Rcase_e_cons_boxed : forall v v' cl instrs_more t e e' arity,
        repr_var (lenv:=lenv) v v' ->
        repr_expr_LambdaANF_Codegen (Ecase v cl) instrs_more ->
        repr_expr_LambdaANF_Codegen e e' ->
        get_ctor_arity cenv t = Ret arity ->
        arity > 0 ->
        repr_expr_LambdaANF_Codegen (Ecase v ((t, e) :: cl))
          [ BI_get_local v'
          ; BI_load T_i32 None 2%N 0%N
          ; BI_const (nat_to_value (Pos.to_nat t))
          ; BI_relop T_i32 (Relop_i ROI_eq)
          ; BI_if (Tf nil nil) e' instrs_more
          ]

| R_app_e : forall v instr t args args',
    (* args are provided properly *)
    repr_fun_args_Codegen (lenv:=lenv) args args' ->
    (* instr reduces to const containing funidx to call *)
    repr_read_var_or_funvar (lenv:=lenv) v instr ->
    repr_expr_LambdaANF_Codegen (Eapp v t args) (args' ++
                                                [instr] ++
                                                [BI_call_indirect (length args)])

| R_letapp_e : forall x x' v instr t args args' e e',
    (* translated assigned var *)
    repr_var (lenv:=lenv) x x' ->
    (* following expression *)
    repr_expr_LambdaANF_Codegen e e' ->
    (* args are provided properly *)
    repr_fun_args_Codegen (lenv:=lenv) args args' ->
    (* instr reduces to const containing funidx to call *)
    repr_read_var_or_funvar (lenv:=lenv) v instr ->
    repr_expr_LambdaANF_Codegen (Eletapp x v t args e)
      ((args' ++ [ instr
                 ; BI_call_indirect (length args)
                 ; BI_get_global result_out_of_mem
                 ; BI_if (Tf nil nil) []
                     ([BI_get_global result_var; BI_set_local x'] ++ e')])).

Definition load_i32 m addr : option value :=
  match load m addr 0%N 4 with (* offset: 0, 4 bytes *)
  | None => None
  | Some bs => Some (wasm_deserialise bs T_i32)
  end.

Definition store_i32 mem addr (v : value) : option memory :=
  store mem addr 0%N (bits v) 4.

Definition tag_to_i32 (t : ctor_tag) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat (Pos.to_nat t)).

Definition immediate_to_i32 (i : immediate) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat i).

(* TODO use i32 instead *)
Inductive wasm_value :=
  | Val_unboxed : immediate -> wasm_value
  | Val_ptr : immediate -> wasm_value
  | Val_funidx : immediate -> wasm_value.

Definition wasm_value_to_immediate (v : wasm_value) :=
    match v with
    | Val_unboxed i => i
    | Val_ptr i => i
    | Val_funidx i => i
    end.

Definition wasm_value_to_i32 (v : wasm_value) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat (wasm_value_to_immediate v)).

Variable host_function : eqType.
Let store_record := store_record host_function.


(* VALUE RELATION *)
(* immediate is pointer to linear memory or function id *)
Inductive repr_val_LambdaANF_Codegen:  LambdaANF.cps.val -> (* val *)
                                        store_record ->     (* sr *)
                                         frame ->           (* fr *)
                                          wasm_value ->     (* wal *)
                                          Prop :=
| Rconstr_unboxed_v : forall v t (sr : store_record) fr,
    Pos.to_nat (t * 2 + 1) = v ->
    get_ctor_arity cenv t = Ret 0 ->
    repr_val_LambdaANF_Codegen (Vconstr t []) sr fr (Val_unboxed v)


| Rconstr_boxed_v : forall v t vs (sr : store_record) fr gmp m (addr : nat) arity,
    (* simple memory model: gmp is increased whenever new mem is needed,
       gmp only increases *)
    sglob_val sr (f_inst fr) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp)) ->
    (-1 < Z.of_nat gmp < Wasm_int.Int32.modulus)%Z ->
    (* constr arity > 0 *)
    get_ctor_arity cenv t = Ret arity ->
    arity > 0 ->
    length vs > 0 ->
    (* addr in bounds of linear memory (later INV: gmp + 4 < length of memory) *)
    (addr + 4 <= gmp) ->
    (* store_record contains memory *)
    List.nth_error sr.(s_mems) 0 = Some m ->
    (* constructor tag is set, see LambdaANF_to_WASM, constr alloc structure*)
    v = tag_to_i32 t ->
    load_i32 m (N.of_nat addr) = Some (VAL_int32 v) ->
    (* arguments are set properly *)
    repr_val_constr_args_LambdaANF_Codegen vs sr fr (4 + addr) ->
    repr_val_LambdaANF_Codegen (Vconstr t vs) sr fr (Val_ptr addr)


| Rfunction_v : forall fds f sr fr tag xs e e' idx ftype ts body,
      repr_funvar f idx ->
      find_def f fds = Some (tag, xs, e) ->
      (* types of local vars: all i32 *)
      ts = repeat T_i32 (length (collect_local_variables e)) ->
      (* find runtime representation of function *)
      nth_error sr.(s_funcs) idx = Some (FC_func_native (f_inst fr) ftype ts body) ->
      ftype = Tf (List.map (fun _ => T_i32) xs) [] ->
      body = e' ->
      repr_expr_LambdaANF_Codegen e e'
        (lenv:=create_local_variable_mapping (xs ++ collect_local_variables e)) ->
      repr_val_LambdaANF_Codegen (Vfun (M.empty _) fds f) sr fr (Val_funidx idx)

with repr_val_constr_args_LambdaANF_Codegen : list LambdaANF.cps.val ->
                                              store_record ->
                                              frame ->
                                              immediate ->
                                              Prop :=
     | Rnil_l: forall sr fr addr,
        repr_val_constr_args_LambdaANF_Codegen nil sr fr addr

     | Rcons_l: forall v wal vs sr fr m addr gmp,
        (* store_record contains memory *)
        List.nth_error sr.(s_mems) 0 = Some m ->

        sglob_val (host_function:=host_function) sr (f_inst fr) global_mem_ptr =
          Some (VAL_int32 (nat_to_i32 gmp)) ->
        (-1 < Z.of_nat gmp < Wasm_int.Int32.modulus)%Z ->
        (addr + 4 <= gmp) ->

        (* constr arg is ptr related to value v *)
        load_i32 m (N.of_nat addr) = Some (VAL_int32 (wasm_value_to_i32 wal)) ->
        repr_val_LambdaANF_Codegen v sr fr wal ->

        (* following constr args are also related *)
        repr_val_constr_args_LambdaANF_Codegen vs sr fr (4 + addr) ->
        repr_val_constr_args_LambdaANF_Codegen (v::vs) sr fr addr.

Scheme repr_val_LambdaANF_Codegen_mut := Induction for repr_val_LambdaANF_Codegen Sort Prop
  with repr_val_constr_args_LambdaANF_Codegen_mut :=
    Induction for repr_val_constr_args_LambdaANF_Codegen Sort Prop.


(* ENVIRONMENT RELATION (also named memory relation in C-backend)*)

Definition stored_in_locals {lenv} (x : cps.var) (v : wasm_value) (f : frame ) :=
  exists i,
  (forall err, translate_var nenv lenv x err = Ret i) /\
  List.nth_error f.(f_locs) i = Some (VAL_int32 (wasm_value_to_i32 v)).

Definition rel_env_LambdaANF_Codegen {lenv} (e : exp) (rho : LambdaANF.eval.env)
                    (sr : store_record) (fr : frame) (fds : fundefs) :=
        (forall x f v ,
            rho ! x = Some v ->
             (* f is var in fds, v is either a Vfun or Vconstr value *)
            subval_or_eq (Vfun (M.empty _) fds f) v ->
            name_in_fundefs fds f)
        /\
        (forall f errMsg,
            name_in_fundefs fds f ->
            (* i is index of function f *)
            exists i, translate_var nenv fenv f errMsg = Ret i /\
            (* function def is related to function index *)
            repr_val_LambdaANF_Codegen (Vfun (M.empty _) fds f) sr fr (Val_funidx i))
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
               repr_val_LambdaANF_Codegen v sr fr w)).

End RELATION.

Section THEOREM.

Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show.
Import Common.compM Common.Pipeline_utils.
Import bytestring.
Import ExtLib.Structures.Monad MonadNotation.
Import ssreflect ssrbool.

Import host datatypes_properties operations opsem interpreter_func properties common.

Import Lia.
Import Relations.Relation_Operators.

Variable cenv:LambdaANF.cps.ctor_env.
Variable funenv:LambdaANF.cps.fun_env.
Variable fenv : CodegenWASM.LambdaANF_to_WASM.fname_env.
Variable nenv : LambdaANF.cps_show.name_env.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
(*Let administrative_instruction := administrative_instruction host_function.*)
Let host_state := host_state host_instance.
Let reduce_trans := @reduce_trans host_function host_instance.


(* TODO: move this to cps_util *)
Definition Forall_constructors_in_e (P: var -> ctor_tag -> list var -> Prop) (e:exp) :=
  forall x t  ys e',
    subterm_or_eq (Econstr x t ys e') e -> P x t ys.


Definition Forall_projections_in_e (P: var -> ctor_tag -> N -> var -> Prop) (e:exp) :=
  forall x t n v e',
    subterm_or_eq (Eproj x t n v e') e -> P x t n v.

(* Note: the fundefs in P is the whole bundle, not the rest of the list *)
Definition Forall_functions_in_e (P: var -> fun_tag -> list var -> exp -> fundefs -> Prop) (e:exp) :=
  forall fds e' f t xs e'',  subterm_or_eq (Efun fds e') e ->
                             fun_in_fundefs fds (f, t, xs, e'') ->
                             P f t xs e'' fds.


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

Definition correct_cenv_of_caselist: ctor_env -> list (ctor_tag * exp) -> Prop :=
  fun cenv cl =>
    Forall_exp_in_caselist (correct_cenv_of_exp cenv) cl.

Lemma correct_cenv_of_case:
  forall cenv v l,
    correct_cenv_of_exp cenv (Ecase v l) ->
    correct_cenv_of_caselist cenv l.
Proof.
  intros; intro; intros.
  eapply Forall_constructors_subterm. apply H.
  constructor. econstructor. eauto.
Qed.


Lemma subterm_exists_witness : forall x t ys e v l,
  subterm_or_eq (Econstr x t ys e) (Ecase v l) ->
  exists a b, In (a, b) l /\ subterm_or_eq (Econstr x t ys e) b.
Proof.
  intros.
  apply clos_rt_rtn1 in H. inv H. inv H0. eexists. exists y. split. eassumption.
  unfold subterm_or_eq. eapply clos_rtn1_rt. assumption.
Qed.

Lemma subterm_witness_subterm : forall v l a e,
  In (a, e) l ->
  subterm_or_eq e (Ecase v l).
Proof.
  intros. constructor. econstructor. eassumption.
Qed.

Lemma subterm_case_list : forall x t ys e   v l c e',
  subterm_or_eq (Econstr x t ys e) (Ecase v l) ->
  subterm_or_eq (Econstr x t ys e) (Ecase v ((c, e') :: l)).
Proof.
  intros. apply subterm_exists_witness in H. destruct H as [a [b [H1 H2]]].
  eapply rt_trans. eassumption. eapply subterm_witness_subterm.
  cbn. right. eassumption.
Qed.

Lemma correct_cenv_case_drop_clause : forall l v c e,
  correct_cenv_of_exp cenv (Ecase v ((c, e) :: l)) ->
  correct_cenv_of_exp cenv (Ecase v l).
Proof.
  unfold correct_cenv_of_exp. unfold Forall_constructors_in_e. intros.
  eapply H. eapply subterm_case_list. eassumption.
Qed.

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

Open Scope list.

Lemma pass_function_args_correct {lenv} : forall l instr,
 pass_function_args nenv lenv fenv l = Ret instr ->
 @repr_fun_args_Codegen fenv nenv lenv l instr.
Proof.
  induction l; intros.
  - cbn in H.  inv H. constructor.
  - cbn in H. destruct (instr_local_var_read nenv lenv fenv a) eqn:Hvar. inv H.
    destruct (pass_function_args nenv lenv fenv l) eqn:prep. inv H. inv H.
    unfold instr_local_var_read in Hvar.
    destruct (is_function_var fenv a) eqn:Hfname.
    - destruct (translate_var nenv fenv a _) eqn:fun_var; inv Hvar.
            constructor. econstructor. eassumption.
        apply IHl; auto.
    - destruct (translate_var  nenv lenv a _) eqn:var_var; inv Hvar.
            constructor.  econstructor. eassumption. apply IHl; auto.
Qed.

Lemma set_nth_constr_arg_correct {lenv} : forall  l instr n,
  set_constructor_args nenv lenv fenv l n = Ret instr ->
  Forall_statements_in_seq' (@set_nth_constr_arg fenv nenv lenv) l instr n.
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

  replace ((nat_to_value (S (n + S (n + S (n + S (n + 0))))))) with
          ((nat_to_value ((1 + n) * 4))). constructor.
  unfold instr_local_var_read in Hvar.
  destruct (is_function_var fenv a) eqn:Hfn.
  - destruct (translate_var nenv fenv a _) eqn:Hvar'. inv Hvar. inv Hvar.
    constructor. econstructor. eassumption.
  - destruct (translate_var nenv lenv a _) eqn:Hloc. inv Hvar. inv Hvar.
    constructor. econstructor. unfold translate_var. eassumption. f_equal. lia.
Qed.

Import seq.

Theorem translate_exp_correct {lenv} :
    forall e instructions,
      correct_cenv_of_exp cenv e ->
    translate_exp nenv cenv lenv fenv e = Ret instructions ->
    @repr_expr_LambdaANF_Codegen cenv fenv nenv lenv e instructions.
Proof.
  induction e using exp_ind'; intros instr Hcenv; intros.
  - (* Econstr *)
    simpl in H.
    destruct (translate_exp nenv cenv lenv fenv e) eqn:H_eqTranslate; inv H.
    destruct (translate_var nenv lenv v _) eqn:H_translate_var. inv H1.
    destruct l as [|v0 l'].
    (* Nullary constructor *)
    { inv H1.
      eapply Rconstr_e with (e':=l0) (x':=i); eauto.
      apply IHe; auto.
      assert (subterm_e e (Econstr v t [] e) ). { constructor; constructor. }
      eapply Forall_constructors_subterm. eassumption. assumption.
      econstructor; eauto.
      eapply Rconstr_asgn_unboxed.
      apply Forall_constructors_in_constr in Hcenv.
      destruct (cenv ! t) eqn:Hc; auto. destruct c. inv Hcenv.
      unfold get_ctor_arity. now rewrite Hc.
    } (* Non-nullary constructor *)
    { remember (v0 :: l') as l.
      destruct (store_constructor nenv cenv lenv fenv t l) eqn:store_constr.
      inv H1. inv H1. cbn.
      repeat match goal with
             |- context C [?x :: ?l] =>
             lazymatch l with [::] => fail | _ => rewrite <-(cat1s x l) end
             end.
      rename i into v'.
      replace ([:: BI_get_global global_mem_ptr] ++
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
                             [:: BI_set_global result_out_of_mem])
                            [::]])
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
          destruct (set_constructor_args nenv lenv fenv (v0 :: l') 0) eqn:Hconstrargs. inv store_constr.
          remember (grow_memory_if_necessary page_size) as grow.
          inversion store_constr.

          replace ([:: BI_get_global constr_alloc_ptr, BI_set_local v' & l0]) with
            ([:: BI_get_global constr_alloc_ptr; BI_set_local v'] ++ l0) by reflexivity.

          replace ([:: BI_get_global global_mem_ptr, BI_set_global constr_alloc_ptr,
                      BI_get_global global_mem_ptr, BI_const (N_to_value page_size),
                      BI_binop T_i32 (Binop_i BOI_add), BI_set_global global_mem_ptr,
                      BI_get_global constr_alloc_ptr, BI_const (nat_to_value (Pos.to_nat t)),
                      BI_store T_i32 None 2%N 0%N
                      & l]) with ([:: BI_get_global global_mem_ptr; BI_set_global constr_alloc_ptr;
                                    BI_get_global global_mem_ptr; BI_const (N_to_value page_size);
                                    BI_binop T_i32 (Binop_i BOI_add); BI_set_global global_mem_ptr] ++
                                     [BI_get_global constr_alloc_ptr; BI_const (nat_to_value (Pos.to_nat t));
                                      BI_store T_i32 None 2%N 0%N] ++ l) by reflexivity.

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
                      & l]) with ([ BI_get_global global_mem_ptr;
                                     BI_set_global constr_alloc_ptr ] ++ [
                                       BI_get_global constr_alloc_ptr; BI_const (nat_to_value (Pos.to_nat t));
                                       BI_store T_i32 None 2%N 0%N;
                                       BI_get_global global_mem_ptr;
                                       BI_const (nat_to_value 4);
                                       BI_binop T_i32 (Binop_i BOI_add);
                                       BI_set_global global_mem_ptr
                                     ] ++ l) by reflexivity.
          repeat rewrite <- app_assoc.
          eapply Rconstr_e with (e' := l0); eauto.
          apply IHe.
          assert (subterm_e e (Econstr v t (v0 :: l') e) ). { constructor; constructor. }
          eapply Forall_constructors_subterm. eassumption. assumption. reflexivity.
          econstructor. eassumption.
          apply Forall_constructors_in_constr in Hcenv; auto.
          destruct (cenv ! t) eqn:Hc. 2:auto. destruct c. inv Hcenv.
          apply Rconstr_asgn_boxed with (arity:=S (length l')); eauto.
          unfold get_ctor_arity. rewrite Hc. f_equal. cbn. lia. lia.
          apply set_nth_constr_arg_correct.
          replace ([:: v0] ++ l') with (v0 :: l') by reflexivity.
          assumption.
    }
  - (* Ecase nil *) simpl in H. destruct (translate_var nenv lenv v _) eqn:Hvar.
                    inv H. inv H. constructor.
  - (* Ecase const *) {
    simpl in H.
    destruct (translate_var nenv lenv v _) eqn:Hvar. inv H.
    destruct (translate_exp nenv cenv lenv fenv e) eqn:Hexp. inv H.
    destruct (get_ctor_arity cenv c) eqn:Harity. inv H.
    destruct (_ i l) eqn:Hprep. inv H. inv H.
    destruct n; cbn.
    { (* unboxed *)
      constructor. econstructor. eassumption. apply IHe0.
      eapply correct_cenv_case_drop_clause. eassumption.
      unfold translate_exp. rewrite Hvar. cbn. now rewrite Hprep.
      apply IHe; auto. eapply Forall_constructors_subterm; eauto.
      constructor. econstructor. cbn. left; eauto. assumption.
    } { (* boxed *)
      econstructor. econstructor. eassumption. apply IHe0.
      eapply correct_cenv_case_drop_clause. eassumption.
      unfold translate_exp. rewrite Hvar. cbn. now rewrite Hprep.
      apply IHe; auto. eapply Forall_constructors_subterm; eauto.
      constructor. econstructor. cbn. left; eauto. eassumption. lia.
      }
    }
  - (* Eproj *) {
    simpl in H.
    destruct (translate_exp nenv cenv lenv fenv e) eqn:He. inv H.
    destruct (translate_var nenv lenv v0 _) eqn:Hy. inv H.
    destruct (translate_var nenv lenv v _) eqn:Hx. inv H.
    injection H => instr'. subst. clear H. constructor. apply IHe; auto.
    unfold correct_cenv_of_exp in Hcenv.
    eapply Forall_constructors_subterm. eassumption.
    unfold subterm_e. constructor. constructor.
    econstructor; eauto. econstructor; eauto. }
  - (* Eletapp *) {
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
    - destruct (translate_var nenv fenv f _) eqn:fun_var; inv Hloc.
      constructor. econstructor. eassumption.
    - destruct (translate_var  nenv lenv f _) eqn:var_var; inv Hloc.
      constructor. econstructor. eassumption. }
  - (* Efun *) inv H.
  - (* Eapp *) {
    simpl in H. unfold translate_call in H.
    destruct (pass_function_args nenv lenv fenv l) eqn:Hargs. inv H.
    destruct (instr_local_var_read nenv lenv fenv v) eqn:Hloc. inv H. inv H. constructor.
    apply pass_function_args_correct. assumption.
    unfold instr_local_var_read in Hloc.
    destruct (is_function_var fenv v) eqn:Hfname.
    - destruct (translate_var nenv fenv v _) eqn:fun_var; inv Hloc.
      constructor. econstructor. eassumption.
    - destruct (translate_var  nenv lenv v _) eqn:var_var; inv Hloc.
      constructor. econstructor. eassumption. }
  - (* Eprim *)
    inv H. inv H.
  - (* Ehalt *)
    simpl in H. destruct (translate_var nenv lenv v _) eqn:Hvar. inv H.
    injection H => instr'. subst. constructor. econstructor. eauto.
Qed.

Definition result_val_LambdaANF_Codegen (val : LambdaANF.cps.val)
                                        (sr : store_record) (fr : frame) : Prop :=

     (exists res_i32 wasmval,
       (* global var *result_var* contains correct return value *)
       sglob_val sr (f_inst fr) result_var = Some (VAL_int32 res_i32)
         /\ wasm_value_to_i32 wasmval = res_i32
         /\ repr_val_LambdaANF_Codegen cenv fenv nenv  _ val sr fr wasmval
         /\ (sglob_val sr (f_inst fr) result_out_of_mem = Some (nat_to_value 0)))
  \/ (sglob_val sr (f_inst fr) result_out_of_mem = Some (nat_to_value 1)).

Lemma i32_exists_nat : forall (x : i32),
  exists n, x = nat_to_i32 n /\ (-1 < Z.of_nat n <  Wasm_int.Int32.modulus)%Z.
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

Lemma val_relation_depends_on_finst : forall v sr fr fr' value,
    f_inst fr = f_inst fr' ->
    repr_val_LambdaANF_Codegen cenv fenv nenv host_function v sr fr value ->
    repr_val_LambdaANF_Codegen cenv fenv nenv host_function v sr fr' value.
Proof.
  intros. inv H0.
  { (* unboxed constructor value *) by constructor. }
  { (* boxed constructor value *)
    have indPrinciple := repr_val_constr_args_LambdaANF_Codegen_mut cenv fenv nenv host_function
    (fun (v : cps.val) (s : datatypes.store_record host_function) (f : frame) (w : wasm_value)
         (H: repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s f w) =>
         (forall f',
            f_inst f = f_inst f' ->
            repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s f' w)
    )
    (fun (l : seq cps.val) (s : datatypes.store_record host_function) (f : frame) (i : immediate)
         (H: repr_val_constr_args_LambdaANF_Codegen cenv fenv nenv host_function l s f i) =>
         (forall f',
                f_inst f = f_inst f' ->
                repr_val_constr_args_LambdaANF_Codegen cenv fenv nenv host_function l s f' i)
    ).
    have H10' := H10. eapply indPrinciple in H10; intros; clear indPrinciple; try eassumption.
    { econstructor; eauto. congruence. }
    { econstructor; eauto. }
    { econstructor; eauto. congruence. }
    { econstructor; eauto. rewrite -H0. eassumption. }
    { econstructor; eauto. }
    { econstructor; eauto. congruence. }
  }
  (* function *)
  { econstructor; eauto. rewrite -H. eassumption. }
Qed.

Lemma val_relation_func_depends_on_funcs : forall val s s' f i,
  s_funcs s = s_funcs s' ->
  repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s f (Val_funidx i) ->
  repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s' f (Val_funidx i).
Proof.
  intros ? ? ? ? ? Hfuncs Hval.
  inv Hval. now econstructor; eauto.
Qed.

Lemma val_relation_depends_on_mem_smaller_than_gmp_and_funcs :
  forall v sr sr' m m' fr fr' gmp gmp' value,
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

    repr_val_LambdaANF_Codegen cenv fenv nenv host_function v sr fr value ->
    repr_val_LambdaANF_Codegen cenv fenv nenv host_function v sr' fr' value.
Proof.
  intros. inv H9.
  (* Nullary constructor value *)
  { now constructor.  }
  (* Non-nullary constructor value *)
  {
  have indPrinciple := repr_val_constr_args_LambdaANF_Codegen_mut cenv fenv nenv host_function
  (fun (v : cps.val) (s : datatypes.store_record host_function) (f : frame) (w : wasm_value)
       (H: repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s f w) =>
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
              repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s' f' w)
    )
  (fun (l : seq cps.val) (s : datatypes.store_record host_function) (f : frame) (i : immediate)
       (H: repr_val_constr_args_LambdaANF_Codegen cenv fenv nenv host_function l s f i) =>
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
             repr_val_constr_args_LambdaANF_Codegen cenv fenv nenv host_function l s' f' i)
  ). have H19' := H19.
    eapply indPrinciple in H19; intros; clear indPrinciple; try eassumption; try lia.
    { assert (gmp = gmp0). { assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp0) by congruence.
                             inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H17; try lia.
                             rewrite Wasm_int.Int32.Z_mod_modulus_id in H17; lia. } subst gmp0.
      assert (m = m0) by congruence; subst m0.
      econstructor; try eassumption. lia. lia. reflexivity.
      rewrite <- H8. assumption. lia. }
    { now constructor. }
    { assert (gmp = gmp0). { assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp0) by congruence.
                             inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H30; try lia.
                             rewrite Wasm_int.Int32.Z_mod_modulus_id in H30; lia. } subst gmp0.
      assert (gmp = gmp1). { assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp1) by congruence.
                             inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H30; try lia.
                             rewrite Wasm_int.Int32.Z_mod_modulus_id in H30; lia. } subst gmp1.
      assert (m = m0) by congruence. subst m0.
      assert (m1 = m2) by congruence. subst m2. subst.
      econstructor; eauto. lia. rewrite <- H28; auto; try lia. }
    { econstructor; eauto. congruence. }
    { econstructor. }
    { assert (gmp = gmp0). {
         assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp0) by congruence.
              inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H31; try lia.
              rewrite Wasm_int.Int32.Z_mod_modulus_id in H31; lia. } subst gmp0.
      econstructor; eauto. lia. assert (gmp1 = gmp). {
         assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp1) by congruence.
              inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H31; try lia.
              rewrite Wasm_int.Int32.Z_mod_modulus_id in H31; lia. } subst. lia.
      rewrite <- H29. assert (m1 = m2) by congruence. subst m2. eassumption.
      assert (gmp1 = gmp). {
                 assert (Ht: nat_to_i32 gmp = nat_to_i32 gmp1) by congruence.
                 inv Ht. rewrite Wasm_int.Int32.Z_mod_modulus_id in H31; try lia.
                 rewrite Wasm_int.Int32.Z_mod_modulus_id in H31; lia. } subst gmp1. lia.
      eapply H9; eauto; lia. }
    { assert (m = m0) by congruence. subst m0. lia. }
    { assert (m = m0) by congruence; subst m0. apply H8. lia. }
  }
  (* function *)
  { econstructor; eauto. rewrite <- H0. rewrite -H. eassumption. }
Qed.

Lemma result_val_LambdaANF_Codegen_depends_on_finst : forall val s f f',
  f_inst f = f_inst f' ->
  result_val_LambdaANF_Codegen val s f ->
  result_val_LambdaANF_Codegen val s f'.
Proof.
  intros ? ? ? ? Hfinst Hres.
  unfold result_val_LambdaANF_Codegen in *.
  destruct Hres as [[res [wal [H1 [H2 [H3 H4]]]]] | Hres].
  { left. exists res, wal. repeat (split; try congruence).
  eapply val_relation_depends_on_finst; eassumption. }
  { right. congruence. }
Qed.

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
  (N.of_nat gmp_v + 4 <= mem_length m)%N.

Definition INV_constr_alloc_ptr_in_linear_memory s f := forall addr t m,
  @sglob_val host_function s (f_inst f) constr_alloc_ptr = Some (VAL_int32 addr) ->
  exists m', store m (Wasm_int.N_of_uint i32m addr) 0%N
                     (bits (nat_to_value (Pos.to_nat t))) (t_length T_i32) = Some m'.

Definition INV_locals_all_i32 f := forall i v,
  nth_error (f_locs f) i = Some v -> exists v', v = (VAL_int32 v').

Definition INV_num_functions_upper_bound sr :=
  (Z.of_nat (length (@s_funcs host_function sr)) < Wasm_int.Int32.modulus)%Z.

Definition INV_inst_globs_nodup f :=
  NoDup (inst_globs (f_inst f)).

Definition INV_table_id sr fr :=
  forall f i errMsg,
    translate_var nenv fenv f errMsg = Ret i ->
    stab_addr (host_function:=host_function) sr fr
      (Wasm_int.nat_of_uint i32m (nat_to_i32 i)) = Some i.

Definition INV_var_idx_inbounds (lenv : localvar_env) fr :=
  forall var varIdx, repr_var (lenv:=lenv) nenv var varIdx ->
                           varIdx < length (f_locs fr).

Definition INV_fvar_idx_inbounds sr :=
  forall fvar fIdx, repr_funvar fenv nenv fvar fIdx ->
                    fIdx < length (s_funcs (host_function:=host_function) sr).

Definition INV_types sr fr :=
  forall i, (Z.of_nat i <= max_function_args)%Z ->
            stypes (host_function:=host_function) sr (f_inst fr) i =
              Some (Tf (List.repeat T_i32 i) [::]).

(* invariants that need to hold throughout the execution of the Wasm program,
   doesn't hold anymore when memory runs out -> just abort  *)

Definition INV (lenv : localvar_env) (* also depends on fenv *)
               (s : store_record)
               (f : frame) :=
    INV_result_var_writable s f
 /\ INV_result_var_out_of_mem_writable s f
 /\ INV_result_var_out_of_mem_is_zero s f
 /\ INV_global_mem_ptr_writable s f
 /\ INV_constr_alloc_ptr_writable s f
 /\ INV_globals_all_mut_i32 s
 /\ INV_linear_memory s f
 /\ INV_global_mem_ptr_in_linear_memory s f
 /\ INV_locals_all_i32 f
 /\ INV_num_functions_upper_bound s
 /\ INV_inst_globs_nodup f
 /\ INV_table_id s f
 /\ INV_var_idx_inbounds lenv f
 /\ INV_types s f.


Lemma set_nth_nth_error_same : forall {X:Type} (l:seq X) e e' i vd,
    nth_error l i = Some e ->
    nth_error (set_nth vd l i e') i = Some e'.
Proof.
  intros. generalize dependent e'. generalize dependent l.
  generalize dependent vd. generalize dependent e. induction i; intros.
  - inv H. destruct l; inv H1. reflexivity.
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

Lemma notNone_Some {A} : forall (o : option A),
  o <> None <-> exists v, o = Some v.
Proof.
  intros. destruct o; split; intros.
  eauto. congruence. contradiction. now destruct H.
Qed.

(** The lemmas [r_eliml] and [r_elimr] are relicts from ancient times,
    kept for compatability for now, TODO rework (use new context representation) **)
Lemma r_eliml: forall hs s f es hs' s' f' es' lconst,
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


Lemma update_global_get_same : forall sr sr' i val fr,
  supdate_glob sr (f_inst fr) i (VAL_int32 val) = Some sr' ->
     @sglob_val host_function sr' (f_inst fr) i = Some (VAL_int32 val).
Proof.
  unfold supdate_glob, supdate_glob_s, sglob_val, sglob, sglob_ind. cbn. intros.
  destruct (nth_error (inst_globs (f_inst fr)) i) eqn:H1. 2: inv H. cbn in H.
  destruct (nth_error (s_globals sr) g) eqn:H2. 2: inv H. inv H. cbn.
  erewrite set_nth_nth_error_same; auto. eassumption.
Qed.

Lemma update_global_get_other : forall i j sr sr' fr num val,
  INV_inst_globs_nodup fr ->
  i <> j ->
  sglob_val sr (f_inst fr) i = Some (VAL_int32 val) ->
  supdate_glob sr (f_inst fr) j (VAL_int32 num) = Some sr' ->
  @sglob_val host_function sr' (f_inst fr) i = Some (VAL_int32 val).
Proof.
  intros ? ? ? ? ? ? ? Hnodup Hneq Hr Hw.
    unfold supdate_glob, sglob_ind, supdate_glob_s in *.
    destruct (nth_error (inst_globs (f_inst fr)) j) eqn:Heqn. 2: inv Hw. cbn in Hw.
    destruct (nth_error (s_globals sr) g) eqn:Heqn'. 2: inv Hw. inv Hw.
    unfold sglob_val, sglob, sglob_ind in *.
    destruct (nth_error (inst_globs (f_inst fr)) i) eqn:Heqn''.  2: inv Hr.
    cbn. cbn in Hr.
    assert (g <> g1). {
      intro. subst. rewrite <- Heqn'' in Heqn.
      apply Hneq. eapply NoDup_nth_error; eauto.
      apply nth_error_Some. congruence. }
    erewrite set_nth_nth_error_other; auto.
     assert (g < length (s_globals sr)) as Hl. { apply nth_error_Some. intro. congruence. }
    lia.
Qed.

Lemma update_global_preserves_memory : forall sr sr' fr v j,
  @supdate_glob host_function sr (f_inst fr) j v = Some sr' ->
    sr.(s_mems) = sr'.(s_mems).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H. cbn in H.
  destruct (nth_error (inst_globs (f_inst fr)) j). 2: inv H. cbn in H.
  destruct (nth_error (s_globals sr) g). inv H. reflexivity. inv H.
Qed.

Lemma update_global_preserves_funcs : forall sr sr' fr v j,
  @supdate_glob host_function sr (f_inst fr) j v = Some sr' ->
    sr.(s_funcs) = sr'.(s_funcs).
Proof.
  intros.
  unfold supdate_glob, supdate_glob_s, sglob_ind in H. cbn in H.
  destruct (nth_error (inst_globs (f_inst fr)) j). 2: inv H. cbn in H.
  destruct (nth_error (s_globals sr) g). inv H. reflexivity. inv H.
Qed.

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

Lemma update_global_preserves_num_functions_upper_bound : forall j sr sr' f  num,
  INV_num_functions_upper_bound sr ->
  supdate_glob sr (f_inst f) j (VAL_int32 num) = Some sr' ->
  INV_num_functions_upper_bound sr'.
Proof.
  unfold INV_num_functions_upper_bound. intros.
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
  (j = global_mem_ptr -> num + 4 < N.to_nat (mem_length m)) ->
  @supdate_glob host_function sr (f_inst f) j (VAL_int32 (nat_to_i32 num)) = Some sr' ->
  INV_global_mem_ptr_in_linear_memory sr' f.
Proof.
  unfold INV_global_mem_ptr_in_linear_memory.
  intros ? ? ? ? ? ? Hinv Hnodup Hmem Hnum Hcond Hupd ? ? Hm Hglob Hunbound.
  assert (m = m0). { apply update_global_preserves_memory in Hupd. congruence. }
  subst m0. destruct (Nat.eq_dec j global_mem_ptr).
  { (* g = global_mem_ptr *)
     subst. have H' := update_global_get_same _ _ _ _ _ Hupd.
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
  (j = global_mem_ptr -> num + 4 < N.to_nat (mem_length m)) ->
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
  (j = global_mem_ptr -> num + 4 < N.to_nat (mem_length m)) ->
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

Corollary update_global_preserves_INV : forall lenv sr sr' i f m num,
  INV lenv sr f ->
  (* if result_out_of_mem is set, INV doesn't need to hold anymore *)
  result_out_of_mem <> i ->
  (* if updated gmp, new value in mem *)
  nth_error (s_mems sr) 0 = Some m ->
  (-1 < Z.of_nat num < Wasm_int.Int32.modulus)%Z ->
  (i = global_mem_ptr -> num + 4 < N.to_nat (mem_length m)) ->
  (* upd. global var *)
  supdate_glob (host_function:=host_function) sr (f_inst f) i
             (VAL_int32 (nat_to_i32 num)) = Some sr' ->
  INV lenv sr' f.
Proof with eassumption.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_result_var_out_of_mem_is_zero...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_global_var_w...
  split. eapply update_global_preserves_globals_all_mut_i32...
  split. eapply update_global_preserves_linear_memory...
  split. eapply update_global_preserves_global_mem_ptr_in_linear_memory...
  split. assumption.
  split. eapply update_global_preserves_num_functions_upper_bound...
  split. assumption.
  split. eapply update_global_preserves_table_id...
  split. assumption.
  eapply update_global_preserves_types...
Qed.

Corollary update_local_preserves_INV : forall lenv sr f f' x' v,
  INV lenv sr f ->
  x' < length (f_locs f) ->
  f' = {| f_locs := set_nth (VAL_int32 v) (f_locs f) x' (VAL_int32 v)
        ; f_inst := f_inst f
        |} ->
  INV lenv sr f'.
Proof with eauto.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]. subst.
  repeat (split; auto).
  { unfold INV_locals_all_i32 in *. cbn. intros.
    destruct (Nat.eq_dec x' i).
    (* i=x' *) subst. apply nth_error_Some in H0. apply notNone_Some in H0. destruct H0.
    erewrite set_nth_nth_error_same in H1; eauto. inv H1. eauto.
    (* i<>x' *) rewrite set_nth_nth_error_other in H1; auto. apply H9 in H1. assumption. }
  { unfold INV_var_idx_inbounds. intros.
    apply H13 in H1. cbn. rewrite length_is_size size_set_nth -length_is_size maxn_nat_max.
    lia. }
Qed.

Corollary change_locals_preserves_INV : forall lenv_old lenv sr f f' l,
  INV lenv_old sr f ->
  INV_var_idx_inbounds lenv f' ->
  INV_locals_all_i32 f' ->
  f' = {| f_locs := l
        ; f_inst := f_inst f
        |} ->
  INV lenv sr f'.
Proof with eauto.
  intros. unfold INV. destruct H as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]]. subst.
  repeat (split; auto).
Qed.

Corollary init_locals_preserves_INV : forall lenv_old lenv sr f f' args n,
  INV lenv_old sr f ->
  (forall var varIdx, repr_var (lenv:=lenv) nenv var varIdx ->
                      varIdx < Datatypes.length args + n) ->
  f' = {| f_locs := [seq nat_to_value i | i <- args] ++
                      repeat (nat_to_value 0) n
        ; f_inst := f_inst f
        |} ->
  INV lenv sr f'.
Proof with eauto.
  intros. subst.
  eapply change_locals_preserves_INV; eauto.
  { unfold INV_var_idx_inbounds. intros. apply H0 in H1. rewrite app_length.
    now rewrite length_is_size size_map -length_is_size repeat_length. }
  { unfold INV_locals_all_i32 in *. cbn. intros.
    destruct (Nat.ltb_spec i (length args)).
    { (* i < length args *)
      rewrite nth_error_app1 in H1. 2: {
         now rewrite length_is_size size_map -length_is_size. }
      apply nth_error_In in H1.
      apply in_map_iff in H1. destruct H1 as [x [Heq Hin]]. subst.
      eexists. reflexivity. }
    { (* i >= length args *)
      assert (Hlen: i < Datatypes.length ([seq nat_to_value i | i <- args]
                                          ++ repeat (nat_to_value 0) n)). {
        apply nth_error_Some. congruence. }
      rewrite app_length length_is_size size_map -length_is_size repeat_length in Hlen.
      rewrite nth_error_app2 in H1. 2: {
        now rewrite length_is_size size_map -length_is_size. }
      have H' := H1.
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
  assert (N.of_nat gmp_v + 4 <= mem_length m)%N. { apply H; auto. } lia.
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

Lemma update_mem_preserves_num_functions_upper_bound : forall s s' m vd,
   INV_num_functions_upper_bound s  ->
   upd_s_mem s (set_nth vd (s_mems s) 0 m) = s' ->
   INV_num_functions_upper_bound s'.
Proof.
  unfold INV_num_functions_upper_bound. intros. subst. cbn. assumption.
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

Corollary update_mem_preserves_INV : forall lenv s s' f m m' vd,
  INV lenv s f ->
  nth_error (s_mems s) 0  = Some m ->
  (mem_length m' >= mem_length m)%N ->
  mem_max_opt m' = Some max_mem_pages ->
  (exists size, mem_size m' = size /\ size <= max_mem_pages)%N ->
  upd_s_mem s (set_nth vd (s_mems s) 0 m') = s' ->
  INV lenv s' f.
Proof with eassumption.
  intros. unfold INV.
  destruct H as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_result_var_out_of_mem_is_zero...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_global_var_w...
  split. eapply update_mem_preserves_all_mut_i32...
  split. eapply update_mem_preserves_linear_memory...
  split. eapply update_mem_preserves_global_mem_ptr_in_linear_memory...
  split. assumption.
  split. eapply update_mem_preserves_num_functions_upper_bound...
  split. assumption.
  split. eapply update_mem_preserves_table_id...
  split. assumption.
  eapply update_mem_preserves_types...
Qed.

Import ssreflect.

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
         | |- reduce _ _ _ ([:: ?instr] ++ ?l3) _ _ _ ?l4 => apply r_elimr
          end
  | 1 => lazymatch goal with
         | |- reduce _ _ _ ([::AI_basic (BI_const ?c1)] ++
                            [::AI_basic ?instr] ++ ?l3) _ _ _ ?l4 =>
            assert ([:: AI_basic (BI_const c1)] ++ [:: AI_basic instr] ++ l3
                  = [:: AI_basic (BI_const c1);
                        AI_basic instr] ++ l3) as H by reflexivity; rewrite H;
                                                       apply r_elimr; clear H
          end
  | 2 => lazymatch goal with
         | |- reduce _ _ _ ([::AI_basic (BI_const ?c1)] ++
                            [::AI_basic (BI_const ?c2)] ++
                            [::AI_basic ?instr] ++ ?l3) _ _ _ ?l4 =>
            assert ([:: AI_basic (BI_const c1)] ++ [:: AI_basic (BI_const c2)] ++
                    [:: AI_basic instr] ++ l3 =
                    [:: AI_basic (BI_const c1); AI_basic (BI_const c2)
                    ;   AI_basic instr] ++ l3) as H by reflexivity; rewrite H;
                                                       apply r_elimr; clear H
          end
  end.

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
  generalize dependent state. generalize dependent sr. generalize dependent fr.
  generalize dependent fr'. generalize dependent sr'. revert instructions hs hs'.
  induction H; intros; subst.
  - inv Heqx. constructor. constructor. now apply rs_label_const.
  - destruct y as [[[? ?] ?] ?].
    assert ((s, s0, f, l) = (s, s0, f, l)) as H' by reflexivity.
    eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[instr])). eapply rt_step.
    eapply r_label with (es:=instructions) (k:=1) (lh:= (LH_rec [] 0 [] (LH_base [] []) [])).
    apply H. cbn. rewrite cats0. reflexivity.
    cbn. reflexivity. rewrite cats0.
    now eapply IHclos_refl_trans_1n.
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

Ltac dostep :=
  eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s] ++ ?[t]));
  first apply rt_step; separate_instr.

(* only returns single list of instructions *)
Ltac dostep' :=
   eapply rt_trans with (y := (?[hs], ?[sr], ?[f'], ?[s]));
   first apply rt_step; separate_instr.

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
  repr_val_LambdaANF_Codegen cenv fenv nenv host_function v sr fr wal ->
 (-1 < Z.of_nat (wasm_value_to_immediate wal) < Wasm_int.Int32.modulus)%Z.
Proof.
  intros ? ? ? ? Hinv H.
  inv H.
  (* - (* constr. value *) cbn. lia. *)
  (* - (* function value *) cbn. *)
  (*   assert (idx < length (s_funcs sr)). { apply nth_error_Some. congruence. } *)
  (*   unfold INV_num_functions_upper_bound in Hinv. lia. *)
Admitted. (* Qed. *)

Lemma extract_constr_arg : forall n vs v sr fr addr m,
  INV_num_functions_upper_bound sr ->
  nthN vs n = Some v ->
  nth_error (s_mems sr) 0 = Some m ->
  (* addr points to the first arg after the constructor tag *)
  repr_val_constr_args_LambdaANF_Codegen cenv fenv nenv host_function vs sr fr addr ->
  exists bs wal, load m (N.of_nat addr + 4 * n) 0%N 4 = Some bs /\
             VAL_int32 (wasm_value_to_i32 wal) = wasm_deserialise bs T_i32 /\
             repr_val_LambdaANF_Codegen cenv fenv nenv host_function v sr fr wal.
Proof.
  intros n vs v sr fr addr m Hinv H H1 H2. generalize dependent v.
  generalize dependent n. generalize dependent m.
  induction H2; intros. 1: inv H.
  assert (n = N.of_nat (N.to_nat n)) by lia. rewrite H8 in H7. generalize dependent v0.
  induction (N.to_nat n); intros.
  - (* n = 0 *)
    inv H7. assert (m = m0) by congruence. subst m0. rewrite N.add_comm. unfold load_i32 in H3.
    destruct (load m (N.of_nat addr) 0%N 4) eqn:Hl; inv H3. exists b. exists wal.
    repeat split. rewrite <- Hl. reflexivity. unfold wasm_value_to_i32.
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
       end)%N with (N.of_nat n0)%N in H7.
    2: { destruct (N.succ (N.of_nat n0)) eqn:Heqn. lia.
         destruct (Pos.of_succ_nat n0) eqn:Har; lia. }
    edestruct IHrepr_val_constr_args_LambdaANF_Codegen. assumption.
    eassumption. eassumption. destruct H9 as [wal' [Hl [Heq Hval]]].
    exists x. exists wal'. split. rewrite -Hl. f_equal. lia. split; eauto.
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
                                  ml_data := ml_data (mem_data m) ++
                                             repeat (ml_init (mem_data m)) (Pos.to_nat 65536) |};
                   mem_max_opt := Some maxlim |})%N). {
     unfold mem_length, memory_list.mem_length. cbn. rewrite app_length. rewrite repeat_length.
     unfold mem_length, memory_list.mem_length in Ha. apply N.leb_le. lia. }
  rewrite Hlen.
  unfold mem_length, memory_list.mem_length in Ha.
  unfold mem_lookup.
  repeat rewrite nth_error_app1; try lia. reflexivity.
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

Definition max_constr_alloc_size := (max_constr_args * 4 + 4)%Z. (* in bytes *)

Lemma signed_upper_bound : forall x,
  (Wasm_int.Int32.signed (Wasm_int.Int32.repr x) < Wasm_int.Int32.half_modulus)%Z.
Proof.
  intros x.
  unfold Wasm_int.Int32.signed. destruct (zlt _ _); auto.
  unfold Wasm_int.Int32.unsigned in *. clear g.
  have H' := Wasm_int.Int32.Z_mod_modulus_range x. simpl_modulus_in H'. simpl_modulus. cbn. lia.
Qed.

Lemma mem_length_upper_bound : forall m,
  (mem_size m <= max_mem_pages)%N ->
  (mem_length m <= (max_mem_pages + 1) * page_size)%N.
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

Lemma memory_grow_reduce_need_grow_mem {lenv} : forall grow state s f gmp m,
  grow = grow_memory_if_necessary page_size ->
  INV lenv s f ->
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
   (state, s, f, [seq AI_basic i | i <- grow])
   (state, s', f, [])
   /\ s_funcs s = s_funcs s'
   /\ (forall wal val, repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s f wal ->
                       repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s' f wal)
   (* enough memory to alloc. constructor *)
   /\ ((INV lenv s' f /\
         (forall m v_gmp, nth_error (s_mems s') 0 = Some m ->
            @sglob_val host_function s' (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 v_gmp)) ->
            (Z.of_nat v_gmp < Wasm_int.Int32.modulus)%Z ->
            (Z.of_nat v_gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z))
       \/ (@sglob_val host_function s' (f_inst f) result_out_of_mem = Some (VAL_int32 (nat_to_i32 1)))).
Proof with eauto.
  (* grow memory if necessary *)
  intros grow state sr fr gmp m H Hinv Hgmp Hm HgmpBound HneedMoreMem. subst.
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
    dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
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
           (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z).
      apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
      have H'' := signed_upper_bound (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size).
      simpl_modulus_in H''. cbn. lia. cbn in H5. lia. }
    dostep. apply r_eliml; auto.
    elimr_nary_instr 0. eapply r_current_memory...

    dostep. elimr_nary_instr 2.
    constructor. apply rs_relop.

    dostep'. constructor. subst.
    rewrite HneedMoreMem. apply rs_if_true. intro H3'. inv H3'.

    dostep'. constructor. apply rs_block with (vs:=[])(n:= 0); auto.
    cbn.
    apply reduce_trans_label.
    dostep'. elimr_nary_instr 1. eapply r_grow_memory_success; eauto.
    dostep'. elimr_nary_instr 2. constructor. apply rs_relop. cbn.
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
      reflexivity. reflexivity. eassumption.
      cbn. destruct (s_mems sr). inv Hm2. reflexivity. eassumption.
      subst. apply mem_length_upper_bound in Hm5; cbn in Hm5. simpl_modulus; cbn; lia.
      rewrite <- Hgmp. reflexivity. subst.
      apply mem_length_upper_bound in Hm5; cbn in Hm5.
      apply mem_grow_increases_length in H4. simpl_modulus; cbn; lia. lia.
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
      assert (v_gmp = gmp). {
        assert (Hgl: sglob_val (upd_s_mem sr (m' :: l)) (f_inst fr) global_mem_ptr
                = sglob_val sr (f_inst fr) global_mem_ptr) by reflexivity.
        rewrite Hgl in H6. rewrite H6 in Hgmp. inv Hgmp.
        repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H8; lia. } subst v_gmp.
      rewrite Hlength'. apply mem_length_upper_bound in Hm5; cbn in Hm5.
      unfold page_size. lia.
    }
  }

  { (* growing memory fails *)
    edestruct INVresM_w as [sr'' HresM].

    eexists. split.
    (* load global_mem_ptr *)
    dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
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
        (Wasm_int.Int32.repr  (* arbitrary number *)
           (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z).
      apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
      have H'' := signed_upper_bound (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size).
      cbn. simpl_modulus_in H''. lia. cbn in H3. lia. }
    dostep. apply r_eliml; auto.
    elimr_nary_instr 0. eapply r_current_memory...

    dostep. elimr_nary_instr 2. constructor. apply rs_relop.

    dostep'. constructor. subst. rewrite HneedMoreMem. apply rs_if_true. discriminate.
    dostep'. constructor. apply rs_block with (vs:=[])(n:= 0); auto.
    apply reduce_trans_label.
    dostep. elimr_nary_instr 1. eapply r_grow_memory_failure; try eassumption.
    dostep. elimr_nary_instr 2. constructor. apply rs_relop. cbn.
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

Lemma small_signed_repr_n_n : forall n,
  (0 <= n <= 5000)%Z->
  Wasm_int.Int32.signed (Wasm_int.Int32.repr n) = n.
Proof.
  intros n H.
  unfold Wasm_int.Int32.signed. cbn.
  rewrite zlt_true.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
  rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
Qed.

Lemma memory_grow_reduce_already_enough_mem {lenv} : forall grow state s f gmp m,
  grow = grow_memory_if_necessary page_size ->
  INV lenv s f ->
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
   (state, s, f, [seq AI_basic i | i <- grow])
   (state, s', f, [])
   /\ s_funcs s = s_funcs s'
   /\ (forall wal val, repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s f wal ->
                       repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s' f wal)
   (* enough memory to alloc. constructor *)
   /\ ((INV lenv s' f /\
       (forall m v_gmp, nth_error (s_mems s') 0 = Some m ->
          @sglob_val host_function s' (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 v_gmp)) ->
          (Z.of_nat v_gmp < Wasm_int.Int32.modulus)%Z ->
          (Z.of_nat v_gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z))
       \/ (@sglob_val host_function s' (f_inst f) result_out_of_mem = Some (VAL_int32 (nat_to_i32 1)))).
Proof with eauto.
  destruct exists_i32 as [my_i32 _].
  (* grow memory if necessary *)
  intros grow state sr fr gmp m H Hinv Hgmp Hm HgmpBound HenoughMem. subst.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM _]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m' [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].
  assert (m' = m) by congruence. subst m'.

  have H' := HgmpInM _ _ Hm2 Hgmp HgmpBound.
  (* enough space already *)
  exists sr. split.
  (* load global_mem_ptr *)
  dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
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
           (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size)) ÷ 65536 <= 10000000)%Z).
    apply OrdersEx.Z_as_OT.quot_le_upper_bound; try lia.
    have H'' := signed_upper_bound (Wasm_int.Int32.intval (nat_to_i32 gmp) + Z.of_N page_size).
    simpl_modulus_in H''. cbn. lia. cbn in H. lia. }
  dostep. apply r_eliml; auto.
  elimr_nary_instr 0. eapply r_current_memory...

  dostep. elimr_nary_instr 2.
  constructor. apply rs_relop.

  dostep'. constructor. subst.
  rewrite HenoughMem. apply rs_if_false. reflexivity.

  dostep'. constructor. apply rs_block with (vs:=[])(n:= 0); auto. cbn.
  apply reduce_trans_label. apply rt_refl. split. reflexivity. split. auto.
  left. split. assumption.

  (* enough space *)
  { intros. unfold max_mem_pages in *.
    rewrite H0 in Hgmp. inv Hgmp.
    repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H3; try lia.
    apply Nat2Z.inj in H3. subst gmp.
    assert (m = m0). { cbn in Hm2. rewrite H in Hm2. now inv Hm2. } subst m0.
    unfold Wasm_int.Int32.lt in HenoughMem.
    destruct (zlt _ _) as [Ha|Ha]. 2: inv HenoughMem. clear HenoughMem.
    unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in Ha. cbn in Ha.

    rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: {
      unfold  Wasm_int.Int32.modulus, two_power_nat. cbn.
      apply mem_length_upper_bound in Hm5; cbn in Hm5. lia. }

    remember (Wasm_int.Int32.signed (Wasm_int.Int32.repr (Z.of_nat v_gmp + 65536)) ÷ 65536)%Z as y.
    unfold Wasm_int.Int32.signed, Wasm_int.Int32.unsigned in Heqy.
    rewrite Z_nat_bin in Ha.
    have Hlength := mem_length_upper_bound _ Hm5.
    unfold page_size, max_mem_pages in Hlength. cbn in Hlength.

    rewrite zlt_true in Heqy. 2: {
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id. lia. simpl_modulus. cbn. lia. }

    unfold Wasm_int.Int32.signed in Heqy. cbn in Heqy.
    rewrite Wasm_int.Int32.Z_mod_modulus_id in Heqy. 2: { simpl_modulus. cbn. lia. }
    cbn in Heqy. replace (Z.of_nat (Pos.to_nat 65536)) with 65536%Z in Heqy by lia.
    rewrite (Z.quot_add (Z.of_nat v_gmp) 1 65536) in Heqy; try lia.

    remember (Wasm_int.Int32.signed
        (Wasm_int.Int32.repr (Z.of_N (mem_size m)))) as n.
    unfold Wasm_int.Int32.signed in Ha.
    subst y. unfold Wasm_int.Int32.signed in Ha. cbn in Ha.

    rewrite Wasm_int.Int32.Z_mod_modulus_id in Ha. 2: {
      assert ((Z.of_nat v_gmp ÷ 65536 < 6000)%Z) as H''. { apply Z.quot_lt_upper_bound; lia. }
      simpl_modulus. cbn.
      assert (Z.of_nat v_gmp ÷ 65536  >= 0)%Z. {
        rewrite Zquot.Zquot_Zdiv_pos; try lia. apply Z_div_ge0; lia.
      } lia. }

    rewrite small_signed_repr_n_n in Heqn; try lia.
    unfold Wasm_int.Int32.signed in Heqn. cbn in Heqn.

    assert ((Z.of_nat v_gmp ÷ 65536 < 6000)%Z) as H''. { apply Z.quot_lt_upper_bound; lia. }
    assert (Z.of_nat v_gmp ÷ 65536  >= 0)%Z. { rewrite Zquot.Zquot_Zdiv_pos; try lia.
    apply Z_div_ge0; lia. }

    rewrite zlt_true in Ha; try lia. subst.

    rewrite N2Z.inj_div in Ha.
    cbn in Ha.
    rewrite Zquot.Zquot_Zdiv_pos in Ha; try lia.
    remember (Z.of_nat v_gmp) as q.
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

Lemma memory_grow_reduce {lenv} : forall grow state s f,
  grow = grow_memory_if_necessary page_size ->
  INV lenv s f ->
  exists s', reduce_trans
   (state, s, f, [seq AI_basic i | i <- grow])
   (state, s', f, [])
   /\ s_funcs s = s_funcs s'
   /\ (forall wal val, repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s f wal ->
                       repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s' f wal)
   (* enough memory to alloc. constructor *)
   /\ ((INV lenv s' f /\
       (forall m v_gmp, nth_error (s_mems s') 0 = Some m ->
            @sglob_val host_function s' (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 v_gmp)) ->
            (Z.of_nat v_gmp < Wasm_int.Int32.modulus)%Z ->
            (Z.of_nat v_gmp + Z.of_N page_size < Z.of_N (mem_length m))%Z))
       \/ (@sglob_val host_function s' (f_inst f) result_out_of_mem = Some (VAL_int32 (nat_to_i32 1)))).
Proof with eauto.
  (* grow memory if necessary *)
  intros grow state sr fr H Hinv. subst.
  unfold grow_memory_if_necessary. cbn. have I := Hinv.
  destruct I as [_ [INVresM_w [_ [INVgmp_w [INVcap_w [INVmuti32 [INVlinmem [HgmpInM [? ?]]]]]]]]].
  have I := INVlinmem. destruct I as [Hm1 [m [Hm2 [size [Hm3 [Hm4 Hm5]]]]]].

  assert (global_var_r global_mem_ptr sr fr) as H2.
  { apply global_var_w_implies_global_var_r; auto. } destruct H2 as [g Hgmp_r].
  destruct (i32_exists_nat g) as [gmp [HgmpEq HgmpBound]]. subst g.
  have H' := HgmpInM _ _ Hm2 Hgmp_r HgmpBound.
  destruct ((~~ Wasm_int.Int32.lt
                 (Wasm_int.Int32.repr
                   (Wasm_int.Int32.signed
                     (Wasm_int.Int32.iadd (nat_to_i32 gmp)
                        (nat_to_i32 (N.to_nat page_size))) ÷ 65536))
                 (Wasm_int.Int32.repr (Z.of_nat (ssrnat.nat_of_bin (mem_size m)))))) eqn:HneedMoreMem.
  2: rename HneedMoreMem into HenoughMem.
  { (* need to grow memory *)
    have H'' := memory_grow_reduce_need_grow_mem _ state _ _ _ _ Logic.eq_refl
                                   Hinv Hgmp_r Hm2 HgmpBound HneedMoreMem. apply H''. }
  { (* enough space already *)
     have H'' := memory_grow_reduce_already_enough_mem _ state _ _ _ _ Logic.eq_refl
                                   Hinv Hgmp_r Hm2 HgmpBound HenoughMem. apply H''. }
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
    apply (H _ (mem_data m)) in H0 as [datf' Hdatf'].
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
  assert (He: exists e, nth_error (ml_data (mem_data m)) (N.to_nat addr) = Some e). {
    apply notNone_Some. intro Hcontra.
    apply nth_error_Some in Hcontra; lia.
  } destruct He.
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
  (N.to_nat (addr + 3)) = Some e).
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


Ltac solve_arith_load_store :=
  repeat (try rewrite length_is_size; try rewrite size_set_nth;
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
  cbn in Harith. unfold store in Hstore.
  destruct (a2 + 0 + N.of_nat 4 <=? mem_length m)%N eqn:Ha. 2: inv Hstore.
  apply N.leb_le in Ha. cbn in Ha. unfold mem_length, memory_list.mem_length in Ha.
  destruct w. inv Hlw. destruct w. inv Hlw. destruct w. inv Hlw. destruct w.
  inv Hlw. destruct w. 2: inv Hlw. clear Hlw. unfold write_bytes in Hstore. cbn in Hstore.
  unfold mem_update in Hstore. cbn in Hstore.
  destruct (a2 + 0 + 0 <? N.of_nat (Datatypes.length (ml_data (mem_data m))))%N eqn:Ha1.
  2: discriminate. cbn in Hstore. rewrite take_drop_is_set_nth in Hstore; try lia.
  rewrite take_drop_is_set_nth in Hstore. 2: solve_arith_load_store.
  assert ((a2 + 0 + 1 <? N.of_nat (Datatypes.length (set_nth b (ml_data (mem_data m))
                  (N.to_nat (a2 + 0 + 0)) b)))%N) as Ha2. { solve_arith_load_store. }
 rewrite Ha2 in Hstore. cbn in Hstore. repeat rewrite take_drop_is_set_nth in Hstore.
 2: solve_arith_load_store.
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

Definition map_injective (m : M.tree nat) := forall x y x' y',
  x <> y ->
  m ! x = Some x' ->
  m ! y = Some y' ->
  x' <> y'.

Definition domains_disjoint (m1 m2: M.tree nat) :=
  (forall x v1, m1 ! x = Some v1 -> m2 ! x = None) /\
  (forall x v2, m2 ! x = Some v2 -> m1 ! x = None).

Lemma HfenvWf_None : forall fds,
   (forall f : var,
          (exists res : fun_tag * seq var * exp,
             find_def f fds = Some res) <->
          (exists i : nat, fenv ! f = Some i)) ->

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
  INV lenv s f ->
  nth_error (s_mems s) 0 = Some m ->
  @sglob_val host_function s (f_inst f) constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap)) ->
  ((N.of_nat v_cap) + page_size < mem_length m)%N ->
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  (-1 < Z.of_nat (length ys + offset) < 2 * max_constr_args)%Z ->
  sglob_val (host_function:=host_function) s (f_inst f)
                 global_mem_ptr = Some (VAL_int32 (nat_to_i32 (4 + (4*offset) + v_cap))) ->
  Forall_statements_in_seq' (set_nth_constr_arg (lenv:=lenv) fenv nenv) ys sargs offset ->
  get_list ys rho = Some vs ->
  (* memory relation: ys are available as locals in frame f *)
  (forall y, In y ys -> find_def y fds = None ->
                                  (exists v6 val, M.get y rho = Some v6
                                     /\ stored_in_locals (lenv:=lenv) nenv y val f
                                     /\ repr_val_LambdaANF_Codegen cenv fenv nenv _ v6 s f val)) ->
  (* correspondence of fenv and fds *)
  (forall y y' v, rho ! y = Some v -> repr_funvar fenv nenv y y' ->
         repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s f (Val_funidx y')) ->
  exists s', reduce_trans
                  (state, s, f, [seq AI_basic i | i <- sargs])
                  (state, s', f, [])
            /\ INV lenv s' f
            (* constructor args val *)
            /\ sglob_val (host_function:=host_function) s' (f_inst f)
                 constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap))
            /\ (0 <= Z.of_nat v_cap < Wasm_int.Int32.modulus)%Z
            /\ repr_val_constr_args_LambdaANF_Codegen cenv fenv nenv _ vs s' f (4 + (4*offset) + v_cap)
            /\ sglob_val (host_function:=host_function) s' (f_inst f)
                 global_mem_ptr = Some (VAL_int32 (nat_to_i32 ((4 + (4*offset) + v_cap) + 4 * (length ys))))
            /\ s_funcs s = s_funcs s'
            /\ (forall (wal : wasm_value) (val : cps.val),
                    repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s f wal ->
                    repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s' f wal)
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
      repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s f wal). {
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
      assert (Hinv' : INV lenv s' f). {
        eapply update_mem_preserves_INV. 6: subst; reflexivity. assumption. eassumption.
        apply mem_store_preserves_length in Hm0. lia.
        apply mem_store_preserves_max_pages in Hm0. congruence.
        eexists. split. reflexivity.
        apply mem_store_preserves_length in Hm0. unfold mem_size in Hmem5.
        now rewrite Hm0 in Hmem5. }

      have I := Hinv'. destruct I as [_ [_ [_ [Hgmp_w [_ [_ [_ [? _]]]]]]]].
      destruct (Hgmp_w (Wasm_int.Int32.iadd (nat_to_i32 gmp) (nat_to_i32 4))) as [s_before_IH ?].

      assert (Hinv_before_IH : INV lenv s_before_IH f). {
        edestruct i32_exists_nat as [? [Heq ?]]. erewrite Heq in H6.
       unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add, nat_to_i32 in Heq. inv Heq.
       repeat rewrite Wasm_int.Int32.Z_mod_modulus_id in H9; try lia.
       2: { rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
            have H' := Hinv_gmpM _ _ Hm H1 H4.
            apply mem_length_upper_bound in Hmem5; cbn in Hmem5. simpl_modulus; cbn; lia. }
       assert (x = gmp + 4) by lia. subst x.
       eapply update_global_preserves_INV; try apply H6. assumption.
       unfold result_out_of_mem, global_mem_ptr. lia. cbn.
       destruct (s_mems s). inv Hm. reflexivity. assumption.
       move => _. apply mem_store_preserves_length in Hm0.
       rewrite H1 in Hgmp.
       assert (-1 < Z.of_nat (4 + 4 * offset + v_cap) < Wasm_int.Int32.modulus)%Z. {
         cbn in Hoffset. unfold max_constr_args in Hmaxargs.
         unfold page_size in Hlen. cbn in Hlen.
         simpl_modulus. apply mem_length_upper_bound in Hmem5; cbn in Hmem5.
         cbn. lia. }

       assert (gmp = (4 + 4 * offset + v_cap)). { apply nat_to_i32_eq_modulus; auto. }
       clear Hgmp.
       cbn. unfold page_size in Hlen. cbn in Hoffset. lia. }

      assert (Hmem_before_IH : nth_error (s_mems s_before_IH) 0 = Some m0). {
        subst s'. erewrite <- update_global_preserves_memory; try eassumption.
        cbn. destruct (s_mems s). inv Hm. reflexivity. }

      assert (Hcap_before_IH: sglob_val (host_function:=host_function) s_before_IH
            (f_inst f) constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 v_cap))). {
        subst. eapply  update_global_get_other; try apply H6; auto. }

      assert (Hlen_m0: (N.of_nat v_cap + page_size < mem_length m0)%N). {
        apply mem_store_preserves_length in Hm0.
        unfold mem_length, memory_list.mem_length in *. congruence. }

      assert (HrelM_before_IH: (forall y : var,
        In y ys ->
        find_def y fds = None ->
        exists (v6 : cps.val) (val : wasm_value),
          rho ! y = Some v6 /\
          stored_in_locals (lenv:=lenv) nenv y val f /\
          repr_val_LambdaANF_Codegen cenv fenv nenv host_function v6 s_before_IH f val)). {
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
          reflexivity. apply update_global_preserves_funcs in H6. rewrite -H6. reflexivity.
          eassumption. eassumption. eassumption.
          have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [INVgmp_M _]]]]]]]].
          have H' := INVgmp_M _ _ Hm H1 H4. simpl_modulus. cbn. lia.
          eapply update_global_get_same in H6. eassumption.
          simpl_modulus. cbn. lia.
          lia.
          intros. assert (Hex: exists v, load_i32 m a = Some v). {
            apply enough_space_to_load. lia. } destruct Hex.
          rewrite H14. symmetry. erewrite load_store_load; try apply Hm0; auto.
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
       rho ! y = Some v -> repr_funvar fenv nenv y y' ->
       repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s_before_IH f (Val_funidx y'))).
     { intros. have H' := HfVal _ _ _ H7 H8.
       eapply val_relation_func_depends_on_funcs; last apply H'. subst.
       now apply update_global_preserves_funcs in H6. }

      have IH := IHys _ _ _ state _ _ _ _ _ _ HenvsDisjoint HfenvWf Hinv_before_IH Hmem_before_IH
                 Hcap_before_IH Hlen_m0 Hmaxargs Hoffset Hgmp_before_IH H3 Hvs HrelM_before_IH HfVal_before_IH.
      clear IHys Hmem_before_IH Hinv_before_IH HrelM_before_IH Hcap_before_IH.
      destruct IH as [sr [Hred [Hinv'' [Hv1 [? [Hv2 [? [? [? [m1 [Hm1 [? ?]]]]]]]]]]]].
      assert (@sglob_val host_function s (f_inst f) constr_alloc_ptr
            = @sglob_val host_function (upd_s_mem s (set_nth m0 (s_mems s) 0 m0)) (f_inst f) constr_alloc_ptr)
      as Hglob_cap by reflexivity.
      have HlenBound := mem_length_upper_bound _ Hmem5. cbn in HlenBound.

      rewrite H0 in Hcap. apply nat_to_i32_eq_modulus in Hcap; try lia. subst v_cap.

      eexists. split.
      (* reduce *)
      dostep. elimr_nary_instr 0. apply r_get_global. rewrite Hglob_cap. eassumption.
      dostep. elimr_nary_instr 2. constructor. constructor. reflexivity.
      eapply rt_trans. apply app_trans_const; auto. apply app_trans. eassumption.

      dostep. elimr_nary_instr 2. eapply r_store_success; try eassumption; auto.
      dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
      dostep. elimr_nary_instr 2. constructor. apply rs_binop_success. reflexivity.
      dostep. elimr_nary_instr 1. apply r_set_global. subst. eassumption.
      apply Hred.
      split. assumption. split. assumption. split. simpl_modulus. cbn. lia. split.
      econstructor. apply Hm1. eassumption. { simpl_modulus.
        apply mem_length_upper_bound in Hmem5. cbn in Hmem5, Hoffset. cbn. lia. } cbn. lia.

      { (* load val *)
        rewrite -H12; try lia.
        apply store_load in Hm0.
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
        - reflexivity.
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
          symmetry. erewrite load_store_load; try apply Hm0 ; eauto.
          remember (S (S (S (S (offset * 4))))) as n. cbn in Hoffset. cbn.
          repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; lia.
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
        - reflexivity.
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

          have Ht := load_store_load _ _ _ _ _ _ _ Har H16 Hm0.
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
        symmetry. erewrite load_store_load; try apply Hm0; eauto.
        remember (S (S (S (S (offset * 4))))) as n.
        cbn. repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; simpl_modulus; cbn; try lia. }}}
Qed.

Lemma store_constr_reduce {lenv} : forall state s f rho fds ys (vs : list cps.val) t sargs,
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  INV lenv s f ->
  (* enough memory available *)
  (forall m gmp_v, nth_error (s_mems s) 0 = Some m ->
             sglob_val s (f_inst f) global_mem_ptr = Some (VAL_int32 (nat_to_i32 gmp_v)) ->
             (-1 < Z.of_nat gmp_v < Wasm_int.Int32.modulus)%Z ->
             Z.of_nat gmp_v + Z.of_N page_size < Z.of_N (mem_length m))%Z ->
  (* memory relation: ys available as local vars *)
  (forall y : var,
         In y ys ->
         find_def y fds = None ->
         exists (v6 : cps.val) (val : wasm_value),
           rho ! y = Some v6 /\
           stored_in_locals (lenv:=lenv) nenv y val f /\
           repr_val_LambdaANF_Codegen cenv fenv nenv host_function v6 s f val) ->
  (Z.of_nat (length ys) <= max_constr_args)%Z ->
  Forall_statements_in_seq (set_nth_constr_arg (lenv:=lenv) fenv nenv) ys sargs ->
  get_list ys rho = Some vs ->

  (* function indices: value relation *)
  (forall (y : positive) (y' : immediate) (v : cps.val),
         rho ! y = Some v ->
         repr_funvar fenv nenv y y' ->
         repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s f (Val_funidx y')) ->

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
    INV lenv s' f /\
    s_funcs s = s_funcs s' /\
    (forall (wal : wasm_value) (val : cps.val),
      repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s f wal ->
      repr_val_LambdaANF_Codegen cenv fenv nenv host_function val s' f wal) /\
      (* cap points to value *)
    (exists cap_v wasmval, sglob_val s' (f_inst f) constr_alloc_ptr = Some (VAL_int32 cap_v)
          /\ wasm_value_to_i32 wasmval = cap_v
          /\ repr_val_LambdaANF_Codegen cenv fenv nenv  _ (Vconstr t vs) s' f wasmval).
Proof.
  intros ? ? ? ? ? ? ? ? ? HenvsDisjoint HfenvWf Hinv HenoughM HmemR Hmaxargs Hsetargs Hrho HfVal.

  have I := Hinv. destruct I as [_ [_ [_ [INVgmp_w [INVcap_w [INVmuti32 [INVmem [_ [_ [_ [INV_instglobs _]]]]]]]]]]].
  destruct INVmem as [_ [m [Hm _]]].
  have INVgmp_r := global_var_w_implies_global_var_r _ _ _ INVmuti32 INVgmp_w.
  destruct INVgmp_r as [gmp_v Hgmp]. clear INVmuti32 INVgmp_w.
  edestruct i32_exists_nat as [x [Hx ?]]. erewrite Hx in Hgmp. subst gmp_v. rename x into gmp_v.
  (* invariants after set_global cap *)
  destruct (INVcap_w (nat_to_i32 gmp_v)) as [s' ?]. clear INVcap_w.
  (* INV after set_global cap *)
  assert (INV lenv s' f) as Hinv'. {
    eapply update_global_preserves_INV; try apply H0; auto.
    unfold result_out_of_mem, constr_alloc_ptr. lia.
    eassumption. intros Hcontra. inv Hcontra. }

   have I := Hinv'. destruct I as [_ [_ [_ [_ [INVcap_w'' [INVmuti32'' [INVlinmem'' _ ]]]]]]].

  (* invariants mem *)
  edestruct INVlinmem'' as [Hmem1'' [m' [Hmem2'' [size'' [Hmem3'' [Hmem4'' Hmem5'']]]]]].
  assert (m' = m). { apply update_global_preserves_memory in H0. congruence. } subst m'.

  assert (exists mem, store m (Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v)) 0%N
                              (bits (nat_to_value (Pos.to_nat t)))
                              (t_length T_i32) = Some mem) as Htest.
  { apply enough_space_to_store. cbn.
    assert ((Datatypes.length (serialise_i32 (nat_to_i32 (Pos.to_nat t)))) = 4) as Hl.
    { unfold serialise_i32, encode_int, bytes_of_int, rev_if_be.
      destruct (Archi.big_endian); reflexivity. } rewrite Hl. clear Hl. cbn.
    rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. subst size''.
    destruct Hinv' as [_ [_ [_ [_ [_ [_ [Hlinmem [INVgmp_M _]]]]]]]].
    destruct Hlinmem as [Hmem1 [m' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst.

    assert (m' = m) by congruence. subst m'.
    assert (Hgmp_r : sglob_val (host_function:=host_function) s' (f_inst f) global_mem_ptr =
              Some (VAL_int32 (nat_to_i32 gmp_v))). { eapply update_global_get_other; try eassumption.
               unfold global_mem_ptr, constr_alloc_ptr. lia. }
    have Htest := INVgmp_M _ _ Hmem2 Hgmp_r. lia. }
  destruct Htest as [m' Hstore]. subst.

  remember (upd_s_mem s' (set_nth m' s'.(s_mems) 0 m')) as s_tag.
  assert (Hinv_tag : INV lenv s_tag f). { subst.
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
  assert (Hinv_before_args : INV lenv s_before_args f). {
    eapply update_global_preserves_INV. 6: eassumption.
    assumption. unfold result_out_of_mem, global_mem_ptr. lia.
    subst s_tag. cbn. destruct (s_mems s'). inv Hmem2''. reflexivity. assumption.
    move => _. have H' := HenoughM _ _ Hm Hgmp H. unfold page_size in H'; cbn in H'.
    apply mem_store_preserves_length in Hstore. lia. }

  assert (Hmem: nth_error (s_mems s_before_args) 0 = Some m'). { subst s_tag. cbn.
    apply update_global_preserves_memory in H1. rewrite -H1. cbn.
    destruct (s_mems s'). inv Hmem2''. reflexivity. }
  assert (Hglob_cap: sglob_val (host_function:=host_function) s_before_args
          (f_inst f) constr_alloc_ptr = Some (VAL_int32 (nat_to_i32 gmp_v))). {
    subst.
    replace (sglob_val (upd_s_mem s' (set_nth m' (s_mems s') 0 m')) (f_inst f) constr_alloc_ptr)
       with (sglob_val s' (f_inst f) constr_alloc_ptr) by reflexivity.
    apply update_global_get_same in H0.
    eapply update_global_get_other in H1; eauto. }
  assert (HenoughM': (N.of_nat gmp_v + page_size < mem_length m')%N). {
    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
    destruct Hlinmem as [Hmem1 [m'' [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
    have Htest := HenoughM _ _ Hmem2 Hgmp H.
    assert (mem_length m' = mem_length m''). {
    apply mem_store_preserves_length in Hstore.
    apply update_global_preserves_memory in H1, H0.
    assert (m = m'') by congruence. subst m''. congruence. } lia. }

  assert (HlenBound: (-1 < Z.of_nat (Datatypes.length ys + 0) < 2 * max_constr_args)%Z). {
    rewrite Nat.add_0_r. cbn. unfold max_constr_args in Hmaxargs. lia. }

  assert (HrelM': forall y : var,
    In y ys ->
    find_def y fds = None ->
    exists (v6 : cps.val) (val : wasm_value),
      rho ! y = Some v6 /\
      stored_in_locals (lenv:=lenv) nenv y val f /\
      repr_val_LambdaANF_Codegen cenv fenv nenv host_function v6 s_before_args f val). {
    intros y Hy Hfd. apply HmemR in Hy; auto. destruct Hy as [val [wal [Hrho' [Hylocal Hval]]]].
    exists val, wal. repeat (split; auto).

    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply Hval.
    reflexivity.
    { subst. apply update_global_preserves_funcs in H0, H1. cbn. subst.
      assert (s_funcs
       (upd_s_mem (host_function:=host_function) s'
          (set_nth m' (s_mems s') 0 m')) = s_funcs s') by reflexivity. congruence. }
    { erewrite update_global_preserves_memory. 2: eassumption. eassumption. }
    { apply update_global_preserves_memory in H1. subst. rewrite <- H1. cbn.
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
      assert (load_i32 m' a = Some x). { eapply load_store_load ; try apply Hstore; eauto. cbn.
       rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. } congruence. }
  }

  assert (Hgmp_before_args : sglob_val  s_before_args (f_inst f) global_mem_ptr =
        Some (VAL_int32 (nat_to_i32 (4 + gmp_v)))).
  { apply update_global_get_same in H1. rewrite H1. do 3! f_equal. lia. }

  assert (HfVal_before_args: (forall (y : positive) (y' : immediate) (v : cps.val),
         rho ! y = Some v ->
         repr_funvar fenv nenv y y' ->
         repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s_before_args f (Val_funidx y'))).
  { intros. have H' := HfVal _ _ _ H2 H3.
    eapply val_relation_func_depends_on_funcs; last eassumption.
    apply update_global_preserves_funcs in H0, H1. subst. now cbn in H1.
  }

  have Hargs := store_constr_args_reduce _ _ _ _ state _ _ _ _ _ _ HenvsDisjoint HfenvWf
                  Hinv_before_args Hmem Hglob_cap HenoughM' Hmaxargs HlenBound Hgmp_before_args
                    Hsetargs Hrho HrelM' HfVal_before_args.
  destruct Hargs as [s_final [Hred [Hinv_final [Hcap_v [? [Hargs_val [Hglobsame
                    [Hfuncs [HvalPreserved [m'' [Hm' [Hmemlen Hmemsame]]]]]]]]]]]].
  {
  cbn in Hargs_val. clear Hsetargs Hrho HenoughM' HlenBound.

  exists s_final. split.
  (* steps *)
  dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
  dostep. elimr_nary_instr 1. apply r_set_global. eassumption. cbn.
  dostep. elimr_nary_instr 0. apply r_get_global. eapply update_global_get_same. eassumption.
  (* write tag *)
  dostep. elimr_nary_instr 2. eapply r_store_success. 4: eassumption.
  reflexivity. eassumption. assumption.

  dostep. elimr_nary_instr 0. apply r_get_global.
  replace (sglob_val (upd_s_mem (host_function:=host_function) s' (set_nth m' (s_mems s') 0 m')))
     with (sglob_val s') by reflexivity.
  eapply update_global_get_other with (j:= constr_alloc_ptr). assumption.
  unfold global_mem_ptr, constr_alloc_ptr. lia.
  2: eassumption. eassumption. cbn.

  dostep. elimr_nary_instr 2. constructor. apply rs_binop_success. reflexivity.
  dostep. elimr_nary_instr 1. apply r_set_global. subst. rewrite HgmpEq. eassumption.
  cbn. apply Hred. split. assumption.
  split. apply update_global_preserves_funcs in H0, H1. subst s_tag. cbn in H1. congruence.
  split. { intros. apply HvalPreserved.
    have HM := HenoughM _ _ Hm Hgmp H.
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H3; eauto.
    apply update_global_preserves_funcs in H0, H1. subst. cbn in H1. congruence.
    unfold page_size in HM; cbn in HM.
    apply mem_length_upper_bound in Hmem5''; cbn in Hmem5''. simpl_modulus; cbn; lia.
    apply mem_store_preserves_length in Hstore. unfold page_size in HM; cbn in HM.
    apply mem_length_upper_bound in Hmem5''; cbn in Hmem5''. simpl_modulus; cbn; lia. lia.

    { intros. assert (exists v, load_i32 m a = Some v). {
        apply enough_space_to_load. unfold store in Hstore.
        destruct ((Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v) + 0 +
            N.of_nat (t_length T_i32) <=?
            mem_length m)%N). 2: inv Hstore. lia. } destruct H5.
      symmetry. erewrite load_store_load; try apply Hstore; eauto.
      cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
  }
  (* constr value in memory *)
  eexists. eexists. split. eassumption.
  split.
  assert (wasm_value_to_i32 (Val_ptr gmp_v) = nat_to_i32 gmp_v) by reflexivity. eassumption.
  econstructor; try eassumption. { assert (Hm'': nth_error (s_mems s) 0 = Some m).
    erewrite update_global_preserves_memory; eassumption. have H' := HenoughM _ _ Hm'' Hgmp H.
    apply mem_length_upper_bound in Hmem5''. cbn in Hmem5''. unfold page_size in H'. cbn in H'.
    unfold max_constr_args in Hmaxargs. simpl_modulus. cbn. lia. }
  admit.
  admit.
  admit.
  lia. reflexivity.
  apply store_load in Hstore.
  rewrite deserialise_bits in Hstore; auto.
  assert ((Wasm_int.N_of_uint i32m (nat_to_i32 gmp_v)) = (N.of_nat gmp_v)) as Heq. {
  unfold nat_to_i32. cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
  rewrite Heq in Hstore.
  rewrite -Hmemsame. eassumption. lia. reflexivity. }
Admitted. (* Qed. *)


Inductive const_val_list : list cps.val -> store_record -> frame -> list nat -> Prop :=
  | CV_nil  : forall s f, const_val_list [] s f []
  | CV_cons : forall s f v vs n w ns,
       repr_val_LambdaANF_Codegen cenv fenv nenv _ v s f w ->
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
  exists w, repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s f w /\
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
  @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv (Eletapp x f t ys e) rho sr fr fds ->
  @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv (Eapp f t ys) rho sr fr fds.
Proof.
  intros ? ? ? ? ? ? ? ? ? [Hfun1 [Hfun2 Hvar]]. split; auto. split; auto.
  intros x' Hocc Hfd.
  assert (Hocc': occurs_free (Eletapp x f t ys e) x'). { inv Hocc; constructor; cbn; auto. }
  now destruct (Hvar _ Hocc' Hfd) as [v' [w [Hrho [Hloc Hval]]]].
Qed.

Lemma fun_args_reduce {lenv} : forall state fr sr fds (ys : seq cps.var) rho vs f t args_instr,
  INV lenv sr fr ->
  get_list ys rho = Some vs ->
  domains_disjoint lenv fenv ->
  (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
  (forall a v, rho ! a = Some v -> find_def a fds <> None -> v = Vfun (M.empty cps.val) fds a) ->
  @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv (Eapp f t ys) rho sr fr fds ->
  repr_fun_args_Codegen (lenv:=lenv) fenv nenv ys args_instr ->
  exists args,
    reduce_trans (state, sr, fr, map AI_basic args_instr)
                 (state, sr, fr, (map (fun a => AI_basic (BI_const (nat_to_value a))) args))
    /\ const_val_list vs sr fr args.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? Hinv Hgetlist HenvsDisjoint HfenvWf HfenvRho HrelM Hargs.
  generalize dependent f. generalize dependent rho. generalize dependent sr.
  revert vs t fr state. induction Hargs; intros.
  { inv Hgetlist. exists []. cbn. split. apply rt_refl. constructor. }
  { (* var *) destruct vs.
    { cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist. }
    assert (HrelM': @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv
        (Eapp f t args) rho sr fr fds). {
          destruct HrelM as [Hfun1 [Hfun2 Hvar]]. split. assumption. split. assumption.
          intros. assert (Hocc : (occurs_free (Eapp f t (a :: args)) x)). {
          inv H0. constructor. constructor. right. assumption.  }
           destruct (Hvar _ Hocc) as [val [wal [Hrho' [Hlocals Hval]]]]; auto. }
    assert (Hgetlist': get_list args rho = Some vs). {
      cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
    assert (Ha: rho ! a = Some v). {
      cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto.
    }
    have IH := IHHargs _ _ _ state _ Hinv _ Hgetlist' HfenvRho _ HrelM'.
    destruct IH as [args' [Hred HconstL]].
    unfold rel_env_LambdaANF_Codegen in HrelM.

    destruct HrelM as [_ [_ Hvar]].
    assert (Hocc: occurs_free (Eapp f t (a :: args)) a). { constructor. cbn. auto. }
    assert (Hf: find_def a fds = None). { apply HfenvWf_None with (f:=a) in HfenvWf.
      rewrite HfenvWf. inv H. unfold translate_var in H0. destruct (lenv ! a) eqn:Ha'; inv H0.
      now apply HenvsDisjoint in Ha'. }
    destruct (Hvar _ Hocc Hf) as [val [wal [Hrho' [Hlocs Hval]]]].
    assert (v = val) by congruence. subst val.
    destruct Hlocs as [a'' [Ha'' HlVar]]. destruct H. rewrite Ha'' in H. inv H.

    exists (wasm_value_to_immediate wal :: args'). cbn. split.
    dostep. elimr_nary_instr 0. apply r_get_local. eassumption.
    apply app_trans_const; auto.
    econstructor; eauto.
  }
  { (* fun *) destruct vs.
    - cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist.
    - assert (HrelM': @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv
        (Eapp f t args) rho sr fr fds). {
          destruct HrelM as [Hfun1 [Hfun2 Hvar]]. split. assumption. split. assumption.
          intros. assert (Hocc : (occurs_free (Eapp f t (a :: args)) x)). {
          inv H0. constructor. constructor. right. assumption. }
           destruct (Hvar _ Hocc) as [val [wal [Hrho' [Hlocals Hval]]]]; auto. }
      assert (Hgetlist': get_list args rho = Some vs). {
        cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
      assert (Ha: rho ! a = Some v). {
        cbn in Hgetlist. destruct (rho ! a), (get_list args rho); inv Hgetlist; auto. }
      have IH := IHHargs _ _ _ state _ Hinv _ Hgetlist' HfenvRho _ HrelM'.
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
      destruct HrelM as [Hfun1 [Hfun2 _]]. inv H.
      eapply Hfun1 in Ha. 2:apply rt_refl.
      apply Hfun2 with (errMsg:=errMsg) in Ha.
      destruct Ha as [a'' [HtransF Hrepr]]. econstructor; eauto.
      cbn. congruence.
   }
Qed.

Lemma numOf_fundefs_length :
  forall f0 fns,
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
     end) f0 = Ret fns -> numOf_fundefs f0 = length fns.
Proof.
  induction f0; intros. 2: { now inv H. }
  destruct (translate_function nenv cenv fenv v l e). inv H.
  destruct (_ f0). inv H. destruct fns; inv H. cbn. now rewrite -IHf0.
Qed.


Inductive expression_restricted : cps.exp -> Prop :=
  | ER_constr : forall x t ys e,
      (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z ->
      expression_restricted e ->
      expression_restricted (Econstr x t ys e)
  | ER_case : forall x ms,
      Forall (fun p => (Z.of_nat (Pos.to_nat (fst p)) < Wasm_int.Int32.modulus)%Z /\
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


Lemma check_restrictions_expression_restricted : forall e e',
  check_restrictions e = Ret tt ->
  subterm_or_eq e' e -> expression_restricted e'.
Proof.
  have IH := exp_mut
    (fun e => check_restrictions e = Ret () -> forall e',
                subterm_or_eq e' e -> expression_restricted e')
    (fun fds => ((fix iter (fds : fundefs) : error Datatypes.unit :=
                   match fds with
                   | Fnil => Ret tt
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
    destruct (Z.of_nat (Datatypes.length l) <=? max_constr_args)%Z eqn:Hlen. 2: inv H3.
    cbn in H3. clear H.
    apply Z.leb_le in Hlen. apply clos_rt_rtn1 in Hsub. inv Hsub. constructor; auto.
    apply IHe; auto. apply rt_refl. inv H. apply IHe; auto. now apply clos_rtn1_rt. }
  { (* Ecase nil *)
    rename H2 into Hsub.
    apply clos_rt_rtn1 in Hsub. inv Hsub. constructor. apply Forall_nil.
    now inv H2. }
  { (* Ecase cons *)
    rename H4 into Hsub, H1 into IHe, H2 into IHe0. inv H3.
    clear H0 H e. rename e0 into e.
    destruct ((Z.of_nat (Pos.to_nat c) <? Wasm_int.Int32.modulus)%Z) eqn:Hlen. 2: inv H2.
    cbn in H2. destruct (check_restrictions e) eqn:Hrestr. inv H2.
    destruct (sequence _ ) eqn:Hseq; inv H2. destruct u.

    assert (check_restrictions (Ecase v l) = Ret ()). {
      unfold check_restrictions. cbn. now rewrite Hseq. }
    assert (expression_restricted (Ecase v l)). {
       apply IHe0; auto. apply rt_refl. }

    apply clos_rt_rtn1 in Hsub. inv Hsub.
    { constructor. apply Forall_cons. cbn. split. now apply Z.ltb_lt in Hlen.
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

Lemma var_mapping_list_lt_length' : forall l loc loc' err_str n,
  translate_var nenv (create_var_mapping n l (M.empty _)) loc err_str = Ret loc' ->
  loc' < length l + n.
Proof.
  intros ? ? ? ? ? H.
  unfold translate_var in H.
  destruct (create_var_mapping n l (M.empty nat)) ! loc eqn:Heqn; inv H.
  generalize dependent loc. revert loc' err_str n.
  induction l; intros. inv Heqn.
  destruct (var_dec loc a).
  (* loc = a *) subst. cbn in Heqn. rewrite Maps.PTree.gss in Heqn. inv Heqn. cbn. lia.
  (* loc <> a *) cbn in Heqn. rewrite Maps.PTree.gso in Heqn; auto. cbn.
  replace (S (Datatypes.length l + n)) with (Datatypes.length l + (S n)) by lia.
  eapply IHl; eauto.
Qed.

Lemma var_mapping_list_lt_length : forall l loc loc' err_str,
  translate_var nenv (create_local_variable_mapping l) loc err_str = Ret loc' ->
  loc' < length l.
Proof.
  intros. apply var_mapping_list_lt_length' in H. lia.
Qed.

Lemma var_mapping_list_lt_length_nth_error_idx : forall l i n x err,
  NoDup l ->
  nth_error l i = Some x ->
  translate_var nenv (create_var_mapping n l (M.empty _)) x err = Ret (n + i).
Proof.
  induction l; intros.
  - destruct i; inv H0.
  - destruct (var_dec a x).
    { (* x=a *)
      subst. destruct i. 2: { cbn in H0. apply nth_error_In in H0.
                              apply NoDup_cons_iff in H. now destruct H. }
      clear H0. cbn. unfold translate_var. now rewrite M.gss. }
    { (* x<> a *)
      cbn. unfold translate_var. rewrite M.gso; auto.
      destruct i. 1: now inv H0.
      apply IHl with (n:=S n) (err:=err) in H0.
      replace (n + S i) with (S n + i) by lia. assumption.
      now inv H. }
Qed.

Lemma local_variable_mapping_gt_idx : forall l idx x x',
  (create_var_mapping idx l (M.empty nat)) ! x = Some x' -> x' >= idx.
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
   NoDup l -> map_injective (create_var_mapping idx l (M.empty nat)).
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

Lemma find_def_in_collect_function_vars : forall fds f e,
  find_def f fds <> None ->
  In f (collect_function_vars (Efun fds e)).
Proof.
  induction fds; intros; last contradiction.
  cbn in H.
  destruct (M.elt_eq f0 v).
  (* f0=v *) subst. now left.
  (* f0<>v *) right. apply IHfds; auto.
Qed.

Lemma find_def_not_in_collect_function_vars : forall fds f e,
  find_def f fds = None ->
  ~ In f (collect_function_vars (Efun fds e)).
Proof.
  induction fds; intros ? ? Hfd Hcontra; last auto.
  cbn in Hfd. destruct (M.elt_eq f0 v).
  (* f0=v *) subst. inv Hfd.
  (* f0<>v *) destruct Hcontra; auto. eapply IHfds; eauto.
  Unshelve. auto.
Qed.

Lemma collect_function_vars_length_numOf_fundefs_eq : forall fds e,
  length (collect_function_vars (Efun fds e)) = numOf_fundefs fds.
Proof.
  induction fds; intros; auto. cbn. f_equal. now eapply IHfds with (e:=e).
Qed.

Lemma set_lists_nth_error {A} : forall xs (vs : list A) rho rho' x v,
  set_lists xs vs rho = Some rho' ->
  In x xs ->
  rho' ! x = Some v ->
  exists k, nth_error vs k = Some v /\ nth_error xs k = Some x.
Proof.
  induction xs; intros.
  - inv H0.
  - destruct H0.
    { (* a=v *)
      subst a. destruct vs. inv H. cbn in H. destruct (set_lists xs vs rho) eqn:Heqn; inv H.
      rewrite M.gss in H1. inv H1. exists 0. now cbn. }
    { (* a<>v *)
      destruct vs. inv H. cbn in H. destruct (set_lists xs vs rho) eqn:Heqn; inv H.
      destruct (var_dec a x). subst.
      - rewrite M.gss in H1; inv H1. exists 0; now cbn. rewrite M.gso in H1; auto.
        destruct (IHxs _ _ _ _ _ Heqn H0 H1) as [k [Hk1 Hk2]]. exists (S k). now cbn.
     }
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
  { (* Econstr *)
    eapply IHHstep; try eassumption. intros.
    destruct (var_dec x0 x).
    { (* x = x0 *)
      subst x0. rewrite M.gss in H0. inv H0.
      apply subval_or_eq_fun in H1. destruct H1 as [v' [H2 H3]].
      have H' := get_list_In_val _ _ _ _ H H3. destruct H' as [y [HyIn Hrho']].
      have H' := Hrho _ _ _ _ _ Hrho' H2. assumption.
    }
    { (* x <> x0 *)
      rewrite M.gso in H0; auto.
      have H' := Hrho _ _ _ _ _ H0 H1. assumption.
    }
    intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
    eapply HnoFd. left. eapply rt_trans; try eassumption.
    apply rt_step. constructor.
  }
  { (* Eproj *)
    eapply IHHstep; try eassumption. intros.
    destruct (var_dec x x0).
    { (* x = x0 *)
      subst x0. rewrite M.gss in H1. symmetry in H1. inv H1.
      apply nthN_In in H0.
      have H' := subval_or_eq_constr _ _ _ t H2 H0.
      eauto. }
    { (* x <> x0*)
      rewrite M.gso in H1; eauto. }
    intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
    eapply HnoFd. left. eapply rt_trans; try eassumption.
    apply rt_step. constructor.
  }
  { (* Ecase *)
    eapply IHHstep; try eassumption.
    intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
    eapply HnoFd. left. eapply rt_trans; try eassumption.
    apply rt_step. econstructor. now apply findtag_In_patterns.
   }
  { (* Eapp *)
    assert (subval_or_eq (Vfun rho' fl f') (Vfun rho' fl f')). {
      constructor. constructor. now eapply find_def_name_in_fundefs.
    }
    have H' := Hrho _ _ _ _ _ H H3. destruct H'. subst.
    eapply IHHstep; try eassumption. intros.
    assert (Hdec: decidable_eq var). { intros n m.
    unfold Decidable.decidable. now destruct (var_dec n m). }
    have H' := In_decidable Hdec x xs. destruct H'.
    { (* In x xs *)
      have H' := set_lists_In _ _ _ _ _ _ H7 H4 H2.
      destruct (get_list_In_val _ _ _ _ H0 H') as [y [HyIn HyRho]].
      eauto.
    }
    { (* ~In x xs *)
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
    }
    intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
    eapply HnoFd. right. split. eassumption.
    now eapply find_def_dsubterm_fds_e.
  }
  { (* Eletapp *)
    eapply IHHstep2; try eassumption. intros.
    destruct (var_dec x x0).
    { (* x = x0 *)
      subst x0. rewrite M.gss in H3. symmetry in H3. inv H3.
      (* same as Eapp *)
      assert (subval_or_eq (Vfun rho' fl f') (Vfun rho' fl f')). {
      constructor. constructor. now eapply find_def_name_in_fundefs.
      }
      have H' := Hrho _ _ _ _ _ H H3. destruct H'. subst.
      eapply IHHstep1; try eassumption. intros.
      assert (Hdec: decidable_eq var). { intros n m.
      unfold Decidable.decidable. now destruct (var_dec n m). }
      have H' := In_decidable Hdec x0 xs. destruct H'.
      { (* In x0 xs *)
        have H' := set_lists_In _ _ _ _ _ _ H8 H5 H2.
        destruct (get_list_In_val _ _ _ _ H0 H') as [y [HyIn HyRho]].
        eauto.
      }
      { (* ~In x0 xs *)
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
      }
       intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
       eapply HnoFd. right. split. eassumption.
       now eapply find_def_dsubterm_fds_e.
    }
    { (* x <> x0 *)
      rewrite M.gso in H3; eauto.
    }
    intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
    eapply HnoFd. left. eapply rt_trans. eassumption.
    apply rt_step. constructor.
  }
  { (* Efun: absurd *)
    exfalso. eapply HnoFd. left. apply rt_refl. reflexivity. }
  { (* Eprim_val *) eapply IHHstep; eauto. intros.
    destruct (var_dec x0 x).
    { (* x = x0 *)
      subst x0. rewrite M.gss in H. inv H.
      now apply subval_or_eq_fun_not_prim in H0.
    }
    { (* x <> x0 *) rewrite M.gso in H; auto. eauto. }
    intros ? ? ? ? [H' | H']. 2: now eapply HnoFd.
    eapply HnoFd. left. eapply rt_trans; try eassumption.
    apply rt_step. constructor.
  }
  { (* Eprim *) inv H0. }
  { (* Ehalt *) eauto. }
  Unshelve. all: assumption.
Qed.


Lemma repr_expr_LambdaANF_Codegen_no_Efun_subterm {lenv} : forall e_body eAny,
  @repr_expr_LambdaANF_Codegen cenv fenv nenv lenv e_body eAny ->

  forall (e' eAny : exp) (fdsAny : fundefs),
  subterm_or_eq e' e_body ->
  e' <> Efun fdsAny eAny.
Proof.
  intros ? ? Hexpr. revert eAny Hexpr.
  induction e_body using exp_ind'; intros.
  { (* Econstr *)
    inv Hexpr.
    have H' := IHe_body _ H5.
    apply rt_then_t_or_eq in H. destruct H as [H | H]. congruence.
    apply clos_trans_tn1 in H. inv H. inv H0.
    eapply H'. apply rt_refl. inv H0.
    apply clos_tn1_trans in H1. eapply H'. now apply t_then_rt.
  } { (* Ecase [] *)
    apply rt_then_t_or_eq in H. destruct H; first congruence.
    apply clos_trans_tn1 in H. inv H. { inv H0. inv H2. }
    inv H0. inv H3.
  } { (* Ecase cons *)
    inv Hexpr.
    { have H' := IHe_body _ H7.
      have H'' := IHe_body0 _ H6. clear IHe_body IHe_body0.
      apply rt_then_t_or_eq in H. destruct H as [H | H]. congruence.
      apply clos_trans_tn1 in H. inv H.
      { inv H0. cbn in H2. destruct H2 as [H2 | H2].
        - inv H2. eapply H'. apply rt_refl.
        - eapply H''. apply rt_step. now econstructor. }
      apply clos_tn1_trans in H1.
      inv H0. destruct H3 as [H3 | H3].
      - inv H3. eapply H'. now apply t_then_rt.
      - eapply H''. eapply rt_trans. now apply t_then_rt.
        apply rt_step. now econstructor. }
     { have H' := IHe_body _ H7. (* TODO duplication *)
       have H'' := IHe_body0 _ H5. clear IHe_body IHe_body0.
       apply rt_then_t_or_eq in H. destruct H as [H | H]. congruence.
       apply clos_trans_tn1 in H. inv H.
       { inv H0. cbn in H2. destruct H2 as [H2 | H2].
         - inv H2. eapply H'. apply rt_refl.
         - eapply H''. apply rt_step. now econstructor. }
       apply clos_tn1_trans in H1.
       inv H0. destruct H3 as [H3 | H3].
       - inv H3. eapply H'. now apply t_then_rt.
       - eapply H''. eapply rt_trans. now apply t_then_rt.
         apply rt_step. now econstructor. }
  } { (* Eproj *)
    inv Hexpr.
    have H' := IHe_body _ H6.
    apply rt_then_t_or_eq in H. destruct H as [H | H]. congruence.
    apply clos_trans_tn1 in H. inv H. inv H0.
    eapply H'. apply rt_refl. inv H0.
    apply clos_tn1_trans in H1. eapply H'. now apply t_then_rt.
  } { (* Eletapp *)
    inv Hexpr.
    have H' := IHe_body _ H7. apply rt_then_t_or_eq in H.
    destruct H as [H|H]; first congruence. apply clos_trans_tn1 in H. inv H.
    inv H0. eapply H'. apply rt_refl. inv H0.
    eapply H'. apply clos_tn1_trans in H1. now apply t_then_rt.
  } { (* Efun *) inv Hexpr.
  } { (* Eapp *)
    apply rt_then_t_or_eq in H. inv H; first congruence.
    apply clos_trans_tn1 in H0. inv H0. inv H. inv H.
  } { (* Eprim_val *) inv Hexpr.
  } { (* Eprim *) inv Hexpr.
  } { (* Ehalt *)
    apply rt_then_t_or_eq in H. destruct H; first congruence.
    apply clos_trans_tn1 in H. inv H. inv H0. inv H0.
  }
Qed.

(* TODO: move up to find_def_dsubterm_fds_e *)
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

(* MAIN THEOREM, corresponds to 4.3.2 in Olivier's thesis *)
Theorem repr_bs_LambdaANF_Codegen_related :
  (* rho is environment containing outer fundefs. e is body of LambdaANF program *)
  forall lenv (rho : eval.env) (v : cps.val) (e : exp) (n : nat) (vars : list cps.var) (fds : fundefs),
    map_injective lenv ->
    domains_disjoint lenv fenv ->
    vars = (collect_local_variables e) ++ (collect_function_vars (Efun fds e))%list ->
    NoDup vars ->
    (* fenv maps f vars to their indices in the wasm module *)
    (forall f, (exists res, find_def f fds = Some res) <-> (exists i, fenv ! f = Some i)) ->
    (* find_def implies fn value: TODO reorganize/combine assumptions about fds *)
    (forall (a : positive) (v : cps.val), rho ! a = Some v -> find_def a fds <> None ->
             v = Vfun (M.empty cps.val) fds a) ->

    (* restricts e w.r.t. to size s.t. all vars fit in i32s *)
    expression_restricted e ->
    (* SSA form, let-bound vars not assigned yet *)
    (forall x, In x (collect_local_variables e) -> rho ! x = None) ->
    bstep_e (M.empty _) cenv rho e v n ->  (* e n-steps to v *)
    forall (hs : host_state) (sr : store_record) (f : frame)
           (instructions : list basic_instruction),

      (* fds only on toplevel so obtained for all funvalues, obtained rho = M.empty *)
      (forall x rho' fds' f' v, rho ! x = Some v -> subval_or_eq (Vfun rho' fds' f') v -> fds' = fds /\ rho' = M.empty _) ->
      (forall a t ys e errMsg, find_def a fds = Some (t, ys, e) ->
          expression_restricted e /\ (forall x, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
          NoDup (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)) /\
          (exists fidx : immediate, translate_var nenv fenv a errMsg = Ret fidx /\
                       repr_val_LambdaANF_Codegen cenv fenv nenv host_function
                        (Vfun (M.empty cps.val) fds a) sr f (Val_funidx fidx))) ->
      (* invariants *)
      INV lenv sr f ->

      (* translate_exp e returns instructions *)
      @repr_expr_LambdaANF_Codegen cenv fenv nenv lenv e instructions ->

      (* relates a LambdaANF evaluation environment [rho] to a WASM environment [store/frame] (free variables in e) *)
      @rel_env_LambdaANF_Codegen cenv fenv nenv _ lenv e rho sr f fds ->
      exists (sr' : store_record) (f' : frame),
        reduce_trans (hs, sr, f, map AI_basic instructions) (hs, sr', f', []) /\
        (* value sr'.res points to value related to v *)
        result_val_LambdaANF_Codegen v sr' f' /\
        f_inst f = f_inst f' /\ s_funcs sr = s_funcs sr' /\
        (* previous values are preserved *)
        (forall wal val, repr_val_LambdaANF_Codegen cenv fenv nenv host_function val sr f wal ->
                         repr_val_LambdaANF_Codegen cenv fenv nenv host_function val sr' f' wal) /\
        (* INV holds if program will continue to run *)
        (INV_result_var_out_of_mem_is_zero sr' f' -> INV lenv sr' f').
Proof with eauto.
  intros lenv rho v e n vars fds HlenvInjective HenvsDisjoint Hvars Hnodup
     HfenvWf HfenvRho HeRestr Hunbound Hev. subst vars.
  generalize dependent lenv.
  induction Hev; intros lenv HlenvInjective HenvsDisjoint state sr fr instructions HfdsEqRhoEmpty Hfds Hinv Hrepr_e Hrel_m.
  - (* Econstr *)
    (* admit. *)
    inversion Hrepr_e.
    inversion H8.
    {
    assert (Hmaxargs: (Z.of_nat (Datatypes.length ys) <= max_constr_args)%Z). { now inv HeRestr. }
    subst t0 x0 vs0 e0 sgrow. rename H7 into Hx'. rename H6 into Hexp.
    { remember (grow_memory_if_necessary page_size) as grow.
      cbn. repeat rewrite map_cat. cbn.

      (* prepare calling memory_grow_reduce *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem [_ [_ [_ [_ [_ [HlocalBound _]]]]]]]]]]]]].
      destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]].
      have Hgrowmem := @memory_grow_reduce lenv _ state sr fr Heqgrow Hinv.
      destruct Hgrowmem as [s' [Hred [Hsfuncs [HvalPreserved [[Hinv' Henoughmem] | HoutofM]]]]].
      have I := Hinv'. destruct I as [_ [_ [HresM0 [Hgmp [_ [Hmuti32 [Hlinmem' _]]]]]]].
      destruct Hlinmem' as [Hmem1' [m' [Hmem2' [size' [Hmem3' _]]]]].

      (* invariants after reducing grow *)
      have INVgmp_r' := global_var_w_implies_global_var_r _ _ _ Hmuti32 Hgmp.
      destruct INVgmp_r' as [n Hgmp'].
      edestruct i32_exists_nat as [gmp_v' [Hn ?]]. erewrite Hn in Hgmp'. clear Hn n.
      have HenoughM := Henoughmem _ _ Hmem2' Hgmp'. clear Henoughmem.

      { assert (HrelM : (forall y : var,
           In y ys ->
           find_def y fds = None ->
           exists (v6 : cps.val) (val : wasm_value),
             rho ! y = Some v6 /\
             stored_in_locals (lenv:=lenv) nenv y val fr /\
             repr_val_LambdaANF_Codegen cenv fenv nenv host_function v6 s' fr val)). {
              destruct Hrel_m as [_ Hvar]. intros.
        assert (Hocc: occurs_free (Econstr x t ys e) y) by (constructor; auto).
        apply Hvar in Hocc; auto. destruct Hocc as [val [wal [Hrho [Hloc Hval]]]].
        exists val, wal. repeat split; auto.
      }

      assert (HenoughM': (forall (m : memory) (gmp_v : nat),
        nth_error (s_mems s') 0 = Some m ->
        sglob_val (host_function:=host_function) s' (f_inst fr) global_mem_ptr =
                                              Some (VAL_int32 (nat_to_i32 gmp_v)) ->
        (-1 < Z.of_nat gmp_v < Wasm_int.Int32.modulus)%Z ->
        (Z.of_nat gmp_v + Z.of_N page_size < Z.of_N (mem_length m))%Z)).
      { intros. assert (m' = m0) by congruence. subst m0.
        assert (gmp_v = gmp_v'). { rewrite Hgmp' in H3. inv H3.
          rewrite Wasm_int.Int32.Z_mod_modulus_id in H7; try lia.
          rewrite Wasm_int.Int32.Z_mod_modulus_id in H7; try lia. }
        subst gmp_v'. lia. }

     assert (HfVal' : (forall (y : positive) (y' : immediate) (v : cps.val),
           rho ! y = Some v ->
           repr_funvar fenv nenv y y' ->
           repr_val_LambdaANF_Codegen cenv fenv nenv host_function v s' fr
             (Val_funidx y'))).
     { intros. destruct Hrel_m as [Hfun1 [Hfun2 _]].
      assert (Hfd: (exists i : nat, fenv ! y = Some i)). {
        inv H3. unfold translate_var in H5. now destruct (fenv ! y) eqn:Hy. }
      apply HfenvWf in Hfd. apply notNone_Some in Hfd.

       have H' := HfenvRho _ _ H2 Hfd. subst v0.
       apply notNone_Some in Hfd. destruct Hfd as [[[f' ys''] e''] ?H].

       assert (Hsubval: subval_or_eq (Vfun (M.empty _) fds y)
        (Vfun (M.empty cps.val) fds y)) by constructor.

       inv H3.
       have H' := Hfun1 _ _ _ H2 Hsubval. apply Hfun2 with (errMsg:=errMsg) in H'.
       destruct H' as [i [HvarI Hval]].
       assert (i = y') by congruence. subst i.
       eapply val_relation_func_depends_on_funcs; try apply Hval. auto.
     }

      have Hconstr := store_constr_reduce state _ _ _ _ _ _ t _ HenvsDisjoint HfenvWf Hinv' HenoughM' HrelM Hmaxargs H12 H HfVal'.
      destruct Hconstr as [s_v [Hred_v [Hinv_v [Hfuncs' [HvalPreserved' [cap_v [wal [? [? Hvalue]]]]]]]]].

    { subst cap_v.
      have Hl := HlocalBound _ _ Hx'. apply nth_error_Some in Hl.
      apply notNone_Some in Hl. destruct Hl as [? Hlx].

      remember ({|f_locs := set_nth (VAL_int32 (wasm_value_to_i32 wal)) (f_locs fr) x' (VAL_int32 (wasm_value_to_i32 wal));
      f_inst := f_inst fr|}) as f_before_IH.

      assert (HfdsEqRhoEmpty_before_IH: (forall (x : positive) (rho'0 : M.t cps.val)
        (fds' : fundefs) (f' : var) v, rho' ! x = Some v -> subval_or_eq (Vfun rho'0 fds' f') v -> fds' = fds /\ rho'0 = M.empty _)). {
        intros x1 rho'0 fds' f' v0 Hrho' Hval'.
        subst rho'.
        destruct (var_dec x x1).
        (* x=x1 *)
        { subst x1. rewrite M.gss in Hrho'. inv Hrho'.
          apply subval_or_eq_fun in Hval'. destruct Hval' as [v' [Hval' Hin]].
          destruct (get_list_In_val _ _ _ _ H Hin) as [y [Hiny Hrho']].
          now eapply HfdsEqRhoEmpty. }
        (* x<>x1 *)
        { rewrite M.gso in Hrho'; auto. now eapply HfdsEqRhoEmpty in Hrho'. }
      }

      assert (Hfds': forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) (errMsg : bytestring.String.t),
        find_def a fds = Some (t, ys, e) ->
          expression_restricted e /\ (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
          NoDup
            (ys ++
             collect_local_variables e ++
             collect_function_vars (Efun fds e)) /\
          (exists fidx : immediate,
             translate_var nenv fenv a errMsg = Ret fidx /\
             repr_val_LambdaANF_Codegen cenv fenv nenv host_function
               (Vfun (M.empty cps.val) fds a) s_v f_before_IH
               (Val_funidx fidx))). {
        intros ? ? ? ? ? Hfd. apply Hfds with (errMsg:=errMsg) in Hfd.
        destruct Hfd as [? [? [? [idx [HtransF Hval]]]]].
        repeat (split; try assumption).
        exists idx. split. assumption.
        eapply val_relation_func_depends_on_funcs.
        2:{ eapply val_relation_depends_on_finst; last apply Hval. now subst. }
        congruence.
      }

      assert (Hinv_before_IH: INV lenv s_v f_before_IH). {
        eapply update_local_preserves_INV; try eassumption.
        apply nth_error_Some. congruence. }
      (* prepare IH *)

      (* memory relation *)
      assert (Hrel_m_v : @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv e rho' s_v f_before_IH fds).
      { clear IHHev Hinv Hmem1 Hmem2 Hmem3 Hmem4 Hmem1' Hmem2' Hmem3'. clear Hinv' Hred_v.
        destruct Hrel_m as [Hfun1 [Hfun2 Hvar]]. unfold rel_env_LambdaANF_Codegen. split.
        { (* fns1 *) intros. subst rho'.
           destruct (var_dec x x1).
           { (* x=x1 *) subst x1. rewrite M.gss in H3. inv H3.
             apply subval_or_eq_fun in H5. destruct H5 as [v1 [Hr1 Hr2]].
             have H'' := get_list_In_val _ _ _ _ H Hr2.
             destruct H'' as [x2 [Hin Hrho]].
             have H' := Hfun1 _ _ _ Hrho Hr1. assumption.
           }
           { (* x<>x1 *) rewrite M.gso in H3; eauto. }
        } split.
        { (* fns2 *)
          intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          assert (Hfs: s_funcs sr = s_funcs s_v) by congruence.
          exists i. split. assumption.
          eapply val_relation_func_depends_on_funcs. eassumption.
          eapply val_relation_depends_on_finst. 2: eassumption.
          subst f_before_IH. reflexivity.
        }
        { (* local vars *)
          intros. destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1. exists (Vconstr t vs), wal.
            subst rho'. rewrite M.gss. split; auto. split.
            subst f_before_IH. exists x'. cbn. split.
            inv Hx'. intro. unfold translate_var. unfold translate_var in H0.
            destruct (lenv ! x); inv H0; reflexivity.
            erewrite set_nth_nth_error_same; eauto.
            subst f_before_IH.
            eapply val_relation_depends_on_finst; try apply Hvalue. reflexivity.
          }
          { (* x <> x1 *)
            assert (Hocc: occurs_free (Econstr x t ys e) x1). { now apply Free_Econstr2. }
            have H' := Hvar _ Hocc H5.
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
            unfold translate_var in Hl1, H7.
            destruct (lenv ! x1) eqn:Hlx1; inv Hl1.
            destruct (lenv ! x) eqn:Hlx2. inv H7.
            have H'' := HlenvInjective _ _ _ _ n Hlx2 Hlx1. contradiction.
            discriminate.
            apply nth_error_Some. congruence.
            apply val_relation_depends_on_finst with (fr:=fr). subst. reflexivity.
            apply HvalPreserved'.
            apply HvalPreserved. assumption.
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
          intros. apply HfenvRho; auto. subst rho'.
          rewrite M.gso in H3; auto. intro Hcontra. subst a.
          apply notNone_Some in H5. apply HfenvWf in H5. destruct H5.
          inv Hx'. destruct HenvsDisjoint as [Hd1 Hd2].
          apply Hd2 in H0. unfold translate_var in H3. now rewrite H0 in H3. }

      have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ HlenvInjective HenvsDisjoint
                 state s_v f_before_IH _ HfdsEqRhoEmpty_before_IH Hfds' Hinv_before_IH Hexp Hrel_m_v.
      destruct IH as [s_final [f_final [Hred_IH [Hval [Hfinst [Hsfuncs' [HvalPres H_INV]]]]]]]. cbn in Hfinst.

      exists s_final, f_final. split.
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
    replace ([:: AI_basic (BI_get_global constr_alloc_ptr)] ++ [:: AI_basic (BI_set_local x')]  ++ [seq AI_basic i | i <- e'])
    with   (([:: AI_basic (BI_get_global constr_alloc_ptr)] ++ [:: AI_basic (BI_set_local x')]) ++ [seq AI_basic i | i <- e'])
    by reflexivity. eapply rt_trans. apply app_trans.
    dostep. elimr_nary_instr 0. apply r_get_global. eassumption.

    assert (f_inst f_before_IH = f_inst fr) as Hfinst'. { subst. reflexivity. }
    dostep'. eapply r_set_local. eassumption.
    apply /ssrnat.leP. apply nth_error_Some. congruence. subst. reflexivity. apply rt_refl. cbn.
    apply Hred_IH. split. assumption. subst f_before_IH. cbn in Hfinst.
    split; first auto. split. congruence.
    split; last auto. intros. apply HvalPres.
    apply val_relation_depends_on_finst with (fr:=fr). reflexivity.
    apply HvalPreserved'. apply HvalPreserved. assumption. }}
    { (* grow mem failed *)
    eexists. eexists. split. eapply rt_trans. apply app_trans. apply Hred.
    dostep. elimr_nary_instr 0. apply r_get_global. eassumption.
    dostep. elimr_nary_instr 2. constructor. apply rs_relop.
    dostep'. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
    dostep'. constructor. eapply rs_block with (vs:=[]); auto.
    dostep'. constructor. apply rs_label_const; auto. apply rt_refl.
    split. right. assumption. split. reflexivity. split. congruence.
    split. auto. intro Hcontra. rewrite Hcontra in HoutofM. inv HoutofM. }} }
    { (* Nullary constructor case *)
      subst.
      inv H8. inv H0.
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
        (map_util.M.set x (Vconstr t vs) rho) ! a = Some v ->
        find_def a fds <> None -> v = Vfun (M.empty val) fds a)). {
        intros. apply HfenvRho. rewrite M.gso in H1. assumption.
        intro. subst a. apply notNone_Some in H2. apply HfenvWf in H2. destruct H2. inv H7. destruct HenvsDisjoint as [Hd1 Hd2]. apply Hd2 in H1. unfold translate_var in H2. rewrite H1 in H2. inv H2. assumption.
      }
      assert (Herestr' :  expression_restricted e). {
        inv HeRestr. assumption.
      }

      assert (Hunbound' : (forall x0 : var,
        In x0 (collect_local_variables e) ->
        (map_util.M.set x (Vconstr t vs) rho) ! x0 = None)). {
        intros. apply NoDup_app_remove_r in Hnodup. cbn in Hnodup. apply NoDup_cons_iff in Hnodup. rewrite M.gso. apply Hunbound. unfold collect_local_variables. cbn. fold collect_local_variables. right. assumption. destruct Hnodup as [Hx _ ]. unfold not. unfold not in Hx. intros Heq. subst x. apply Hx in H1. contradiction.
      }

      assert (HfdsEqRhoEmpty' : (forall (x0 : positive) (rho' : M.t val) (fds' : fundefs)
          (f' : var) (v : val),
        (map_util.M.set x (Vconstr t vs) rho) ! x0 = Some v ->
        subval_or_eq (Vfun rho' fds' f') v -> fds' = fds /\ rho' = M.empty val)). {
        intros x0 rho' fds' f' v0 Hrho' Hval'.
        destruct (var_dec x x0).
        { subst x0. rewrite M.gss in Hrho'. inv Hrho'. apply subval_or_eq_fun in Hval'. destruct Hval' as [v' [Hval' Hin]].
          destruct (get_list_In_val _ _ _ _ H Hin) as [y [Hiny Hrho']].
          eapply HfdsEqRhoEmpty; eauto.
        }
        { rewrite M.gso in Hrho'. eapply HfdsEqRhoEmpty; eauto. auto.
        }
      }

      assert (Hfds' :  (forall (a : var) (t : fun_tag) (ys : seq var) (e : exp) (errMsg : string),
        find_def a fds = Some (t, ys, e) ->
        expression_restricted e /\
        (forall x : var, occurs_free e x -> In x ys \/ find_def x fds <> None) /\
        NoDup
          (ys ++ collect_local_variables e ++ collect_function_vars (Efun fds e)) /\
        (exists fidx : immediate,
           translate_var nenv fenv a errMsg = Ret fidx /\
           repr_val_LambdaANF_Codegen cenv fenv nenv host_function
             (Vfun (M.empty val) fds a) sr f_before_IH (Val_funidx fidx)))). {
        intros ? ? ? ? ? Hfd. apply Hfds with (errMsg:=errMsg) in Hfd. destruct Hfd as [? [? [? [idx [Htransf Hval]]]]].
        split. assumption.
        split. assumption.
        split. assumption.
        exists idx. split. assumption. eapply val_relation_func_depends_on_funcs. auto. eapply val_relation_depends_on_finst; last apply Hval. subst. reflexivity.
      }
      assert (Hinv' : INV lenv sr f_before_IH). {
eapply update_local_preserves_INV; try
eassumption.
destruct Hinv as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [H' _]]]]]]]]]]]]]. destruct (H' x x'). assumption. auto. auto.
      }
      assert (Hrel_m' : @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv e
         (map_util.M.set x (Vconstr t vs) rho) sr f_before_IH fds). { admit. }
      have IH := IHHev HNoDup' HfenvRho' Herestr' Hunbound' _ HlenvInjective HenvsDisjoint state sr f_before_IH _ HfdsEqRhoEmpty' Hfds' Hinv' H6 Hrel_m'.
      destruct IH as [sr' [f' [Hred [Hval [Hfinst [Hsfuncs [HvalPres H_INV]]]]]]].
      exists sr', f'.
      split.
      dostep.
      elimr_nary_instr 2.
      constructor. apply rs_binop_success. reflexivity.
      dostep.
      elimr_nary_instr 2.
      constructor. apply rs_binop_success. reflexivity.
      dostep.
      elimr_nary_instr 1.
      eapply r_set_local with (f':=f_before_IH).
      subst f_before_IH. reflexivity.
      have I := Hinv.
      destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HlocalBound _]]]]]]]]]]]]].
      apply /ssrnat.leP.
      apply HlocalBound in H7. assumption.
      subst f_before_IH. reflexivity.
      apply Hred.
      split. apply Hval.
      split. subst f_before_IH. apply Hfinst.
      split. apply Hsfuncs.
      split. { intros. apply HvalPres. eapply val_relation_depends_on_finst.
               2:eassumption.
               subst. reflexivity.
      }
      assumption.
    }

  - (* Eproj ctor_tag t, let x := proj_n y in e *)
    { inv Hrepr_e.
      rename H8 into Hx', H9 into Hy'.

      (* y is constr value with correct tag, arity *)
      assert (Hy : occurs_free (Eproj x t n y e) y) by constructor.
      have Hrel_m' := Hrel_m.
      destruct Hrel_m' as [Hfun1 [Hfun2 Hvar]].
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

      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [HfnsUpperBound [_ [_ [HlocalBound _]]]]]]]]]]]]].
      have Hextr := extract_constr_arg n vs v _ _ _ _ HfnsUpperBound H0 H9 H15.
      destruct Hextr as [bs [wal [Hload [Heq Hbsval]]]].

      assert (Hrm: @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv e (map_util.M.set x v rho) sr
       {| f_locs := set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32);
                                                   f_inst := f_inst fr |} fds). {
        split; intros.
        { (* funs1 *)
          destruct (var_dec x x1).
          { (* x = x1 *)
            subst x1. rewrite M.gss in H10. inv H10. rename v0 into v.
            apply nthN_In in H0.
            have H' := subval_or_eq_constr _ _ _ t H12 H0.
            have HF := Hfun1 _ _ _ Hrho H'. apply Hfun2 with (errMsg:=""%bs) in HF.
            destruct HF as [i [Htrans Hval]].
            inv Hval. eapply find_def_name_in_fundefs. eassumption.
          }
          { (* x <> x1*)
            rewrite M.gso in H10; auto.
            have H' := Hfun1 _ _ _ H10 H12. apply Hfun2 with (errMsg:=""%bs) in H'.
            destruct H' as [i [Htf Hval]].
            inv Hval. eapply find_def_name_in_fundefs. eassumption.
           }
        } split.
        { (* funs2 *)
          intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
          destruct Hnfd as [i [Htrans Hval]].
          exists i. split. assumption.
          eapply val_relation_depends_on_finst. 2: eassumption. reflexivity.
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
            unfold wasm_deserialise in Heq. rewrite -Heq.
            have Hl := HlocalBound _ _ Hx'. apply nth_error_Some in Hl.
            apply notNone_Some in Hl. destruct Hl.
            eapply set_nth_nth_error_same. eassumption.
            eapply val_relation_depends_on_finst; try eassumption; auto. }
          { (* x <> x1 *)
            assert (Hocc: occurs_free (Eproj x t n y e) x1). { constructor; assumption. }
            apply Hvar in Hocc; auto. destruct Hocc as [v6 [wal' [Henv [Hloc Hval]]]].
            exists v6. exists wal'. repeat split; auto.
            rewrite map_util.M.gsspec.
            rewrite peq_false. assumption. auto.
            destruct Hloc as [x1' [? ?]].
            unfold stored_in_locals. cbn.

            assert (x1' <> x'). { intro. subst x1'.
              inv Hx'. unfold translate_var in H16.
              destruct (lenv ! x) eqn:Heqn; inv H16.
              specialize H13 with err_str. unfold translate_var in H13.
              destruct (lenv ! x1) eqn:Heqn'; inv H13.
              have Hcontra := HlenvInjective _ _ _ _ n0 Heqn Heqn'.
              now apply Hcontra. }

          exists x1'. split; auto.
          rewrite set_nth_nth_error_other; auto. eapply HlocalBound. eassumption.
          eapply val_relation_depends_on_finst; try eassumption; auto.
        }
     }}

     assert (HfdsEqRhoEmpty': forall (x1 : positive) (rho' : M.t cps.val) (fds' : fundefs) (f' : var) v0,
                                                 (map_util.M.set x v rho) ! x1 = Some v0 ->
                                                 subval_or_eq (Vfun rho' fds' f') v0 ->
                                                 fds' = fds /\ rho' = M.empty _). {
        intros x1 rho' fds' f' v0 Hrho' Hval.
        destruct (var_dec x x1).
        (* x=x1 *)
        { subst x1. rewrite M.gss in Hrho'. inv Hrho'.
          assert (In v0 vs). { now eapply nthN_In. }
          assert (Hsub: subval_or_eq (Vfun rho' fds' f') (Vconstr t vs)).
          { now eapply subval_or_eq_constr. }
          have H' := HfdsEqRhoEmpty _ _ _ _ _ Hrho Hsub. now destruct H'. }
        (* x<>x1 *)
        { rewrite M.gso in Hrho'; auto. eapply HfdsEqRhoEmpty in Hrho'.
          eassumption. eassumption. }
     }

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
           repr_val_LambdaANF_Codegen cenv fenv nenv host_function
             (Vfun (M.empty cps.val) fds a) sr
             {|
               f_locs :=
                 set_nth (wasm_deserialise bs T_i32)
                   (f_locs fr) x' (wasm_deserialise bs T_i32);
               f_inst := f_inst fr
             |} (Val_funidx fidx)))). {
         intros ? ? ? ? ? Hfd. apply Hfds with (errMsg:=errMsg) in Hfd.
         destruct Hfd as [? [? [? [idx [HtransF Hval]]]]].
         repeat (split; try assumption).
         exists idx. split. assumption.
         eapply val_relation_func_depends_on_funcs.
         2:{ eapply val_relation_depends_on_finst; last apply Hval. now subst. }
         congruence.
      }

     assert (Hinv': INV lenv sr {| f_locs := set_nth (wasm_deserialise bs T_i32)
                                (f_locs fr) x' (wasm_deserialise bs T_i32);
                      f_inst := f_inst fr |}). {
       cbn. eapply update_local_preserves_INV. 3: reflexivity.
       assumption. apply nth_error_Some. intros. apply nth_error_Some.
       eapply HlocalBound. eassumption. }

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

     have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _ HlenvInjective HenvsDisjoint
                      state _ _ _ HfdsEqRhoEmpty' Hfds' Hinv' H7 Hrm.
     destruct IH as [sr' [f' [Hred [Hval [Hfinst [Hsfuncs [HvalPres H_INV]]]]]]]. cbn in Hfinst.

     exists sr', f'. cbn. split.
     { (* take steps *)
       have Htmp := Hy'. inv Htmp.

       have I := Hinv'. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem _]]]]]]].
       have Hly := HlocalBound _ _ Hy'.
       have Hlx := HlocalBound _ _ Hx'.
       rewrite H in H10. injection H10 => ?. subst. clear H10.

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
       eassumption. apply H9.

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
       (* dostep' with fr *)
       eapply rt_trans with (y := (?[hs], ?[sr], {|
             f_locs :=
               set_nth (wasm_deserialise bs T_i32) (f_locs fr) x' (wasm_deserialise bs T_i32);
             f_inst := f_inst fr
           |}, ?[s])); first  apply rt_step.

       cbn. separate_instr. elimr_nary_instr 1.
       apply r_set_local with (vd := (wasm_deserialise bs T_i32)). reflexivity.
       apply /ssrnat.leP. apply HlocalBound in Hx'. assumption.
       reflexivity. cbn. apply Hred. }
     do 4 (split; auto).
     intros. apply HvalPres. now apply val_relation_depends_on_finst with (fr:=fr).
    }
  - (* Ecase *)
    { generalize dependent y. generalize dependent instructions.
      induction cl; intros; subst. inv H1. destruct a. rename c0 into t0.

      assert (caseConsistent cenv cl t). { inv H0. assumption. }
      cbn in H1. destruct (M.elt_eq t0 t).
      { (* t0 = t *)
        inv H1. clear IHcl.
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem [_ [_ [_ [_ [_ [HlocalBound _]]]]]]]]]]]]].
        inv Hrepr_e.
        { (* unboxed constructor TODO *) admit. }
        { (* boxed constructor *)
          rename H6 into Hy'.

          assert (Hy : occurs_free (Ecase y ((t, e) :: cl)) y) by constructor.
          have Hrel_m' := Hrel_m.
          destruct Hrel_m' as [Hfun1 [Hfun2 Hvar]].
          assert (HfdNone: find_def y fds = None). {
            apply HfenvWf_None with (f:=y) in HfenvWf. rewrite HfenvWf.
            inv Hy'. unfold translate_var in H1. destruct (lenv ! y) eqn:Hy'; inv H1.
            now apply HenvsDisjoint in Hy'. }
          apply Hvar in Hy; auto. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
          rewrite Hrho in H. inv H.
          have Hrepr' := Hrepr. inv Hrepr'.
          (* unboxed absurd *) assert (arity = 0) by congruence. lia.
          (* boxed *)
          destruct Hlocal as [i [Hl1 Hl2]]. inv Hy'. rewrite Hl1 in H. inv H.

        assert (Hrel: @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv e rho sr fr fds).
        { unfold rel_env_LambdaANF_Codegen. eauto. }

        assert (HeRestr': expression_restricted e). { inv HeRestr. now inv H1. }
        assert (Hunbound': (forall x : var, In x (collect_local_variables e) ->
                                                    rho ! x = None)). {
          intros. apply Hunbound. cbn. now apply in_or_app. }

        assert (Hnodup': NoDup (collect_local_variables e ++
                                collect_function_vars (Efun fds e))). {
          intros. cbn in Hnodup. rewrite <- app_assoc in Hnodup.
          now apply NoDup_app_remove_middle in Hnodup.
        }

      have IH := IHHev Hnodup' HfenvRho HeRestr' Hunbound' _ HlenvInjective HenvsDisjoint
                       state _ _ _ HfdsEqRhoEmpty Hfds Hinv H9 Hrel.
      destruct IH as [sr' [fr' [Hstep [Hval [Hfinst [HvalPres H_INV]]]]]].

      exists  sr', fr'. split.
      { (* steps *)
        dostep. elimr_nary_instr 0.
        apply r_get_local. eassumption.

        unfold load_i32 in H15.
        destruct (load m (N.of_nat addr) (N.of_nat 0) 4) eqn:Hload.

        dostep. elimr_nary_instr 1. eapply r_load_success. apply Hlinmem. eassumption.
        assert (N.of_nat addr = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))).
        { cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
        rewrite <- H. apply Hload.

        remember (VAL_int32 (tag_to_i32 t)) as tag.

        dostep. elimr_nary_instr 2. constructor. apply rs_relop. cbn.

        dostep'. constructor. apply rs_if_true.
        cbn. unfold nat_to_i32. unfold tag_to_i32.
        unfold Wasm_int.Int32.eq.
        cbn in Hload. rewrite Hload in H15. subst. injection H15 => H11'.
        destruct (zeq (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (decode_int b)))
          (Wasm_int.Int32.unsigned (Wasm_int.Int32.repr (Z.of_nat (Pos.to_nat t))))) eqn:Heq.
        discriminate. contradiction.

        dostep'. constructor. eapply rs_block with (vs := []); auto. unfold to_e_list. cbn.
        eapply reduce_trans_label. apply Hstep. unfold load_i32 in H15. rewrite Hload in H15. inv H15. }
        auto. }
      }
    {

    (* t0 <> t *)
    inv H0. inv Hrepr_e. (* unboxed TODO *) admit.
    assert (Hrel: @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv (Ecase y cl) rho sr fr fds).
    { unfold rel_env_LambdaANF_Codegen. destruct Hrel_m as [Hfun1 [Hfun2 Hvar]]. eauto. }

    assert (HeRestr' : expression_restricted (Ecase y cl)). { inv HeRestr. inv H3.
                                                               now constructor. }
    assert (Hunbound' : forall x : var, In x (collect_local_variables (Ecase y cl)) ->
                                        rho ! x = None). {
      intros. apply Hunbound. now apply in_or_app. }

    assert (Hnodup' : NoDup (collect_local_variables (Ecase y cl) ++
                             collect_function_vars (Efun fds (Ecase y cl)))). {
      cbn in Hnodup. rewrite <- app_assoc in Hnodup. now apply NoDup_app_remove_l in Hnodup.
    }

    have IH := IHcl H10 H1 _ _ Hnodup' HeRestr' Hunbound' H H11 Hrel.
    destruct IH as [sr' [f' [Hred [Hval [Hfinst [HvalPres H_INV]]]]]].

    (* t <> t0 *)
    assert (Hy : occurs_free (Ecase y ((t0, e0) :: cl)) y) by constructor.
    have Hrel_m' := Hrel_m.
    destruct Hrel_m' as [Hfun Hvar].
    assert (HfNone: find_def y fds = None). {
      apply HfenvWf_None with (f:=y) in HfenvWf. rewrite HfenvWf. inv H8.
      unfold translate_var in H0. destruct (lenv ! y) eqn:Hy'; inv H0.
      now apply HenvsDisjoint in Hy'. }
    apply Hvar in Hy; auto. destruct Hy as [v6 [wal [Hrho [Hlocal Hrepr]]]].
    rewrite Hrho in H. inv H.

    have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [Hlinmem [_ [_ [_ [_ [_ [HlocalBound _]]]]]]]]]]]]].
    have Hl := HlocalBound _ _ H8. apply nth_error_Some in Hl. apply notNone_Some in Hl.
    destruct Hl as [x H].
    have Htmp := H8. inv Htmp.
    have Hrepr' := Hrepr. inv Hrepr'.  (* unboxed absurd TODO *) admit.
    inv Hlocal. destruct H3.
    rewrite H3 in H0. inv H0. rewrite H4 in H. inv H.

    eexists. eexists. cbn. split.

    (* execute instructions *)
    dostep. elimr_nary_instr 0.
    apply r_get_local. eassumption.
    assert (Harith: (N.of_nat addr) = (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))).
    { cbn. rewrite Wasm_int.Int32.Z_mod_modulus_id; lia. }
    cbn. rewrite Harith in H22. unfold load_i32 in H22.
    destruct (load m (Wasm_int.N_of_uint i32m (wasm_value_to_i32 (Val_ptr addr)))
         (N.of_nat 0) 4) eqn:Hload.
    { dostep. elimr_nary_instr 1.
      eapply r_load_success.
      apply Hlinmem. eassumption.
      apply Hload. rewrite Hload in H22.
      assert (Hser: wasm_deserialise b T_i32 = VAL_int32 (tag_to_i32 t)) by congruence.
      rewrite Hser.

      dostep. elimr_nary_instr 2.
      constructor. apply rs_relop.
      assert (Hb0: (wasm_bool
                (app_relop (Relop_i ROI_eq) (VAL_int32 (tag_to_i32 t))
                   (nat_to_value (Pos.to_nat t0)))) = nat_to_i32 0). {
        unfold nat_to_value, nat_to_i32, tag_to_i32.
        unfold wasm_bool. cbn. unfold Wasm_int.Int32.eq. cbn. rewrite zeq_false; auto.

        assert (HtBounds: (Z.of_nat (Pos.to_nat t) < Wasm_int.Int32.modulus /\
                           Z.of_nat (Pos.to_nat t0) < Wasm_int.Int32.modulus)%Z). {
          inv HeRestr. inv H22. rewrite Forall_forall in H0. apply findtag_In in H1.
          assert (H': In (t, e) ((t0, e0) :: cl)). { now right. }
          assert (H'' : In (t0, e0) ((t0, e0)::cl)). { now left. }
          apply H0 in H'. apply H0 in H''. destruct H', H''. split; auto. }
        destruct HtBounds.
        repeat rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia. }
      rewrite Hb0.
      dostep'. constructor. apply rs_if_false. reflexivity.

      dostep'. constructor. eapply rs_block with (vs := []); eauto. cbn.
      eapply reduce_trans_label. unfold to_e_list. apply Hred.
     } unfold load_i32 in H22. rewrite Hload in H22. inv H22. auto. }
   }
  - (* Eapp *)
    { inv Hrepr_e. rename args' into args_instr.
      (* treat direct + indirect calls in one *)
      assert (Hval: exists fidx,
        reduce_trans (state, sr, fr, [AI_basic instr])
                     (state, sr, fr, [AI_basic (BI_const (nat_to_value fidx))]) /\
        repr_val_LambdaANF_Codegen cenv fenv nenv _ (Vfun (M.empty _) fds f') sr fr (Val_funidx fidx)). {
      inv H8.
      { (* indirect call *)
        assert (Hocc: occurs_free (Eapp f t ys) f) by constructor.
        have Hrel := Hrel_m. destruct Hrel as [_ [_ Hvar]].
        assert (HfNone: find_def f fds = None). {
          apply HfenvWf_None with (f:=f) in HfenvWf. rewrite HfenvWf.
          inv H3. unfold translate_var in H4. destruct (lenv ! f) eqn:Hf'; inv H4.
          now apply HenvsDisjoint in Hf'. }
        apply Hvar in Hocc; auto. destruct Hocc as [val [wal [Hrho [[j [Htrans Hwal]] Hval]]]].
        inv H3. rewrite Htrans in H4. inv H4.
        rewrite H in Hrho. inv Hrho. inv Hval.
        rewrite H1 in H8. symmetry in H8. inv H8.
        rename i into locIdx.
        assert (fl = fds). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. } subst fl.
        exists idx. split.
        dostep'. apply r_get_local. eassumption. apply rt_refl.
        econstructor; eauto. }
      { (* direct call *)
        inv H3. unfold translate_var in H4. destruct (fenv ! f) eqn:Hf; inv H4.
        assert (Hf': exists i, fenv ! f = Some i) by eauto.
        apply HfenvWf in Hf'.
        assert (Htemp: rho' = M.empty _ /\ f = f'). {
          apply HfenvRho in H. now inv H. now destruct Hf'. }
        inv Htemp. rename f' into f.
        assert (fl = fds). { apply HfenvRho in H. now inv H. now destruct Hf'. } subst fl.
        destruct Hrel_m as [Hfun1 [Hfun2 _]].
        assert (Hsubval: subval_or_eq (Vfun (M.empty cps.val) fds f)
                                      (Vfun (M.empty cps.val) fds f)) by constructor.
        have H' := Hfun1 _ _ _ H Hsubval. apply Hfun2 with (errMsg:=errMsg) in H'.
        destruct H' as [idx [HtransF Hval]].
        assert (idx = i). { unfold translate_var in HtransF. now rewrite Hf in HtransF. }
        subst idx. exists i. split. apply rt_refl.
        assumption.
      }
    }

    destruct Hval as [fidx [HredF Hval]]. inv Hval.
    assert (fl = fds). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. } subst fl.
    rewrite H9 in H1. inv H1. rename H16 into Hexpr.

    repeat rewrite map_cat. cbn.
    have Hfargs := fun_args_reduce state _ _ _ _ _ _ _ _ _ Hinv H0 HenvsDisjoint HfenvWf HfenvRho Hrel_m H7.
    destruct Hfargs as [args [HfargsRed HfargsRes]].

    remember {| f_locs := [seq nat_to_value a | a <- args] ++
                     n_zeros (repeat T_i32 (Datatypes.length (collect_local_variables e)));
               f_inst := f_inst fr |} as f_before_IH.

    (* prepare IH *)
    remember (create_local_variable_mapping (xs ++(collect_local_variables e))) as lenv_before_IH.
    assert (HfdsEqRhoEmpty_before_IH: (forall (x : positive) (rho' : M.t cps.val) (fds' : fundefs) (f' : var) v,
      rho'' ! x = Some v -> subval_or_eq (Vfun rho' fds' f') v ->
                                     fds' = fds /\ rho' = M.empty _)). {
      intros.
      assert (rho' = M.empty _). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. } subst rho'.
      assert (Hdec: decidable_eq var). {
        intros n m. unfold Decidable.decidable. now destruct (var_dec n m). }
      have H' := In_decidable Hdec x xs. clear Hdec. destruct H'.
      { (* In x xs *)
        have H' := set_lists_In _ _ _ _ _ _ H4 H1 H2.
        destruct (get_list_In_val _ _ _ _ H0 H') as [y [Hin Hrho]].
        eapply HfdsEqRhoEmpty in Hrho. now destruct Hrho. eassumption. }
      { (* ~In x xs *)
        have H' := set_lists_not_In _ _ _ _ _ H2 H4. rewrite H1 in H'.
        erewrite def_funs_find_def in H'. inv H'.
        { apply subval_fun in H3. now destruct H3 as [? [? ?]].
          assert (Hfd: find_def x fds <> None). {
            have H' := set_lists_not_In _ _ _ _ _ H2 H4.
            rewrite H1 in H'. inv H'. intro Hcontra.
            eapply def_funs_not_find_def in Hcontra. erewrite Hcontra in H10.
            discriminate.
          }
          apply notNone_Some in Hfd. destruct Hfd.
          now eapply find_def_name_in_fundefs. }
        intro Hcontra.
        apply def_funs_spec in H'. destruct H' as [[? ?] | [? Hcontra']]. 2: inv Hcontra'.
        apply name_in_fundefs_find_def_is_Some in H5. now destruct H5 as [? [? [? ?]]].
      }
    }

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
           repr_val_LambdaANF_Codegen cenv fenv nenv
             host_function
             (Vfun (M.empty cps.val) fds a) sr
             f_before_IH (Val_funidx fidx)))). {
         intros ? ? ? ? ? Hfd. eapply Hfds with (errMsg:=errMsg) in Hfd.
         destruct Hfd as [? [? [? [idx [HtransF Hval]]]]].
         repeat (split; try assumption).
         exists idx. split. assumption.
         eapply val_relation_func_depends_on_funcs.
         2:{ eapply val_relation_depends_on_finst; last apply Hval. now subst. }
         congruence.
    }

    assert (Hinv_before_IH : INV lenv_before_IH sr f_before_IH). {
       subst. eapply init_locals_preserves_INV; try eassumption; try reflexivity.
       intros. inv H1. apply var_mapping_list_lt_length in H3.
       rewrite app_length in H3.
       apply const_val_list_length_eq in HfargsRes.
       rewrite <- HfargsRes.
       apply set_lists_length_eq in H2. rewrite <- H2. eassumption.
       repeat f_equal. unfold n_zeros. rewrite map_repeat_eq.
       rewrite <- map_map_seq. cbn. now rewrite map_repeat_eq. }

    assert (Hrelm: @rel_env_LambdaANF_Codegen cenv fenv nenv host_function
                              lenv_before_IH e rho'' sr f_before_IH fds). {
      unfold rel_env_LambdaANF_Codegen. split.
      { (* funs1 *) intros.
        assert (rho' = M.empty _). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. }
        subst rho'.
        assert (Hdec: decidable_eq var). {
          intros n m. unfold Decidable.decidable. now destruct (var_dec n m). }
       have H' := In_decidable Hdec x xs. clear Hdec. destruct H'.
       { (* In x xs *)
         have H' := set_lists_In _ _ _ _ _ _ H4 H1 H2.
         destruct (get_list_In_val _ _ _ _ H0 H') as [y [Hiny HyRho]].
         destruct Hrel_m as [Hfun1 [Hfun2 _]]. eauto.
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
         destruct H3 as [f1 [?H ?H]]. inv H3. inv H10.
         apply name_in_fundefs_find_def_is_Some in H5.
         destruct H5 as [? [? [? ?]]]. apply Hfds with (errMsg:=""%bs) in H3.
         now destruct H3 as [_ [_ [_ [fidx' [HtransF Hval]]]]].
      }} split.
      { (* fun2 *)
        destruct Hrel_m as [_ [Hfun2 _]].
        intros ? ? Hnfd. apply Hfun2 with (errMsg:=errMsg) in Hnfd.
        destruct Hnfd as [i [Htrans Hval]].
        exists i. split. assumption.
        eapply val_relation_depends_on_finst. 2: eassumption.
        subst f_before_IH. reflexivity. }
      { (* vars *)
        intros. destruct Hrel_m as [_ HrelVars].
        assert (In x xs). {
          apply Hfds with (errMsg:=""%bs) in H9; auto. destruct H9 as [? [Hxxs ?]].
          have H' := Hxxs _ H1. now destruct H'. }
        destruct (get_set_lists_In_xs _ _ _ _ _ H4 H2) as [v' Hv'].
        have H' := set_lists_nth_error _ _ _ _ _ _ H2 H4 Hv'.
        destruct H' as [k [Hvk Hxk]].
        have H'' := const_val_list_nth_error _ _ _ _ _ _ HfargsRes Hvk.
        destruct H'' as [w [Hw Hnth]].
        exists v', w. split; auto. split; auto.

        unfold stored_in_locals. subst lenv_before_IH f_before_IH. exists k.
        split. {
          intros. unfold create_local_variable_mapping.
          rewrite (var_mapping_list_lt_length_nth_error_idx _ k); auto.
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
        subst f_before_IH. eapply val_relation_depends_on_finst; last eassumption.
        reflexivity. }
    }

    assert (HeRestr' : expression_restricted e). {
        apply Hfds with (errMsg:=""%bs) in H9. now destruct H9. }

    assert (Hunbound': (forall x : var, In x (collect_local_variables e) -> rho'' ! x = None)). {
      intros.
      assert (rho' = M.empty _). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. } subst rho'.
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
    assert (rho' = M.empty _). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. }
    subst rho'.
    eapply def_funs_find_def in H3. now erewrite H' in H3. }

    subst lenv_before_IH.
    have IH := IHHev Hnodup' HfenvRho' HeRestr' Hunbound' _  HlenvInjective' HenvsDisjoint'
                   state _ _ _ HfdsEqRhoEmpty_before_IH Hfds_before_IH Hinv_before_IH Hexpr Hrelm.

    destruct IH as [sr_final [fr_final [Hred [Hval [Hfinst [Hfuncs [HvalPres H_INV]]]]]]].

    (* start execution *)
    eexists. eexists. split.
    eapply rt_trans. apply app_trans. apply HfargsRed.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    separate_instr. apply app_trans. apply HredF.
    eapply rt_trans. apply app_trans_const. apply map_const_const_list.
    dostep'. eapply r_call_indirect_success; eauto.
    { (* table identity map *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Htableid _]]]]]]]]]]]].
      inv H6. eapply Htableid. eassumption. }
    { (* type *)
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Htype]]]]]]]]]]]]].
      assert (Hlen: length xs = length ys). {
        apply set_lists_length_eq in H2.
        apply get_list_length_eq in H0. rewrite H2 H0. reflexivity. }
      rewrite Htype. 2: { inv HeRestr. congruence. } rewrite -Hlen. cbn. inv H9.
      now rewrite map_repeat_eq. } apply rt_refl.
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
    eapply reduce_trans_local.
    dostep'. constructor. eapply rs_block with (vs:=[]); auto. cbn.
    (* apply IH *)
    eapply reduce_trans_label. eassumption. split.
    eapply result_val_LambdaANF_Codegen_depends_on_finst; try apply Hval.
    subst f_before_IH. now rewrite -Hfinst. split. reflexivity. split. congruence.
    split. { intros. apply val_relation_depends_on_finst with (fr:=fr_final).
             subst f_before_IH. cbn in Hfinst. congruence.
             apply HvalPres. apply val_relation_depends_on_finst with (fr:=fr).
             subst f_before_IH. reflexivity. assumption. }
    intro H_INV'. have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [? [_ [_ [_ [? _]]]]]]]]]]]]].
    eapply change_locals_preserves_INV with (l:=fr.(f_locs)); auto. apply H_INV.
    unfold INV_result_var_out_of_mem_is_zero in H_INV'.
      subst f_before_IH. rewrite Hfinst in H_INV'. apply H_INV'.
      subst f_before_IH. cbn in Hfinst. rewrite -Hfinst. cbn.
      now destruct fr.
    }

  - (* Eletapp *)
    (* needs 2 IH, first one for the function body (mostly copy paste from Eapp, could be refactored),
                   second one for the continuation, similar to the other cases *)
    { inv Hrepr_e. rename args' into args_instr. rename e into e_cont, x into x_res.
      (* treat direct + indirect calls in one *)
      assert (Hval: exists fidx,
        reduce_trans (state, sr, fr, [AI_basic instr])
                     (state, sr, fr, [AI_basic (BI_const (nat_to_value fidx))])
     /\ @repr_val_LambdaANF_Codegen cenv fenv nenv _ (Vfun (M.empty _) fds f') sr fr (Val_funidx fidx)
     /\ exists e_body', repr_expr_LambdaANF_Codegen cenv fenv nenv e_body e_body'
                 (lenv:=(create_local_variable_mapping (xs ++ collect_local_variables e_body)%list))). {
      inv H12.
      { (* indirect call *)
        assert (Hocc: occurs_free (Eletapp x_res f t ys e_cont) f). { constructor. by left. }
        have Hrel := Hrel_m. destruct Hrel as [_ Hlocals].
        assert (HfNone: find_def f fds = None). {
          apply HfenvWf_None with (f:=f) in HfenvWf. rewrite HfenvWf.
          inv H3. unfold translate_var in H4. destruct (lenv ! f) eqn:Hf'; inv H4.
          now apply HenvsDisjoint in Hf'. }
        apply Hlocals in Hocc; auto. destruct Hocc as [val [wal [Hrho [[j [Htrans Hwal]] Hval]]]].
        inv H3. rewrite Htrans in H4. inv H4.
        rewrite H in Hrho. inv Hrho. inv Hval.
        rewrite H1 in H7. symmetry in H7. inv H7.
        rename i into locIdx.
        assert (fl = fds). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. } subst fl.
        exists idx. split.
        dostep'. apply r_get_local. eassumption. apply rt_refl. split.
        econstructor; eauto. eauto. }
      { (* direct call *)
        inv H3. unfold translate_var in H4. destruct (fenv ! f) eqn:Hf; inv H4.
        assert (Hf': exists i, fenv ! f = Some i) by eauto.
        apply HfenvWf in Hf'.
        assert (Htemp: rho' = M.empty _ /\ f = f'). {
          apply HfenvRho in H. now inv H. now destruct Hf'. }
        inv Htemp. rename f' into f.
        assert (fl = fds). { apply HfenvRho in H. now inv H. now destruct Hf'. } subst fl.
        destruct Hrel_m as [Hfun1 [Hfun2 _]].
        assert (Hsubval: subval_or_eq (Vfun (M.empty cps.val) fds f)
                                      (Vfun (M.empty cps.val) fds f)) by constructor.
        have H' := Hfun1 _ _ _ H Hsubval. apply Hfun2 with (errMsg:=errMsg) in H'.
        destruct H' as [idx [HtransF Hval]].
        assert (idx = i). { unfold translate_var in HtransF. now rewrite Hf in HtransF. }
        subst idx. exists i. split. apply rt_refl.
        split. assumption. inv Hval. rewrite H7 in H1. inv H1. eauto.
      }
    }

    destruct Hval as [fidx [HredF [Hval [e_body' HexprBody]]]]. inv Hval.
    assert (fl = fds). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. } subst fl.
    rewrite H7 in H1. inv H1. rename H18 into Hexpr.

    repeat rewrite map_cat. cbn.
    have Hrel_m' := rel_env_app_letapp _ _ _ _ _ _ _ _ _ Hrel_m.
    have Hfargs := fun_args_reduce state _ _ _ _ _ _ _ _ _ Hinv H0 HenvsDisjoint HfenvWf HfenvRho Hrel_m' H11.
    destruct Hfargs as [args [HfargsRed HfargsRes]].

    remember {| f_locs := [seq nat_to_value a | a <- args] ++
                     n_zeros (repeat T_i32 (Datatypes.length (collect_local_variables e_body)));
               f_inst := f_inst fr |} as f_before_IH.

    (* prepare IH1 for e_body *)
    remember (create_local_variable_mapping (xs ++ collect_local_variables e_body)) as lenv_before_IH.
    assert (HfdsEqRhoEmpty_before_IH: (forall (x : positive) (rho' : M.t cps.val) (fds' : fundefs) (f' : var) v,
      rho'' ! x = Some v -> subval_or_eq (Vfun rho' fds' f') v ->
                                     fds' = fds /\ rho' = M.empty _)). {
      intros.
      assert (rho' = M.empty _). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. } subst rho'.
      assert (Hdec: decidable_eq var). {
        intros n m. unfold Decidable.decidable. now destruct (var_dec n m). }
      have H' := In_decidable Hdec x xs. clear Hdec. destruct H'.
      { (* In x xs *)
        have H' := set_lists_In _ _ _ _ _ _ H4 H1 H2.
        destruct (get_list_In_val _ _ _ _ H0 H') as [y [Hin Hrho]].
        eapply HfdsEqRhoEmpty in Hrho. now destruct Hrho. eassumption. }
      { (* ~In x xs *)
        have H' := set_lists_not_In _ _ _ _ _ H2 H4. rewrite H1 in H'.
        erewrite def_funs_find_def in H'. inv H'.
        { apply subval_fun in H3. now destruct H3 as [? [? ?]].
          assert (Hfd: find_def x fds <> None). {
            have H' := set_lists_not_In _ _ _ _ _ H2 H4.
            rewrite H1 in H'. inv H'. intro Hcontra.
            eapply def_funs_not_find_def in Hcontra. erewrite Hcontra in H8.
            discriminate.
          }
          apply notNone_Some in Hfd. destruct Hfd.
          now eapply find_def_name_in_fundefs. }
        intro Hcontra.
        apply def_funs_spec in H'. destruct H' as [[? ?] | [? Hcontra']]; subst. 2: inv Hcontra'.
        apply name_in_fundefs_find_def_is_Some in H5. now destruct H5 as [? [? [? ?]]]. }
    }

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
           repr_val_LambdaANF_Codegen cenv fenv nenv
             host_function
             (Vfun (M.empty cps.val) fds a) sr
             f_before_IH (Val_funidx fidx)))). {
         intros ? ? ? ? ? Hfd. eapply Hfds with (errMsg:=errMsg) in Hfd.
         destruct Hfd as [? [? [? [idx [HtransF Hval]]]]].
         repeat (split; try assumption).
         exists idx. split. assumption.
         eapply val_relation_func_depends_on_funcs.
         2:{ eapply val_relation_depends_on_finst; last apply Hval. now subst. }
         congruence.
    }

    assert (Hinv_before_IH : INV lenv_before_IH sr f_before_IH). {
       subst. eapply init_locals_preserves_INV; try eassumption; try reflexivity.
       intros. inv H1. apply var_mapping_list_lt_length in H3.
       rewrite app_length in H3.
       apply const_val_list_length_eq in HfargsRes.
       rewrite <- HfargsRes.
       apply set_lists_length_eq in H2. rewrite <- H2. eassumption.
       repeat f_equal. unfold n_zeros. rewrite map_repeat_eq.
       rewrite <- map_map_seq. cbn. now rewrite map_repeat_eq. }

    assert (Hrelm: @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv_before_IH
                              e_body rho'' sr f_before_IH fds). {
      unfold rel_env_LambdaANF_Codegen. split.
      { (* funs1 *) intros.
        assert (rho' = M.empty _). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. }
        subst rho'.
        assert (Hdec: decidable_eq var). {
          intros n m. unfold Decidable.decidable. now destruct (var_dec n m). }
       have H' := In_decidable Hdec x xs. clear Hdec. destruct H'.
       { (* In x xs *)
         have H' := set_lists_In _ _ _ _ _ _ H4 H1 H2.
         destruct (get_list_In_val _ _ _ _ H0 H') as [y [Hiny HyRho]].
         destruct Hrel_m as [Hfun1 [Hfun2 _]]. eauto. }
       { (* ~In x xs *)
         have H' := set_lists_not_In _ _ _ _ _ H2 H4. rewrite H1 in H'.
         erewrite def_funs_find_def in H'.
         2:{ intro Hcontra. apply def_funs_not_find_def with (fds':=fds) (rho:=M.empty _) in Hcontra.
             rewrite Hcontra in H'. inv H'. } inv H'.
         have H' := set_lists_not_In _ _ _ _ _ H2 H4.
         rewrite H1 in H'.
         apply def_funs_spec in H'. destruct H' as [[? ?] | [? Hcontra]]. 2: inv Hcontra.
         apply subval_fun in H3. 2: assumption.
         destruct H3 as [f1 [?H ?H]]. inv H3. inv H8. assumption. }
      } split.
      { (* funs2 *)
        intros ? ? Hnfd. destruct Hrel_m as [_ [Hfun2 _]].
        apply Hfun2 with (errMsg:=errMsg) in Hnfd.
        destruct Hnfd as [i [Htrans Hval]].
        exists i. split. assumption.
        eapply val_relation_depends_on_finst. 2: eassumption.
        subst f_before_IH. reflexivity. }
      { (* vars *)
        intros. destruct Hrel_m as [_ HrelVars].
        assert (In x xs). {
          apply Hfds with (errMsg:=""%bs) in H7; auto. destruct H7 as [? [Hxxs ?]].
          have H' := Hxxs _ H1. now destruct H'. }
        have H' := get_set_lists_In_xs _ _ _ _ _ H4 H2. destruct H' as [v'' Hv'].
        have H' := set_lists_nth_error _ _ _ _ _ _ H2 H4 Hv'.
        destruct H' as [k [Hvk Hxk]].
        have H'' := const_val_list_nth_error _ _ _ _ _ _ HfargsRes Hvk.
        destruct H'' as [w [Hw Hnth]].
        exists v'', w. split; auto. split; auto.

        unfold stored_in_locals. subst lenv_before_IH f_before_IH. exists k.
        split. {
          intros. unfold create_local_variable_mapping.
          rewrite (var_mapping_list_lt_length_nth_error_idx _ k); auto.
          apply Hfds with (errMsg:=""%bs) in H7. destruct H7 as [_ [_ [HnodupE _]]].
          rewrite catA in HnodupE. apply NoDup_app_remove_r in HnodupE. assumption.
          rewrite nth_error_app1; auto. apply nth_error_Some. intro.
          rewrite H5 in Hxk. inv Hxk. }
        cbn.
        rewrite nth_error_app1. 2: {
          rewrite length_is_size size_map -length_is_size.
          apply const_val_list_length_eq in HfargsRes.
          rewrite -HfargsRes.
          apply nth_error_Some. congruence. } assumption.
        subst f_before_IH. eapply val_relation_depends_on_finst; last eassumption.
        reflexivity. }
    }

    assert (HeRestr' : expression_restricted e_body). {
        apply Hfds with (errMsg:=""%bs) in H7. now destruct H7. }

    assert (Hunbound': (forall x : var, In x (collect_local_variables e_body) -> rho'' ! x = None)). {
      intros.
      assert (rho' = M.empty _). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. } subst rho'.
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
    assert (rho' = M.empty _). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. }
    subst rho'.
    eapply def_funs_find_def in H3. now erewrite H' in H3. }

    subst lenv_before_IH.
    have IH_body := IHHev1 Hnodup' HfenvRho' HeRestr' Hunbound' _  HlenvInjective' HenvsDisjoint'
                   state _ _ _ HfdsEqRhoEmpty_before_IH Hfds_before_IH Hinv_before_IH Hexpr Hrelm.
    clear HfenvRho' Hnodup' Hunbound' HeRestr' IHHev1.

    destruct IH_body as [sr_after_call [fr_after_call [Hred [Hval [Hfinst [Hfuncs [HvalPres H_INV]]]]]]].

    assert (Hcont: exists (sr_final : store_record) (fr_final : frame),
      reduce_trans (state, sr_after_call, fr, [ AI_basic (BI_get_global result_out_of_mem)
                                              ; AI_basic (BI_if (Tf [::] [::]) [::]
                                                 [:: BI_get_global result_var, BI_set_local x' & e'])])
                   (state, sr_final, fr_final, [])
         /\ result_val_LambdaANF_Codegen v' sr_final fr_final
         /\ fr_final.(f_inst) = fr.(f_inst)
         /\ sr_final.(s_funcs) = sr.(s_funcs)
            (* previous values are preserved *)
         /\ (forall wal val, repr_val_LambdaANF_Codegen cenv fenv nenv host_function val sr fr wal ->
                             repr_val_LambdaANF_Codegen cenv fenv nenv host_function val sr_final fr_final wal)
         /\ (INV_result_var_out_of_mem_is_zero sr_final fr_final -> INV lenv sr_final fr_final)). {
      assert (rho' = M.empty _). { eapply HfdsEqRhoEmpty in H. now destruct H. apply rt_refl. } subst rho'.
      destruct Hval as [Hsuccess | HOutOfMem].
      { (* success *)
        clear Hexpr. rename H10 into Hexpr.
        destruct Hsuccess as [w [wal [Hres [Heq [Hval HresM]]]]].
        have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HlocalBound _]]]]]]]]]]]]].

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

        assert (HfdsEqRhoEmpty_before_cont_IH: (forall (x : positive) (rho' : M.t val)
                                               (fds' : fundefs) (f' : var) (v0 : val),
           (map_util.M.set x_res v rho) ! x = Some v0 ->
             subval_or_eq (Vfun rho' fds' f') v0 ->
             fds' = fds /\ rho' = M.empty val)). {
          intros x ? ? ? ? Hrho' Hval'.
          destruct (var_dec x x_res).
          { (* x = x_res *)
            subst x_res. rewrite M.gss in Hrho'. symmetry in Hrho'. inv Hrho'.
            have H' := step_preserves_empty_env_fds _ _ _ _ fds _ _ _ _ _ Hev1 Hval'.
            edestruct H'.
            { intros ? ? ? ? ? Hrho Hsubval.
              assert (Hdec: decidable_eq var). { intros n m.
              unfold Decidable.decidable. now destruct (var_dec n m). }
              have H'' := In_decidable Hdec x0 xs. destruct H''.
              { (* In x0 xs *)
                have H'' := set_lists_In _ _ _ _ _ _ H1 Hrho H2.
                destruct (get_list_In_val _ _ _ _ H0 H'') as [y [HyIn HyRho]].
                have H12' := HfdsEqRhoEmpty _ _ _ _ _ HyRho Hsubval.
                destruct H12'. subst. destruct Hrel_m as [Hfun1 _].
                eapply Hfun1 in HyRho. 2: eassumption. auto.
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
                apply subval_fun in Hsubval.
                destruct Hsubval as [ff [Heq Hfundef]]. now inv Heq.
                apply def_funs_spec in H''. destruct H'' as [[? ?] | [? Hcontra]].
                assumption. inv Hcontra.
              }
            }
            { intros ? ? ? ? [HbodyNofun | HfdsNofun].
              - eapply repr_expr_LambdaANF_Codegen_no_Efun_subterm; eauto.
              - destruct HfdsNofun as [Hsub HsubFds].
                eapply dsubterm_fds_e_find_def in HsubFds.
                2:{ now apply NoDup_app_remove_l in Hnodup. }
                destruct HsubFds as [? [? [? Hfd]]].
                have Hfd' := Hfd.
                eapply Hfds in Hfd. destruct Hfd as [_ [_ [_ [? [? HvalFun]]]]]. inv HvalFun.
                assert (e = e'') by congruence. subst e''.
                eapply repr_expr_LambdaANF_Codegen_no_Efun_subterm; eauto.
            }
            now destruct H3.
          }
          { (* x <> x_res *)
            rewrite M.gso in Hrho'; auto. eapply HfdsEqRhoEmpty in Hrho'.
            eassumption. eassumption.
          }
        }

        assert (Hinv_before_cont_IH: INV lenv sr_after_call f_before_cont). {
          subst f_before_cont f_before_IH; cbn in Hfinst. apply H_INV in HresM.
          eapply update_local_preserves_INV. 3: subst w; reflexivity.
          eapply change_locals_preserves_INV with (l := f_locs fr). eassumption.
          assumption.
          have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [Hlocs32 _]]]]]]]]]. assumption.
          rewrite -Hfinst. now destruct fr.
          eapply HlocalBound. eassumption. }

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
               repr_val_LambdaANF_Codegen cenv fenv nenv
                 host_function
             (Vfun (M.empty cps.val) fds a) sr_after_call
             f_before_cont (Val_funidx fidx)))). {
             intros ? ? ? ? ? Hfd. eapply Hfds with (errMsg:=errMsg) in Hfd.
             destruct Hfd as [? [? [? [idx [HtransF' Hval']]]]].
             repeat (split; try assumption).
             exists idx. split. assumption.
             eapply val_relation_func_depends_on_funcs.
             2:{ eapply val_relation_depends_on_finst; last apply Hval'. now subst. }
             congruence.
        }

        assert (HrelM': @rel_env_LambdaANF_Codegen cenv fenv nenv host_function lenv
                          e_cont (map_util.M.set x_res v rho) sr_after_call f_before_cont fds). {
          unfold rel_env_LambdaANF_Codegen. split; intros.
          { (* funs1 *)
            destruct (var_dec x x_res).
            { (* x = x_res *)
              subst x_res. rewrite M.gss in H1. inv H1. rename v0 into v.
              destruct Hrel_m as [Hfun1 [Hfun2 _]].
              assert (Hsubval: subval_or_eq (Vfun (M.empty val) fds f0)
                                            (Vfun (M.empty val) fds f0)).
              { apply rt_refl. }
              have H''1 := Hfun1 _ _ _ _ Hsubval.

              have H' := step_preserves_empty_env_fds _ _ _ _ fds _ _ _ _ _ Hev1 H3.
              edestruct H'.
              { intros ? ? ? ? ? Hrho Hsubval'.
                assert (Hdec: decidable_eq var). { intros n m.
                unfold Decidable.decidable. now destruct (var_dec n m). }
                have H'' := In_decidable Hdec x0 xs. destruct H''.
                { (* In x0 xs *)
                  have H'' := set_lists_In _ _ _ _ _ _ H1 Hrho H2.
                  destruct (get_list_In_val _ _ _ _ H0 H'') as [y [HyIn HyRho]].
                  have H12' := HfdsEqRhoEmpty _ _ _ _ _ HyRho Hsubval'.
                  destruct H12'. subst.
                  eapply Hfun1 in HyRho. 2: eassumption. auto.
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
              - eapply repr_expr_LambdaANF_Codegen_no_Efun_subterm; eauto.
              - destruct HfdsNofun as [Hsub HsubFds].
                eapply dsubterm_fds_e_find_def in HsubFds.
                2:{ now apply NoDup_app_remove_l in Hnodup. }
                destruct HsubFds as [? [? [? Hfd]]].
                have Hfd' := Hfd.
                eapply Hfds in Hfd. destruct Hfd as [_ [_ [_ [? [? HvalFun]]]]]. inv HvalFun.
                assert (e = e'') by congruence. subst e''.
                eapply repr_expr_LambdaANF_Codegen_no_Efun_subterm; eauto. }
              { now destruct H4. }
           }
           { (* x <> x_res*)
             rewrite M.gso in H1; auto.
             destruct Hrel_m' as [Hfun1 [Hfun2 Hvar]].
             have H' := Hfun1 _ _ _ H1 H3. assumption.
           }
         } split.
         { (* funs2 *)
            intros ? ? Hnfd. destruct Hrel_m as [_ [Hfun2 _]].
            apply Hfun2 with (errMsg:=errMsg) in Hnfd.
            destruct Hnfd as [i [Htrans' Hval']].
            exists i. split. assumption.
            eapply val_relation_func_depends_on_funcs with (s:=sr). congruence.
            eapply val_relation_depends_on_finst; try eassumption.
            subst f_before_cont. reflexivity.
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
              have Hl := HlocalBound _ _ H9. apply nth_error_Some in Hl.
              apply notNone_Some in Hl. destruct Hl. subst f_before_cont.
              eapply set_nth_nth_error_same. eassumption.
              eapply val_relation_depends_on_finst; last apply Hval.
              subst f_before_cont f_before_IH. cbn.
              cbn in Hfinst. congruence. }
            { (* x <> x_res *)
              assert (Hocc: occurs_free (Eletapp x_res f t ys e_cont) x).
              { now apply Free_Eletapp2. }
              destruct Hrel_m as [_ [_ Hvar]].

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
              have Hl := HlocalBound _ _ H9. assumption.
              apply val_relation_depends_on_finst with (fr:=fr_after_call).
              subst f_before_cont f_before_IH. cbn.
              cbn in Hfinst. congruence. apply HvalPres.
              apply val_relation_depends_on_finst with (fr:=fr).
              subst f_before_IH. reflexivity. assumption.
            }
          }
        }

        have IH_cont := IHHev2 Hnodup' HfenvRho' HeRestr' Hunbound' lenv HlenvInjective HenvsDisjoint
                   state _ _ _ HfdsEqRhoEmpty_before_cont_IH Hfds_before_cont_IH Hinv_before_cont_IH Hexpr HrelM'.
        destruct IH_cont as [sr_final [fr_final [Hred' [Hval' [Hfinst' [Hfuncs' [HvalPres' H_INV']]]]]]]. clear IHHev2.

        exists sr_final, fr_final. split.
        dostep'. elimr_nary_instr 0. apply r_get_global. rewrite -Hfinst in HresM. subst f_before_IH. eassumption.
        dostep'. constructor. apply rs_if_false. reflexivity.
        dostep'. constructor. eapply rs_block with (vs := []); eauto. cbn.
        eapply reduce_trans_label.
        dostep'. elimr_nary_instr 0. apply r_get_global. rewrite -Hfinst in Hres. subst f_before_IH. eassumption.
        dostep'. elimr_nary_instr 1. eapply r_set_local with (f' := f_before_cont).
        subst f_before_cont. reflexivity.
        apply /ssrnat.leP. eapply HlocalBound. eassumption.
        subst f_before_cont w. reflexivity.
        assumption. split; auto.
        split. rewrite -Hfinst'. subst f_before_cont.
        reflexivity. split. congruence. split; last auto.
        intros. { apply HvalPres'. apply val_relation_depends_on_finst with (fr:=fr_after_call). subst. cbn. cbn in Hfinst. congruence. apply HvalPres.
        apply val_relation_depends_on_finst with (fr:=fr). subst f_before_IH. reflexivity.
        assumption. }
      }
      { (* out of mem *)
        exists sr_after_call, fr. split.
        dostep. elimr_nary_instr 0. apply r_get_global. rewrite -Hfinst in HOutOfMem. subst f_before_IH. eassumption.
        dostep'. constructor. apply rs_if_true. intro Hcontra. inv Hcontra.
        dostep'. constructor. eapply rs_block with (vs := []); eauto. cbn.
        dostep'. constructor. now apply rs_label_const. apply rt_refl.
        split. right. subst f_before_IH. rewrite -Hfinst in HOutOfMem. assumption.
        split. reflexivity. split. congruence. split.
        { intros. apply val_relation_depends_on_finst with (fr:=fr_after_call).
          subst f_before_IH. cbn in Hfinst. congruence. apply HvalPres.
          apply val_relation_depends_on_finst with (fr:=fr). subst f_before_IH. reflexivity.
          assumption. }
        intro Hcontra. unfold INV_result_var_out_of_mem_is_zero in Hcontra.
        subst f_before_IH. cbn in Hfinst. rewrite Hfinst in Hcontra.
        rewrite HOutOfMem in Hcontra. inv Hcontra.
      }
    }
    destruct Hcont as [sr_final [fr_final [Hred_final [Hval_final [Hfinst' [Hfuncs' [HvalPres' H_INV']]]]]]].

    (* start execution *)
    eexists. eexists. split.
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
      have I := Hinv. destruct I as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Htype]]]]]]]]]]]]].
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
    eapply reduce_trans_local.
    dostep'. constructor. eapply rs_block with (vs:=[]); auto. cbn.
    (* apply IH1: function body *)
    eapply reduce_trans_label. eassumption. cbn. apply Hred_final.
    do 4 (split; auto).
    }
  - (* Efun *)      inv Hrepr_e. (* absurd, fn defs only on topmost level *)
  - (* Eprim_val *) inv Hrepr_e. (* absurd, primitives not supported *)
  - (* Eprim *)     inv Hrepr_e. (* absurd, primitives not supported *)
  - (* Ehalt *)
    cbn. inv Hrepr_e. destruct Hrel_m as [_ [_ Hvar]].
    assert (HfNone: find_def x fds = None). {
      apply HfenvWf_None with (f:=x) in HfenvWf. rewrite HfenvWf.
      inv H1. unfold translate_var in H0. destruct (lenv ! x) eqn:Hx; inv H0. now apply HenvsDisjoint in Hx. }
     destruct (Hvar x) as [v6 [wal [Henv [Hloc Hrepr]]]]; auto.
    rewrite Henv in H. inv H.

    have I := Hinv. destruct I as [INVres [_ [HMzero [Hgmp_r [_ [Hmuti32 [Hlinmem [HgmpInMem [_ [Hfuncs [Hinstglobs _]]]]]]]]]]].
    apply global_var_w_implies_global_var_r in Hgmp_r; auto. destruct Hgmp_r.
    edestruct i32_exists_nat as [x'' [Hx'' ?]]. erewrite Hx'' in H. subst.

    destruct Hlinmem as [Hmem1 [m [Hmem2 [size [Hmem3 [Hmem4 Hmem5]]]]]]. subst.
    apply mem_length_upper_bound in Hmem5. cbn in Hmem5.
    have HinM := HgmpInMem _ _ Hmem2 H.

    unfold INV_result_var_writable, global_var_w in INVres.
    specialize INVres with (wasm_value_to_i32 wal).
    destruct INVres as [s' Hs].

    exists s', fr. cbn. split.
    destruct Hloc as [ilocal [H4 Hilocal]]. inv H1. erewrite H4 in H2. injection H2 => H'. subst.
    (* execute wasm instructions *)
    dostep. apply r_elimr. eapply r_get_local. eassumption.
    dostep'. apply r_set_global. eassumption.
    apply rt_refl.
    split; auto.
    unfold result_val_LambdaANF_Codegen. left.
    exists (wasm_value_to_i32 wal). exists wal.
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
        now rewrite -(update_global_preserves_memory _ _ _ _ _ Hs). }
      assert (sglob_val (host_function:=host_function) s' (f_inst fr) global_mem_ptr =
                                                    Some (VAL_int32 (nat_to_i32 x''))). {
      erewrite update_global_get_other; try eassumption. reflexivity. now intro.
    }
    eapply val_relation_depends_on_mem_smaller_than_gmp_and_funcs; try apply H2; eauto.
    eapply update_global_preserves_funcs. eassumption.
    simpl_modulus. cbn. lia. simpl_modulus. cbn. lia.
    }
    intro H_INV. eapply update_global_preserves_INV. 6: eassumption.
    assumption. now intro. eassumption.
    eapply value_bounds; eauto. now intro.
    Unshelve. all: try assumption; try apply ""%bs.
Admitted. (* Qed *)

End THEOREM.

Section MAIN.

Import host instantiation_spec.
Import Lia.
Import Relations.Relation_Operators.
Import ssreflect seq eqtype.

Import LambdaANF.toplevel LambdaANF.cps LambdaANF.cps_show.
Import Common.compM Common.Pipeline_utils.

Import ExtLib.Structures.Monad.
Import MonadNotation.
Import numerics.
Import bytestring.

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

Lemma reduce_nil_false : forall state s f,
  ~ exists y,
  (reduce_tuple (host_instance:=host_instance))
  (state, s, f, []) y.
Proof.
  intros ? ? ? [[[[hs' s'] f'] instr'] Hcontra]. cbn in Hcontra.
  remember [] as l. revert Heql.
  induction Hcontra; intros; subst; try discriminate.
  { inv H. destruct vs; inv H0. destruct vs; inv H0.
    destruct lh; cbn in H1; destruct (v_to_e_list l); inv H1. }
  { destruct vcs; inv Heql. }
  { destruct vcs; inv Heql. }
  { destruct vcs; inv Heql. }
  { destruct lh; cbn in Heql; destruct (v_to_e_list l); inv Heql.
    destruct es; auto. inv H0. }
Qed.


Lemma reduce_const_false : forall state state' s s' f f' c instr,
  ~ (reduce_tuple (host_instance:=host_instance))
  (state, s, f, [AI_basic (BI_const c)]) (state', s', f', instr).
Proof.
  intros ? ? ? ? ? ? ? ? Hcontra. cbn in Hcontra.
  remember ([AI_basic (BI_const c)]) as instr'. generalize dependent c.
  induction Hcontra; intros; try discriminate. subst.
  { inv H. destruct vs; inv H0. destruct vs; inv H4.
           destruct vs; inv H0. destruct vs; inv H4.
           destruct lh; inv H1. destruct (v_to_e_list l); inv H2.
           destruct l1; inv H3. destruct (v_to_e_list l); inv H2.
           destruct l2; inv H3. }
  { destruct ves; inv Heqinstr'. destruct ves; inv H11. }
  { destruct ves; inv Heqinstr'. destruct ves; inv H8. }
  { destruct ves; inv Heqinstr'. destruct ves; inv H8. }
  { subst.
    destruct lh; cbn in Heqinstr'.
    destruct (v_to_e_list l). 2:{ inv Heqinstr'. destruct l1, es, l0; inv H1.
    eapply reduce_nil_false. eexists (hs', s', f', es'). eassumption. }
    destruct es; inv Heqinstr'. cbn in H.
    eapply reduce_nil_false. eexists (hs', s', f', es'). eassumption.
    now destruct es, l0; inv H1.
    destruct (v_to_e_list l); inv Heqinstr'. destruct l2; inv H1. }
Qed.

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
  destruct y as [[[hs' s'] f'] instr'].
  exfalso. eapply reduce_const_false. eassumption.
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
                               end (list_function_types (Pos.to_nat 100))
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
    match e with Efun fds _ => i < numOf_fundefs fds + 4 | _ => True end.
Proof.
  intros. unfold create_fname_mapping, translate_var in H.
  destruct ((create_var_mapping 4 (collect_function_vars e)
         (M.empty nat)) ! f) eqn:Hf; inv H.
  destruct e; auto. rename f0 into fds.
  have H' := translate_fvar_fname_mapping_aux _ _ _ _ _ _ _ Hf.
  apply H'. intros. inv H.
Qed.

Lemma e_offs_increasing' : forall len n i l  s fr state,
  Forall2
        (fun (e : module_element) (c : Wasm_int.Int32.T) =>
         opsem.reduce_trans (host_instance:=host_instance)
           (state, s, {| f_locs := []; f_inst := f_inst fr |},
           to_e_list (modelem_offset e))
           (state, s, {| f_locs := []; f_inst := f_inst fr |},
           [AI_basic (BI_const (VAL_int32 c))]))
        (table_element_mapping len n) l ->
 i < len ->
nth_error l i = Some (nat_to_i32 (n + i)).
Proof.
  induction len; intros; first lia.
  inv H. apply reduce_trans_const_eq in H3. inv H3.
  destruct i.
  (* i=0 *) rewrite Nat.add_0_r. reflexivity.
  (* i=Si' *) assert (i < len) as Hi by lia. clear H0.
  cbn. replace (n + S i) with ((S n) + i) by lia.
  eapply IHlen; eauto.
Qed.

Lemma table_element_mapping_length : forall len i,
  Datatypes.length (table_element_mapping len i) = len.
Proof.
  induction len; intros; cbn; auto.
  now rewrite IHlen.
Qed.

Lemma e_offs_increasing : forall e_offs len state s fr,
  Forall2  (fun (e : module_element) (c : Wasm_int.Int32.T) =>
               opsem.reduce_trans (host_instance:=host_instance)
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
      |}] ++ (table_element_mapping len 4))%list e_offs ->
 (forall i, i < len + 4 -> nth_error e_offs i = Some (nat_to_i32 i)) /\
 length e_offs = len + 4.
Proof.
  intros.
  apply Forall2_app_inv_l in H.
  destruct H as [l1 [l2 [Hl1 [Hl2 Heq]]]]. subst e_offs.
  inv Hl1. inv H3. inv H5. inv H6. inv H7.
  apply reduce_trans_const_eq in H1, H2, H3, H4.
  inv H1. inv H2. inv H3. inv H4.
  split. intros.
  destruct i. reflexivity.
  destruct i. reflexivity.
  destruct i. reflexivity.
  destruct i. reflexivity. cbn.
  assert (i < len) by lia. clear H0.
  assert (Hi: i < len) by lia. clear H.
  have H' := e_offs_increasing' _ _ _ _ _ _ _ Hl2 Hi. assumption.
  apply Forall2_length in Hl2. cbn.
  rewrite table_element_mapping_length in Hl2. lia.
Qed.

Fixpoint increasing_nats (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => (increasing_nats n') ++ [n']
  end.

Lemma nth_error_funcidcs {A} : forall (l : list A) n idx,
  n < length l ->
  nth_error (map (fun '(Mk_funcidx i) => i) (funcidcs (length l) idx)) n =
  Some (idx + n).
Proof.
  induction l; intros; cbn in H. lia.
  destruct n; cbn. f_equal. lia.
  assert (n < length l) by lia.
  replace (idx + S n) with (S idx + n) by lia.
  now apply IHl.
Qed.

Lemma init_tab_nth_error_same : forall s s' f t n anything,
  inst_tab (f_inst f) = [0] ->
  inst_funcs (f_inst f) = [:: 0, 1, 2, 3 & map (fun '(Mk_funcidx i) => i)
                             (funcidcs (Datatypes.length (table_data t) - 4) 4)] ->
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
  destruct (Nat.leb_spec n 3).
  (* n <= 3 *)
  destruct n; cbn; auto. destruct n; cbn; auto. destruct n; cbn; auto. destruct n; cbn; auto. lia.
  (* 3 < n *)
  assert ([:: 0, 1, 2, 3
    & map (fun '(Mk_funcidx i) => i)
        (funcidcs (Datatypes.length table_data - 4) 4)] = map (fun '(Mk_funcidx i) => i)
        (funcidcs (Datatypes.length table_data) 0)). {
     assert (length table_data = 4 + (length table_data - 4)) by lia.
     rewrite H1. cbn. rewrite OrdersEx.Nat_as_OT.sub_0_r. reflexivity. }
  rewrite H1.
  rewrite nth_error_funcidcs; auto.
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
    apply nth_error_Some in Hlen'. apply notNone_Some in Hlen'. destruct Hlen'.
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
  inst_funcs (f_inst f) = [:: 0, 1, 2, 3 & map (fun '(Mk_funcidx i0) => i0)
                          (funcidcs (Datatypes.length (table_data t) - 4) 4)] ->
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
     [:: 0, 1, 2, 3
       & map (fun '(Mk_funcidx i0) => i0)
           (funcidcs (Datatypes.length (table_data t) - 4) 4)] ->
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

Lemma list_function_types_nth_error : forall i maxargs,
  i <= maxargs ->
  nth_error (list_function_types maxargs) i =
    Some (Tf (repeat T_i32 i) []).
Proof.
  intros. generalize dependent i.
  induction maxargs; intros; destruct i; cbn; auto.
  inv H. cbn.
  rewrite nth_error_map. rewrite IHmaxargs; try lia.
  reflexivity.
Qed.

Lemma find_def_in_collection_function_vars : forall fds f e,
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

Lemma translate_functions_exists_original_fun : forall fds fds'' fns wasmFun e,
  NoDup (collect_function_vars (Efun fds e)) ->
  (fix iter (fds : fundefs) : error (seq.seq wasm_function) :=
               match fds with
               | Fcons x _ xs e fds' =>
                   match
                     translate_function nenv cenv (create_fname_mapping (Efun fds'' e)) x
                       xs e
                   with
                   | Err t => fun _  : wasm_function -> error (seq.seq wasm_function) => Err t
                   | Ret a => fun m2 : wasm_function -> error (seq.seq wasm_function) => m2 a
                   end
                     (fun fn : wasm_function =>
                      match iter fds' with
                      | Err t =>
                          fun _ : seq.seq wasm_function -> error (seq.seq wasm_function) =>
                          Err t
                      | Ret a =>
                          fun m2 : seq.seq wasm_function -> error (seq.seq wasm_function) =>
                          m2 a
                      end (fun following : seq.seq wasm_function => Ret (fn :: following)%SEQ))
               | Fnil => Ret []
               end) fds = Ret fns ->
   In wasmFun fns ->
   exists f t ys e, find_def f fds = Some (t, ys, e) /\ match wasmFun.(type) with
                                                        | Tf args _ => length ys = length args
                                                        end.
Proof.
  induction fds; intros fds'' fns wasmFun e' Hnodup Htrans Hin. 2: { inv Htrans. inv Hin. }
  destruct (translate_function nenv cenv
        (create_fname_mapping (Efun _ e)) v l
        e) eqn:transF. inv Htrans. cbn.
  destruct ((fix iter (fds : fundefs) : error (seq.seq wasm_function) :=
              match fds with
              | Fcons x _ xs e0 fds' =>
                  match
                    translate_function nenv cenv
                      (create_fname_mapping (Efun _ e0)) x xs e0
                  with
                  | Err t =>
                      fun _ : wasm_function -> error (seq.seq wasm_function) => Err t
                  | Ret a =>
                      fun m2 : wasm_function -> error (seq.seq wasm_function) => m2 a
                  end
                    (fun fn : wasm_function =>
                     match iter fds' with
                     | Err t =>
                         fun _ : seq.seq wasm_function ->
                               error (seq.seq wasm_function) => Err t
                     | Ret a => fun m2 : seq.seq wasm_function ->
                                error (seq.seq wasm_function) => m2 a
                     end
                       (fun following : seq.seq wasm_function =>
                        Ret (fn :: following)%SEQ))
              | Fnil => Ret []
              end) fds) eqn:Htra; inv Htrans. destruct Hin.
  { (* wasmFun is first fn *) subst w.
    exists v, f, l, e. destruct (M.elt_eq); last contradiction.
    split; auto.
    unfold translate_function in transF.
    destruct (translate_exp _ _ _ _) eqn:HtransE. inv transF.
    destruct (translate_var _ _ _ _) eqn:HtransFvar. inv transF.
    inv transF. cbn. now rewrite map_length. }
  { (* wasmFun is not first fn *)
    eapply IHfds in H; auto. 2: { now inv Hnodup. }
    { destruct H as [f' [t' [ys' [e'' [Hfdef Hty]]]]].
      exists f', t', ys', e''. split; auto. rewrite -Hfdef.
      destruct (M.elt_eq f' v); auto. subst v. exfalso.
      inv Hnodup. apply H1. clear H2. cbn.
      eapply find_def_in_collection_function_vars. apply notNone_Some. eauto.
    }
    eassumption.
  }
  Unshelve. all: assumption.
Qed.

Lemma translate_funcs_fenv : forall fds fns fenv e,
  map_injective fenv ->
  (fix iter (fds : fundefs) :
                 error (seq wasm_function) :=
               match fds with
               | Fcons x _ xs e0 fds' =>
                   match
                     translate_function nenv cenv fenv x xs e0
                   with
                   | Err t => fun _ : wasm_function -> error (seq wasm_function) => Err t
                   | Ret a => fun m2 : wasm_function -> error (seq wasm_function) => m2 a
                   end
                     (fun fn : wasm_function =>
                      match iter fds' with
                      | Err t => fun _ : seq wasm_function -> error (seq wasm_function) => Err t
                      | Ret a => fun m2 : seq wasm_function -> error (seq wasm_function) => m2 a
                      end
                        (fun following : seq wasm_function =>
                         Ret (fn :: following)))
               | Fnil => Ret [::]
               end) fds = Ret fns ->

  (forall x i, i < numOf_fundefs fds ->
               length fns = numOf_fundefs fds ->
                (nth_error (collect_function_vars (Efun fds e)) i = Some x ->
                 option_map (fun f => fidx f) (nth_error fns i) = (fenv ! x))).
Proof.
  induction fds; intros. 2:{ cbn in H1. lia. }
  destruct fns. inv H2.
  destruct (translate_function _ _ _ _ _ _) eqn:HtransF. inv H0.
  destruct ((fix iter (fds : fundefs) : error (seq wasm_function) := _) fds) eqn:Hfix; inv H0.
  destruct i.
  { (* i=0 *) cbn. inv H3.
      unfold translate_function in HtransF.
      destruct (translate_exp _ _ _ _ _). inv HtransF.
      destruct (translate_var _ _ _ _) eqn:HtransV. inv HtransF. inv HtransF.
      unfold translate_var in HtransV.
      destruct (fenv ! x) eqn:HtransV'; inv HtransV. reflexivity.
  }
  { (* i=Si' *) cbn in H1. cbn.
    eapply IHfds; eauto. lia. }
  Unshelve. assumption.
Qed.

Lemma translate_funcs_idx_bounds : forall fds fns fenv min max,
  (forall f f', fenv ! f = Some f' -> min <= f' < max) ->
  length fns = numOf_fundefs fds ->
  (fix iter (fds : fundefs) :
                 error (seq wasm_function) :=
               match fds with
               | Fcons x _ xs e0 fds' =>
                   match
                     translate_function nenv cenv fenv x xs e0
                   with
                   | Err t => fun _ : wasm_function -> error (seq wasm_function) => Err t
                   | Ret a => fun m2 : wasm_function -> error (seq wasm_function) => m2 a
                   end
                     (fun fn : wasm_function =>
                      match iter fds' with
                      | Err t => fun _ : seq wasm_function -> error (seq wasm_function) => Err t
                      | Ret a => fun m2 : seq wasm_function -> error (seq wasm_function) => m2 a
                      end
                        (fun following : seq wasm_function =>
                         Ret (fn :: following)))
               | Fnil => Ret [::]
               end) fds = Ret fns ->

  forall idx, In idx (map fidx fns) -> min <= idx < max.
Proof.
  induction fds; intros. 2:{ inv H1. contradiction. }
  destruct fns. inv H0.
  destruct (translate_function _ _ _ _ _ _) eqn:HtransF. inv H1.
  destruct ((fix iter (fds : fundefs) : error (seq wasm_function) := _) fds) eqn:Hfix; inv H1.
  destruct H2.
  { (* i=0 *) subst.
      unfold translate_function in HtransF.
      destruct (translate_exp _ _ _ _ _). inv HtransF.
      destruct (translate_var _ _ _ _) eqn:HtransV. inv HtransF. inv HtransF.
      unfold translate_var in HtransV. cbn.
      destruct (fenv ! v) eqn:HtransV'; inv HtransV. now apply H in HtransV'.
  }
  { (* i=Si' *) cbn in H1. cbn.
    eapply IHfds; eauto. }
Qed.

Lemma translate_funcs_increasing_fids : forall fds fns fenv e e',
  fenv = create_fname_mapping e ->
  match e with Efun fds' _ => fds' = fds | _ => True end ->
  map_injective fenv ->
  NoDup (collect_function_vars (Efun fds e')) ->
  (fix iter (fds : fundefs) :
                 error (seq wasm_function) :=
               match fds with
               | Fcons x _ xs e0 fds' =>
                   match
                     translate_function nenv cenv
                       (create_fname_mapping e) x xs e0
                   with
                   | Err t => fun _ : wasm_function -> error (seq wasm_function) => Err t
                   | Ret a => fun m2 : wasm_function -> error (seq wasm_function) => m2 a
                   end
                     (fun fn : wasm_function =>
                      match iter fds' with
                      | Err t => fun _ : seq wasm_function -> error (seq wasm_function) => Err t
                      | Ret a => fun m2 : seq wasm_function -> error (seq wasm_function) => m2 a
                      end (fun following : seq wasm_function => Ret (fn :: following)))
               | Fnil => Ret [::]
               end) fds = Ret fns ->
  (forall i j i' j', i > j -> nth_error (map (fun f => fidx f) fns) i = Some i' ->
                              nth_error (map (fun f => fidx f) fns) j = Some j' -> i' > j').
Proof.
  intros ? ? ? ? ? ? Hfds Hinj Hnodup HtransFns ? ? ? ? Hgt Hi Hj.
  rewrite nth_error_map in Hi. rewrite nth_error_map in Hj.
  destruct (nth_error fns i) eqn:Hio. 2: inv Hi. cbn in Hi. inv Hi.
  destruct (nth_error fns j) eqn:Hjo. 2: inv Hj. cbn in Hj. inv Hj.

  have Hlen := numOf_fundefs_length _ _ _ _ _ HtransFns. symmetry in Hlen.

  assert (Hilen: i < numOf_fundefs fds). { rewrite -Hlen. now apply nth_error_Some. }
  have Hilen' := Hilen. rewrite <- (collect_function_vars_length_numOf_fundefs_eq _ e) in Hilen'.
  apply nth_error_Some in Hilen'. apply notNone_Some in Hilen'. destruct Hilen' as [v Hiv].
  have Hi' := translate_funcs_fenv _ _ _ _ Hinj HtransFns _ _ Hilen Hlen Hiv.
  rewrite Hio in Hi'. cbn in Hi'.

  assert (Hjlen: j < numOf_fundefs fds). { rewrite -Hlen. now apply nth_error_Some. }
  have Hjlen' := Hjlen. rewrite <- (collect_function_vars_length_numOf_fundefs_eq _ e) in Hjlen'.
  apply nth_error_Some in Hjlen'. apply notNone_Some in Hjlen'. destruct Hjlen' as [v' Hjv'].
  have Hj' := translate_funcs_fenv _ _ _ _ Hinj HtransFns _ _ Hjlen Hlen Hjv'.
  rewrite Hjo in Hj'. cbn in Hj'.
  symmetry in Hj', Hi'.
  destruct e; (try now inv Hjv'). subst f. clear HtransFns.
  remember (fidx w) as i'. remember (fidx w0) as j'. clear Heqi' Heqj'.

  assert (Hi'': translate_var nenv (create_fname_mapping (Efun fds e)) v ""%bs = Ret i'). {
    unfold translate_var. now rewrite Hi'. }
  assert (Hj'': translate_var nenv (create_fname_mapping (Efun fds e)) v' ""%bs = Ret j'). {
    unfold translate_var. now rewrite Hj'. }
  unfold create_fname_mapping in Hi'.
  rewrite (var_mapping_list_lt_length_nth_error_idx _ _ _ 4 _ _ _ Hiv) in Hi''; auto.
  rewrite (var_mapping_list_lt_length_nth_error_idx _ _ _ 4 _ _ _ Hjv') in Hj''; auto.
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
  nth_error l i = Some i' -> n+i=i'.
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
  (forall idx, In idx (map fidx fns) -> 4 <= idx < length fns + 4) ->
  nth_error fns j = Some func ->
  nth_error fns (fidx func - 4) = Some func.
Proof.
  intros.
  assert (Hin: In func fns). { eapply nth_error_In. eassumption. }
  apply in_map with (f:=fidx) in Hin.
  apply H0 in Hin.
  destruct (fidx func) eqn:Hfi. lia. do 3! (destruct i; try lia). cbn.
  replace (i-0) with i by lia.
  assert (Hlen: i < length fns) by lia.

  assert (Ho: option_map fidx (nth_error fns j) = option_map fidx (Some func)) by congruence.
  rewrite <- nth_error_map in Ho.

  assert (Hbounds: (forall j j' : nat,
    nth_error [seq fidx f | f <- fns] j = Some j' ->
    4 <= j' < Datatypes.length [seq fidx f | f <- fns] + 4)). {
    intros. apply nth_error_In in H2. apply H0 in H2. now rewrite map_length.
  }

  have H' := increasing_list_fact_id _ _ _ 4 H Hbounds Ho.
  assert (i=j) by lia. now subst i.
Qed.


Lemma translate_funcs_NoDup : forall fds fns fenv e e',
  fenv = create_fname_mapping e ->
  match e with Efun fds' _ => fds' = fds | _ => True end ->
  map_injective fenv ->
  NoDup (collect_function_vars (Efun fds e')) ->
  (fix iter (fds : fundefs) :
                 error (seq wasm_function) :=
               match fds with
               | Fcons x _ xs e0 fds' =>
                   match
                     translate_function nenv cenv
                       (create_fname_mapping e) x xs e0
                   with
                   | Err t => fun _ : wasm_function -> error (seq wasm_function) => Err t
                   | Ret a => fun m2 : wasm_function -> error (seq wasm_function) => m2 a
                   end
                     (fun fn : wasm_function =>
                      match iter fds' with
                      | Err t => fun _ : seq wasm_function -> error (seq wasm_function) => Err t
                      | Ret a => fun m2 : seq wasm_function -> error (seq wasm_function) => m2 a
                      end (fun following : seq wasm_function => Ret (fn :: following)))
               | Fnil => Ret [::]
               end) fds = Ret fns ->
  NoDup (map (fun f => fidx f) fns).
Proof.
  intros ? ? ? ? ? ? Hfds Hinj Hnodup HtransFns. subst fenv.
  have H' := translate_funcs_increasing_fids _ _ _ _ _ Logic.eq_refl Hfds Hinj Hnodup HtransFns.
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

Lemma translate_funcs_find_def : forall fds f fns t ys e fenv,
  NoDup (collect_function_vars (Efun fds e)) ->
  (fix iter (fds : fundefs) :  error (seq wasm_function) :=
               match fds with
               | Fcons x _ xs e0 fds' =>
                   match
                     translate_function nenv cenv fenv x xs e0
                   with
                   | Err t => fun _ : wasm_function -> error (seq wasm_function) => Err t
                   | Ret a => fun m2 : wasm_function -> error (seq wasm_function) => m2 a
                   end
                     (fun fn : wasm_function =>
                      match iter fds' with
                      | Err t => fun _ : seq wasm_function -> error (seq wasm_function) => Err t
                      | Ret a => fun m2 : seq wasm_function -> error (seq wasm_function) => m2 a
                      end
                        (fun following : seq wasm_function =>
                         Ret (fn :: following)))
               | Fnil => Ret [::]
               end) fds = Ret fns ->
  find_def f fds = Some (t, ys, e) ->
  (forall f t ys e, find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e) ->
  exists idx e' locs ftype func, repr_funvar fenv nenv f idx /\
    locs = repeat T_i32 (length (collect_local_variables e)) /\
    ftype = Tf (List.map (fun _ => T_i32) ys) [] /\
    In func fns /\
    func.(fidx) = idx /\ func.(type) = ftype /\ func.(locals) = locs /\ func.(body) = e' /\
    repr_expr_LambdaANF_Codegen cenv fenv nenv e e'
     (lenv := create_local_variable_mapping (ys ++ collect_local_variables e)).
Proof.
  induction fds; intros ? ? ? ? ? ? Hnodup HtransFns HfDef HcorrCenv. 2: inv HfDef.
  destruct (translate_function _ _ _ _ _ _) eqn:Hf. inv HtransFns.
  destruct (_ fds) eqn:Hfns; inv HtransFns.
  cbn in HfDef. destruct (M.elt_eq f0 v).
  { (* f0=v *)
    inv HfDef.
    unfold translate_function in Hf.
    destruct (translate_exp _ _ _ _ _) eqn:Hexp. inv Hf.
    destruct (translate_var _ _ _ _) eqn:Hvar; inv Hf.
    exists i, l. eexists. eexists. eexists.
    split. { econstructor. eassumption. }
    do 2! (split; try reflexivity).
    split. now left.
    cbn. rewrite map_repeat_eq.
    repeat (split; first reflexivity).
    eapply translate_exp_correct in Hexp; eauto. eapply HcorrCenv with (f:=v). cbn.
    destruct (M.elt_eq v v); try contradiction. reflexivity.
  }
  { (* f0<>v *)
    assert (Hnodup': NoDup (collect_function_vars (Efun fds e0))). {
      now inv Hnodup. }
    assert (HcorrCenv': (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
      find_def f fds = Some (t, ys, e) ->
      correct_cenv_of_exp cenv e)). {
    intros. have H' := HcorrCenv f1 t0 ys0 e1. apply H'. cbn.
    assert (f1 <> v). {
      inv Hnodup. intro. subst. apply H2.
      apply find_def_in_collect_function_vars; auto. congruence. }
    destruct (M.elt_eq f1 v); auto; congruence. }
    have IH := IHfds _ _ _ _ _ _ Hnodup' Hfns HfDef HcorrCenv'.
    destruct IH as [idx [e' [locs [type [func [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
    inversion H.
    repeat eexists.
    repeat (split; eauto).
    rewrite -H3 in H8. eassumption.
    now right. all: congruence. }
Qed.


Lemma module_instantiate_INV_and_more_hold :
forall e eAny topExp fds num_funs module fenv main_lenv sr f exports,
  NoDup (collect_function_vars (Efun fds eAny)) ->
  expression_restricted e ->
  topExp = match e with | Efun _ _ => e | _ => Efun Fnil e end ->
  (match topExp with Efun fds' _ => fds' | _ => Fnil end) = fds ->
  (forall (f : var) (t : fun_tag) (ys : seq var) (e : exp),
      find_def f fds = Some (t, ys, e) -> correct_cenv_of_exp cenv e) ->
  num_funs = match topExp with | Efun fds _ => numOf_fundefs fds | _ => 42 (* unreachable*) end ->
  (Z.of_nat num_funs < max_num_functions)%Z ->
  LambdaANF_to_WASM nenv cenv e = Ret (module, fenv, main_lenv) ->
  (* for INV_locals_all_i32, the initial context has no local vars for simplicity *)
  (f_locs f) = [] ->
  (* instantiate with the two imported functions *)
  instantiate host_function host_instance initial_store module
    [MED_func (Mk_funcidx 0); MED_func (Mk_funcidx 1)] (sr, (f_inst f), exports, None) ->
  INV fenv nenv _ (M.empty _) sr f /\
  inst_funcs (f_inst f) = [:: 0, 1, 2, 3 & map (fun '(Mk_funcidx i) => i) (funcidcs num_funs 4)] /\
  (forall a errMsg, find_def a fds <> None ->
	exists fidx : immediate,
	  translate_var nenv fenv a errMsg = Ret fidx /\
	  repr_val_LambdaANF_Codegen cenv fenv nenv host_function
	    (Vfun (M.empty val) fds a) sr f (Val_funidx fidx)) /\
  (* pp_fn not called, discard *)
   exists pp_fn e' fns, s_funcs sr = [:: FC_func_host (Tf [T_i32] []) hfn,
                                         FC_func_host (Tf [T_i32] []) hfn,
                                         pp_fn,
                       FC_func_native (f_inst f) (Tf [] [])
                         (map (fun _ : var => T_i32)
                            (collect_local_variables
                               match e with
                               | Efun _ exp => exp
                               | _ => e
                               end)) e'
                     & map
                         (fun f0 : wasm_function =>
                          FC_func_native (f_inst f)
                            (Tf
                               (repeat T_i32
                                  match type f0 with
                                  | Tf args _ => Datatypes.length args
                                  end) []) (locals f0)
                            (body f0)) fns] /\
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
  match e with
  | Efun fds _ =>
    (fix iter (fds0 : fundefs) : error (seq.seq wasm_function) :=
     match fds0 with
     | Fcons x _ xs e fds' =>
        match translate_function nenv cenv fenv x xs e with
        | Err t => fun _ : wasm_function -> error (seq.seq wasm_function) => Err t
        | Ret a => fun m2 : wasm_function -> error (seq.seq wasm_function) => m2 a
        end
      (fun fn : wasm_function =>
        match iter fds' with
        | Err t => fun _ : seq.seq wasm_function -> error (seq.seq wasm_function) => Err t
        | Ret a => fun m2 : seq.seq wasm_function -> error (seq.seq wasm_function) => m2 a
        end (fun following : seq.seq wasm_function => Ret (fn :: following)%SEQ))
     | Fnil => Ret []
     end) fds
  | _ => Ret []
  end = Ret fns.
Proof.
  intros e eAny topExp fds num_funs module fenv lenv s f exports Hnodup HeRestr HtopExp Hfds HcenvCorrect Hnumfuns
    HfdsLength Hcompile Hflocs Hinst. subst num_funs topExp.
  unfold instantiate in Hinst.
  unfold LambdaANF_to_WASM in Hcompile.
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
  apply reduce_trans_const_eq in H1, H2, H3. subst y y0 y1.
  (* data offsets of mem init. red. to const, empty list *)
  inv HinstData. apply reduce_trans_const_eq in H4. subst y2.
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
  assert (Hlen: (length (table_data t) - 4) = length fns /\ length (table_data t) >= 4). {
    subst s'. inv Heqts. cbn. rewrite repeat_length. cbn.
    replace (ssrnat.nat_of_bin (N.of_nat (Datatypes.length fns + 4))) with
      (Z.to_nat (Z.of_nat (ssrnat.nat_of_bin (N.of_nat (Datatypes.length fns + 4))))) by lia.
    rewrite Z_nat_bin. lia.
  } destruct Hlen as [Hlen HminLen]. rewrite -Hlen in F3.
  assert (Hlen': length e_offs = length fns + 4). { now rewrite HeoffsLen -Hlen. }
  rewrite -Hlen' in HeoffsVals.
  assert (HlenMax: (Z.of_nat (Datatypes.length e_offs) < Wasm_int.Int32.modulus)%Z). {
  apply numOf_fundefs_length in HtransFns.
  unfold max_num_functions in HfdsLength. simpl_modulus; cbn. lia. }
  assert (Hlen'': Datatypes.length e_offs = Datatypes.length (table_data t)) by lia.
  have H' := init_tabs_effect s' _ _ e_offs _ Heqts Hnone F2 F3 Logic.eq_refl HeoffsVals HlenMax Hlen''.
  rewrite Hlen' in H'.
  destruct H' as [t' [Ht' [HtVal' [NtNone' [Htables [Hfuncs [Hmems Hglobals]]]]]]].
  rewrite -Hinst in Hglobals, Hmems, Hfuncs.

  assert (Hw: type w = Tf [T_i32] [] /\ locals w = [T_i32]). {
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
    have H' := translate_functions_exists_original_fun _ _ _ _ _ Hnodup HtransFns Hin.
    destruct H' as [f'' [t'' [ys'' [e'' [Hdef Hty]]]]].
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
   { unfold INV_num_functions_upper_bound. cbn.
     rewrite Hfuncs. cbn.
     rewrite map_length.
     destruct e; inv HtopExp'; try (inv HtransFns; simpl_modulus; cbn; lia).
     erewrite <- numOf_fundefs_length; eauto.
     unfold max_num_functions in HfdsLength. simpl_modulus. cbn. lia. }
   split. (* inst_globs (f_inst f) no dups *)
   unfold INV_inst_globs_nodup. rewrite F0.
   repeat constructor; cbn; lia.
   split. (* INV_table_id *)
   { unfold INV_table_id. intros.
     unfold stab_addr, stab_index. rewrite F2. cbn.
     intros.
     assert (Z.of_nat i < max_num_functions + 4)%Z. {
       destruct e; inv H. apply translate_fvar_fname_mapping in H1.
       inv HtopExp'. lia. }
     (* from translate_var *)
     rewrite Wasm_int.Int32.Z_mod_modulus_id. 2: {
      simpl_modulus; cbn. unfold max_num_functions in H0. lia. }
      subst s. rewrite Ht'. cbn.
      rewrite HtVal'. cbn. f_equal. lia.
      have H' := H.
      apply translate_fvar_fname_mapping in H'.
      destruct e; inv H. symmetry in HtopExp'; inv HtopExp'.
      apply numOf_fundefs_length in HtransFns. rewrite HtransFns in H'.
      apply nth_error_In with (n:=i). rewrite nth_error_map.
      rewrite HeoffsVals; try lia. cbn. f_equal.
      rewrite Wasm_int.Int32.Z_mod_modulus_id; try lia.
  }
  split.
  (* INV_var_idx_inbounds *)
  { unfold INV_var_idx_inbounds. intros. inv H. inv H0. }
  (* types *)
  { unfold INV_types. intros. unfold stypes. cbn. unfold max_function_args in H.
   rewrite F4. apply list_function_types_nth_error. lia. }
  split.
  (* inst_funcs (f_inst f) *)
  { rewrite F3. repeat f_equal. intros. rewrite H2. reflexivity.
    destruct e; inv HtopExp'; inv HtransFns; auto.
    symmetry. rewrite Hlen. cbn. eapply numOf_fundefs_length. eassumption. }
  split. (* val relation holds for functions *)
  { intros. apply notNone_Some in H. destruct H as [[[v' ys'] e''] Hfd].
    assert (Hnodup' : NoDup (collect_function_vars (Efun fds e))). {
      replace (collect_function_vars (Efun fds e'')) with
              (collect_function_vars (Efun fds e0)) by reflexivity. assumption. }

    have H' := translate_funcs_find_def _ _ _ _ _ e'' _ Hnodup' HtransFns Hfd HcenvCorrect.
    destruct H' as [fidx [e''' [? [? [func [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
    subst. eauto.
    exists (fidx func).
    split. { inv H. unfold translate_var. unfold translate_var in H0.
      destruct ((create_fname_mapping e) ! a); auto. inv H0. }
    econstructor; eauto. rewrite Hfuncs. cbn.
    assert (fidx func >= 4). { inv H. unfold translate_var in H0.
      destruct ((create_fname_mapping e) ! a) eqn:Ha; inv H0.
      now apply local_variable_mapping_gt_idx in Ha. }
    apply In_nth_error in H2. destruct H2 as [j Hj].
    assert (nth_error fns (fidx func - 4) = Some func). {
      assert (Hinj: map_injective (create_fname_mapping e)). {
        apply create_local_variable_mapping_injective.
        destruct e; try (by constructor). now inv HtopExp'.
      }
      assert (Hfds: match e with | Efun fds' _ => fds' = fds | _ => True end). {
        destruct e;auto. now inv HtopExp'. }
      have H'' := translate_funcs_increasing_fids _ _ _ _ _ Logic.eq_refl Hfds
                    Hinj Hnodup' HtransFns. clear Hfds.
      inv H.
      apply translate_fvar_fname_mapping in H1.
      destruct e; inv HtopExp'; try (now inv Hfd).
      assert (Hlen''': numOf_fundefs fds = length fns). {
        now apply numOf_fundefs_length in HtransFns.
      }
      rewrite Hlen''' in H1.

      assert (Hbounds: forall idx, In idx [seq fidx i | i <- fns] ->
        4 <= idx < Datatypes.length fns + 4). {

        intros ? Hidx.
        symmetry in Hlen'''.
        have H' := translate_funcs_idx_bounds _ _ _ _ _ _ Hlen''' HtransFns _ Hidx. apply H'.
        intros ? ? Hf.
        split. { now apply local_variable_mapping_gt_idx in Hf. }
        assert (HtransF: translate_var nenv
                (create_fname_mapping (Efun fds e0)) f0 ""%bs = Ret f'). {
         unfold translate_var. now rewrite Hf. }
         apply var_mapping_list_lt_length' in HtransF.
         rewrite collect_function_vars_length_numOf_fundefs_eq in HtransF. lia.
      }
      eapply fns_fidx_nth_error_fidx; eauto.
    }

    assert (HnodupFns: NoDup fns). {
      assert (Hinj: map_injective (create_fname_mapping e)). {
        apply create_local_variable_mapping_injective.
        destruct e; try (by constructor). now inv HtopExp'.
      }
      assert (Hfds: match e with | Efun fds' _ => fds' = fds | _ => True end). {
        destruct e;auto. now inv HtopExp'. }
      have H' := translate_funcs_NoDup _ _ _ _ _ Logic.eq_refl Hfds Hinj Hnodup' HtransFns.
      apply NoDup_nth_error. rewrite NoDup_nth_error in H'.
      intros. apply H'.
      - now rewrite map_length.
      - do 2! rewrite nth_error_map. now rewrite H3.
    }

    destruct (fidx func). lia. do 3! (destruct i; try lia). cbn.
    replace (S (S (S (S i))) - 4) with i in H1 by lia.

    assert (i = j). {
      rewrite -H1 in Hj.
      rewrite NoDup_nth_error in HnodupFns.
      assert (Hn: nth_error fns i <> None) by congruence.
      apply nth_error_Some in Hn. symmetry in Hj.
      now apply HnodupFns.
    } subst i.
    rewrite nth_error_map.
    rewrite Hj. cbn. f_equal. f_equal. rewrite H4.
    now rewrite map_repeat_eq -map_map_seq.
  }
  exists (FC_func_native (f_inst f) (Tf [T_i32] []) [T_i32] (body w)), e', fns.
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
	split. rewrite -Hexpr.
	replace (match e with | Efun _ exp => exp
                        | _ => e end) with e0 by now destruct e.
  reflexivity.
  rewrite -HtransFns. destruct e; inv HtopExp'; auto.
Qed.

Lemma repeat0_n_zeros : forall l,
   repeat (nat_to_value 0) (Datatypes.length l)
 = n_zeros (map (fun _ : var => T_i32) l).
Proof.
  induction l; cbn; auto.
  now rewrite IHl.
Qed.


(* MAIN THEOREM, corresponds to 4.3.1 in Olivier's thesis *)
Theorem LambdaANF_Codegen_related :
  forall (v : cps.val) (e : exp) (n : nat) (vars : list cps.var)
         (hs : host_state) module fenv lenv
         (sr : store_record) (fr : frame) exports,
  (* evaluation of LambdaANF expression *)
  bstep_e (M.empty _) cenv (M.empty _) e v n ->
  (* compilation function *)
  LambdaANF_to_WASM nenv cenv e = Ret (module, fenv, lenv) ->
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

       result_val_LambdaANF_Codegen cenv fenv nenv _ v sr' fr.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? ?  Hstep LANF2WASM Hcenv HvarsEq HvarsNodup Hfreevars Hinst.
  subst vars.

  assert (HeRestr: expression_restricted e).
  { unfold LambdaANF_to_WASM in LANF2WASM. destruct (check_restrictions e) eqn:HeRestr.
    inv LANF2WASM. destruct u. eapply check_restrictions_expression_restricted; eauto.
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
      now eapply find_def_dsubterm_fds_e. }

  assert (Hnodup': NoDup
       (collect_function_vars
          (Efun match
               match e with
               | Efun _ _ => e
               | _ => Efun Fnil e
               end
             with
             | Efun fds' _ => fds'
             | _ => Fnil
             end e))). { destruct e; cbn; auto.
                         now eapply NoDup_app_remove_l in HvarsNodup. }

  have HI := module_instantiate_INV_and_more_hold _ _ _ _ _ _ _ _ _ _ _ Hnodup' HeRestr
               Logic.eq_refl Logic.eq_refl Hcenv' Logic.eq_refl Hmaxfuns LANF2WASM HflocsNil Hinst.
  clear Hfinst Hnodup' Hcenv'.
  destruct HI as [Hinv [HinstFuncs [HfVal [pp_fn [e' [fns' [HsrFuncs [Hexpr' Hfns']]]]]]]].

  remember (Build_frame (repeat (nat_to_value 0) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.

  unfold LambdaANF_to_WASM in LANF2WASM.
  remember (list_function_types (Z.to_nat max_function_args)) as ftypes.
  simpl in LANF2WASM.
  destruct (check_restrictions e). inv LANF2WASM.
  destruct (generate_constr_pp_function cenv nenv e) eqn:Hppconst. inv LANF2WASM.
  destruct (match _ with
       | Efun fds _ => _ fds
       | _ => Err _
       end) eqn:Hfuns. inv LANF2WASM. rename l into fns.
  destruct (match e with
                    | Efun _ _ => e
                    | _ => Efun Fnil e
                    end) eqn:HtopExp; try (by inv LANF2WASM).
  destruct (translate_exp nenv cenv _ _ _) eqn:Hexpr. inv LANF2WASM. rename l into wasm_main_instr.
  inv LANF2WASM.

  (* from lemma module_instantiate_INV_and_more_hold *)
  assert (e' = wasm_main_instr). { destruct e; inv HtopExp; congruence. } subst e'. clear Hexpr'.
  assert (fns = fns'). { destruct e; inv HtopExp; congruence. } subst fns'. clear Hfns'.

  remember (Build_frame (repeat (nat_to_value 0) (length (collect_local_variables e))) (f_inst fr)) as f_before_IH.
  remember (create_local_variable_mapping (collect_local_variables e)) as lenv.
  remember (create_fname_mapping e) as fenv.

  assert (Hinv_before_IH: INV fenv nenv _ lenv sr f_before_IH). { subst.
    destruct Hinv as [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]].
    unfold INV. repeat (split; try assumption).
    unfold INV_locals_all_i32. cbn. intros. exists (nat_to_i32 0).
    assert (i < (length (repeat (nat_to_value 0) (Datatypes.length (collect_local_variables e))))).
    { subst. now apply nth_error_Some. }
    rewrite nth_error_repeat in H13. inv H13. reflexivity. rewrite repeat_length in H14. assumption.
    unfold INV_var_idx_inbounds. intros. rewrite repeat_length. inv H13.
    eapply var_mapping_list_lt_length. eassumption. }

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
      subst lenv fenv. eapply variable_mappings_nodup_disjoint; eauto.
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
        rewrite find_def_in_collection_function_vars in H.
        apply notNone_Some. apply variable_mapping_In_Some.
        + now eapply NoDup_app_remove_l in HvarsNodup.
        + assumption.
      - destruct H as [i H]. apply variable_mapping_Some_In in H; auto.
        rewrite <- find_def_in_collection_function_vars in H.
        now apply notNone_Some.
    }

    assert (HfenvRho: (forall (a : positive) (v0 : val),
         (def_funs fds fds (M.empty val) (M.empty val)) ! a = Some v0 ->
         find_def a fds <> None -> v0 = Vfun (M.empty val) fds a)). {
      intros ? ? H H0. eapply def_funs_find_def in H0. erewrite H in H0.
      now inv H0. eassumption. }

    assert (HeRestr' : expression_restricted e). { now inv HeRestr. }
    assert (Hunbound: (forall x : var,
         In x (collect_local_variables e) ->
         (def_funs fds fds (M.empty val) (M.empty val)) ! x = None)). {
      intros. eapply def_funs_not_find_def. eassumption.
      destruct (find_def x fds) eqn:Hdec; auto. exfalso.
      assert (Hdec': find_def x fds <> None) by congruence. clear Hdec p.
      apply find_def_in_collect_function_vars with (e:=e) in Hdec'.
      cbn in HvarsNodup. rewrite <- catA in HvarsNodup.
      eapply NoDup_app_remove_middle in HvarsNodup; last eassumption.
      have H' := NoDup_app_In _ _ _ _ _ HvarsNodup H.
      now eapply H'.
    }

    assert (HfdsEqRhoEmpty_before_IH: (forall (x : positive) (rho' : M.t val)
           (fds' : fundefs) (f' : var) v,
           (def_funs fds fds (M.empty val) (M.empty val)) ! x = Some v ->
             subval_or_eq (Vfun rho' fds' f') v ->
             fds' = fds /\ rho' = M.empty _)). {
       intros. have H' := H.
       apply def_funs_spec in H.
       destruct H as [[? ?] | [? Hcontra]]. 2: inv Hcontra.
       rewrite def_funs_eq in H'. 2: assumption.
       inv H'. apply subval_fun in H0. destruct H0 as [? [Hval Hfd]].
         now inv Hval. assumption.
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
           repr_val_LambdaANF_Codegen cenv fenv nenv
             host_function (Vfun (M.empty val) fds a)
             sr f_before_IH (Val_funidx fidx))). {
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
        exists fidx. split. assumption.
        eapply val_relation_depends_on_finst; last apply Hval.
        subst f_before_IH. reflexivity. }
    }

    assert (Hrelm : rel_env_LambdaANF_Codegen cenv fenv
       (lenv:=create_local_variable_mapping (collect_local_variables e))
         nenv host_function e (def_funs fds fds (M.empty val) (M.empty val))
          sr f_before_IH fds). {
      split.
      { (* funs1 (follows from previous Hfds) *)
        intros ? ? ? Hdf Hval. have H' := Hdf.
        apply def_funs_spec in Hdf.
        destruct Hdf as [[? ?] | [? H]]. 2: inv H.
        rewrite def_funs_eq in H'. 2: assumption.
        inv H'. apply subval_fun in Hval. 2: assumption.
        destruct Hval as [? [Hval ?]]. inv Hval. assumption.
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

    subst lenv.
    have HMAIN := repr_bs_LambdaANF_Codegen_related cenv funenv fenv nenv _ host_instance
                    _ _ _ _ _ _ _ HlenvInjective
                      HenvsDisjoint Logic.eq_refl Hnodup' HfenvWf HfenvRho
                      HeRestr' Hunbound Hstep hs _ _ _
                         HfdsEqRhoEmpty_before_IH Hfds Hinv_before_IH Hexpr Hrelm.

    destruct HMAIN as [s' [f' [Hred [Hval [Hfinst _]]]]]. cbn.
    exists s'. split.
    dostep'. apply r_call. cbn.
    rewrite HinstFuncs. reflexivity.
    dostep'. eapply r_invoke_native with (ves:=[]) (vcs:=[]) (t1s:=[]) (t2s:=[])(f' := f_before_IH); eauto.
    rewrite HsrFuncs. subst f_before_IH. cbn. rewrite Hfinst.  reflexivity.
    subst f_before_IH. cbn. apply repeat0_n_zeros.
    eapply reduce_trans_local.
    dostep'. constructor. eapply rs_block with (vs:=[]); eauto. cbn.
    apply reduce_trans_label. apply Hred.
    eapply result_val_LambdaANF_Codegen_depends_on_finst; try apply Hval.
    subst f_before_IH. now cbn in Hfinst.
  }

  { (* top exp is not Efun _ _ *)
    rename f0 into fds. assert (fds = Fnil). {
      destruct e; inv HtopExp; auto. exfalso. eauto.
    } subst fds. injection Hfuns => ?. subst fns. clear Hfuns.
    cbn in HsrFuncs, HinstFuncs, Hmaxfuns.
    assert (e0 = e). { destruct e; inv HtopExp; auto. exfalso. eauto. }
    subst e0. clear HtopExp.

    eapply translate_exp_correct in Hexpr; eauto.

    assert (Hrelm : rel_env_LambdaANF_Codegen cenv fenv
       (lenv:=create_local_variable_mapping (collect_local_variables e))
       nenv host_function e (M.empty _) sr f_before_IH Fnil). {
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

    assert (HfdsEqRhoEmpty_before_IH: (forall (x : positive) (rho' : M.t val)
           (fds' : fundefs) (f' : var) v,
           (M.empty _) ! x = Some v -> subval_or_eq (Vfun rho' fds' f') v ->
             fds' = Fnil /\ rho' = M.empty _)). { intros. inv H. }

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
           repr_val_LambdaANF_Codegen cenv fenv nenv
             host_function (Vfun (M.empty val) Fnil a)
             sr f_before_IH (Val_funidx fidx))). {
        intros ? ? ? ? ? Hcontra. inv Hcontra. }

    assert (Hunbound : (forall x : var,
         In x (collect_local_variables e) ->
         (M.empty val) ! x = None)). { intros. reflexivity. }

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

    assert (HfenvRho: forall (a : positive) (v : val),
        (M.empty val) ! a = Some v ->
        find_def a Fnil <> None -> v = Vfun (M.empty val) Fnil a). {
      intros. discriminate. }

    subst lenv.
    have HMAIN := repr_bs_LambdaANF_Codegen_related cenv funenv fenv nenv _ host_instance _ (M.empty _)
                    _ _ _ _ _ HlenvInjective HenvsDisjoint Logic.eq_refl Hnodup' HfenvWf
                      HfenvRho HeRestr Hunbound Hstep hs _ _ _ HfdsEqRhoEmpty_before_IH Hfds
                        Hinv_before_IH Hexpr Hrelm.
    destruct HMAIN as [s' [f' [Hred [Hval [Hfinst _]]]]]. cbn.
    exists s'. split.
    dostep'. apply r_call. cbn.
    rewrite HinstFuncs. reflexivity.
    dostep'. eapply r_invoke_native with (ves:=[]) (vcs:=[]) (t1s:=[]) (t2s:=[])(f' := f_before_IH); eauto.
    rewrite HsrFuncs. subst f_before_IH. cbn. rewrite Hfinst.  reflexivity.
    subst f_before_IH. cbn.
    assert (HexpEq: match e with | Efun _ exp => exp
                                 | _ => e end= e).
    { destruct e; auto. exfalso. eauto. } rewrite HexpEq. clear HexpEq. apply repeat0_n_zeros.
    eapply reduce_trans_local.
    dostep'. constructor. eapply rs_block with (vs:=[]); eauto. cbn.
    apply reduce_trans_label. apply Hred.
    eapply result_val_LambdaANF_Codegen_depends_on_finst; try eassumption. subst. cbn in Hfinst. congruence.
  } Unshelve. all: auto.
Qed.

End MAIN.
