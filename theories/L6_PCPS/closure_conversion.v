(* Computational definition and declarative spec for closure conversion. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import L6.cps L6.cps_util L6.set_util L6.hoisting L6.identifiers L6.ctx
        L6.Ensembles_util L6.List_util L6.functions L6.cps_show L6.state.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Coq.Strings.String  Coq.Strings.Ascii.
Require Import Common.AstCommon.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import ListNotations Nnat MonadNotation.

Require Import compcert.lib.Maps.

Open Scope ctx_scope.
Open Scope monad_scope.
Open Scope fun_scope.
Open Scope string.

(** * Closure conversion as a relation  *)

Section CC.
  Variable (clo_tag : ctor_tag). (* Tag for closure records *)

  Variable (clo_itag : ind_tag). (* Dummy ind_tag for closure records *)

  Inductive project_var :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Names of the functions in the current function block *)
    Ensemble var -> (* Names of global (i.e. already closed) functions *)
    (var -> var) -> (* renaming of function names *)
    ctor_tag -> (* tag of the current environment constructor *)
    var -> (* The environment argument *)
    list var -> (* The environment *)
    Ensemble var -> (* The free set *)
    var -> (* Before projection *)
    var -> (* After projection *)
    exp_ctx -> (* Context that will perform the projection *)
    Ensemble var -> (* The new free set *)
    Prop :=
  | Var_in_Scope :
      forall Scope Funs GFuns f c Γ FVs S x,
        In _ Scope x ->
        project_var Scope Funs GFuns f c Γ FVs S x x Hole_c S
  | Var_in_Funs :
      forall Scope Funs GFuns f c Γ FVs S x y,
        ~ In _ Scope x ->
        In _ Funs x ->
        In _ S y ->
        project_var Scope Funs GFuns f c Γ FVs S x y
                    (Econstr_c y clo_tag [(f x); Γ] Hole_c) (Setminus _ S (Singleton _ y))
  | Var_in_GFuns :
      forall Scope Funs GFuns f c c' Γ FVs S x y g_env,
        ~ In _ Scope x ->
        ~ In _ Funs x ->
        In _ GFuns x ->
        In _ S y ->
        In _ (S \\ [set y]) g_env ->
        project_var Scope Funs GFuns f c Γ FVs S x y
                    (Econstr_c g_env c' [] (Econstr_c y clo_tag [(f x); g_env] Hole_c)) (S \\ [set y] \\ [set g_env])
  | Var_in_FVs :
      forall Scope Funs GFuns f c Γ FVs S x y N,
        ~ In _ Scope x ->
        ~ In _ Funs x ->
        ~ In _ GFuns x ->
        nthN FVs N = Some x ->
        In _ S y ->
        project_var Scope Funs GFuns f c Γ FVs S x y
                    (Eproj_c y c N Γ Hole_c) (S \\ [set y]).

  Inductive project_vars :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Names of the functions in the current function block *)
    Ensemble var -> (* Names of global functions *)
    (var -> var) -> (* renaming of function names *)
    ctor_tag -> (* tag of the current environment constructor *)
    var -> (* The environment argument *)
    list var -> (* The free variables *)
    Ensemble var -> (* The free set *)
    list var -> (* Before projection *)
    list var -> (* After projection *)
    exp_ctx -> (* Context that will perform the projection *)
    Ensemble var -> (* The new free set *)
    Prop :=
  | VarsNil :
      forall Scope Funs GFuns f c Γ FVs S,
        project_vars Scope Funs GFuns f c Γ FVs S [] [] Hole_c S
  | VarsCons :
      forall Scope Funs GFuns f c Γ FVs y y' ys ys' C1 C2 S1 S2 S3,
        project_var Scope GFuns Funs f c Γ FVs S1 y y' C1 S2 ->
        project_vars Scope GFuns Funs f c Γ FVs S2 ys ys' C2 S3 ->
        project_vars Scope GFuns Funs f c Γ FVs S1 (y :: ys) (y' :: ys') (comp_ctx_f C1 C2) S3.

  Inductive make_closures :
    fundefs -> (* The function block *)
    Ensemble var -> (* The free set *)
    var -> (* The environment variable *)
    exp_ctx -> (* The context that constructs the closures *)
    (var -> var) -> (* The new renaming *)
    Ensemble var -> (* The new free set *)
    Prop :=
  | closures_Fnil :
      forall Γ f S,
        make_closures Fnil S Γ Hole_c f S
  | closures_Fcons :
      forall f xs t e B Γ C g S S',
        make_closures B (Setminus _ S (Singleton _ (g f))) Γ C g S' ->
        In _ S (g f) ->
        make_closures (Fcons f t xs e B) S Γ
                      (Econstr_c f clo_tag [(g f) ; Γ] C)
                      g S'.

  Inductive add_global_funs : Ensemble var -> (* Previous GFuns *)
                              Ensemble var -> (* New Funs *)
                              Ensemble var -> (* FVs of Funs *)
                              Ensemble var -> (* New GFuns *)
                              Type := 
  | Closed :
      forall GFuns Funs FVs,
        FVs <--> Empty_set _ ->
        add_global_funs GFuns Funs FVs (Funs :|: GFuns)        
  | Open :
      forall GFuns Funs FVs,
        ~ FVs <--> Empty_set _ -> (* maybe not needed, but it shouldn't hurt *)
        add_global_funs GFuns Funs FVs (GFuns \\ Funs).
      

  Inductive Closure_conversion :
    Ensemble var -> (* Variables in the current scope *)
    Ensemble var -> (* Names of the functions in the current function block *)
    Ensemble var -> (* Names of global functions *)
    (var -> var) -> (* renaming of function names *)
    ctor_tag -> (* tag of the current environment constructor *)
    var -> (* The environment argument *)
    list var -> (* The free variables - need to be ordered *)
    exp -> (* Before cc *)
    exp -> (* After cc *)
    exp_ctx -> (* The context that the output expression should be put in *)
    Prop :=
  | CC_Econstr :
      forall Scope Funs GFuns f c Γ FVs S' S x ys ys' C C' t e e',
        (* Variables for projected vars should not shadow the variables in
         scope, i.e. Scope U FV U { Γ } *)
        Disjoint _ S (Scope :|: (image f ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
        project_vars Scope Funs GFuns f c Γ FVs S ys ys' C S' ->
        (* We do not care about ys'. Should never be accessed again so do not
         add them aτ the current scope *)
        Closure_conversion (x |: Scope) Funs (GFuns \\ [set x]) f c Γ FVs e e' C' ->
        Closure_conversion Scope Funs GFuns f c Γ FVs (Econstr x t ys e)
                           (Econstr x t ys' (C' |[ e' ]|)) C
  | CC_Ecase :
      forall Scope Funs GFuns f c Γ FVs x x' C S S' pats pats',
        Disjoint _ S (Scope :|: (image f ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
        project_var Scope Funs GFuns f c Γ FVs S x x' C S' ->
        Forall2 (fun (pat pat' : ctor_tag * exp) =>
                   (fst pat) = (fst pat') /\
                   exists C' e',
                     snd pat' = C' |[ e' ]| /\
                     Closure_conversion Scope Funs GFuns f c Γ FVs (snd pat) e' C')
                pats pats' ->
        Closure_conversion Scope Funs GFuns f c Γ FVs (Ecase x pats) (Ecase x' pats') C
  | CC_Eproj :
      forall Scope Funs GFuns f c Γ FVs S S' x y y' C C' t N e e',
        Disjoint _ S (Scope :|: (image f ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
        project_var Scope Funs GFuns f c Γ FVs S y y' C S' ->
        Closure_conversion (x |: Scope) Funs (GFuns \\ [set x]) f c Γ FVs e e' C' ->
        Closure_conversion Scope Funs GFuns f c Γ FVs (Eproj x t N y e)
                           (Eproj x t N y' (C' |[ e' ]|)) C
  | CC_Efun :
      forall Scope Funs GFuns GFuns' f c Γ c' Γ' FVs FVs' FVs'' B B' e e' C C' Ce S1 S1' S2 S2' S3,
        (* The environment contains all the variables that are free in B *)
        (occurs_free_fundefs B) \\ GFuns <--> (FromList FVs') ->
        (* needed for cost preservation *)
        NoDup FVs' ->
        (* Project the FVs to construct the environment *)
        Disjoint _ S1 (Scope :|: (image f ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ])))  ->
        project_vars Scope Funs GFuns f c Γ FVs S1 FVs' FVs'' C' S1' ->
        (* Γ' is the variable that will hold the record of the environment *)
        Disjoint _ S3 (name_in_fundefs B :|: (Scope :|: (image f ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ])))) ->
           In _ S3 Γ' ->
        Disjoint _ S2 (bound_var (Efun B e) :|: (Γ' |: (Scope :|: (image f ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))))) ->
        make_closures B S2  Γ' C f S2' ->
        add_global_funs GFuns (name_in_fundefs B) (FromList FVs') GFuns' ->
        Closure_conversion_fundefs (name_in_fundefs B) GFuns' f c' FVs' B B' ->
        (* Add B in Funs if its only fvs are names are in GFuns *)
        Closure_conversion (Union _ (name_in_fundefs B) Scope) Funs GFuns' f c Γ FVs e e' Ce  ->
        Closure_conversion Scope Funs GFuns f c Γ FVs (Efun B e)
                           (Efun B' (C |[ Ce |[ e' ]| ]|)) (comp_ctx_f C' (Econstr_c Γ' c' FVs'' Hole_c))
  | CC_Eletapp :
      forall Scope Funs GFuns g c Γ FVs x f f' f'' ft e env' ys ys' C C' e' S S',
        Disjoint _ S (Scope :|: (image g ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
        (* Project the function name and the actual parameter *)
        project_vars Scope Funs GFuns g c Γ FVs S (f :: ys) (f' :: ys') C S' ->
        (* (* Project the actual parameters *) *)
        (* project_vars Scope Funs Γ FVs S1 ys ys' C2 S2 -> *)
        (* The name of the function pointer and the name of the environment
         should not shadow the variables in the current scope and the
         variables that where used in the projections *)
        In _ S' f'' -> In _ S' env' -> f'' <> env' ->
        Closure_conversion (Union _ (Singleton _ x) Scope) Funs GFuns g c Γ FVs e e' C' ->
        Closure_conversion Scope Funs GFuns g c Γ FVs (Eletapp x f ft ys e)
                           (Eproj f'' clo_tag 0%N f'
                                  (Eproj env' clo_tag 1%N f'
                                         (Eletapp x f'' ft (env' :: ys') (C' |[ e' ]|)))) C
  | CC_Eapp :
      forall Scope Funs GFuns g c Γ FVs f f' f'' ft env' ys ys' C S S',
        Disjoint _ S (Scope :|: (image g ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
        (* Project the function name and the actual parameter *)
        project_vars Scope Funs GFuns g c Γ FVs S (f :: ys) (f' :: ys') C S' ->
        (* (* Project the actual parameters *) *)
        (* project_vars Scope Funs Γ FVs S1 ys ys' C2 S2 -> *)
        (* The name of the function pointer and the name of the environment
         should not shadow the variables in the current scope and the
         variables that where used in the projections *)
        In _ S' f'' -> In _ S' env' -> f'' <> env' ->
        Closure_conversion Scope Funs GFuns g c Γ FVs (Eapp f ft ys)
                           (Eproj f'' clo_tag 0%N f'
                                  (Eproj env' clo_tag 1%N f'
                                         (Eapp f'' ft (env' :: ys')))) C
  | CC_Eprim :
      forall Scope Funs GFuns g c Γ FVs S S' x ys ys' C C' f e e',
        Disjoint _ S (Scope :|: (image g ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
        project_vars Scope Funs GFuns g c Γ FVs S ys ys' C S' ->
        Closure_conversion (x |: Scope) Funs GFuns g c Γ FVs e e' C' ->
        Closure_conversion Scope Funs GFuns g c Γ FVs (Eprim x f ys e)
                           (Eprim x f ys' (C' |[ e' ]|)) C
  | CC_Ehalt :
      forall Scope Funs GFuns g c Γ FVs x x' C S S',
        Disjoint _ S (Scope :|: (image g ((Funs \\ Scope) :|: GFuns) :|: (FromList FVs :|: [set Γ]))) ->
        (* Project the function name and the actual parameter *)
        project_var Scope Funs GFuns g c Γ FVs S x x' C S' ->
        Closure_conversion Scope Funs GFuns g c Γ FVs (Ehalt x) (Ehalt x') C
  with Closure_conversion_fundefs :
         Ensemble var -> (* The function names in the current block *)
         Ensemble var -> (* The global function names *)
         (var -> var) -> (* renaming of function names *)
         ctor_tag -> (* tag of the current environment constructor *)
         list var -> (* The environment *)
         fundefs -> (* Before cc *)
         fundefs -> (* After cc *)
         Prop :=
       | CC_Fcons :
           forall Funs GFuns g c Γ' FVs S f t ys e e' C defs defs',
             (* The environment binding should not shadow the current scope
         (i.e. the names of the mut. rec. functions and the other arguments) *)
             Disjoint _ S (image g (Funs :|: GFuns) :|: (FromList ys :|: bound_var e)) ->
             In _ S  Γ' ->
             Closure_conversion_fundefs Funs GFuns g c FVs defs defs' ->
             Closure_conversion (FromList ys) Funs (GFuns \\ FromList ys) g c Γ' FVs e e' C ->
             Closure_conversion_fundefs Funs GFuns g c FVs (Fcons f t ys e defs )
                                        (Fcons (g f) t (Γ' :: ys) (C |[ e' ]|) defs')
       | CC_Fnil :
           forall Funs GFuns g c FVs,
             Closure_conversion_fundefs Funs GFuns g c FVs Fnil Fnil.


  (** * Computational defintion of closure conversion *)


  Inductive VarInfo : Type :=
  (* A free variable, i.e. a variable outside the scope of the current function.
   The argument is position of a free variable in the env record *)
  | FVar : N -> VarInfo
  (* A function defined in the current block of function definitions. The first
   argument is the new name of the function (code pointer) *)
  | MRFun : var -> VarInfo
  (* A variable declared in the scope of the current function *)
  | BoundVar : VarInfo.

  
  (* Maps variables to [VarInfo] *)
  Definition VarInfoMap := M.t VarInfo.

  (* A global function name *)
  Inductive GFunInfo : Type := GFun : var -> GFunInfo.

  Definition GFunMap := M.t GFunInfo.

  Definition ccstate := @compM unit.

  Import MonadNotation.


  (** Commonly used suffixes *)
  Definition clo_env_suffix := "_env".
  Definition clo_suffix := "_clo".
  Definition code_suffix := "_code".
  Definition proj_suffix := "_proj".
  

  (** Looks up a variable in the map and handles it appropriately *) 
  Definition get_var (x : var) (map : VarInfoMap) (gfuns : GFunMap) (c : ctor_tag) (Γ : var)
  : ccstate (var * (exp -> exp)) :=
    match Maps.PTree.get x map with
      | Some entry =>
        match entry with
          | FVar pos =>
            (* pick a fresh name, register its pretty name *)
            y <- get_name x proj_suffix ;;
            ret (y, fun e => Eproj y c pos Γ e)   
          | MRFun code_ptr  =>
            (* get the new name of the function and pack it together with the
               current environment argument to construct the closure *)
            y <- get_name x clo_suffix ;;
            ret (y, fun e => Econstr y clo_tag [code_ptr; Γ] e)
          | BoundVar => ret (x, id)
        end
      | None =>
        match M.get x gfuns with
        | Some (GFun code_ptr) =>
          (* get the new name of the function and pack it together with the *)
          (*      current environment argument to construct the closure *)
          c_env <- make_record_ctor_tag 0 ;;
          g_env <- get_name x "bogus_env" ;;
          y <- get_name x clo_suffix ;;
          ret (y, fun e => Econstr g_env c_env [] (Econstr y clo_tag [code_ptr; Γ] e))
        | None => ret (x, id) (* should never reach here *)
        end
    end.
  
  Fixpoint get_vars (xs : list var) (map : VarInfoMap) (gfuns : GFunMap)
           (c : ctor_tag) (Γ : var) : ccstate (list var * (exp -> exp)) :=
    match xs with
      | [] => ret ([], id)
      | x :: xs =>
        t1 <- get_var x map gfuns c Γ ;;
        let '(y, f) := t1 in
        t2 <- get_vars xs map gfuns c Γ ;; 
        let '(ys, f') := t2 in
        ret (y :: ys, fun e => f (f' e))
    end.

  (** Add some bound variables in the map *)
  Fixpoint add_params args  (mapfv : VarInfoMap) : VarInfoMap :=
    match args with
      | [] => mapfv
      | x :: xs =>
        M.set x BoundVar (add_params xs mapfv)
    end.

  (** Construct the closure environment and the new variable map *)
  Definition make_env (fvs : list var) (mapfv_new : VarInfoMap)
             (mapfv_old : VarInfoMap) (c_old : ctor_tag) (Γ_new Γ_old : var) (gfuns : GFunMap) 
  : ccstate (ctor_tag * VarInfoMap * (exp -> exp)) :=
    (* put the free variables in a new map *)
    let '(map_new', n) :=
        (fix add_fvs (l:list M.elt) n map :=
           match l with
             | [] => (map, n)
             | x :: xs =>
               add_fvs xs (n + 1)%N (Maps.PTree.set x (FVar n) map)
           end) fvs 0%N (Maps.PTree.empty VarInfo)
    in
    t1 <- get_vars fvs mapfv_old gfuns c_old Γ_old ;;
    let '(fv', g') :=  t1 in
    c_new <- make_record_ctor_tag n ;;
    ret (c_new, map_new', fun e => g' (Econstr Γ_new c_new fv' e)).
  
  (** Construct closures after a function definition block *)
  Fixpoint make_full_closure (defs : fundefs) (mapfv_new mapfv_old : VarInfoMap) (gfuns : GFunMap) 
           (Γ : var) (is_closed : bool)
  : ccstate (VarInfoMap * VarInfoMap * GFunMap * (exp -> exp)) :=
    match defs with
      | Fcons f typ xs e defs' =>
        (* The new name of the function *)
        code_ptr <- get_name f "" ;;
        t <- make_full_closure defs' mapfv_new mapfv_old gfuns Γ is_closed ;;
        let '(mapfv_new', mapfv_old', gfuns', g') := t in
        (* update the new map *)
        let mapfv_new'' :=
            Maps.PTree.set f (MRFun code_ptr) mapfv_new'
        in
        (* update the old map *)
        let mapfv_old'' :=
            Maps.PTree.set f BoundVar mapfv_old'
        in
        gfuns'' <- (if is_closed then
                     (* f_str <- get_pp_name f ;; *)
                     (* log_msg ("Adding " ++ f_str) ;; *)
                     ret (M.set f (GFun code_ptr) gfuns')
                   else ret gfuns') ;;
        ret (mapfv_new'', mapfv_old'', gfuns'',
             (fun e => Econstr f clo_tag [code_ptr; Γ] (g' e)))
      | Fnil => ret (mapfv_new, mapfv_old, gfuns, id)
    end.

  Definition bool_to_string (b : bool) : string :=
    if b then "true" else "false".

  (** Closure conversion *)
  Fixpoint exp_closure_conv (e : exp) (mapfv : VarInfoMap) (gfuns : GFunMap)
           (c : ctor_tag) (Γ : var) : ccstate (exp * (exp -> exp)) := 
    match e with
      | Econstr x tag ys e' =>
        t1 <- get_vars ys mapfv gfuns c Γ ;;
        let '(ys', f) := t1 in
        ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) gfuns c Γ ;;
        ret (Econstr x tag ys' ((snd ef) (fst ef)), f)
      | Ecase x pats =>
        pats' <-
        (fix mapM_cc l :=
         match l with
           | [] => ret []
           | (y, e) :: xs =>
             ef <- exp_closure_conv e mapfv gfuns c Γ ;;
             xs' <- mapM_cc xs ;;
             ret ((y, ((snd ef) (fst ef))) :: xs')
         end) pats;;
        t1 <- get_var x mapfv gfuns c Γ ;;
        let '(x', f1) := t1 in           
        ret (Ecase x' pats', f1)
      | Eproj x tag n y e' =>
        t1 <- get_var y mapfv gfuns c Γ ;;
        let '(y', f) := t1 in
        ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) gfuns c Γ ;;
        ret (Eproj x tag n y' ((snd ef) (fst ef)), f)
      | Eletapp x f ft xs e' =>
        t1 <- get_var f mapfv gfuns c Γ ;;
        let '(f', g1) := t1 in
        t2 <- get_vars xs mapfv gfuns c Γ ;;
        let '(xs', g2) := t2 in
        ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) gfuns c Γ ;;
        ptr <- get_name f code_suffix ;;
        Γ <- get_name f clo_env_suffix ;;
        ret (Eproj ptr clo_tag 0 f'
                   (Eproj Γ clo_tag 1 f'
                          (Eletapp x ptr ft (Γ :: xs')
                                   ((snd ef) (fst ef)))),
             fun e => g1 (g2 e))
      | Efun defs e =>
        let fv := fundefs_fv defs in
        let fvs :=  List.filter (fun x => match M.get x gfuns with Some _ => false | None => true end) (PS.elements fv) in
        (* let fvs := PS.elements fv in *)
         Γ' <- get_name_no_suff "env";;
        (* register its pretty name *)
        t1 <- make_env fvs (Maps.PTree.empty VarInfo) mapfv c Γ' Γ gfuns ;;
        let '(c', mapfv_new, g1) := t1 in
        let is_closed := match fvs with [] => true | _ => false end in
        (* debug *)
        (* fv_names <- get_pp_names_list fvs ;; *)
        (* log_msg (concat " " ("Closed" :: bool_to_string is_closed :: "Block has fvs :" :: fv_names)) ;; *)
        
        t2 <- make_full_closure defs mapfv_new mapfv gfuns Γ' is_closed ;;
        let '(mapfv_new', mapfv_old', gfuns', g2) := t2 in
        ef <- exp_closure_conv e mapfv_old' gfuns' c Γ ;;
        defs' <- fundefs_closure_conv defs mapfv_new' gfuns' c' ;;
        ret (Efun defs' (g2 ((snd ef) (fst ef))), g1)
      | Eapp f ft xs =>
        t1 <- get_var f mapfv gfuns c Γ ;;
        let '(f', g1) := t1 in     
        t2 <- get_vars xs mapfv gfuns c Γ ;;
        let '(xs', g2) := t2 in
        ptr <- get_name f code_suffix ;;
        Γ <- get_name f clo_env_suffix ;;
        ret (Eproj ptr clo_tag 0 f'
                   (Eproj Γ clo_tag 1 f'
                          (Eapp ptr ft (Γ :: xs'))), fun e => g1 (g2 e))
    | Eprim x prim ys e' =>
      t1 <- get_vars ys mapfv gfuns c Γ ;;
      let '(ys', f) := t1 in
      ef <- exp_closure_conv e' (Maps.PTree.set x BoundVar mapfv) gfuns c Γ ;;
         ret (Eprim x prim ys' ((snd ef) (fst ef)), f)
    | Ehalt x =>
      t1 <- get_var x mapfv gfuns c Γ ;;
      let '(x', f) := t1 in
      ret (Ehalt x', f)
    end
  with fundefs_closure_conv (defs : fundefs) (mapfv : VarInfoMap) (gfuns : GFunMap) (c : ctor_tag)
       : ccstate fundefs  :=
         match defs with
           | Fcons f tag ys e defs' =>
             (* Add arguments to the map *)
             let mapfv' := add_params ys mapfv in
             (* formal parameter for the environment pointer *)
             Γ <- get_name_no_suff "env" ;;
             ef <- exp_closure_conv e mapfv' gfuns c Γ ;;
             defs'' <- fundefs_closure_conv defs' mapfv gfuns c ;;
             (* find the new name of the function *)
             let code_ptr :=
                 match Maps.PTree.get (f : var) (mapfv : VarInfoMap) with
                   | Some entry =>
                     match entry with
                       | MRFun ptr => ptr
                       | _ => f (* should never reach here *)
                     end
                   | None => f (* should never reach here *)
                 end
             in
             ret (Fcons code_ptr tag (Γ :: ys) ((snd ef) (fst ef)) defs'')
           | Fnil => ret Fnil
         end.

  Definition closure_conversion_hoist (e : exp) (c: comp_data) : error exp * comp_data :=
    let Γ := 1%positive in
    let '(ef'_err, (c', _)) :=
        run_compM (exp_closure_conv e (Maps.PTree.empty VarInfo) (Maps.PTree.empty GFunInfo) 1%positive Γ)
                                        c tt in
    match ef'_err with
    | Ret (e', f') => (Ret (exp_hoist (f' e')), c')
    | Err str => (Err str, c')
    end.
    

  Definition populate_map (l : list (var * val)) map  :=
    fold_left (fun map x => M.set (fst x) BoundVar map) l map.

  (* Definition closure_conversion_hoist_open (rho : eval.env) (e : exp) ctag itag cenv nmap : exp := *)
  (*   let Γ := ((max_list (map fst (M.elements rho)) (max_var e 1%positive)) + 1)%positive in *)
  (*   let map := populate_map (M.elements rho) (Maps.PTree.empty VarInfo) in *)
  (*   let next := (Γ + 1)%positive in *)
  (*   let state := mkCont next ctag itag cenv nmap in *)
  (*   let '(e, f, s) := runState *)
  (*                       (exp_closure_conv e map (Maps.PTree.empty GFunInfo) 1%positive Γ) *)
  (*                       state in *)
  (*   exp_hoist (f e). *)
  
End CC.