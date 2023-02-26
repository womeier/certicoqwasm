From Coq Require Import ZArith. 
From CertiCoq Require Import LambdaANF.toplevel.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Template Require Import bytestring MCString.

Require Import MSets.MSetAVL.
Require Import POrderedType.

Require Import LambdaANF.cps LambdaANF.cps_show CodegenWASM.wasm.

Import MonadNotation.

(*
(* Expressions [exp] of the LambdaANF language. *)
Inductive exp : Type :=
| Econstr: var -> ctor_tag -> list var -> exp -> exp
| Ecase: var -> list (ctor_tag * exp) -> exp
| Eproj: var -> ctor_tag -> N -> var -> exp -> exp
| Eletapp: var -> var -> fun_tag -> list var -> exp -> exp
| Efun: fundefs -> exp -> exp
| Eapp: var -> fun_tag -> list var -> exp
| Eprim_val : var -> primitive -> exp -> exp
| Eprim: var -> prim -> list var -> exp -> exp (* where prim is id *)
| Ehalt : var -> exp
with fundefs : Type :=
| Fcons: var -> fun_tag -> list var -> exp -> fundefs -> fundefs
| Fnil: fundefs.

*)

Definition constr_alloc_function_prefix := "$alloc_constr_".
Definition global_mem_ptr := Generic "$ptr".

Definition translate_var (nenv : name_env) (v : cps.var) : var :=
  Generic ("$" ++ show_tree (show_var nenv v)).


(* translate all expressions (except fundefs)

  the return value of an instruction is pushed on the stack
*)
Fixpoint translate_exp (nenv : name_env) (cenv : ctor_env) (ftag_flag : bool) (e : exp) : error wasm_instr :=
   match e with
   | Efun fundefs e => Err "unexpected nested function definition"
   | Econstr x c ys e => Ret (WI_comment ("econstr: " ++ show_tree (show_var nenv x)))
   | Ecase x arms => Ret (
     WI_block (* TODO: choose dynamically *)
              [ WI_comment ("ecase: " ++ show_tree (show_var nenv x))
              ; WI_comment "load <mem address>"
              ; WI_comment "compare with possible constrs"
              ; WI_local_get (translate_var nenv x)
              ; WI_return
              ])

   | Eproj x tg n y e => Ret (WI_comment "proj")
   | Eletapp x f ft ys e => Ret (WI_comment "letapp")
   | Eapp x ft ys => Ret (WI_comment "app")
   | Eprim_val x p e => Ret (WI_comment "prim val")
   | Eprim x p ys e => Ret (WI_comment "prim")
   | Ehalt e => Ret WI_return
   end.

Fixpoint collect_local_variables' (nenv : name_env) (e : exp) {struct e} : list cps.var :=
  match e with
  | Efun _ e' => collect_local_variables' nenv e'
  | Econstr x _ _ e' => x :: collect_local_variables' nenv e'
  | Ecase _ arms => List.concat (map (fun a => collect_local_variables' nenv (snd a)) arms)
  | Eproj x _ _ _ e' => x :: collect_local_variables' nenv e'
  | Eletapp x _ _ _ e' => collect_local_variables' nenv e'
  | Eprim x _ _ e' => x :: collect_local_variables' nenv e'
  | Eprim_val x _ e' => x :: collect_local_variables' nenv e'
  | Eapp _ _ _ => []
  | Ehalt _ => []
  end.

Definition collect_local_variables (nenv : name_env) (e : exp) : list var :=
  map (translate_var nenv) (collect_local_variables' nenv e).


Definition translate_function (nenv : name_env) (cenv : ctor_env) (ftag_flag : bool)
                            (name : cps.var) (args : list cps.var) (body : exp): error wasm_function :=
  bodyRes <- translate_exp nenv cenv ftag_flag body ;;
  Ret
  {| name := translate_var nenv name
   ; export := true
   ; args := map (fun p => (translate_var nenv p, I64)) args
   ; ret_type := I64
   ; locals := map (fun p => (p, I64)) (collect_local_variables nenv body)
   ; body := bodyRes
   |}.

Module S := Make Positive_as_OT.

Fixpoint collect_constr_tags' (e : exp) {struct e} : S.t :=
  match e with
  | Efun fds e' => S.union (collect_constr_tags' e')
          ((fix iter (fds : fundefs) : S.t :=
            match fds with
            | Fnil => S.empty
            | Fcons _ _ _ e'' fds' =>
                S.union (collect_constr_tags' e'') (iter fds')
            end) fds)
  | Econstr _ tg _ e' => S.add tg (collect_constr_tags' e')
  | Ecase _ arms => fold_left (fun _s a => S.union _s (S.add (fst a) (collect_constr_tags' (snd a)))) arms S.empty
  | Eproj _ _ _ _ e' => collect_constr_tags' e'
  | Eletapp _ _ _ _ e' => collect_constr_tags' e'
  | Eprim _ _ _ e' => collect_constr_tags' e'
  | Eprim_val _ _ e' => collect_constr_tags' e'
  | Eapp _ _ _ => S.empty
  | Ehalt _ => S.empty
  end.

Definition collect_constr_tags (e : exp) : list ctor_tag :=
  S.elements (collect_constr_tags' e).

(* cenv : Map[ctor_tag -> rec]:

{ ctor_name     : name    (* the name of the constructor *)
; ctor_ind_name : name    (* the name of its inductive type *)
; ctor_ind_tag  : ind_tag (* ind_tag of corresponding inductive type *)
; ctor_arity    : N       (* the arity of the constructor *)
; ctor_ordinal  : N       (* the [ctor_tag]s ordinal in inductive defn starting at zero *)
}.

*)

(* generates argument list for constructor with arity n*)
Fixpoint arg_list (n : nat) : list (var * type) :=
  match n with
  | 0 => []
  | S n' => arg_list n' ++ [(Generic ("$arg" ++ string_of_nat n'), I32)]
  end.

Definition constr_id (cenv : ctor_env) (c : ctor_tag) : nat :=
  Pos.to_nat c.

Definition generate_constr_alloc_function (cenv : ctor_env) (c : ctor_tag) : wasm_function :=
  let ctor_id := string_of_nat (constr_id cenv c) in
  let ctor_name := show_tree (show_con cenv c) in
  let return_var := Generic "$ret_pointer" in
(*  let info :=
    (match M.get c cenv with
     | Some {| ctor_name := nNamed name
             ; ctor_ind_name := nNamed ind_name
             |} => "ind type: " ++ ind_name ++ ", constr name: " ++ name
     | _ => "error: didn't find information of constructor"
     end) in *)

  let args := arg_list
    (match M.get c cenv with 
     | Some {| ctor_arity := n |} => N.to_nat n
     | _ => 42 (*TODO: handle error*)
     end) in

  {| name := Generic (constr_alloc_function_prefix ++ ctor_id)
   ; export := true
   ; args := args
   ; ret_type := I32
   ; locals := [(return_var, I32)]
   ; body := WI_block
    ([ WI_comment ("constructor: " ++ ctor_name)
     ; WI_comment "save ret pointer"
     ; WI_global_get global_mem_ptr
     ; WI_local_set return_var

     ; WI_comment "store const id"
     ; WI_global_get global_mem_ptr
     ; WI_const (Generic (ctor_id)) I32
     ; WI_store I32
     ; WI_global_get global_mem_ptr
     ; WI_const (Generic "4") I32
     ; WI_add I32
     ; WI_global_set global_mem_ptr
     ] ++ (* store argument pointers in memory *)
       concat (map (fun arg =>
         [ WI_comment ("store " ++ var_show (fst arg) ++ " in memory")
         ; WI_global_get global_mem_ptr
         ; WI_local_get (fst arg)
         ; WI_store I32
         ; WI_global_get global_mem_ptr
         ; WI_const (Generic "4") I32
         ; WI_add I32
         ; WI_global_set global_mem_ptr
         ]
       ) args) 
     ++
     [ WI_comment "ptr to beginning of memory segment"
     ; WI_local_get return_var
     ; WI_return
     ])
   |}.
(* generates for constr e a function that takes the arguments
  and allocates a record in the linear memory
*)

Definition LambdaANF_to_WASM (nenv : name_env) (cenv : ctor_env) (ftag_flag : bool) (e : exp) : error wasm_module := 
  let (fns, mainExpr) :=
    match e with
    | Efun fds exp => (* fundefs only allowed on the uppermost level *)
      ((fix iter (fds : fundefs) : list wasm_function :=
          match fds with
          | Fnil => []
          | Fcons x tg xs e fds' =>
              match translate_function nenv cenv ftag_flag x xs e with
              | Ret fn => fn :: (iter fds')
              (* TODO : pass on error*)
              | Err _ => []
              end
          end) fds, exp)
    | _ => ([], e)
  end in

  let constr_alloc_functions :=
    map (generate_constr_alloc_function cenv) (collect_constr_tags e) in

  mainInstr <- translate_exp nenv cenv ftag_flag mainExpr ;;
  Ret {| memory := Generic "100"
       ; functions := constr_alloc_functions ++ fns
       ; global_vars := [(global_mem_ptr, I32, Generic "0")]
       ; comment := "constructors: " ++ (fold_left (fun _s p => _s ++ string_of_nat (constr_id cenv p) ++ ", ") (collect_constr_tags e) "")
       ; start := mainInstr
       |}.

Definition LambdaANF_to_WASM_Wrapper (prims : list (kername * string * bool * nat * positive)) (args : nat) (t : toplevel.LambdaANF_FullTerm) : error wasm_module * string :=
  let '(_, pr_env, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  (LambdaANF_to_WASM nenv cenv true (* print flag *) prog, "").

Definition compile_LambdaANF_to_WASM (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaANF_FullTerm wasm_module :=
  fun s =>
    debug_msg "Translating from LambdaANF to WASM" ;;
    opts <- get_options ;;
    let args := c_args opts in
    LiftErrorLogCertiCoqTrans "CodegenWASM" (LambdaANF_to_WASM_Wrapper prims args) s.
