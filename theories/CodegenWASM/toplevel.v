From Coq Require Import ZArith. 
From CertiCoq Require Import LambdaANF.toplevel.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Template Require Import bytestring MCString.

Require Import LambdaANF.cps LambdaANF.cps_show.


Import MonadNotation.

(* TODO use WasmCert-Coq*)

(* from: https://github.com/WebAssembly/spec/blob/main/interpreter/syntax/ast.ml
  | Br of var                         (* break to n-th surrounding label *)
  | BrIf of var                       (* conditional break *)
  | BrTable of var list * var         (* indexed break *)
  | CallIndirect of var * var         (* call function through table *)
  | MemorySize                        (* size of memory *)
  | MemoryGrow                        (* grow memory *)
  | Test of testop                    (* numeric test *)
  | Compare of relop                  (* numeric comparison *)
  | Unary of unop                     (* unary numeric operator *)
  | Binary of binop                   (* binary numeric operator *)
*)

Inductive type :=
  | I32
  | I64.

Inductive var :=
  (* TODO*)
  | Generic : string -> var.
    
Inductive wasm_instr :=
  | WI_unreachable : wasm_instr                               (* trap unconditionally *)
  | WI_nop : wasm_instr                                       (* do nothing *)
  | WI_comment : string -> wasm_instr                         (* do nothing *)
  | WI_block : list wasm_instr -> wasm_instr                  (* execute in sequence, for now just a list of instructions without block nesting *)
  | WI_if : wasm_instr -> wasm_instr -> wasm_instr            (* conditional *)
  | WI_return : wasm_instr                                    (* break from function body *)
  | WI_call : var -> wasm_instr                               (* call function *) 
  | WI_local_get : var -> wasm_instr                          (* read local variable *)
  | WI_local_set : var -> wasm_instr                          (* write local variable *)
  | WI_global_get : var -> wasm_instr                         (* read global variable *)
  | WI_global_set : var -> wasm_instr                         (* write global variable *)
  | WI_load : type -> wasm_instr                              (* read memory at address *)
  | WI_store : type -> wasm_instr                             (* write memory at address *)
  | WI_const : var -> type -> wasm_instr                      (* constant *)
  | WI_add : type -> wasm_instr                               (* add *)
  | WI_eq : type -> wasm_instr.                               (* equality check *)

Record wasm_function :=
  { name : var
  ; export : bool                                             (* export publicly *)
  ; args : list (var * type)
  ; ret_type : type
  ; locals : list (var * type)
  ; body : wasm_instr
  }.

Record wasm_module :=
  { functions : list wasm_function
  ; memory : var                                              (* size *)
  ; global_vars : list (var * type * var)                     (* var, type, init_value *)
  ; start : wasm_instr
  }.

Definition quote : string := String.String "034"%byte String.EmptyString.

Definition type_show (t : type) :=
  match t with 
  | I32 => "i32"
  | I64 => "i64"
  end.

Definition var_show (v : var) :=
  match v with Generic s => s end.


Definition instr_list_show (l : list wasm_instr) (show : wasm_instr -> string) : string :=
  (fold_left (fun _s i => _s ++ show i) l "").

(* TODO: typeclass show *)
Fixpoint instr_show (e : wasm_instr) : string := 
  (match e with
  | WI_unreachable => "unreachable"
  | WI_nop  => "nop"
  | WI_comment s => nl ++ ";; " ++ s
  | WI_block instructions => instr_list_show instructions instr_show
  | WI_return => "return"
  | WI_local_get x => "local.get " ++ var_show x
  | WI_local_set x => "local.set " ++ var_show x
  | WI_global_get x => "global.get " ++ var_show x
  | WI_global_set x => "global.set " ++ var_show x
  | WI_if thenBranch elseBranch => "if" ++ nl ++
                                      (* then *)
                                      instr_show thenBranch ++ nl ++
                                    "else" ++ nl ++
                                    instr_show elseBranch ++ nl ++
                                    "end"
  | WI_call f => "call " ++ var_show f
  | WI_load t => type_show t ++ ".load"
  | WI_store t => type_show t ++ ".store"
  | WI_const n t => type_show t ++ ".const " ++ var_show n
  | WI_add t => type_show t ++ ".add"
  | WI_eq t => type_show t ++ ".eq"
(*| Indirect function calls *)
  end) ++ nl.

Definition parameters_show (prefix : string) (l : list (var * type)) : string :=
  fold_left (fun _s p => 
    let name := var_show (fst p) in
    let type := type_show (snd p) in
      _s ++ " (" ++ prefix ++ " " ++ name ++ " " ++ type ++ ")") l "".
  
Definition function_show (f : wasm_function) : string :=
  "(func " ++ var_show f.(name) ++ (if f.(export)
                                    then " (export " ++ quote ++ var_show f.(name) ++ quote ++ ")"
                                    else "") ++ nl
    ++ parameters_show "param" f.(args) ++ " (result " ++ type_show f.(ret_type) ++ ")" ++ nl
    ++ parameters_show "local" f.(locals) ++ nl
    ++ instr_show f.(body) ++ nl ++ ")".

Definition global_vars_show (prefix : string) (l : list (var * type * var)) : string :=
  fold_left (fun _s p => 
    let '(v, t, i) := p in
    let name := var_show v in
    let type := type_show t in
    let init := (match t with
                 | I32 => "i32.const " ++ var_show i
                 | I64 => "i64.const " ++ var_show i
                 end) in
      _s ++ " (" ++ prefix ++ " " ++ name ++ " " ++ type  ++ " (" ++ init ++ ")" ++ ")") l "".

Definition wasm_module_show (m : wasm_module) : string :=
  "(module" ++ nl ++ ";;" ++ nl ++
  "(memory " ++ var_show m.(memory) ++ ")" ++ nl ++
    global_vars_show "global" m.(global_vars) ++ nl ++
    (fold_left (fun s f => s ++ nl ++ function_show f) m.(functions) "") ++ nl ++ ")".

(********************** BEGIN TRANSLATION *******************************)

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

Fixpoint collect_constr_tags (e : exp) {struct e} : list ctor_tag :=
(* TODO: make unique, use set *)
  match e with
  | Efun _ e' => collect_constr_tags e'
  | Econstr _ t _ e' => t :: collect_constr_tags e'
  | Ecase _ arms => List.concat (map (fun a => collect_constr_tags (snd a)) arms)
  | Eproj _ _ _ _ e' => collect_constr_tags e'
  | Eletapp _ _ _ _ e' => collect_constr_tags e'
  | Eprim _ _ _ e' => collect_constr_tags e'
  | Eprim_val _ _ e' => collect_constr_tags e'
  | Eapp _ _ _ => []
  | Ehalt _ => []
  end.

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

Definition generate_constr_alloc_function (cenv : ctor_env) (c : ctor_tag) : wasm_function :=
  let ctor_id := show_tree (show_con cenv c) in  (*TODO: translate to I32, fail if e.g. too large*)
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
    ([ WI_comment "save ret pointer"
     ; WI_global_get global_mem_ptr
     ; WI_local_set return_var

     ; WI_comment "copy const id"
     ; WI_global_get global_mem_ptr
     ; WI_const (Generic (ctor_id)) I32
     ; WI_store I32
     ; WI_global_get global_mem_ptr
     ; WI_const (Generic "4") I32
     ; WI_add I32
     ; WI_global_set global_mem_ptr
     ] ++ (* store argument pointers in memory *)
       concat (map (fun arg =>
         [ WI_comment ("storing " ++ var_show (fst arg) ++ " in memory")
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
     [ WI_comment "return pointer to beginning of memory segment"
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
    map (generate_constr_alloc_function cenv) (collect_constr_tags mainExpr) in

  mainInstr <- translate_exp nenv cenv ftag_flag mainExpr ;;
  Ret {| memory := Generic "100"
       ; functions := constr_alloc_functions ++ fns
       ; global_vars := [(Generic "$ptr", I64, Generic "0")]
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
