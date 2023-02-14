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
  | I64.

Inductive var :=
  (* TODO*)
  | Generic : string -> var.
    
Inductive wasm_instr :=
  | WI_unreachable : wasm_instr                               (* trap unconditionally *)
  | WI_noop : wasm_instr                                      (* do nothing *)
  | WI_noop_comment : string -> wasm_instr                    (* do nothing *)
  | WI_drop : wasm_instr                                      (* forget a value *)
  | WI_block : list wasm_instr -> wasm_instr                  (* execute in sequence *)
  | WI_if : list wasm_instr -> list wasm_instr -> wasm_instr  (* conditional *)
  | WI_return : wasm_instr                                    (* break from function body *)
  | WI_call : var -> wasm_instr                               (* call function *) 
  | WI_local_get : var -> wasm_instr                          (* read local variable *)
  | WI_local_set : var -> wasm_instr                          (* write local variable *)
  | WI_global_get : var -> wasm_instr                         (* read global variable *)
  | WI_global_set : var -> wasm_instr                         (* write global variable *)
  | WI_load : var -> wasm_instr                               (* read memory at address *)
  | WI_store : var -> wasm_instr                              (* write memory at address *)
  | WI_const : var -> wasm_instr.                             (* constant *)

Record wasm_function :=
  { name : var
  ; args : list (var * type)
  ; retType : type
  ; locals : list (var * type)
  ; body : wasm_instr
  }.

Record wasm_module :=
  { functions : list wasm_function
  ; start : wasm_instr
  }.

Definition type_show (t : type) :=
  match t with I64 => "i64" end.

Definition var_show (v : var) :=
  match v with Generic s => s end.


Definition instr_list_show (l : list wasm_instr) (show : wasm_instr -> string) : string :=
  (fold_left (fun _s i => _s ++ show i ++ nl) l "") ++ nl.

(* TODO: typeclass show *)
(* TODO readd environment variables and stuff *)
Fixpoint instr_show (e : wasm_instr) : string := 
  (match e with
  | WI_unreachable => "unreachable"
  | WI_noop  => "nop"
  | WI_noop_comment s => "nop ;; " ++ s
  | WI_block instructions => "(block " ++ instr_list_show instructions instr_show ++ ")"
  | WI_return => "return"
  | WI_local_get x => "local.get " ++ var_show x
  | WI_local_set x => "local.set " ++ var_show x
  | WI_global_get x => "global.get " ++ var_show x
  | WI_global_set x => "global.set " ++ var_show x
  | WI_if thenBranch elseBranch => "if (result i64) " ++ nl
                                ++ "(then " ++ instr_list_show thenBranch instr_show ++ ")"
                                ++ "(else " ++ instr_list_show elseBranch instr_show ++ ")"
  | _ => "nop ;; this instruction can't be translated yet"
(*
  | Indirect function calls
  | WI_call : var -> wasm_instr                               (* call function *) 
  | WI_load : var -> wasm_instr                               (* read memory at address *)
  | WI_store : var -> wasm_instr                              (* write memory at address *)
  | WI_const : var -> wasm_instr                             (* constant *)
  | WI_drop : wasm_instr                                      (* forget a value *) *)
  end) ++ nl.

Definition parameters_show (prefix : string) (l : list (var * type)) : string :=
  fold_left (fun _s p => 
    let name := var_show (fst p) in
    let type := type_show (snd p) in
      _s ++ " (" ++ prefix ++ " " ++ name ++ " " ++ type ++ ")") l "".
  
Definition function_show (f : wasm_function) : string :=
  "(func " ++ var_show f.(name) ++ parameters_show "param" f.(args)
                               ++ parameters_show "local" f.(locals) ++ nl
                               ++ "(return " ++ type_show f.(retType) ++ ")" ++ nl
    ++ instr_show f.(body) ++ nl ++ ")".

Definition wasm_module_show (m : wasm_module) : string :=
  "(module " ++ (fold_left (fun s f => s ++ nl ++ function_show f) m.(functions) "") ++ nl ++ ")".

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

Definition translate_var (nenv : name_env) (v : cps.var) : var :=
  Generic ("$" ++ show_tree (show_var nenv v)).


(* translate all expressions (except fundefs)

  the return value of an instruction is pushed on the stack
*)
Fixpoint translate_exp (nenv : name_env) (cenv : ctor_env) (ftag_flag : bool) (e : exp) : error wasm_instr :=
   match e with
   | Efun fundefs e => Err "unexpected nested function definition"
   | Econstr x c ys e => Ret (WI_noop_comment ("econstr: " ++ show_tree (show_var nenv x)))
   | Ecase x arms => Ret (
     WI_block (* TODO: choose dynamically *)
              [ WI_noop_comment ("ecase: " ++ show_tree (show_var nenv x))
              ; WI_local_get (translate_var nenv x)
              ; WI_return
              ])

   | Eproj x tg n y e => Ret (WI_noop_comment "proj")
   | Eletapp x f ft ys e => Ret (WI_noop_comment "letapp")
   | Eapp x ft ys => Ret (WI_noop_comment "app")
   | Eprim_val x p e => Ret (WI_noop_comment "prim val")
   | Eprim x p ys e => Ret (WI_noop_comment "prim")
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
  {| name := translate_var nenv name;
     args := map (fun p => (translate_var nenv p, I64)) args;
     retType := I64;
     locals := map (fun p => (p, I64)) (collect_local_variables nenv body);
     body := bodyRes |}.

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

  mainInstr <- translate_exp nenv cenv ftag_flag mainExpr ;;
  Ret {| functions := fns;
         start := mainInstr |}.

Definition LambdaANF_to_WASM_Wrapper (prims : list (kername * string * bool * nat * positive)) (args : nat) (t : toplevel.LambdaANF_FullTerm) : error wasm_module * string :=
  let '(_, pr_env, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  (LambdaANF_to_WASM nenv cenv true (* print flag *) prog, "").

Definition compile_LambdaANF_to_WASM (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaANF_FullTerm wasm_module :=
  fun s =>
    debug_msg "Translating from LambdaANF to WASM" ;;
    opts <- get_options ;;
    let args := c_args opts in
    LiftErrorLogCertiCoqTrans "CodegenWASM" (LambdaANF_to_WASM_Wrapper prims args) s.
