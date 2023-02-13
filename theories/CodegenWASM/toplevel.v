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
  | WI_const : var -> wasm_instr                              (* constant *)
  | WI_debug : string -> wasm_instr.

Record function :=
  { name : string
  ; args : list (var * type)
  ; body : list wasm_instr
  }.

Record wasm_module :=
  { functions : list function
  ; start : wasm_instr
  }.

Definition type_show (t : type) :=
  match t with I64 => "i64" end.

Definition var_show (v : var) :=
  match v with Generic s => s end.

(* TODO: typeclass show *)
(* TODO readd environment variables and stuff *)
Definition instr_show (e : wasm_instr) := 
  match e with
  | WI_debug s => "WASM_SHOW: " ++ s
  | _ => "WASM_SHOW"
  end.

Definition function_show (f : function) : string :=
  "(func" ++ f.(name) ++ (fold_left (fun s p => " (param " ++
                                                  (var_show (fst p) ++ " " ++
                                                  type_show (snd p) ++ ")")
                                                ) f.(args) "" ).

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

Fixpoint fundefs_length (fs : cps.fundefs) :=
  match fs with
  | Fnil => 0
  | Fcons _ _ _ _ fds' => 1 + fundefs_length fds'
  end.

Fixpoint LambdaANF_to_WASM (nenv : name_env) (cenv : ctor_env) (ftag_flag : bool) (e : exp) : error wasm_module := 
  Ret 
  {| functions := [];
     start :=
      (WI_debug ("kjljkL" ++ (* show_env nenv cenv ftag_flag nenv ++ *)
      match e with
      | Econstr x c ys e => "econstr: " ++ show_tree (show_var nenv x)
      | Ecase x arms => "ecase: " ++ show_tree (show_var nenv x)
      | Eproj _ _ _ _ _ => "proj"
      | Eletapp _ _ _ _ _ => "letapp"
      | Efun fundefs e => "fun (" ++ string_of_nat (fundefs_length fundefs) ++ ")"
      | Eapp _ _ _ => "app"
      | Eprim_val _ _ _ => "prim val"
      | Eprim _ _ _ _ => "prim"
      | Ehalt e => "halt"
      end))
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
