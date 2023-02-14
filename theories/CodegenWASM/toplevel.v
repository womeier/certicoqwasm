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

Record function :=
  { name : string
  ; args : list (var * type)
  ; retType : type
  ; locals : list (var * type)
  ; body : list wasm_instr (* normal expression *)
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
  | _ => "WASM_SHOW instr"
  end.

Definition parameters_show (prefix : string) (l : list (var * type)) : string :=
  fold_left (fun _s p => 
    let name := var_show (fst p) in
    let type := type_show (snd p) in
      _s ++ " (" ++ prefix ++ " " ++ name ++ " " ++ type ++ ")") l "".
  
Definition function_show (f : function) : string :=
  "(func" ++ f.(name) ++ parameters_show "param" f.(args) ++ parameters_show "local" f.(locals) ++ nl ++ 
   "(return " ++ type_show f.(retType) ++ ")"
  ++ ")".

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

Fixpoint LambdaANF_to_WASM (nenv : name_env) (cenv : ctor_env) (ftag_flag : bool) (e : exp) : error wasm_module := 
  Ret 
  {| functions :=
        match e with
        | Efun fds _ => 
          (* translate functions *)
(*          (fix iter (fds : fundefs) : M unit :=
            match fds with
            | Fnil =>
            | Fcons x tg xs e fds' =>
                   iter fds'
            end) fds *)
            []
           
        | _ => []
        end;
    
     start :=
      match e with
      | Econstr x c ys e => WI_noop_comment ("econstr: " ++ show_tree (show_var nenv x))
      | Ecase x arms => WI_noop_comment ("ecase: " ++ show_tree (show_var nenv x))
      | Eproj _ _ _ _ _ => WI_noop_comment "proj"
      | Eletapp _ _ _ _ _ => WI_noop_comment "letapp"
      | Efun fundefs e => WI_noop_comment "TODO: unexpected nested function definition" (* TODO *)
      | Eapp _ _ _ => WI_noop_comment "app"
      | Eprim_val _ _ _ => WI_noop_comment "prim val"
      | Eprim _ _ _ _ => WI_noop_comment "prim"
      | Ehalt e => WI_noop_comment "halt"
      end
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
