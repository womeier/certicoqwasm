From Coq Require Import ZArith. 
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Template Require Import bytestring MCString.

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
  ; comment : string
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
  | WI_if thenBranch WI_nop => "if" ++ nl ++
                                  instr_show thenBranch ++ nl ++
                               "end"
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
    ++ instr_show f.(body) ++ ")" ++ nl.

Definition global_vars_show (prefix : string) (l : list (var * type * var)) : string :=
  fold_left (fun _s p => 
    let '(v, t, i) := p in
    let name := var_show v in
    let type := type_show t in
    let init := (match t with
                 | I32 => "i32.const " ++ var_show i
                 | I64 => "i64.const " ++ var_show i
                 end) in
      _s ++ " (" ++ prefix ++ " " ++ name ++ " (mut " ++ type  ++ ") (" ++ init ++ ")" ++ ")") l "".

Definition wasm_module_show (m : wasm_module) : string :=
  "(module" ++ nl ++ ";;" ++ nl ++
  ";; " ++ m.(comment) ++ nl ++
  "(memory " ++ var_show m.(memory) ++ ") ;; * 64 KB" ++ nl ++
    global_vars_show "global" m.(global_vars) ++ nl ++
    (fold_left (fun s f => s ++ nl ++ function_show f) m.(functions) "") ++ ")".
