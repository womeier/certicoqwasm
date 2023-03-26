Unset Universe Checking. (* maybe https://github.com/DeepSpec/InteractionTrees/issues/254 *)
From Wasm Require Import datatypes prettyprint.

From Coq Require Import ZArith.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.
From MetaCoq.Template Require Import bytestring MCString.

Import MonadNotation.

Record wasm_function :=
  { name : immediate
  ; export_name : string
  ; args : list (immediate * value_type)
  ; ret_type : option value_type
  ; locals : list (immediate * value_type)
  ; body : list basic_instruction
  }.

Record wasm_module :=
  { functions : list wasm_function
  ; memory : immediate                                                       (* size *)
  ; global_vars : list (immediate * value_type * immediate)                  (* var, type, init_value *)
  ; function_imports : list (string * immediate * string * list value_type)  (* namespace, function variable, import name, parameter types, currently no return value_type needed *)
  ; comment : string
  }.

Definition quote : string := String.String "034"%byte String.EmptyString.

Definition type_show (t : value_type) :=
  match t with
  | T_i32 => "i32"
  | T_i64 => "i64"
  | T_f32 => "f32"
  | T_f64 => "f64"
  end.

Definition var_show_identifier (v : immediate) :=
  "(;" ++ string_of_nat v ++ ";)".

Definition parameters_show (prefix : string) (l : list (immediate * value_type)) : string :=
  fold_left (fun _s p =>
    let name := var_show_identifier (fst p) in
    let type := type_show (snd p) in
      _s ++ " (" ++ prefix ++ " " ++ name ++ " " ++ type ++ ")") l "".

Definition function_show (f : wasm_function) : string :=
  let ret_type := match f.(ret_type) with
                  | None => ""
                  | Some t => "(result " ++ type_show t ++ ")"
                  end
  in
  "(func " ++ var_show_identifier f.(name) ++ " (export " ++ quote ++ f.(export_name) ++ quote ++ ")"
    ++ parameters_show "param" f.(args) ++ " " ++ ret_type ++ nl
    ++ parameters_show "local" f.(locals) ++ nl
    ++ pp_basic_instructions 2 f.(body) ++ ")" ++ nl.

Definition global_vars_show (prefix : string) (l : list (immediate * value_type * immediate)) : string :=
  fold_left (fun _s p =>
    let '(v, t, i) := p in
    let name := var_show_identifier v in
    let type := type_show t in
    let init := type_show t ++ ".const " ++ string_of_nat i
    in
    _s ++ "(" ++ prefix ++ " " ++ name ++ " (mut " ++ type  ++ ") (" ++ init ++ ")" ++ ") ") l "".

Definition function_imports_show (fns : list (string * immediate * string * list value_type)) :=
  fold_left (fun _s f =>
    let '(namespace, var, import_name, arg_types) := f in
    let func := "(func " ++ var_show_identifier var ++ " (param" ++ (fold_left (fun _s' t => _s' ++ " " ++ type_show t) arg_types "") ++ "))"
    in
    _s ++ nl ++ "(import " ++ quote ++ namespace ++ quote ++ " " ++ quote ++ import_name ++ quote ++ " " ++ func ++ ")"
  ) fns "".

Definition wasm_module_show (m : wasm_module) : string :=
  "(module" ++ nl ++ ";;" ++ nl ++
  ";; " ++ m.(comment) ++ nl ++
  function_imports_show m.(function_imports) ++ nl ++
  "(memory " ++ string_of_nat m.(memory) ++ ") ;; * 64 KB" ++ nl ++
  global_vars_show "global" m.(global_vars) ++ nl ++
  (fold_left (fun _s f => _s ++ nl ++ function_show f) m.(functions) "") ++ ")".
