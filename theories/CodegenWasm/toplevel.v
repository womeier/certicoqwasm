From Wasm Require Import datatypes.

From Coq Require Import ZArith List.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import LambdaANF.cps LambdaANF.cps_show CodegenWasm.LambdaANF_to_Wasm.

Require Import ExtLib.Structures.Monad.
Import MonadNotation.

Definition LambdaANF_to_Wasm_Wrapper (prims : list (kername * string * bool * nat * positive)) (args : nat) (t : toplevel.LambdaANF_FullTerm) : error module * string :=
  let '(_, pr_env, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  match LambdaANF_to_Wasm nenv cenv prog with
  | Ret res => let '(module, _, _) := res in (Ret module, "")
  | Err err => (Err err, "")
  end.

Definition compile_LambdaANF_to_Wasm (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaANF_FullTerm module :=
  fun s =>
    debug_msg "Translating from LambdaANF to Wasm" ;;
    opts <- get_options ;;
    let args := c_args opts in
    LiftErrorLogCertiCoqTrans "CodegenWasm" (LambdaANF_to_Wasm_Wrapper prims args) s.
