Unset Universe Checking. (* maybe https://github.com/DeepSpec/InteractionTrees/issues/254 *)
From Wasm Require Import datatypes.

From Coq Require Import ZArith List.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import LambdaANF.cps LambdaANF.cps_show CodegenWASM.LambdaANF_to_WASM.

Require Import ExtLib.Structures.Monad.
Import MonadNotation.

Definition LambdaANF_to_WASM_Wrapper (prims : list (kername * string * bool * nat * positive)) (args : nat) (t : toplevel.LambdaANF_FullTerm) : error module * string :=
  let '(_, pr_env, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  (LambdaANF_to_WASM nenv cenv prog, "").

Definition compile_LambdaANF_to_WASM (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaANF_FullTerm module :=
  fun s =>
    debug_msg "Translating from LambdaANF to WASM" ;;
    opts <- get_options ;;
    let args := c_args opts in
    LiftErrorLogCertiCoqTrans "CodegenWASM" (LambdaANF_to_WASM_Wrapper prims args) s.
