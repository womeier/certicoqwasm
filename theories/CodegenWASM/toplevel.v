From Coq Require Import ZArith. 
From CertiCoq Require Import LambdaANF.toplevel.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.

Require Import LambdaANF.cps.

Definition compile_LambdaANF_to_WASM (e : exp) : error string := Ret "(resulting WASM program)".

(*
Definition compile_LambdaANF_to_WASM (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaANF_FullTerm string :=
  fun s =>
    debug_msg "Translating from LambdaANF to WASM" ;;
    opts <- get_options ;;
    LiftErrorCertiCoqTrans "Codegen" WASM_trans s.
      *)
