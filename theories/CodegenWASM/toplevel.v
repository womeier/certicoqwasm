From Coq Require Import ZArith. 
From CertiCoq Require Import LambdaANF.toplevel.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import ExtLib.Structures.Monad.

Require Import LambdaANF.cps LambdaANF.cps_show.


Import MonadNotation.

Inductive wasm_term :=
| Wconst : nat -> wasm_term
| Wadd : wasm_term
| Wdebug : string -> wasm_term.

(* TODO readd environment variables and stuff *)
Definition wasm_show (e : wasm_term) := 
  match e with
  | Wdebug s => "WASM_SHOW: " ++ s
  | _ => "WASM_SHOW"
  end.

Definition LambdaANF_to_WASM (e : exp) : error wasm_term := Ret (Wdebug "(resulting WASM program test)").

Definition LambdaANF_to_WASM_Wrapper (prims : list (kername * string * bool * nat * positive)) (args : nat) (t : toplevel.LambdaANF_FullTerm) : error wasm_term * string :=
  let '(_, pr_env, cenv, ctag, itag, nenv, fenv, _, prog) := t in
  (LambdaANF_to_WASM prog, "").

Definition compile_LambdaANF_to_WASM (prims : list (kername * string * bool * nat * positive)) : CertiCoqTrans toplevel.LambdaANF_FullTerm wasm_term :=
  fun s =>
    debug_msg "Translating from LambdaANF to WASM" ;;
    opts <- get_options ;;
    let args := c_args opts in
    LiftErrorLogCertiCoqTrans "CodegenWASM" (LambdaANF_to_WASM_Wrapper prims args) s.
