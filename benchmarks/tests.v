Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.
Require Import CertiCoq.Benchmarks.lib.coind.
From MetaCoq.Utils Require Import bytestring MCString.
From CertiCoq.Plugin Require Import CertiCoq.

Definition foo := 0.

Open Scope bs.

Import ListNotations.
Import VeriStar.

CertiCoq -help.

(* CertiCoq Generate Glue -file "basics" [ nat, list, bool ]. *)

(* Demo 1 *)

Definition demo1 := List.app (List.repeat true 500) (List.repeat false 300).

(* Demo 2 *)

Fixpoint repeat2 {A : Type} (x y : A) (n : nat) :=
  match n with
  | 0 => []
  | S n => x :: y :: repeat2 x y n
  end.

Definition demo2 := List.map negb (repeat2 true false 100).

(* Demo 3 *)

Definition demo3 := andb.

(* List sum *)

Definition list_sum := List.fold_left plus (List.repeat 1 100) 0.

(* Veristar *)

Definition vs_easy :=
  (fix loop (n : nat) (res : veristar_result) :=
     match n with
     | 0 =>
       match res with
       | Valid => true
       | _ => false
       end
     | S n =>
       let res := check_entailment example_ent in
       loop n res
     end) 100  Valid.

Definition vs_hard :=
  match vs.main_h with
  | Valid => true
  | _ => false
  end.

(* Binom *)

Definition binom := Binom.main.

(* Color *)
Definition color := Color.main.

(* Lazy factorial. Needs coinductive types *)

(* Definition lazy_factorial := coq_msg_info (string_of_Z (coind.lfact 150)). *)

(* Sha *)
Definition test := "Coq is a formal proof management system. It provides a formal language to write mathematical definitions, executable algorithms and theorems together with an environment for semi-interactive development of machine-checked proofs. Typical applications include the certification of properties of programming languages (e.g. the CompCert compiler certification project, the Verified Software Toolchain for verification of C programs, or the Iris framework for concurrent separation logic), the formalization of mathematics (e.g. the full formalization of the Feit-Thompson theorem, or homotopy type theory), and teaching."%string.

Definition sha := sha256.SHA_256 (sha256.str_to_bytes test).

Definition sha_fast := sha256.SHA_256' (sha256.str_to_bytes test).

Eval compute in "Compiling demo1".

CertiCoq Generate WASM -debug demo1.
(* CertiCoq Compile -O 0 -cps -ext "_cps" demo1. *)
(* CertiCoq Compile -cps -ext "_cps_opt" demo1. *)

Eval compute in "Compiling demo2".

CertiCoq Generate WASM -debug demo2.
(* CertiCoq Compile -O 0 -cps -ext "_cps" demo2. *)
(* CertiCoq Compile -cps -ext "_cps_opt" demo2. *)

(*
Eval compute in "Compiling demo3".

CertiCoq Generate WASM -cps -debug demo3.
(* CertiCoq Compile -O 0 -cps -ext "_cps" demo3. *)
(* CertiCoq Compile -cps -ext "_cps_opt" demo3. *)
*)

Eval compute in "Compiling list_sum".

CertiCoq Generate WASM -debug list_sum.
(* CertiCoq Compile -O 0 -cps -ext "_cps" list_sum. *)
(* CertiCoq Compile -cps -ext "_cps_opt" list_sum. *)


Eval compute in "Compiling vs_easy".

(* CertiCoq Generate WASM -cps -time -debug vs_easy. *)
CertiCoq Generate WASM -time -debug vs_easy.
(* CertiCoq Compile -O 0 -cps -ext "_cps" -time_anf vs_easy. *)
(* CertiCoq Compile -time -cps -ext "_cps_opt" vs_easy. *)

Eval compute in "Compiling vs_hard".

(* CertiCoq Generate WASM -cps -time -debug vs_hard. *)
CertiCoq Generate WASM -time -debug vs_hard.
(* CertiCoq Compile -O 0 -cps -ext "_cps" vs_hard. *)
(* CertiCoq Compile -cps -ext "_cps_opt" vs_hard. *)


Eval compute in "Compiling binom".

(* CertiCoq Generate WASM -cps -time -debug binom. *)
CertiCoq Generate WASM -time -debug binom.
(* CertiCoq Compile -O 0 -cps -ext "_cps" binom. *)
(* CertiCoq Compile -cps -ext "_cps_opt" binom. *)

(* Eval compute in "Compiling lazy factorial". *)

(* CertiCoq Compile -O 1 lazy_factorial.
CertiCoq Compile -ext "_opt" lazy_factorial.
CertiCoq Compile -args 1000 -config 9 -O 1 -ext "_opt_ll" lazy_factorial. *)
(* CertiCoq Compile -O 0 -cps -ext "_cps" demo1. *)
(* CertiCoq Compile -cps -ext "_cps_opt" demo1. *)


Eval compute in "Compiling color".

CertiCoq Generate WASM -time -debug color.
(* CertiCoq Compile -O 0 -time -cps -ext "_cps" color. *)
(* CertiCoq Compile -time -cps -ext "_cps_opt" color. *)

(* Don't compile slow sha *)
(* Eval compute in "Compiling sha". *)

(* CertiCoq Compile -cps -ext "_cps" sha. *)
(* CertiCoq Compile sha. *)
(* CertiCoq Compile -O 1 -cps -ext "_cps_opt" sha. *)
(* CertiCoq Compile -O 1 -ext "_opt" sha. *)

Eval compute in "Compiling sha_fast".

(* CertiCoq Generate WASM -cps -time -debug sha_fast. *)
CertiCoq Generate WASM -time -debug sha_fast.
(* CertiCoq Compile -O 0 -cps -ext "_cps" sha_fast. *)
(* CertiCoq Compile -cps -ext "_cps_opt" sha_fast. *)
