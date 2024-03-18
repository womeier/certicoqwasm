Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.
Require Import CertiCoq.Benchmarks.lib.coind.
From MetaCoq.Utils Require Import bytestring MCString.
(* From CertiCoq.Plugin Require Import CertiCoq. *)

From Coq Require Import Bool.
From Coq Require Import Extraction.
From Coq Require Import List.
From Coq Require Import Program.

Definition foo := 0.

Open Scope bs.

Import ListNotations.
Import VeriStar.

(* CertiCoq -help. *)


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


From RustExtraction Require Import Loader ExtrRustBasic.
From RustExtraction Require Import ExtrRustUncheckedArith.

Eval compute in "Compiling demo1".
Redirect "rust/demo1.rs" Rust Extract demo1.

Eval compute in "Compiling demo2".
Redirect "rust/demo2.rs" Rust Extract demo2.

Eval compute in "Compiling list_sum".
Redirect "rust/list_sum.rs" Rust Extract list_sum.

Eval compute in "Compiling vs_easy".
Redirect "rust/vs_easy.rs" Rust Extract vs_easy.

Eval compute in "Compiling vs_hard".
Redirect "rust/vs_hard.rs" Rust Extract vs_hard.

Eval compute in "Compiling binom".
Redirect "rust/binom.rs" Rust Extract binom.

(* Eval compute in "Compiling color". *)
Eval compute in "Compiling color".
(* Require Import ZArith. *)
Redirect "rust/color.rs" Rust Extract color.

Eval compute in "Compiling sha_fast".
Redirect "rust/sha_fast.rs" Rust Extract sha_fast.
