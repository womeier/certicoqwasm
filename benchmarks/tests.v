Require Import Arith List String.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.
Require Import CertiCoq.Benchmarks.lib.coind.
Require Import CertiCoq.Benchmarks.lib.BernsteinYangTermination.
Require Import CertiCoq.Benchmarks.lib.stack_machine.
Require Import BinNat Uint63.

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

Definition list_sum := List.fold_left Nat.add (List.repeat 1 100) 0.

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


Fixpoint ack (n m : nat) : nat :=
  match n with
  | O => S m
  | S p => let fix ackn (m : nat) :=
            match m with
            | O => ack p 1
            | S q => ack p (ackn q)
            end
          in ackn m
  end.
Definition ack_3_9 := ack 3 9.

Fixpoint even n :=
  match n with
  | O => true
  | S m => odd m
  end
  with odd n :=
    match n with
    | O => false
    | S k => even k
    end.
Definition even_10000 := even (100 * 100).

Definition bernstein_yang := W 10.

Definition stack_machine_gauss_nat :=
  let n := 1000 in
  match (s_execute' (gauss_sum_sintrs_nat n)) with
  | [ n' ] => Some (n' - (n * (n + 1))/2)
  | _ => None
  end.

Definition stack_machine_gauss_N :=
  let n := 1000%N in
  match (s_execute' (gauss_sum_sintrs_N n)) with
  | [ n' ] => Some (n' - (n * (n + 1))/2)%N
  | _ => None
  end.

Definition stack_machine_gauss_PrimInt :=
  let n := 1000%uint63 in
  match (s_execute' (gauss_sum_sintrs_PrimInt n)) with
  | [ n' ] => Some (n' - (n * (n + 1))/2)%uint63
  | _ => None
  end.

From RustExtraction Require Import Loader ExtrRustBasic.
(* comment out for naive *)
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


Eval compute in "Compiling sm_gauss_nat".
Redirect "rust/sm_gauss_nat.rs" Rust Extract stack_machine_gauss_nat.

Eval compute in "Compiling sm_gauss_N".
Redirect "rust/sm_gauss_N.rs" Rust Extract stack_machine_gauss_N.

Eval compute in "Compiling sm_gauss_primInt".
Redirect "rust/sm_gauss_primInt.rs" Rust Extract stack_machine_gauss_PrimInt.

(* the following three are taken from coq-rust-extraction *)
Eval compute in "Compiling ack_3_9".
Redirect "rust/ack_3_9.rs" Rust Extract ack_3_9.

(* bernstein_yang: compilation fine, runs for quite long *)
Eval compute in "Compiling BernsteinYang".
Redirect "rust/bernstein_yang.rs" Rust Extract bernstein_yang.

Eval compute in "Compiling Even_10000".
Redirect "rust/even_10000.rs" Rust Extract even_10000.
