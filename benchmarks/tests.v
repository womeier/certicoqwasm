Require Import Arith List String Uint63 BinNat BinInt Strings.Byte.
Require Import CertiCoq.Benchmarks.lib.vs.
Require Import CertiCoq.Benchmarks.lib.Binom.
Require Import CertiCoq.Benchmarks.lib.Color.
Require Import CertiCoq.Benchmarks.lib.sha256.
Require Import CertiCoq.Benchmarks.lib.coind.
(* Require Import CertiCoq.Benchmarks.lib.BersteinYangTermination. *)
(* Require Import CertiCoq.Benchmarks.lib.stack_machine. *)
From MetaCoq.Utils Require Import bytestring MCString.
From CertiCoq.Plugin Require Import CertiCoq.

Open Scope nat.
Import ListNotations.

CertiCoq -help.

Fixpoint compcert_bytes_to_stdlib_bytes (bs : list compcert.lib.Integers.Byte.int) : list Byte.byte :=
  match bs with
  | [] => []
  | b::bs' => match Coq.Strings.Byte.of_N (Z.to_N (compcert.lib.Integers.Byte.intval b)) with
              | Some x => x :: compcert_bytes_to_stdlib_bytes bs'
              | None => [] (* unreachable, since in bound*)
              end
  end.

Definition stdlib_bytes_to_compcert_bytes (bs : list Byte.byte) : list compcert.lib.Integers.Byte.int :=
  str_to_bytes (string_of_list_byte bs).


Compute (compcert_bytes_to_stdlib_bytes (stdlib_bytes_to_compcert_bytes [xaf; xff; "000"%byte])).

(* Compute (SHA_256' (str_to_bytes "hallo"%string)). *)
(* Compute (bytes_to_stdlib_bytes (SHA_256' (str_to_bytes "hallo"%string))). *)


(* Definition SHA_256_stdlib_bytes (bs : list compcert.lib.Integers.byte) :=
  compcert_bytes_to_stdlib_bytes (SHA_256' bs). *)

(* Sha *)
Definition test_bytes := list_byte_of_string "hallo".
Compute test_bytes.

Definition sha_fast (bytes: list Byte.byte) :=
  compcert_bytes_to_stdlib_bytes
  match bytes with
  | _ => sha256.SHA_256' (stdlib_bytes_to_compcert_bytes bytes)
  end.

(* Definition sha_fast := SHA_256_stdlib_bytes test_bytes. *)

(* Definition sha_fast := fun (n : nat) => S n. *)

Compute (sha_fast []).

Eval compute in "Compiling sha_fast"%bs.
CertiCoq Compile Wasm -time -debug sha_fast.
CertiCoq Show IR sha_fast.

(* Run on the generated Wasm binary, the resulting binary is what is used in the demo.
   wasm-opt --coalesce-locals --enable-tail-call CertiCoq.Benchmarks.tests.sha_fast.wasm -o sha_fast.wasm
*)

(* CertiCoq Compile Wasm -cps -time -debug sha_fast. *)
(* CertiCoq Compile -O 0 -cps -ext "_cps" sha_fast. *)
(* CertiCoq Compile -cps -ext "_cps_opt" sha_fast. *)
(* CertiCoq Generate Glue -file "glue_sha_fast" [ ]. *)

(* Eval compute in "Custom"%bs. *)

(* Definition custom (bs: list Byte.byte) := *)
(*   if ((List.length bs) >? 0%nat) then (bs ++ []) else bs. *)

(* CertiCoq Compile Wasm -debug custom. *)
(* CertiCoq Show IR custom. *)
