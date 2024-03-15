From CertiCoq.Plugin Require Import CertiCoq.

From Coq Require Import List Uint63 ZArith.

Import ListNotations.

Definition one := 1%uint63.

(* Definition list_of_prims := [ 1%uint63 ; 2%uint63 ; 3%uint63 ]. *)

Definition large_number := 9223372036854775807%uint63.

CertiCoq Compile Wasm one.

(* CertiCoq Compile Wasm list_of_prims. *)

CertiCoq Compile Wasm large_number.
