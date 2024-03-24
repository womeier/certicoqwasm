From CertiCoq.Plugin Require Import CertiCoq.

From Coq Require Import List Uint63 ZArith.

Import ListNotations.

Definition addition := 1000 + 1000.

Definition addition_primitive := (1000 + 1000)%uint63.

CertiCoq Compile Wasm addition.

CertiCoq Compile Wasm addition_primitive.

Definition subtraction := 1000 - 1000.

Definition subtraction_primitive := (1000 - 1000)%uint63.

CertiCoq Compile Wasm subtraction.

CertiCoq Compile Wasm subtraction_primitive.

Definition multiplication := 250 * 250.

Definition multiplication_primitive := (250 * 250)%uint63. 

CertiCoq Compile Wasm multiplication.

CertiCoq Compile Wasm multiplication_primitive.

Definition division := 1000 / 1000.

Definition division_primitive := (1000 / 1000)%uint63.

CertiCoq Compile Wasm division.

CertiCoq Compile Wasm division_primitive.

Definition modulus := 1000 mod 1000.

Definition modulus_primitive := (1000 mod 1000)%uint63.

CertiCoq Compile Wasm modulus.

CertiCoq Compile Wasm modulus_primitive.

Definition list_sum := List.fold_left plus (List.repeat 1 10000) 0.

Definition list_sum_primitive :=
  List.fold_left Uint63.add (List.repeat 1%uint63 10000) 0%uint63.

CertiCoq Compile Wasm list_sum.

CertiCoq Compile Wasm list_sum_primitive.

