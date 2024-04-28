From CertiCoq.Plugin Require Import CertiCoq.

From Coq Require Import List Uint63 ZArith.

Import ListNotations.

Definition addition_primitive := (42 + 42 =? Uint63.to_Z (42 + 42)%uint63)%Z.

Definition addition_primitive_overflow := ((9223372036854775807 + 1) mod Uint63.wB  =? Uint63.to_Z (9223372036854775807 + 1)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addition_primitive" addition_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addition_primitive_overflow" addition_primitive_overflow.
