From CertiCoq.Plugin Require Import CertiCoq.

From Coq Require Import List Uint63 ZArith.

Import ListNotations.

(* A collection of sanity checks *)

Definition max_uint63 := 9223372036854775807%uint63.
Definition max_uint63_Z := 9223372036854775807%Z.

Definition addition_primitive := (42 + 42 =? Uint63.to_Z (42 + 42)%uint63)%Z.

Definition addition_primitive_overflow := ((max_uint63_Z + 1) mod Uint63.wB  =? Uint63.to_Z (max_uint63 + 1)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addition_primitive" addition_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addition_primitive_overflow" addition_primitive_overflow.

Definition subtraction_primitive := (42 - 42 =? Uint63.to_Z (42 - 42)%uint63)%Z.

Definition subtraction_primitive_underflow := ((0 -1) mod Uint63.wB  =? Uint63.to_Z (0 - 1)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subtraction_primitive" subtraction_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subtraction_primitive_underflow" subtraction_primitive_underflow.

Definition multiplication_primitive := (42 * 42 =? Uint63.to_Z (42 * 42)%uint63)%Z.

Definition multiplication_primitive_overflow := ((2 * max_uint63_Z) mod Uint63.wB =? Uint63.to_Z (2 * max_uint63)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.multiplication_primitive" multiplication_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.multiplication_primitive_overflow" multiplication_primitive_overflow.

Definition division_primitive := (7 / 3 =? Uint63.to_Z (7 / 3)%uint63)%Z.

Definition division_primitive_0 := (42 / 0 =? Uint63.to_Z (42 / 0)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.division_primitive" division_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.division_primitive_0" division_primitive_0.

Definition land_primitive := (Z.land 3 7 =? Uint63.to_Z (3 land 7)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.land_primitive" land_primitive.

Definition lor_primitive := (Z.lor 3 7 =? Uint63.to_Z (3 lor 7)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lor_primitive" lor_primitive.

Definition lsl_primitive := (Z.shiftl 1 8 =? Uint63.to_Z (1 << 8)%uint63)%Z.

Definition lsl_primitive_overflow := ((Z.shiftl 1 63) mod Uint63.wB =? Uint63.to_Z (1 << 63)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsl_primitive" lsl_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsl_primitive_overflow" lsl_primitive_overflow.

Definition lsr_primitive := (Z.shiftr 256 8 =? Uint63.to_Z (256 >> 8)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsr_primitive" lsr_primitive.

Definition eqb_true_primitive := (42 =? 42)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.eqb_true_primitive" eqb_true_primitive.

Definition eqb_false_primitive := (41 =? 42)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.eqb_false_primitive" eqb_false_primitive.
