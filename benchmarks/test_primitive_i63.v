From CertiCoq.Plugin Require Import CertiCoq.

From Coq Require Import List Uint63 ZArith.

Import ListNotations.

(* A collection of sanity checks *)

Definition max_uint63 := 9223372036854775807%uint63.
Definition max_uint63_Z := 9223372036854775807%Z.

Definition addition_primitive := (42 + 42 =? Uint63.to_Z (42 + 42)%uint63)%Z.

Definition addition_primitive_overflow := ((max_uint63_Z + 1) mod Uint63.wB  =? Uint63.to_Z (max_uint63 + 1)%uint63)%Z.

Definition addition_primitive1 := (2 + 3 =? 5)%uint63.

Definition addition_primitive2 := (9223372036854775807 + 1 =? 0)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addition_primitive" addition_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addition_primitive_overflow" addition_primitive_overflow.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addition_primitive1" addition_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addition_primitive2" addition_primitive2.

Definition addc_primitive_C0 :=
  match (Uint63.addc 1 2) with
  | C0 i => (i =? 3)%uint63
  | _ => false
  end.

Definition addc_primitive_C1 :=
  match (Uint63.addc max_uint63 1) with
  | C0 _ => false
  | C1 i => (i =? 0)%uint63
  end.

Definition addc_primitive1 :=
  match (Uint63.addc 2 3) with
  | C0 i => (i =? 5)%uint63
  | _ => false
  end.

Definition addc_primitive2 :=
  match (Uint63.addc 9223372036854775807 2) with
  | C1 i => (i =? 1)%uint63
  | _ => false
  end.

Definition addcarryc_primitive_C0 :=
  match (Uint63.addcarryc 40 1) with
  | C0 i => (i =? 42)%uint63
  | C1 _ => false
  end.

Definition addcarryc_primitive_C1 :=
  match (Uint63.addcarryc max_uint63 1) with
  | C0 _  => false
  | C1 i => (i =? 1)%uint63
  end.

Definition addcarryc_primitive1 :=
  match (Uint63.addcarryc 2 3) with
  | C0 i  => (i =? 6)%uint63
  | _ => false
  end.

Definition addcarryc_primitive2 :=
  match (Uint63.addcarryc 9223372036854775807 2) with
  | C1 i  => (i =? 2)%uint63
  | _ => false
  end.


CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addc_primitive_C0" addc_primitive_C0.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addc_primitive_C1" addc_primitive_C1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addc_primitive1" addc_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addc_primitive2" addc_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addcarryc_primitive_C0" addcarryc_primitive_C0.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addcarryc_primitive_C1" addcarryc_primitive_C1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addcarryc_primitive1" addcarryc_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addcarryc_primitive2" addcarryc_primitive2.

Definition subtraction_primitive := (42 - 42 =? Uint63.to_Z (42 - 42)%uint63)%Z.

Definition subtraction_primitive_underflow := ((0 -1) mod Uint63.wB  =? Uint63.to_Z (0 - 1)%uint63)%Z.
Definition sub_primitive1 := (3 - 2 =? 1)%uint63.

Definition sub_primitive2 := (0 - 1 =? 9223372036854775807)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subtraction_primitive" subtraction_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subtraction_primitive_underflow" subtraction_primitive_underflow.

Definition subc_primitive_C0 :=
  match (Uint63.subc 2 2) with
  | C0 i => (i =? 0)%uint63
  | _ => false
  end.

Definition subc_primitive_C1 :=
  match (Uint63.subc 1 2) with
  | C0 _ => false
  | C1 i => (i =? max_uint63)%uint63
  end.

Definition subcarryc_primitive_C0 :=
  match (Uint63.subcarryc 2 1) with
  | C0 i => (i =? 0)%uint63
  | _ => false
  end.

Definition subcarryc_primitive_C1 :=
  match (Uint63.subcarryc 2 2) with
  | C0 _  => false
  | C1 i => (i =? max_uint63)%uint63
  end.

Definition subc_primitive1 :=
  match (Uint63.subc 3 2) with
  | C0 i => (i =? 1)%uint63
  | _ => false
  end.

Definition subc_primitive2 :=
  match (Uint63.subc 0 1) with
  | C1 i => (i =? 9223372036854775807)%uint63
  | _ => false
  end.

Definition subcarryc_primitive1 :=
  match (Uint63.subcarryc 3 1) with
  | C0 i => (i =? 1)%uint63
  | _ => false
  end.

Definition subcarryc_primitive2 :=
  match (Uint63.subcarryc 0 1) with
  | C1 i => (i =? 9223372036854775806)%uint63
  | _ => false
  end.


CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subc_primitive_C0" subc_primitive_C0.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subc_primitive_C1" subc_primitive_C1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subc_primitive1" subc_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subc_primitive2" subc_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subcarryc_primitive_C0" subcarryc_primitive_C0.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subcarryc_primitive_C1" subcarryc_primitive_C1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subcarryc_primitive1" subcarryc_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.subcarryc_primitive2" subcarryc_primitive2.

Definition multiplication_primitive := (42 * 42 =? Uint63.to_Z (42 * 42)%uint63)%Z.

Definition multiplication_primitive_overflow := ((2 * max_uint63_Z) mod Uint63.wB =? Uint63.to_Z (2 * max_uint63)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.multiplication_primitive" multiplication_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.multiplication_primitive_overflow" multiplication_primitive_overflow.

Definition mulc_test a b :=
  let '(q, r) := (Uint63.mulc a b)%uint63 in
  (Uint63.to_Z a * Uint63.to_Z b =? (Uint63.to_Z q) * Uint63.wB + Uint63.to_Z r)%Z.

Definition mulc_primitive := mulc_test 2 3.

Definition mulc_primitive_overflow := mulc_test 9223372036854775807 2.

Definition mulc_primitive_0 := mulc_test 0 0.

Definition mulc_primitive1 :=
  let '(h, l) := Uint63.mulc 2 3 in andb (h =? 0)%uint63 (l =? 6)%uint63.

Definition mulc_primitive2 :=
  let '(h, l) := Uint63.mulc 9223372036854775807 2 in andb (h =? 1)%uint63 (l =? 9223372036854775806)%uint63.

Definition mulc_primitive3 :=
  let '(h, l) := Uint63.mulc 0 0 in andb (h =? 0)%uint63 (l =? 0)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.mulc_primitive" mulc_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.mulc_primitive1" mulc_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.mulc_primitive2" mulc_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.mulc_primitive3" mulc_primitive3.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.mulc_primitive_overflow" mulc_primitive_overflow.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.mulc_primitive_0" mulc_primitive_0.

Definition division_primitive := (42 / 48 =? Uint63.to_Z (42 / 48)%uint63)%Z.

Definition division_primitive_0 := (42 / 0 =? Uint63.to_Z (42 / 0)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.division_primitive" division_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.division_primitive_0" division_primitive_0.

Definition modulo_primitive := (7 mod 3 =? Uint63.to_Z (7 mod 3)%uint63)%Z.

Definition modulo_primitive1 := (6 mod 3 =? 0).

Definition modulo_primitive2 := (5 mod 3 =? 2).

Definition modulo_primitive_0 := (42 mod 0 =? Uint63.to_Z (42 mod 0)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.modulo_primitive" modulo_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.modulo_primitive1" modulo_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.modulo_primitive2" modulo_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.modulo_primitive_0" modulo_primitive_0.

Definition diveucl_test x y := 
  let '(q, r) := diveucl x y in
  let '(q', r') := Z.div_eucl (to_Z x) (to_Z y) in
  andb (q' =? Uint63.to_Z q)%Z (r' =? Uint63.to_Z r)%Z.

Definition diveucl_primitive1 := diveucl_test 6 3.

Definition diveucl_primitive2 := diveucl_test 5 3.
  
Definition diveucl_primitive_0 :=
  let '(q, r) := (Uint63.diveucl 42 0)%uint63 in
  let '(q', r') := (Z.div_eucl 42 0)%Z in
  andb (q' =? Uint63.to_Z q)%Z (r' =? Uint63.to_Z r)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.diveucl_primitive1" diveucl_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.diveucl_primitive2" diveucl_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.diveucl_primitive_0" diveucl_primitive_0.

Definition addmuldiv_primitive p x y:=
  let r := (Uint63.addmuldiv p x y)%uint63 in
  let r' := (((to_Z x) * 2 ^ (to_Z p) + (to_Z y) / 2 ^ (63 - to_Z p))  mod Uint63.wB)%Z in
  (r' =? to_Z r)%Z.

Definition addmuldiv_primitive1 := addmuldiv_primitive 7 9 13.

Definition addmuldiv_primitive2 := addmuldiv_primitive 32 3 5629499534213120.

Definition addmuldiv_primitive3 := addmuldiv_primitive 65 9 13.

(* Definition addmuldiv_test := addmuldiv 32 0 2147483648. *)

(* Definition addmuldiv_test := addmuldiv 41 3019397 0. *)

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addmuldiv" addmuldiv_test.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addmuldiv_primitive1" addmuldiv_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addmuldiv_primitive1" addmuldiv_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addmuldiv_primitive2" addmuldiv_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.addmuldiv_primitive3" addmuldiv_primitive2.

Definition div21 xh xl y :=
  let '(q, r) := (Uint63.diveucl_21 xh xl y)%uint63 in
  let '(q', r') := (Z.div_eucl (to_Z xh * Uint63.wB + to_Z xl) (to_Z y))%Z in
  andb (q' =? Uint63.to_Z q)%Z (r' =? Uint63.to_Z r)%Z.

Definition div21_test := diveucl_21 2173603 984071702952542208 6639724220743942144.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.div21" div21_test.

Definition diveucl_21_primitive1 := div21 1 1 2.

Definition diveucl_21_primitive2 :=
  let '(q, r) := (diveucl_21 1 1 0) in
  andb (0 =? to_Z q)%Z (0 =? to_Z r)%Z.

Definition diveucl_21_primitive3 :=
  let '(q, r) := (diveucl_21 1 1 0) in
  andb (0 =? to_Z q)%Z (0 =? to_Z r)%Z.

Definition diveucl_21_primitive4 := div21 9305446873517 1793572051078448654 4930380657631323783.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.diveucl_21_primitive1" diveucl_21_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.diveucl_21_primitive2" diveucl_21_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.diveucl_21_primitive3" diveucl_21_primitive3.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.diveucl_21_primitive4" diveucl_21_primitive4.

Definition land_primitive := (Z.land 3 7 =? Uint63.to_Z (3 land 7)%uint63)%Z.

Definition land_primitive1 := (0 land 0 =? 0)%uint63.

Definition land_primitive2 := (9223372036854775807 land 0 =? 0)%uint63.

Definition land_primitive3 := (0 land 9223372036854775807 =? 0)%uint63.

Definition land_primitive4 := (9223372036854775807 land 9223372036854775807 =? 9223372036854775807)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.land_primitive" land_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.land_primitive1" land_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.land_primitive2" land_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.land_primitive3" land_primitive3.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.land_primitive4" land_primitive4.

Definition lor_primitive := (Z.lor 3 7 =? Uint63.to_Z (3 lor 7)%uint63)%Z.

Definition lor_primitive1 := (0 lor 0 =? 0)%uint63.

Definition lor_primitive2 := (9223372036854775807 lor 0 =? 9223372036854775807)%uint63.

Definition lor_primitive3 := (0 lor 9223372036854775807 =? 9223372036854775807)%uint63.

Definition lor_primitive4 := (9223372036854775807 lor 9223372036854775807 =? 9223372036854775807)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lor_primitive" lor_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lor_primitive1" lor_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lor_primitive2" lor_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lor_primitive3" lor_primitive3.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lor_primitive4" lor_primitive4.

Definition lxor_primitive := (Z.lxor 3 7 =? Uint63.to_Z (3 lxor 7)%uint63)%Z.

Definition lxor_primitive1 := (Z.lxor 0 0 =? 0)%uint63.

Definition lxor_primitive2 := (9223372036854775807 lxor 0 =? 9223372036854775807)%uint63.

Definition lxor_primitive3 := (0 lxor 9223372036854775807 =? 9223372036854775807)%uint63.

Definition lxor_primitive4 := (9223372036854775807 lxor 9223372036854775807 =? 0)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lxor_primitive" lxor_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lxor_primitive1" lxor_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lxor_primitive2" lxor_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lxor_primitive3" lxor_primitive3.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lxor_primitive4" lxor_primitive4.

Definition lsl_primitive := (Z.shiftl 1 8 =? Uint63.to_Z (1 << 8)%uint63)%Z.

Definition lsl_primitive_overflow := ((Z.shiftl 8 64) mod Uint63.wB =? Uint63.to_Z (8 << 64)%uint63)%Z.

Definition lsl_primitive1 := (6917529027641081856 ?= to_Z (3 << 61)%uint63)%Z.

Definition lsl_primitive2 := (0 ?= to_Z (2 << 62)%uint63)%Z.

Definition lsl_primitive3 := (0 ?= to_Z (9223372036854775807 << 64)%uint63)%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsl_primitive" lsl_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsl_primitive_overflow" lsl_primitive_overflow.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsl_primitive1" lsl_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsl_primitive2" lsl_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsl_primitive3" lsl_primitive3.

Definition lsr_primitive := (Z.shiftr 256 8 =? Uint63.to_Z (256 >> 8)%uint63)%Z.

Definition lsr_primitive1 := (6917529027641081856 >> 61 =? 3)%uint63.

Definition lsr_primitive2 := (2305843009213693952 >> 62 =? 0)%uint63.

Definition lsr_primitive3 := (9223372036854775807 >> 64 =? 0)%uint63.


CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsr_primitive" lsr_primitive.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsr_primitive" lsr_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsr_primitive" lsr_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.lsr_primitive" lsr_primitive3.

Definition eqb_true_primitive := (42 =? 42)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.eqb_true_primitive" eqb_true_primitive.

Definition eqb_false_primitive := negb (41 =? 42)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.eqb_false_primitive" eqb_false_primitive.

Definition ltb_true_primitive := (41 <? 42)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.ltb_true_primitive" ltb_true_primitive.

Definition ltb_false_primitive := negb (42 <? 42)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.ltb_false_primitive" ltb_false_primitive.

Definition ltb_primitive1 := negb (1 <? 1)%uint63.

Definition ltb_primitive2 := (1 <? 2)%uint63.

Definition ltb_primitive3 := negb (9223372036854775807 <? 0)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.ltb_primitive1" ltb_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.ltb_primitive2" ltb_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.ltb_primitive3" ltb_primitive3.

Definition leb_true_primitive := (42 <=? 42)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.leb_true_primitive" leb_true_primitive.

Definition leb_false_primitive := negb (43 <=? 42)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.leb_false_primitive" leb_false_primitive.

Definition leb_primitive1 := (1 <=? 1)%uint63.

Definition leb_primitive2 := (1 <=? 2)%uint63.

Definition leb_primitive3 := negb (9223372036854775807 <=? 0)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.leb_primitive1" leb_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.leb_primitive2" leb_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.leb_primitive3" leb_primitive3.

Definition compare_eq_primitive := match (Uint63.compare 42 42)%uint63 with Eq => true | _ => false end.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.compare_eq_primitive" compare_eq_primitive.

Definition compare_lt_primitive := match (Uint63.compare 1 3)%uint63 with Lt => true | _ => false end.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.compare_lt_primitive" compare_lt_primitive.

Definition compare_gt_primitive := 
  match (Uint63.compare 3 1)%uint63 with Gt => true | _ => false end.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.compare_gt_primitive" compare_gt_primitive.

Definition head0_primitive1 := (61 =? to_Z (head0 3))%Z.

Definition head0_primitive2 := (0 =? to_Z (head0 4611686018427387904))%Z.

Definition head0_primitive3 := (63 =? to_Z (head0 0))%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.head0_primitive1" head0_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.head0_primitive2" head0_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.head0_primitive3" head0_primitive3.

Definition tail0_primitive1 := (61 =? to_Z (tail0 2305843009213693952))%Z.

Definition tail0_primitive2 := (0 =? to_Z (tail0 1))%Z.

Definition tail0_primitive3 := (63 =? to_Z (tail0 0))%Z.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.tail0_primitive1" tail0_primitive1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.tail0_primitive2" tail0_primitive2.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.tail0_primitive3" tail0_primitive3.

Definition unsigned_test1 := (1 / (0-1) =? 0)%uint63.

Definition unsigned_test2 := (3 mod (0-1) =? 3)%uint63.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.unsigned_test1" unsigned_test1.

CertiCoq Compile Wasm -file "CertiCoq.Benchmarks.tests.unsigned_test2" unsigned_test2.
