Set Warnings "-primitive-turned-into-axiom".
From CertiCoq.Plugin Require Import CertiCoq.

From Coq Require Import List Uint63 ZArith.

Import ListNotations.

Open Scope uint63_scope.

Definition mulc1 := mulc 5357761869 5357761869.

CertiCoq Compile Wasm -file "compute.mulc1" mulc1.

Definition mulc2 := mulc 4119217344 4119217344.

CertiCoq Compile Wasm -file "compute.mulc2" mulc2.

Definition mulc3 := mulc 3233547968 3233547968.

Compute mulc3.

CertiCoq Compile Wasm -file "compute.mulc3" mulc3.

Definition mulc4 := mulc 3707969149 3707969149.

CertiCoq Compile Wasm -file "compute.mulc4" mulc4.

Definition mulc5 := mulc 3588435989 3588435989.

CertiCoq Compile Wasm -file "compute.mulc5" mulc5.

Definition mulc6 := mulc 3833655472 3833655472.

CertiCoq Compile Wasm -file "compute.mulc6" mulc6.

Definition mulc7 := mulc 2530677307 2530677307.

CertiCoq Compile Wasm -file "compute.mulc7" mulc7.

Definition mulc8 := mulc 3817394099 3817394099.

CertiCoq Compile Wasm -file "compute.mulc8" mulc8.

Definition mulc9 := mulc 3692918037 3692918037.

CertiCoq Compile Wasm -file "compute.mulc9" mulc9.

Definition mulc10 := mulc 3244824223 3244824223.

CertiCoq Compile Wasm -file "compute.mulc10" mulc10.

Definition mulc11 := mulc 5270842249 5270842249.

CertiCoq Compile Wasm -file "compute.mulc11" mulc11.

Definition mulc12 := mulc 4201676260 2250457835.

CertiCoq Compile Wasm -file "compute.mulc12" mulc12.

Definition mulc13 := mulc 2250457836 2250457836.

CertiCoq Compile Wasm -file "compute.mulc13" mulc13.

                         

(* Unit tests taken from https://github.com/coq/coq/tree/master/test-suite/primitive/uint63 *)

Definition add1 := 2 + 3. (* = 5 *)

CertiCoq Compile Wasm add1.

Definition add2 := 9223372036854775807 + 1. (* = 0 *)

CertiCoq Compile Wasm add2.

Definition addc1 := 2 +c 3 (* = C0 5 *).

CertiCoq Compile Wasm addc1.

Definition addc2 := 9223372036854775807 +c 2. (* = C1 1 *)

CertiCoq Compile Wasm addc2.

Definition addcarryc1 := addcarryc 2 3. (* = C0 6 *)

CertiCoq Compile Wasm addcarryc1.

Definition addcarryc2 := addcarryc 9223372036854775807 2. (* = C1 2 *)

CertiCoq Compile Wasm addcarryc2.

Definition sub1 := 3 - 2. (* = 1 *)

CertiCoq Compile Wasm sub1.

Definition sub2 := 0 - 1. (* = 9223372036854775807 *)

CertiCoq Compile Wasm sub2.

Definition subc1 := 3 -c 2. (* = C0 1 *)

CertiCoq Compile Wasm subc1.

Definition subc2 := 0 -c 1. (* = C1 9223372036854775807 *)

CertiCoq Compile Wasm subc2.

Definition subcarryc1 := subcarryc 3 1. (* = C0 1 *)

CertiCoq Compile Wasm subcarryc1.

Definition subcarryc2 := subcarryc 0 1. (* = C1 9223372036854775806 *)

CertiCoq Compile Wasm subcarryc2.

Definition mul1 := 2 * 3. (* = 6 *)

CertiCoq Compile Wasm mul1.

Definition mul2 := 9223372036854775807 * 2. (* = 9223372036854775806 *)

CertiCoq Compile Wasm mul2.

Definition mulc1 := mulc 2 3. (* = WW 0 6. *)

CertiCoq Compile Wasm mulc1.

Definition mulc2 := mulc 9223372036854775807 2. (* = WW 1 9223372036854775806 *)

CertiCoq Compile Wasm mulc2.

Definition mulc3 := mulc 0 0. (* = W0. *)

CertiCoq Compile Wasm mulc3.

Definition div1 := 6 / 3. (* = 2 *)

CertiCoq Compile Wasm div1.

Definition div2 := 3 / 2. (* = 1 *)

CertiCoq Compile Wasm div2.

Definition mod1 := 6 mod 3. (* = 0 *)

CertiCoq Compile Wasm mod1.

Definition mod2 := 5 mod 3. (* = 2 *)

CertiCoq Compile Wasm mod2.

Definition land1 := 0 land 0. (* = 0 *)

CertiCoq Compile Wasm land1.

Definition land2 := 9223372036854775807 land 0. (* = 0 *)

CertiCoq Compile Wasm land2.

Definition land3 := 0 land 9223372036854775807. (* = 0 *)

CertiCoq Compile Wasm land3.

Definition land4 := 9223372036854775807 land 9223372036854775807. (* = 9223372036854775807 *)

CertiCoq Compile Wasm land4.

Definition lor1 := 0 lor 0. (* = 0 *)

CertiCoq Compile Wasm lor1.

Definition lor2 := 9223372036854775807 lor 0. (* = 9223372036854775807 *)

CertiCoq Compile Wasm lor2.

Definition lor3 := 0 lor 9223372036854775807. (* = 9223372036854775807 *)

CertiCoq Compile Wasm lor3.

Definition lor4 := 9223372036854775807 lor 9223372036854775807. (* = 9223372036854775807 *)

CertiCoq Compile Wasm lor4.

Definition lxor1 := 0 lxor 0. (* = 0 *)

CertiCoq Compile Wasm lxor1.

Definition lxor2 := 9223372036854775807 lxor 0. (* = 9223372036854775807 *)

CertiCoq Compile Wasm lxor2.

Definition lxor3 :=  0 lxor 9223372036854775807. (* = 9223372036854775807 *)

CertiCoq Compile Wasm lxor3.

Definition lxor4 := 9223372036854775807 lxor 9223372036854775807. (* = 0 *)

CertiCoq Compile Wasm lxor4.

Definition lsl1 := 3 << 61. (* = 6917529027641081856 *)

CertiCoq Compile Wasm lsl1.

Definition lsl2 := 2 << 62. (* = 0 *)

CertiCoq Compile Wasm lsl2.

Definition lsl3 := 9223372036854775807 << 64. (* = 0 *)

CertiCoq Compile Wasm lsl3.

Definition lsr1 := 6917529027641081856 >> 61. (* = 3 *)

CertiCoq Compile Wasm lsr1.

Definition lsr2 := 2305843009213693952 >> 62. (* = 0 *)

CertiCoq Compile Wasm lsr2.

Definition lsr3 := 9223372036854775807 >> 64. (* = 0 *)

CertiCoq Compile Wasm lsr3.

Definition compare1 := 1 ?= 1. (* = Eq *)

CertiCoq Compile Wasm compare1.

Definition compare2 := 1 ?= 2. (* = Lt *)

CertiCoq Compile Wasm compare2.

Definition compare3 := 9223372036854775807 ?= 0. (* = Gt *)

CertiCoq Compile Wasm compare3.

Definition eqb1 := 1 =? 1. (* = true *)

CertiCoq Compile Wasm eqb1.

Definition eqb2 := 9223372036854775807 =? 0. (* = false *)

CertiCoq Compile Wasm eqb2.

Definition ltb1 := 1 <? 1. (* = false *)

CertiCoq Compile Wasm ltb1.

Definition ltb2 := 1 <? 2. (* = true *)

CertiCoq Compile Wasm ltb2.

Definition ltb3 := 9223372036854775807 <? 0. (* = false *)

CertiCoq Compile Wasm ltb3.

Definition leb1 := 1 <=? 1. (* = true *)

CertiCoq Compile Wasm leb1.

Definition leb2 := 1 <=? 2. (* = true *)

CertiCoq Compile Wasm leb2.

Definition leb3 := 9223372036854775807 <=? 0. (* = false *)

CertiCoq Compile Wasm leb3.

Definition head0_1 := head0 3. (* = 61 *)

CertiCoq Compile Wasm head0_1.

Definition head0_2 := head0 4611686018427387904. (* = 0 *)

CertiCoq Compile Wasm head0_2.

Definition head0_3 := head0 0. (* = 63 *)

CertiCoq Compile Wasm head0_3.

Definition tail0_1 := tail0 2305843009213693952. (* = 61 *)

CertiCoq Compile Wasm tail0_1.

Definition tail0_2 := tail0 1. (* = 0 *)

CertiCoq Compile Wasm tail0_2.

Definition tail0_3 := tail0 0. (* = 63 *)

CertiCoq Compile Wasm tail0_3.

Definition diveucl1 := diveucl 6 3. (* = (2,0) *)

CertiCoq Compile Wasm diveucl1.

Definition diveucl2 := diveucl 5 3. (* = (1,2) *)

CertiCoq Compile Wasm diveucl2.

Definition diveucl_21_1 := diveucl_21 1 1 2. (* = (4611686018427387904,1) *)

CertiCoq Compile Wasm diveucl_21_1.

Definition diveucl_21_2 := diveucl_21 3 1 2. (* = (0, 0) *)

CertiCoq Compile Wasm diveucl_21_2.

Definition diveucl_21_3 := diveucl_21 1 1 0. (* = (0,0) *)

CertiCoq Compile Wasm diveucl_21_3.

Definition diveucl_21_4 := diveucl_21 9223372036854775807 0 1. (* = (0,0) *)

CertiCoq Compile Wasm diveucl_21_4.

Definition diveucl_21_5 := diveucl_21 9305446873517 1793572051078448654 4930380657631323783. (* = (17407905077428, 3068214991893055266) *)

CertiCoq Compile Wasm diveucl_21_5.

Definition unsigned1 := 1/(0-1). (* = 0 *)

CertiCoq Compile Wasm unsigned1.

Definition unsigned2 := 3 mod (0-1). (* = 3 *)

CertiCoq Compile Wasm unsigned2.
