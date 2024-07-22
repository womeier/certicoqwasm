From Coq Require Import ZArith BinNat.
From Wasm Require Import datatypes operations.

(* Common global variables *)
Definition global_mem_ptr    : globalidx := 0%N. (* ptr to next free memory, increased after allocation, there is no GC *)
Definition constr_alloc_ptr  : globalidx := 1%N. (* ptr to beginning of constr alloc in linear mem *)
Definition result_var        : globalidx := 2%N. (* final result *)
Definition result_out_of_mem : globalidx := 3%N. (* ran out of memory *)

(* Global variables used to hold temporary variables for primitive operations *)
Definition glob_tmp1         : globalidx := 4%N.
Definition glob_tmp2         : globalidx := 5%N.
Definition glob_tmp3         : globalidx := 6%N.
Definition glob_tmp4         : globalidx := 7%N.

Definition nat_to_i32 (n : nat) :=
  Wasm_int.Int32.repr (BinInt.Z.of_nat n).

Definition nat_to_i64 (n : nat) :=
  Wasm_int.Int64.repr (BinInt.Z.of_nat n).

Definition nat_to_value (n : nat) :=
  VAL_int32 (nat_to_i32 n).

Definition nat_to_value64 (n : nat) :=
  VAL_int64 (nat_to_i64 n).
