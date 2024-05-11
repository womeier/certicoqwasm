From CertiCoq.Plugin Require Import CertiCoq.
Require Import primes.

CertiCoq Compile Wasm -debug -file "CertiCoq.Benchmarks.tests.prime5883627479" check_5883627479.
