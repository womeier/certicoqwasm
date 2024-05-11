
From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Definition check_cert := test_Certif.

Lemma prime_13 : prime 13.
Proof.
 apply (Pocklington_refl
         (Pock_certif 13 2 ((2,2)::nil) 1)
        ((Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.


Definition cert_13 :=
  (Pock_certif 13 2 ((2,2)::nil) 1) ::
    (Proof_certif 2 prime2) ::
       nil.

Definition check_13 := check_cert cert_13.

Eval compute in check_13.

Compute check_13.

Lemma prime_5883627479 : prime 5883627479.
Proof.
 apply (Pocklington_refl
         (Pock_certif 5883627479 7 ((43, 1)::(17, 1)::(2,1)::nil) 939)
        ((Proof_certif 43 prime43) ::
         (Proof_certif 17 prime17) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

Definition cert_5883627479 :=
           (Pock_certif 5883627479 7 ((43, 1)::(17, 1)::(2,1)::nil) 939) ::
        (Proof_certif 43 prime43) ::
         (Proof_certif 17 prime17) ::
         (Proof_certif 2 prime2) ::
         nil.

Definition check_5883627479 := check_cert cert_5883627479.

Eval native_compute in check_5883627479.

Compute check_5883627479.

Lemma prime_2596681421 : prime 2596681421.
Proof.
 apply (Pocklington_refl
         (Pock_certif 2596681421 2 ((3019397, 1)::(2,2)::nil) 1)
        ((Pock_certif 3019397 2 ((151, 1)::(2,2)::nil) 166) ::
         (Proof_certif 151 prime151) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

Definition cert_2596681421 :=
         (Pock_certif 2596681421 2 ((3019397, 1)::(2,2)::nil) 1) :: 
        (Pock_certif 3019397 2 ((151, 1)::(2,2)::nil) 166) ::
         (Proof_certif 151 prime151) ::
         (Proof_certif 2 prime2) ::
         nil.

Definition check_2596681421 := check_cert cert_2596681421.

Eval vm_compute in check_2596681421.
Compute check_2596681421.

Lemma prime_3521471777 : prime 3521471777.
Proof.
 apply (Pocklington_refl
         (Pock_certif 3521471777 3 ((7879, 1)::(2,5)::nil) 1)
        ((Proof_certif 7879 prime7879) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

Definition cert_3521471777 :=
  (Pock_certif 3521471777 3 ((7879, 1)::(2,5)::nil) 1) ::
        (Proof_certif 7879 prime7879) ::
         (Proof_certif 2 prime2) ::
          nil.

Definition check_352147177 := check_cert cert_3521471777.

Eval compute in check_352147177.

Compute check_352147177.

Lemma prime_7890427667 : prime 7890427667.
Proof.
 apply (Pocklington_refl
         (Pock_certif 7890427667 2 ((32605073, 1)::(2,1)::nil) 1)
        ((Pock_certif 32605073 3 ((853, 1)::(2,4)::nil) 1) ::
         (Proof_certif 853 prime853) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

Definition cert_7890427667 :=
         (Pock_certif 7890427667 2 ((32605073, 1)::(2,1)::nil) 1) ::
        (Pock_certif 32605073 3 ((853, 1)::(2,4)::nil) 1) ::
         (Proof_certif 853 prime853) ::
         (Proof_certif 2 prime2) ::
         nil.

Definition check_7890427667 := check_cert cert_7890427667.

Eval compute in check_7890427667.

Compute check_7890427667.

Lemma prime_9359893831 : prime 9359893831.
Proof.
 apply (Pocklington_refl
         (Pock_certif 9359893831 3 ((17, 1)::(7, 1)::(5, 1)::(3, 1)::(2,1)::nil) 1437)
        ((Proof_certif 17 prime17) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

Definition cert_9359893831 :=
         (Pock_certif 9359893831 3 ((17, 1)::(7, 1)::(5, 1)::(3, 1)::(2,1)::nil) 1437) ::
        (Proof_certif 17 prime17) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 5 prime5) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil.

Definition check_9359893831 := check_cert cert_9359893831.

Eval compute in check_9359893831.

Compute check_9359893831.

Lemma prime_9822974443 : prime 9822974443.
Proof.
 apply (Pocklington_refl
         (Pock_certif 9822974443 2 ((3083, 1)::(2,1)::nil) 2258)
        ((Proof_certif 3083 prime3083) ::
         (Proof_certif 2 prime2) ::
          nil)).
 native_cast_no_check (refl_equal true).
Qed.

Definition cert_9822974443 :=
           (Pock_certif 9822974443 2 ((3083, 1)::(2,1)::nil) 2258) ::
        (Proof_certif 3083 prime3083) ::
         (Proof_certif 2 prime2) ::
          nil.

Definition check_9822974443 := check_cert cert_9822974443.

Eval compute in check_9822974443.

Compute check_9822974443.

(* From CertiCoq.Plugin Require Import CertiCoq. *)

(* CertiCoq Compile -debug -file "CertiCoq.Benchmarks.tests.prime13" check_13. *)

(* CertiCoq Compile Wasm -debug -file "CertiCoq.Benchmarks.tests.prime13" check_13. *)

(* CertiCoq Compile -debug -file "CertiCoq.Benchmarks.tests.prime5883627479" check_5883627479. *)

(* CertiCoq Compile Wasm -debug -file "CertiCoq.Benchmarks.tests.prime5883627479" check_5883627479. *)

(* CertiCoq Compile -debug -file "CertiCoq.Benchmarks.tests.prime2596681421" check_2596681421. *)

(* CertiCoq Compile Wasm -debug -file "CertiCoq.Benchmarks.tests.prime2596681421" check_2596681421. *)

(* CertiCoq Compile -debug -file "CertiCoq.Benchmarks.tests.prime3521471777" check_3521471777. *)

(* CertiCoq Compile Wasm -debug -file "CertiCoq.Benchmarks.tests.prime3521471777" check_3521471777. *)

(* CertiCoq Compile -debug -file "CertiCoq.Benchmarks.tests.prime7890427667" check_7890427667. *)

(* CertiCoq Compile Wasm -debug -file "CertiCoq.Benchmarks.tests.prime7890427667" check_7890427667. *)

(* CertiCoq Compile -debug -file "CertiCoq.Benchmarks.tests.prime9359893831" check_9359893831. *)

(* CertiCoq Compile Wasm -debug -file "CertiCoq.Benchmarks.tests.prime9359893831" check_9359893831. *)

(* CertiCoq Compile -debug -file "CertiCoq.Benchmarks.tests.prime9822974443" check_9822974443. *)

(* CertiCoq Compile Wasm -debug -file "CertiCoq.Benchmarks.tests.prime9822974443" check_9822974443. *)
