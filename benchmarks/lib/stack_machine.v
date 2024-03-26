Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Import ListNotations.

Inductive id : Type :=
| Id: string -> id.

Definition beq_id (a b: id) : bool :=
  match a, b with
  | Id a', Id b' => if string_dec a' b' then true else false
  end.

Definition total_map (A: Type) := id -> A.

Definition t_empty {A: Type} (v: A) : total_map A :=
  fun (_ : id) => v.

Definition t_update {A: Type} (m: total_map A) (k: id) (v: A) : total_map A :=
  fun (x : id) => if beq_id k x then v else m x.

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum x => [SPush x]
  | AId k => [SLoad k]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Definition aexp1 : aexp :=
  AMult (ANum 100) (ANum 100).

Definition aexp_list_sum : aexp :=
  List.fold_left (fun a n => APlus a (ANum n)) (List.repeat 1 1000) (ANum 0).

Definition prog1 :=
  s_compile aexp_list_sum.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
  | [] => stack
  | (SPush n) :: prog' => s_execute st (n :: stack) prog'
  | (SLoad k) :: prog' => s_execute st ((st k) :: stack) prog'
  | SPlus :: prog' => s_execute st (((hd 0 (tl stack)) + (hd 0 stack)) :: (tl (tl stack)))
                                prog'
  | SMinus :: prog' => s_execute st (((hd 0 (tl stack)) - (hd 0 stack)) :: (tl (tl stack)))
                                prog'
  | SMult :: prog' => s_execute st (((hd 0 (tl stack)) * (hd 0 stack)) :: (tl (tl stack)))
                                prog'
  end.

Definition exec1 :=
  s_execute empty_state [] prog1.

Lemma s_execute_app: forall st stack si1 si2,
  s_execute st stack (si1 ++ si2) =
  s_execute st (s_execute st stack si1) si2.
Proof.
  intros.
  generalize dependent st.
  generalize dependent stack.
  generalize dependent si2.
  induction si1; intros.
  - reflexivity.
  - destruct a; simpl; apply IHsi1.
Qed.

Lemma s_compile_append: forall st stack e,
  s_execute st stack (s_compile e) =
  (aeval st e) :: stack.
Proof.
  intros.
  generalize dependent st.
  generalize dependent stack.
  induction e; simpl; intros;
    try reflexivity;
    repeat rewrite s_execute_app;
    rewrite IHe1; rewrite IHe2;
    reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  apply s_compile_append.
Qed.
