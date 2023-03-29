From MetaCoq.Template Require Import bytestring MCString.
Require Import OrderedTypeAlt.

Module StringComp.
  (* inspired by metacoq/theories/Kernames.v , metacoq/theories/utils/bytestring.v *)
  Definition t := string.

  Definition eq := @eq string.
  Lemma eq_equiv : RelationClasses.Equivalence eq.
  Proof. apply _. Qed.

  Definition compare s1 s2 :=
       StringOT.compare s1 s2.

  Lemma compare_sym : forall x y, (compare y x) = CompOpp (compare x y).
  Proof.
    intros. apply StringOT.compare_sym.
  Defined.

  Lemma compare_trans :
    forall c x y z, (compare x y) = c -> (compare y z) = c -> (compare x z) = c.
  Proof.
    intros. eapply StringOT.compare_trans in H0; eauto.
  Qed.

End StringComp.

Module MyStringOT := OrderedType_from_Alt StringComp.
