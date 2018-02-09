Require Export RelationClasses.
Require Import Permutation.

Instance eq_Equivalence A : Equivalence (eq (A:=A)).
Proof.
  constructor; hnf; intros; congruence.
Qed.

Instance Permutation_Equivalence A : Equivalence (Permutation (A:=A)).
Proof.
  constructor; hnf; intros.
  apply Permutation_refl.
  apply Permutation_sym; auto.
  eapply Permutation_trans; eauto.
Qed.

Instance iff_Equivalence : Equivalence iff.
Proof.
  constructor; hnf; intuition auto.
Qed.
