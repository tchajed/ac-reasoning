Require Import AssociativeCommutative.

Set Implicit Arguments.

Require Import Arith.
Require Import Permutation.
Require Import List.
Import ListNotations.
Open Scope list.

Instance nat_plus_AC : AssociativeCommutative nat plus eq.
Proof.
  constructor; hnf; intros.
  - rewrite Nat.add_assoc; auto.
  - apply Nat.add_comm.
  - constructor; hnf; intros; congruence.
  - exact 0.
  - congruence.
Qed.

Instance list_AC A : AssociativeCommutative (list A) (app (A:=A)) (Permutation (A:=A)).
Proof.
  constructor; hnf.
  - intros.
    rewrite app_assoc; auto.
  - intros.
    apply Permutation_app_comm.
  - constructor; hnf; intros; eauto.
    apply Permutation_sym; auto.
    econstructor; eauto.
  - exact nil.
  - intros.
    eapply Permutation_app; eauto.
Qed.

Theorem nat_rewrite : forall (x y z w: nat),
    x + y + x + z + y + w =
    x + x + y + z + y + w.
Proof.
  intros.
  match goal with
  | [ |- ?t = ?t' ] =>
    quote t; requote t'
  end.
  ac_simplify.
  reflexivity.
Qed.

Theorem list_rewrite : forall A (x y z w: list A),
    Permutation (x ++ y ++ x ++ z ++ y ++ w)
                (x ++ x ++ y ++ z ++ y ++ w).
Proof.
  intros.
  match goal with
  | [ |- Permutation ?t ?t' ] =>
    quote t; requote t'
  end.
  ac_simplify.
  match goal with
  (* note that ac_simplify reduces to a left associative tree of operations,
    whereas [++] is parsed as right associative. *)
  | [ |- Permutation (((((x ++ x) ++ y) ++ y) ++ z) ++ w)
                    (((((x ++ x) ++ y) ++ y) ++ z) ++ w) ] =>
    reflexivity
  end.
Qed.
