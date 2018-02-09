Require Import AssociativeCommutative.

Set Implicit Arguments.

Require Import Arith.
Require Import Permutation.
Require Import List.
Import ListNotations.
Open Scope list.

Require Import Equivalences.

Instance nat_plus_AC : AssociativeCommutative nat plus eq.
Proof.
  ac_instance.
  - rewrite Nat.add_assoc; auto.
  - apply Nat.add_comm.
Qed.

Instance list_AC A : AssociativeCommutative (list A) (app (A:=A)) (Permutation (A:=A)).
Proof.
  ac_instance.
  - rewrite app_assoc; auto.
  - apply Permutation_app_comm.
  - eapply Permutation_app; eauto.
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

(** TODO: multiple AC instances for different operations confuse the rewrite;
    should be more careful about instantiating the typeclasses once and for all *)
Instance nat_mult_AC : AssociativeCommutative nat mult eq.
Proof.
  ac_instance.
  - rewrite Nat.mul_assoc; auto.
  - rewrite Nat.mul_comm; auto.
Qed.

Instance prop_and_AC : AssociativeCommutative Prop and iff.
Proof.
  ac_instance; intuition auto.
  exact True.
Qed.

Instance prop_or_AC : AssociativeCommutative Prop or iff.
Proof.
  ac_instance; intuition auto.
  exact False.
Qed.
