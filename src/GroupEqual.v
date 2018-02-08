Require Import Permutation.
Require Import Recdef FunInd.
Require Import Omega.

Require List.
Import List.ListNotations.
Open Scope list.

Set Implicit Arguments.

Section GroupEqual.

  Variable A:Type.
  Variable equal:A -> A -> bool.

  Fixpoint gather_eq (x0: A) (acc: list A) (l: list A) : list A * list A :=
    match l with
    | [] => (acc, l)
    | x::xs => if equal x x0 then
                gather_eq x0 (acc ++ [x]) xs
              else
                let (xs, l') := gather_eq x0 acc xs in
                (xs, x::l')
    end.

  Definition gather_eq1 (x:A) l : list A :=
    fst (gather_eq x [] l).

  Definition gather_eq2 (x:A) l : list A :=
    snd (gather_eq x [] l).

  Theorem gather_eq_lengths : forall x l acc xs l',
      gather_eq x acc l = (xs, l') ->
      length xs + length l' = length acc + length l.
  Proof.
    induction l; simpl; intros; auto.
    inversion H; subst; auto.
    destruct (equal a x); simpl.
    apply IHl in H; simpl in *.
    rewrite List.app_length in *; simpl in *.
    omega.
    destruct_with_eqn (gather_eq x acc l); simpl in *.
    inversion H; subst; clear H; simpl.
    apply IHl in Heqp.
    omega.
  Qed.

  Lemma gather_eq12_lengths : forall (x:A) l,
      length (gather_eq1 x l) + length (gather_eq2 x l) = length l.
  Proof.
    unfold gather_eq1, gather_eq2; intros.
    destruct_with_eqn (gather_eq x [] l).
    apply gather_eq_lengths in Heqp; simpl in *; auto.
  Qed.

  Lemma gather_eq2_smaller : forall (x:A) xs,
      length (gather_eq2 x xs) < S (length xs).
  Proof.
    intros.
    pose proof (gather_eq12_lengths x xs).
    omega.
  Qed.

  Hint Resolve gather_eq2_smaller.

  Function group_eq (l: list A) {measure length l} : list A :=
    match l with
    | [] => []
    | x::xs => x::gather_eq1 x xs ++ group_eq (gather_eq2 x xs)
    end.
  Proof.
    simpl; intros; subst; auto.
  Qed.

  Theorem group_eq_length : forall (l: list A),
      length (group_eq l) = length l.
  Proof.
    intros.
    remember (length l).
    generalize dependent l.
    induction n using lt_wf_ind; intros; subst.
    rewrite group_eq_equation.
    destruct l; intros; subst; simpl in *; auto.
    rewrite List.app_length.
    erewrite H; try reflexivity.
    rewrite gather_eq12_lengths; auto.
    auto.
  Qed.

  Hint Constructors Permutation.
  Hint Resolve Permutation_sym.
  Hint Resolve Permutation_middle.

  Theorem gather_eq_permutation : forall (x:A) l acc xs l',
      gather_eq x acc l = (xs, l') ->
      Permutation (xs ++ l') (acc ++ l).
  Proof.
    induction l; simpl; intros.
    inversion H; subst; clear H; simpl.
    rewrite List.app_nil_r; auto.
    destruct (equal a x).
    apply IHl in H.
    rewrite <- List.app_assoc in H; auto.
    destruct_with_eqn (gather_eq x acc l).
    inversion H; subst; clear H.
    apply IHl in Heqp.
    eauto.
  Qed.

  Theorem gather_eq12_permutation : forall (x:A) l,
      Permutation (gather_eq1 x l ++ gather_eq2 x l) l.
  Proof.
    unfold gather_eq1, gather_eq2; intros.
    destruct_with_eqn (gather_eq x [] l); simpl.
    apply gather_eq_permutation in Heqp; auto.
  Qed.

  Theorem group_eq_permutation : forall (l: list A),
      Permutation (group_eq l) l.
  Proof.
    intros.
    remember (length l).
    generalize dependent l.
    induction n using lt_wf_ind; intros; subst.
    rewrite group_eq_equation.
    destruct l.
    auto.
    constructor.
    transitivity (gather_eq1 a l ++ gather_eq2 a l);
      [ | eauto using gather_eq12_permutation ].
    eapply Permutation_app; eauto.
    eapply H; simpl; eauto.
  Qed.

End GroupEqual.

Ltac compute_group_eq :=
  rewrite group_eq_equation; unfold gather_eq1, gather_eq2, gather_eq;
  cbn [fst snd].

Module Examples.

  Example gather_eq_ex1 :
    gather_eq (fun x y => if PeanoNat.Nat.eq_dec x y then true else false)
              3 [] [2;3;4;3;2;3;5] =
    ([3;3;3], [2;4;2;5]) := eq_refl.

  Example group_eq_ex1 :
    group_eq (fun x y => if Nat.eq_dec x y then true else false)
             [2;3;4;3;2;3;5] = [2;2;3;3;3;4;5].
  Proof.
    repeat (compute_group_eq; cbn [Nat.eq_dec app nat_rec nat_rect]).
    reflexivity.
  Qed.

End Examples.
