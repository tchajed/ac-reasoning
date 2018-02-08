Set Implicit Arguments.

Require Import Quote.
Require Import Permutation.
Require Import Recdef FunInd.
Require Import Omega.
Require List.
Import List.ListNotations.
Open Scope list.

Definition nat_eq_dec : forall (x y:nat), {x=y}+{x<>y}.
Proof.
  decide equality.
Defined.

Section GroupEqual.

  Fixpoint gather_eq A (equal: A -> A -> bool) (x0: A) (acc: list A) (l: list A) : list A * list A :=
    match l with
    | [] => (acc, l)
    | x::xs => if equal x x0 then
                gather_eq equal x0 (acc ++ [x]) xs
              else
                let (xs, l') := gather_eq equal x0 acc xs in
                (xs, x::l')
    end.

  Example gather_eq_ex1 :
    gather_eq (fun x y => if PeanoNat.Nat.eq_dec x y then true else false)
              3 [] [2;3;4;3;2;3;5] =
    ([3;3;3], [2;4;2;5]) := eq_refl.

  Definition gather_eq1 A equal (x:A) l : list A :=
    fst (gather_eq equal x [] l).

  Definition gather_eq2 A equal (x:A) l : list A :=
    snd (gather_eq equal x [] l).

  Theorem gather_eq_lengths : forall A (equal: A -> A -> bool) x l acc xs l',
      gather_eq equal x acc l = (xs, l') ->
      length xs + length l' = length acc + length l.
  Proof.
    induction l; simpl; intros; auto.
    inversion H; subst; auto.
    destruct (equal a x); simpl.
    apply IHl in H; simpl in *.
    rewrite List.app_length in *; simpl in *.
    omega.
    destruct_with_eqn (gather_eq equal x acc l); simpl in *.
    inversion H; subst; clear H; simpl.
    apply IHl in Heqp.
    omega.
  Qed.

  Lemma gather_eq12_lengths : forall A equal (x:A) l,
      length (gather_eq1 equal x l) + length (gather_eq2 equal x l) = length l.
  Proof.
    unfold gather_eq1, gather_eq2; intros.
    destruct_with_eqn (gather_eq equal x [] l).
    apply gather_eq_lengths in Heqp; simpl in *; auto.
  Qed.

  Lemma gather_eq2_smaller : forall A equal (x:A) xs,
      length (gather_eq2 equal x xs) < S (length xs).
  Proof.
    intros.
    pose proof (gather_eq12_lengths equal x xs).
    omega.
  Qed.

  Hint Resolve gather_eq2_smaller.

  Function group_eq A (equal: A -> A -> bool) (l: list A) {measure length l} : list A :=
    match l with
    | [] => []
    | x::xs => x::gather_eq1 equal x xs ++ group_eq equal (gather_eq2 equal x xs)
    end.
  Proof.
    simpl; intros; subst; auto.
  Qed.

  Theorem group_eq_length : forall A equal (l: list A),
      length (group_eq equal l) = length l.
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

  Theorem gather_eq_permutation : forall A equal (x:A) l acc xs l',
      gather_eq equal x acc l = (xs, l') ->
      Permutation (xs ++ l') (acc ++ l).
  Proof.
    induction l; simpl; intros.
    inversion H; subst; clear H; simpl.
    rewrite List.app_nil_r; auto.
    destruct (equal a x).
    apply IHl in H.
    rewrite <- List.app_assoc in H; auto.
    destruct_with_eqn (gather_eq equal x acc l).
    inversion H; subst; clear H.
    apply IHl in Heqp.
    eauto.
  Qed.

  Theorem gather_eq12_permutation : forall A equal (x:A) l,
      Permutation (gather_eq1 equal x l ++ gather_eq2 equal x l) l.
  Proof.
    unfold gather_eq1, gather_eq2; intros.
    destruct_with_eqn (gather_eq equal x [] l); simpl.
    apply gather_eq_permutation in Heqp; auto.
  Qed.

  Theorem group_eq_permutation : forall A equal (l: list A),
      Permutation (group_eq equal l) l.
  Proof.
    intros.
    remember (length l).
    generalize dependent l.
    induction n using lt_wf_ind; intros; subst.
    rewrite group_eq_equation.
    destruct l.
    auto.
    constructor.
    transitivity (gather_eq1 equal a l ++ gather_eq2 equal a l);
      [ | eauto using gather_eq12_permutation ].
    eapply Permutation_app; eauto.
    eapply H; simpl; eauto.
  Qed.

End GroupEqual.

Class assoc_comm A (op: A -> A -> A) :=
  { associative : forall x y z, op (op x y) z = op x (op y z);
    commutative : forall x y, op x y = op y x; }.

Class monoid A (op: A -> A -> A) :=
  { unit: A;
    left_id : forall x, op unit x = x; }.

Section AssociativeCommutativeReasoning.

  Variable A:Type.
  Variable op: A -> A -> A.
  Infix "∘" := op (at level 40, left associativity).

  Hypothesis op_ac : assoc_comm op.
  Existing Instance op_ac.

  Hypothesis op_monoid : monoid op.
  Existing Instance op_monoid.

  Lemma right_id : forall x, x ∘ unit = x.
  Proof.
    intros.
    rewrite commutative.
    apply left_id.
  Qed.

  Fixpoint op_foldl (acc:A) (l: list A) :=
    match l with
    | [] => acc
    | x::xs => op_foldl (op acc x) xs
    end.

  Inductive binop_tree :=
  | Leaf (x:A)
  | Atom (i:index)
  | Node (l:binop_tree) (r:binop_tree).

  Fixpoint op_tree (vm: varmap A) (t:binop_tree) :=
    match t with
    | Leaf x => x
    | Atom i => varmap_find unit i vm
    | Node l r => op_tree vm l ∘ op_tree vm r
    end.

  Ltac quote_tree t :=
    quote op_tree in t using (fun t' => change t with t').

  Lemma op_foldl_acc:
    forall (l: list A) (acc1 : A) (acc2: A),
      op_foldl (acc1 ∘ acc2) l = acc1 ∘ op_foldl acc2 l.
  Proof.
    induction l; simpl; intros; auto.
    rewrite associative.
    auto.
  Qed.

  Lemma op_foldl_acc_unit:
    forall (l: list A) (acc : A),
      op_foldl acc l = acc ∘ op_foldl unit l.
  Proof.
    intros.
    rewrite <- (right_id acc) at 1.
    apply op_foldl_acc.
  Qed.

  Lemma op_foldl_app : forall l1 acc l2,
      op_foldl acc (l1 ++ l2) =
      op_foldl acc l1 ∘ op_foldl unit l2.
  Proof.
    induction l1; simpl; intros; auto.
    apply op_foldl_acc_unit.
  Qed.

  Fixpoint flatten vm (t:binop_tree) : list A :=
    match t with
    | Leaf x => [x]
    | Atom i => [varmap_find unit i vm]
    | Node l r => flatten vm l ++ flatten vm r
    end.

  Theorem op_tree_flatten : forall vm t,
      op_tree vm t = op_foldl unit (flatten vm t).
  Proof.
    induction t; simpl.
    rewrite left_id; auto.
    rewrite left_id; auto.
    rewrite op_foldl_app.
    congruence.
  Qed.

  Theorem a_ex1 : forall x y z,
      x ∘ y ∘ (x ∘ z) = x ∘ y ∘ x ∘ z.
  Proof.
    intros.
    match goal with
    | [ |- ?t = ?t' ] =>
      quote_tree t; quote_tree t'
    end.

    rewrite !op_tree_flatten.
    simpl.
    reflexivity.
  Qed.

  Inductive term :=
  | term_atom : A -> term
  | term_var : index -> term.

  Definition find_term vm (t:term) : A :=
    match t with
    | term_atom x => x
    | term_var i => varmap_find unit i vm
    end.

  Fixpoint op_term_foldl (vm: varmap A) (acc:A) (l: list term) : A :=
    match l with
    | nil => acc
    | x::xs => op_term_foldl vm (acc ∘ find_term vm x) xs
    end.

  Fixpoint flatten_terms (t:binop_tree) : list term :=
    match t with
    | Leaf x => [term_atom x]
    | Atom i => [term_var i]
    | Node l r => flatten_terms l ++ flatten_terms r
    end.

  Lemma op_term_foldl_acc:
    forall (l: list term) vm (acc1 : A) (acc2: A),
      op_term_foldl vm (acc1 ∘ acc2) l = acc1 ∘ op_term_foldl vm acc2 l.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; rewrite ?associative; auto.
  Qed.

  Lemma op_term_foldl_acc_unit:
    forall (l: list term) vm (acc : A),
      op_term_foldl vm acc l = acc ∘ op_term_foldl vm unit l.
  Proof.
    intros.
    rewrite <- (right_id acc) at 1.
    apply op_term_foldl_acc.
  Qed.

  Lemma op_term_foldl_app : forall l1 vm acc l2,
      op_term_foldl vm acc (l1 ++ l2) =
      op_term_foldl vm acc l1 ∘ op_term_foldl vm unit l2.
  Proof.
    induction l1; simpl; intros; auto.
    apply op_term_foldl_acc_unit.
  Qed.

  Theorem op_term_foldl_flatten_terms : forall vm t,
      op_tree vm t = op_term_foldl vm unit (flatten_terms t).
  Proof.
    induction t; simpl.
    rewrite left_id; auto.
    rewrite left_id; auto.
    rewrite op_term_foldl_app; congruence.
  Qed.

  Lemma xzy_xyz_rewrite : forall x y z,
      x ∘ z ∘ y = x ∘ y ∘ z.
  Proof.
    intros.
    rewrite ?associative.
    f_equal.
    apply commutative.
  Qed.

  Hint Resolve xzy_xyz_rewrite.

  Theorem op_foldl_permutation : forall vm acc (l1 l2: list term),
      Permutation l2 l1 ->
      op_term_foldl vm acc l1 = op_term_foldl vm acc l2.
  Proof.
    induction 1; simpl; auto.
    replace (acc ∘ find_term vm x) with (find_term vm x ∘ acc) by (apply commutative).
    rewrite ?op_term_foldl_acc; congruence.
    rewrite xzy_xyz_rewrite; auto.
    congruence.
  Qed.

  Definition term_eq (t1 t2: term) : bool :=
    match t1 with
    | term_atom _ => false
    | term_var i => match t2 with
                   | term_atom _ => false
                   | term_var i' => index_eq i i'
                   end
    end.

  Ltac compute_group_eq :=
    rewrite group_eq_equation; unfold gather_eq1, gather_eq2, gather_eq;
    cbn [term_eq index_eq fst snd].

  Example op_term_ex1 : forall x y z,
      x ∘ y ∘ z ∘ x ∘ y = unit ∘ x ∘ x ∘ y ∘ y ∘ z.
  Proof.
    intros.
    match goal with
    | [ |- ?t = _ ] =>
      quote_tree t
    end.
    rewrite op_term_foldl_flatten_terms; cbn [flatten_terms app].
    erewrite op_foldl_permutation;
      [ | apply group_eq_permutation with (equal:=term_eq) ].
    repeat compute_group_eq; cbn [app].
    simpl.
    reflexivity.
  Qed.

End AssociativeCommutativeReasoning.
