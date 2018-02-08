Set Implicit Arguments.

Require Import Quote.
Require Import Permutation.
Require Import GroupEqual.

Require List.
Import List.ListNotations.
Open Scope list.

Definition nat_eq_dec : forall (x y:nat), {x=y}+{x<>y}.
Proof.
  decide equality.
Defined.

Class assoc_comm A (op: A -> A -> A) :=
  { associative : forall x y z, op (op x y) z = op x (op y z);
    commutative : forall x y, op x y = op y x; }.

Class monoid A (op: A -> A -> A) :=
  { unit: A;
    left_id : forall x, op unit x = x; }.

Section AssociativeCommutativeReasoning.

  Variable A:Type.
  Variable op: A -> A -> A.
  Infix "*" := op.

  Hypothesis op_ac : assoc_comm op.
  Existing Instance op_ac.

  Hypothesis op_monoid : monoid op.
  Existing Instance op_monoid.

  Lemma right_id : forall x, x * unit = x.
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
    | Node l r => op_tree vm l * op_tree vm r
    end.

  Ltac quote_tree t :=
    quote op_tree in t using (fun t' => change t with t').

  Lemma op_foldl_acc:
    forall (l: list A) (acc1 : A) (acc2: A),
      op_foldl (acc1 * acc2) l = acc1 * op_foldl acc2 l.
  Proof.
    induction l; simpl; intros; auto.
    rewrite associative.
    auto.
  Qed.

  Lemma op_foldl_acc_unit:
    forall (l: list A) (acc : A),
      op_foldl acc l = acc * op_foldl unit l.
  Proof.
    intros.
    rewrite <- (right_id acc) at 1.
    apply op_foldl_acc.
  Qed.

  Lemma op_foldl_app : forall l1 acc l2,
      op_foldl acc (l1 ++ l2) =
      op_foldl acc l1 * op_foldl unit l2.
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
      x * y * (x * z) = x * y * x * z.
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
    | x::xs => op_term_foldl vm (acc * find_term vm x) xs
    end.

  Fixpoint flatten_terms (t:binop_tree) : list term :=
    match t with
    | Leaf x => [term_atom x]
    | Atom i => [term_var i]
    | Node l r => flatten_terms l ++ flatten_terms r
    end.

  Lemma op_term_foldl_acc:
    forall (l: list term) vm (acc1 : A) (acc2: A),
      op_term_foldl vm (acc1 * acc2) l = acc1 * op_term_foldl vm acc2 l.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; rewrite ?associative; auto.
  Qed.

  Lemma op_term_foldl_acc_unit:
    forall (l: list term) vm (acc : A),
      op_term_foldl vm acc l = acc * op_term_foldl vm unit l.
  Proof.
    intros.
    rewrite <- (right_id acc) at 1.
    apply op_term_foldl_acc.
  Qed.

  Lemma op_term_foldl_app : forall l1 vm acc l2,
      op_term_foldl vm acc (l1 ++ l2) =
      op_term_foldl vm acc l1 * op_term_foldl vm unit l2.
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
      x * z * y = x * y * z.
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
    replace (acc * find_term vm x) with (find_term vm x * acc) by (apply commutative).
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

  Example op_term_ex1 : forall x y z,
      x * y * z * x * y = unit * x * x * y * y * z.
  Proof.
    intros.
    match goal with
    | [ |- ?t = _ ] =>
      quote_tree t
    end.
    rewrite op_term_foldl_flatten_terms; cbn [flatten_terms app].
    erewrite op_foldl_permutation;
      [ | apply group_eq_permutation with (equal:=term_eq) ].
    repeat (compute_group_eq; cbn [term_eq index_eq]); cbn [app].
    simpl.
    reflexivity.
  Qed.

End AssociativeCommutativeReasoning.
