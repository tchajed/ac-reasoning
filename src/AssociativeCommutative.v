Set Implicit Arguments.

Require Import Permutation.
Require Import GroupEqual.
Require Import RelationClasses.
Require Import Morphisms.

Require Import NonEmptyList.

Require List.
Import List.ListNotations.
Open Scope list.

Section Typeclasses.

  Variable A:Type.

  Class Associative (op: A -> A -> A) (R: A -> A -> Prop) :=
    associative: forall x y z, R (op (op x y) z) (op x (op y z)).

  Class Commutative (op: A -> A -> A) (R: A -> A -> Prop) :=
    commutative : forall x y, R (op x y) (op y x).

  Class Default :=
    default_val: A.

  Class AssociativeCommutative (op: A -> A -> A) (R: A -> A -> Prop) :=
    { ac_associative :> Associative op R;
      ac_commutative :> Commutative op R;
      ac_equiv :> Equivalence R;
      ac_def :> Default;
      ac_op_respects_equiv : forall x x' y y',
          R x x' ->
          R y y' ->
          R (op x y) (op x' y'); }.

End Typeclasses.

Arguments Associative A op R : clear implicits.
Arguments Commutative A op R : clear implicits.
Arguments AssociativeCommutative A op R : clear implicits.
Arguments default_val {A} {_}.
Arguments ac_def {A} {_}.

Module varmap.
  Definition I := nat.
  Inductive t (A:Type) : Type :=
  | empty
  | cons (i:I) (x:A) (xs:t A).

  Definition index_eq (i1 i2:I) : bool :=
    Nat.eqb i1 i2.

  Theorem index_eq_prop : forall i1 i2,
      index_eq i1 i2 = true <-> i1 = i2.
  Proof.
    apply PeanoNat.Nat.eqb_eq.
  Qed.

  Fixpoint find {A} `{Default A} (i:nat) (vm: t A) : A :=
    match vm with
    | empty _ => default_val
    | cons i' x vm' => if Nat.eqb i i' then x else find i vm'
    end.

  Fixpoint length A (ctx: t A) : nat :=
    match ctx with
    | empty _ => O
    | cons _ _ ctx' => S (length ctx')
    end.

End varmap.

Section BinOps.

  Inductive binop_tree {A} :=
  | Leaf (x:A)
  | Atom (i:varmap.I)
  | Node (l:binop_tree) (r:binop_tree).

  Fixpoint op_tree A `{Default A} (op: A -> A -> A) (vm: varmap.t A) t :=
    match t with
    | Leaf x => x
    | Atom i => varmap.find i vm
    | Node l r => op (op_tree op vm l) (op_tree op vm r)
    end.

End BinOps.

Arguments binop_tree A : clear implicits.

Ltac reify_helper op var term ctx :=
  let reify_rec term ctx := reify_helper op var term ctx in
  lazymatch ctx with
  | context[varmap.cons ?i term _] =>
    constr:( (ctx, @Atom var i) )
  | _ =>
    lazymatch term with
    | op ?x ?y =>
      let ctx_x := reify_rec x ctx in
      let ctx_y := reify_rec y (fst ctx_x) in
      let r := (eval cbv [fst snd] in
                   (fst ctx_y, @Node var (snd ctx_x) (snd ctx_y))) in
      constr:(r)
    | _ =>
      let v' := (eval cbv [varmap.length] in (varmap.length ctx)) in
      let ctx' := constr:( varmap.cons v' term ctx ) in
      constr:( (ctx', @Atom var v') )
    end
  end.

Ltac reify op term :=
  lazymatch type of term with
  | ?A => reify_helper op A term (varmap.empty A)
  end.

Ltac quote_with ctx term :=
  lazymatch term with
  | ?op _ _ =>
    lazymatch type of term with
    | ?A => let ctx_x := reify_helper op A term ctx in
             let ctx := (eval cbv [fst] in (fst ctx_x)) in
             let x := (eval cbv [snd] in (snd ctx_x)) in
             change term with (op_tree op ctx x)
    end
  end.

Ltac quote term :=
  match type of term with
  | ?A => quote_with (varmap.empty A) term
  end.

Section AssociativeCommutativeReasoning.

  Variable A:Type.
  Variable op: A -> A -> A.
  Infix "*" := op.

  Variable equiv: A -> A -> Prop.
  Infix "==" := equiv (at level 60, no associativity).

  Hypothesis op_ac : AssociativeCommutative A op equiv.
  Existing Instance op_ac.

  Instance op_proper :
    Proper (equiv ==> equiv ==> equiv) op.
  Proof.
    unfold Proper, respectful; intros.
    eapply ac_op_respects_equiv; eauto.
  Qed.

  Lemma equiv_refl : forall x, x == x.
  Proof.
    reflexivity.
  Qed.

  Hint Resolve equiv_refl.

  Fixpoint op_foldl (acc:A) (l: list A) :=
    match l with
    | [] => acc
    | x::xs => op_foldl (op acc x) xs
    end.

  Definition op_foldl1 (l: nelist A) :=
    op_foldl (hd l) (tl l).

  Lemma op_foldl_acc:
    forall (l: list A) (acc1 : A) (acc2: A),
      op_foldl (acc1 * acc2) l == acc1 * op_foldl acc2 l.
  Proof.
    induction l; simpl; intros; auto.
    rewrite IHl.
    rewrite IHl.
    apply associative.
    typeclasses eauto.
  Qed.

  Instance op_foldl_proper :
    Proper (equiv ==> eq ==> equiv) op_foldl.
  Proof.
    unfold Proper, respectful; intros; subst.
    rename y0 into l.
    induction l; simpl; auto.
    rewrite ?op_foldl_acc.
    eapply ac_op_respects_equiv; eauto.
  Qed.

  Lemma op_foldl_app : forall l1 acc x l,
      op_foldl acc (l1 ++ x::l) ==
      op_foldl acc l1 * op_foldl x l.
  Proof.
    induction l1; simpl; intros; auto.
    rewrite op_foldl_acc; auto.
  Qed.

  Lemma op_foldl1_app : forall l1 l2,
      op_foldl1 (append l1 l2) ==
      op_foldl1 l1 * op_foldl1 l2.
  Proof.
    unfold op_foldl1.
    destruct l1, l2; simpl; intros; auto.
    apply op_foldl_app.
  Qed.

  Fixpoint flatten vm (t:binop_tree A) : nelist A :=
    match t with
    | Leaf x => single x
    | Atom i => single (varmap.find i vm)
    | Node l r => append (flatten vm l) (flatten vm r)
    end.

  Theorem op_tree_flatten : forall vm t,
      op_tree op vm t == op_foldl1 (flatten vm t).
  Proof.
    induction t; simpl; auto.
    rewrite op_foldl1_app.
    eapply ac_op_respects_equiv; eauto.
  Qed.

  Theorem a_ex1 : forall x y z,
      x * y * (x * z) == x * y * x * z.
  Proof.
    intros.
    match goal with
    | [ |- ?t == ?t' ] =>
      quote t; quote t'
    end.

    rewrite !op_tree_flatten.
    cbv.
    reflexivity.
  Qed.

  Inductive term :=
  | term_atom : A -> term
  | term_var : varmap.I -> term.

  Definition find_term vm (t:term) : A :=
    match t with
    | term_atom x => x
    | term_var i => varmap.find i vm
    end.

  Fixpoint op_term_foldl (vm: varmap.t A) (acc:A) (l: list term) : A :=
    match l with
    | nil => acc
    | x::xs => op_term_foldl vm (acc * find_term vm x) xs
    end.

  Definition op_term_foldl1 (vm: varmap.t A) (l: nelist term) : A :=
    op_term_foldl vm (find_term vm (hd l)) (tl l).

  Fixpoint flatten_terms (t:binop_tree A) : nelist term :=
    match t with
    | Leaf x => single (term_atom x)
    | Atom i => single (term_var i)
    | Node l r => append (flatten_terms l) (flatten_terms r)
    end.

  Lemma op_term_foldl_acc:
    forall (l: list term) vm (acc1 : A) (acc2: A),
      op_term_foldl vm (acc1 * acc2) l ==
      acc1 * op_term_foldl vm acc2 l.
  Proof.
    induction l; simpl; intros; auto.
    rewrite ?IHl.
    apply associative.
    typeclasses eauto.
  Qed.

  Instance op_term_foldl_proper :
    Proper (eq ==> equiv ==> eq ==> equiv) op_term_foldl.
  Proof.
    unfold Proper, respectful; intros; subst.
    induction y1; simpl; auto.
    rewrite ?op_term_foldl_acc; auto.
    eapply ac_op_respects_equiv; eauto.
  Qed.

  Lemma op_term_foldl_app : forall vm l1 acc x l,
      op_term_foldl vm acc (l1 ++ x::l) ==
      op_term_foldl vm acc l1 * op_term_foldl vm (find_term vm x) l.
  Proof.
    induction l1; simpl; intros; auto.
    rewrite op_term_foldl_acc; auto.
  Qed.

  Lemma op_term_foldl1_app : forall l1 vm l2,
      op_term_foldl1 vm (append l1 l2) ==
      op_term_foldl1 vm l1 * op_term_foldl1 vm l2.
  Proof.
    unfold op_term_foldl1.
    destruct l1, l2; simpl; intros.
    apply op_term_foldl_app.
  Qed.

  Theorem op_term_foldl_flatten_terms : forall vm t,
      op_tree op vm t == op_term_foldl1 vm (flatten_terms t).
  Proof.
    induction t; simpl; auto.
    rewrite op_term_foldl1_app; auto.
    apply ac_op_respects_equiv; eauto.
  Qed.

  Lemma xzy_xyz_rewrite : forall x y z,
      x * z * y == x * y * z.
  Proof.
    intros.
    rewrite ?associative by typeclasses eauto.
    rewrite (commutative z y); auto.
  Qed.

  Hint Resolve xzy_xyz_rewrite.

  Theorem op_foldl_permutation : forall vm acc (l1 l2: list term),
      Permutation l1 l2 ->
      op_term_foldl vm acc l1 == op_term_foldl vm acc l2.
  Proof.
    induction 1; simpl; auto.
    rewrite commutative by typeclasses eauto.
    rewrite ?op_term_foldl_acc; auto.
    eapply ac_op_respects_equiv; eauto.
    rewrite xzy_xyz_rewrite; auto.
    etransitivity; eauto.
  Qed.

  Ltac especialize H :=
    lazymatch type of H with
    | forall (_: _ = _), _ =>
      specialize (H eq_refl)
    | forall (_:?T), _ =>
      let x := fresh "x" in
      evar (x:T);
      specialize (H x);
      subst x
    end.

  Theorem op_foldl_permutation_general : forall vm acc1 acc2 (l1 l2: list term),
      Permutation (acc1::l1) (acc2::l2) ->
      op_term_foldl vm (find_term vm acc1) l1 ==
      op_term_foldl vm (find_term vm acc2) l2.
  Proof.
    intros.
    remember (acc1::l1) as l1'.
    remember (acc2::l2) as l2'.
    generalize dependent acc1.
    generalize dependent l1.
    generalize dependent acc2.
    generalize dependent l2.
    induction H; intros; subst; try congruence;
      repeat match goal with
             | [ H: _ :: _ = _ :: _ |- _ ] =>
               inversion H; subst; clear H
             end;
      simpl.
    apply op_foldl_permutation; eauto.
    rewrite commutative by typeclasses eauto; eauto.
    destruct l'.
    exfalso; eapply Permutation_nil_cons; eauto.
    repeat especialize IHPermutation1.
    repeat especialize IHPermutation2.
    etransitivity; eauto.
  Qed.

  Definition term_eq (t1 t2: term) : bool :=
    match t1 with
    | term_atom _ => false
    | term_var i => match t2 with
                   | term_atom _ => false
                   | term_var i' => varmap.index_eq i i'
                   end
    end.

  Theorem op_term_foldl1_group : forall vm (l: nelist term),
      op_term_foldl1 vm l ==
      let (x, l') := l in
      op_term_foldl vm
                    (find_term vm x)
                    (gather_eq1 term_eq (hd l) l' ++
                                group_eq term_eq (gather_eq2 term_eq (hd l) l')).
  Proof.
    unfold op_term_foldl1.
    destruct l; simpl.
    eapply op_foldl_permutation.
    symmetry.
    transitivity (gather_eq1 term_eq t l ++ gather_eq2 term_eq t l).
    eapply Permutation_app; eauto.
    eapply group_eq_permutation.
    apply gather_eq12_permutation.
  Qed.

  Example op_term_ex1 : forall x y z,
      x * y * z * x * y == x * x * y * y * z.
  Proof.
    intros.
    lazymatch goal with
    | [ |- ?t == _ ] =>
      quote t;
        lazymatch goal with
        | [ |- op_tree _ ?ctx _ == ?t' ] =>
          quote_with ctx t'
        | _ => idtac
        end
    end.
    rewrite !op_term_foldl_flatten_terms; cbv [flatten_terms append single app].
    rewrite !op_term_foldl1_group; cbv [find_term].
    repeat (rewrite group_eq_equation;
            cbv beta iota zeta delta
                [op_term_foldl find_term
                   varmap.find term_eq varmap.index_eq Nat.eqb
                   fst snd hd tl app
                   gather_eq gather_eq1 gather_eq2]).
    match goal with
    | |- ?t == ?t => reflexivity
    end.
  Qed.

End AssociativeCommutativeReasoning.

Ltac requote term :=
  match goal with
  | [ |- context[op_tree _ ?ctx _] ] =>
    quote_with ctx term
  end.

Ltac ac_simplify :=
  rewrite !op_term_foldl_flatten_terms; cbn [flatten_terms append single app];
  rewrite !op_term_foldl1_group; cbn [find_term];
  repeat (rewrite group_eq_equation;
          cbn beta iota zeta delta
              [op_term_foldl
                 find_term
                 varmap.find term_eq varmap.index_eq Nat.eqb
                 fst snd hd tl app
                 gather_eq gather_eq1 gather_eq2]).

Ltac ac_instance :=
  constructor; hnf; intros;
  [ (* assoc *) | (* comm *) |
    (* equivalence relation *)
    typeclasses eauto |
    (* default *)
    try constructor |
    (* respectful *)
    try congruence ].
