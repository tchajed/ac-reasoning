# Associative Commutative reasoning in Coq

This library provide a tactic for automating associative-commutative reasoning. Here's a simple example case:

```
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
  reflexivity.
Qed.
```
