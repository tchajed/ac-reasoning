# Associative Commutative reasoning in Coq

This library (aims to) provide a tactic for automating associative-commutative reasoning. Here's a simple use case:

```
Theorem list_rewrite : forall A (l1 l2 l3 l4: list A),
  Permutation (l1 ++ l2 ++ l1 ++ l3 ++ l2 ++ l4)
              (l1 ++ l1 ++ l3 ++ l2 ++ l2 ++ l4).
```
