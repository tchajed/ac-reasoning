Require Import AssociativeCommutative.

Require Import Quote.
Require Import Arith.
Require Import Permutation.

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
    rewrite List.app_assoc; auto.
  - intros.
    apply Permutation_app_comm.
  - constructor; hnf; intros; eauto.
    apply Permutation_sym; auto.
    econstructor; eauto.
  - exact nil.
  - intros.
    eapply Permutation_app; eauto.
Qed.

Fixpoint op_tree_nat (vm: varmap nat) (t:binop_tree nat) :=
  match t with
  | Leaf x => x
  | Atom i => varmap_find default_val i vm
  | Node l r => op_tree_nat vm l + op_tree_nat vm r
  end.

Theorem nat_rewrite : forall (x y z w: nat),
    x + y + x + z + y + w =
    x + x + y + z + y + w.
Proof.
  intros.
  (* quote can't handle this *)
  Fail match goal with
       | [ |- ?t = _ ] =>
         quote op_tree_nat in t using (fun t' => idtac t)
       end.
Abort.
