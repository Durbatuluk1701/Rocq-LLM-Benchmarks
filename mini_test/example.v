(* example.v *)
Require Import Lia.

(* A simple option type *)
Inductive myOption (A : Type) : Type :=
| mySome : A -> myOption A
| myNone : myOption A.
Arguments mySome {A} _.
Arguments myNone {A}.

(* A binary tree *)
Inductive Tree (A : Type) : Type :=
| Leaf : Tree A
| Node : A -> Tree A -> Tree A -> Tree A.
Arguments Leaf {A}.
Arguments Node {A} _ _ _.

Fixpoint tree_from_list {A} (l : list A) : Tree A :=
  match l with
  | nil => Leaf
  | cons x xs => Node x (tree_from_list xs) Leaf
  end.

Fixpoint tree_depth {A} (t : Tree A) : nat :=
  match t with
  | Leaf => 0
  | Node _ l r => S (max (tree_depth l) (tree_depth r))
  end.

Theorem tree_depth_nonneg {A} (t : Tree A) : tree_depth t >= 0.
Proof.
  induction t.
  - simpl; econstructor.
  - simpl.
    assert (tree_depth t1 >= tree_depth t2 \/ tree_depth t2 >= tree_depth t1) as [H|H] by lia;
    [ erewrite max_l | erewrite max_r ]; lia.
Qed.

Theorem tree_depth_zero_iff {A} (t : Tree A) : tree_depth t = 0 <-> t = Leaf.
Proof.
  destruct t; simpl in *; intuition;
  try congruence.
Qed.

Theorem tree_from_list_depth : forall {A} (l1 : list A),
  tree_depth (tree_from_list l1) = length l1.
Proof.
  induction l1; simpl in *; eauto; subst; lia.  Qed.

Definition test1 {A} (x : myOption A) : bool :=
  match x with
  | mySome _ => true
  | myNone   => false
  end.

(* In a string: "Some and None should not be renamed" *)
Definition test2 : Tree nat := Node 0 Leaf Leaf.

(* A comment with Node and myOption *)
(* Don’t touch: Some, None, Tree, Node, Leaf *)
