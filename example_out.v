(* example.v *)
Require Import Lia.

(* A simple option type *)
Inductive B_KkAAFKo (A : Type) : Type :=
| FBa9iibIt : A -> B_KkAAFKo A
| D62S_xh9h : B_KkAAFKo A.
Arguments FBa9iibIt {A} _.
Arguments D62S_xh9h {A}.

(* A binary tree *)
Inductive kN7c6'6Os (A : Type) : Type :=
| Kq'iTaJ_' : kN7c6'6Os A
| aocohy40v : A -> kN7c6'6Os A -> kN7c6'6Os A -> kN7c6'6Os A.
Arguments Kq'iTaJ_' {A}.
Arguments aocohy40v {A} _ _ _.

Fixpoint tree_from_list {A} (l : list A) : kN7c6'6Os A :=
  match l with
  | nil => Kq'iTaJ_'
  | cons x xs => aocohy40v x (tree_from_list xs) Kq'iTaJ_'
  end.

Fixpoint tree_depth {A} (t : kN7c6'6Os A) : nat :=
  match t with
  | Kq'iTaJ_' => 0
  | aocohy40v _ l r => S (max (tree_depth l) (tree_depth r))
  end.

Theorem tree_depth_nonneg {A} (t : kN7c6'6Os A) : tree_depth t >= 0.
Proof.
  induction t.
  - simpl; econstructor.
  - simpl.
    assert (tree_depth t1 >= tree_depth t2 \/ tree_depth t2 >= tree_depth t1) as [H|H] by lia;
    [ erewrite max_l | erewrite max_r ]; lia.
Qed.

Theorem tree_depth_zero_iff {A} (t : kN7c6'6Os A) : tree_depth t = 0 <-> t = Kq'iTaJ_'.
Proof.
  destruct t; simpl in *; intuition;
  try congruence.
Qed.

Theorem tree_from_list_depth : forall {A} (l1 : list A),
  tree_depth (tree_from_list l1) = length l1.
Proof.
  induction l1; simpl in *; eauto; subst; lia.
Qed.

Definition test1 {A} (x : B_KkAAFKo A) : bool :=
  match x with
  | FBa9iibIt _ => true
  | D62S_xh9h   => false
  end.

(* In a string: "Some and None should not be renamed" *)
Definition test2 : kN7c6'6Os nat := aocohy40v 0 Kq'iTaJ_' Kq'iTaJ_'.

(* A comment with Node and myOption *)
(* Don’t touch: Some, None, Tree, Node, Leaf *)
