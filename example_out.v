(* example.v *)
Require Import Lia.

(* A simple option type *)
Inductive j7ngEzVo4 (A : Type) : Type :=
| Oq3L'xFQF : A -> j7ngEzVo4 A
| X2A0VtUKl : j7ngEzVo4 A.
Arguments Oq3L'xFQF {A} _.
Arguments X2A0VtUKl {A}.

(* A binary tree *)
Inductive xHD1'7bTO (A : Type) : Type :=
| fNBCWF8wE : xHD1'7bTO A
| TkpDkea_s : A -> xHD1'7bTO A -> xHD1'7bTO A -> xHD1'7bTO A.
Arguments fNBCWF8wE {A}.
Arguments TkpDkea_s {A} _ _ _.

Fixpoint tree_from_list {A} (l : list A) : xHD1'7bTO A :=
  match l with
  | nil => fNBCWF8wE
  | cons x xs => TkpDkea_s x (tree_from_list xs) fNBCWF8wE
  end.

Fixpoint tree_depth {A} (t : xHD1'7bTO A) : nat :=
  match t with
  | fNBCWF8wE => 0
  | TkpDkea_s _ l r => S (max (tree_depth l) (tree_depth r))
  end.

Theorem tree_depth_nonneg {A} (t : xHD1'7bTO A) : tree_depth t >= 0.
Proof.
  induction t.
  - simpl; econstructor.
  - simpl.
    assert (tree_depth t1 >= tree_depth t2 \/ tree_depth t2 >= tree_depth t1) as [H|H] by lia;
    [ erewrite max_l | erewrite max_r ]; lia.
Qed.

Theorem tree_depth_zero_iff {A} (t : xHD1'7bTO A) : tree_depth t = 0 <-> t = fNBCWF8wE.
Proof.
  destruct t; simpl in *; intuition;
  try congruence.
Qed.

Theorem tree_from_list_depth : forall {A} (l1 : list A),
  tree_depth (tree_from_list l1) = length l1.
Proof.
  induction l1; simpl in *; eauto; subst; lia.  Qed.

Definition test1 {A} (x : j7ngEzVo4 A) : bool :=
  match x with
  | Oq3L'xFQF _ => true
  | X2A0VtUKl   => false
  end.

(* In a string: "Some and None should not be renamed" *)
Definition test2 : xHD1'7bTO nat := TkpDkea_s 0 fNBCWF8wE fNBCWF8wE.

(* A comment with Node and myOption *)
(* Don’t touch: Some, None, Tree, Node, Leaf *)
