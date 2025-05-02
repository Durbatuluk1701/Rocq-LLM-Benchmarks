(* example.v *)
Require Import Lia.

(* A simple option type *)
Inductive gk2jg0sYF (A : Type) : Type :=
| ymTbjZzZh : A -> gk2jg0sYF A
| gGLvlDWht : gk2jg0sYF A.
Arguments ymTbjZzZh {A} _.
Arguments gGLvlDWht {A}.

(* A binary tree *)
Inductive ltHFO'MTO (A : Type) : Type :=
| mrmC1yuDp : ltHFO'MTO A
| otC4qdz7e : A -> ltHFO'MTO A -> ltHFO'MTO A -> ltHFO'MTO A.
Arguments mrmC1yuDp {A}.
Arguments otC4qdz7e {A} _ _ _.

Fixpoint Y1Ra2Q26k {A} (l : list A) : ltHFO'MTO A :=
  match l with
  | nil => mrmC1yuDp
  | cons x xs => otC4qdz7e x (Y1Ra2Q26k xs) mrmC1yuDp
  end.

Fixpoint Ttq5PT1iS {A} (t : ltHFO'MTO A) : nat :=
  match t with
  | mrmC1yuDp => 0
  | otC4qdz7e _ l r => S (max (Ttq5PT1iS l) (Ttq5PT1iS r))
  end.

Theorem W0pd2JvnZ {A} (t : ltHFO'MTO A) : Ttq5PT1iS t >= 0.
Proof.
  induction t.
  - simpl; econstructor.
  - simpl.
    assert (Ttq5PT1iS t1 >= Ttq5PT1iS t2 \/ Ttq5PT1iS t2 >= Ttq5PT1iS t1) as [H|H] by lia;
    [ erewrite max_l | erewrite max_r ]; lia.
Qed.

Theorem OVpdb1gfi {A} (t : ltHFO'MTO A) : Ttq5PT1iS t = 0 <-> t = mrmC1yuDp.
Proof.
  destruct t; simpl in *; intuition;
  try congruence.
Qed.

Theorem qFdkKxbuj : forall {A} (l1 : list A),
  Ttq5PT1iS (Y1Ra2Q26k l1) = length l1.
Proof.
  induction l1; simpl in *; eauto; subst; lia.  Qed.

Definition LlzWDKcJr {A} (x : gk2jg0sYF A) : bool :=
  match x with
  | ymTbjZzZh _ => true
  | gGLvlDWht   => false
  end.

(* In a string: "Some and None should not be renamed" *)
Definition wRCQcfZjP : ltHFO'MTO nat := otC4qdz7e 0 mrmC1yuDp mrmC1yuDp.

(* A comment with Node and myOption *)
(* Don’t touch: Some, None, Tree, Node, Leaf *)
