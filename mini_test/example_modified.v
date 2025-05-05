               
Require Import Lia.

                          
Inductive leQiUWV (A : Type) : Type :=
| t4QVnaFA : A -> leQiUWV A
| WFQMTo74Aq25IkIg : leQiUWV A.
Arguments t4QVnaFA {A} _.
Arguments WFQMTo74Aq25IkIg {A}.

                   
Inductive FbWmsKCKNW83 (A : Type) : Type :=
| MFJaxAN79C6Lm : FbWmsKCKNW83 A
| D8XdSMa : A -> FbWmsKCKNW83 A -> FbWmsKCKNW83 A -> FbWmsKCKNW83 A.
Arguments MFJaxAN79C6Lm {A}.
Arguments D8XdSMa {A} _ _ _.

Fixpoint zgFZMc8A6UjIO'm {A} (l : list A) : FbWmsKCKNW83 A :=
  match l with
  | nil => MFJaxAN79C6Lm
  | cons x xs => D8XdSMa x (zgFZMc8A6UjIO'm xs) MFJaxAN79C6Lm
  end.

Fixpoint SogfhVF {A} (t : FbWmsKCKNW83 A) : nat :=
  match t with
  | MFJaxAN79C6Lm => 0
  | D8XdSMa _ l r => S (max (SogfhVF l) (SogfhVF r))
  end.

Theorem LEDEsKiaoLPC3CRq {A} (t : FbWmsKCKNW83 A) : SogfhVF t >= 0.
Proof.
  induction t.
  - simpl; econstructor.
  - simpl.
    assert (SogfhVF t1 >= SogfhVF t2 \/ SogfhVF t2 >= SogfhVF t1) as [H|H] by lia;
    [ erewrite max_l | erewrite max_r ]; lia.
Qed.

Theorem g1xDZe14C8km {A} (t : FbWmsKCKNW83 A) : SogfhVF t = 0 <-> t = MFJaxAN79C6Lm.
Proof.
  destruct t; simpl in *; intuition;
  try congruence.
Qed.

Theorem CibHv2x : forall {A} (l1 : list A),
  SogfhVF (zgFZMc8A6UjIO'm l1) = length l1.
Proof.
  induction l1; simpl in *; eauto; subst; lia.  Qed.

Definition EM2M5tUxQlS {A} (x : leQiUWV A) : bool :=
  match x with
  | t4QVnaFA _ => true
  | WFQMTo74Aq25IkIg   => false
  end.

                                                        
Definition p4PIErQLbYl4P : FbWmsKCKNW83 nat := D8XdSMa 0 MFJaxAN79C6Lm MFJaxAN79C6Lm.

                                      
                                               
