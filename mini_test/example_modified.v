               
Require Import Lia.

                          
Inductive pVqM5RLOUCDma3IoM (A : Type) : Type :=
| VGeaXYabEnsvxS : A -> pVqM5RLOUCDma3IoM A
| bOWGLYJX : pVqM5RLOUCDma3IoM A.
Arguments VGeaXYabEnsvxS {A} _.
Arguments bOWGLYJX {A}.

                   
Inductive FUzDjn''ewI (A : Type) : Type :=
| H12KOEaMC7K96sRkH : FUzDjn''ewI A
| u9jYZOr82l7QB : A -> FUzDjn''ewI A -> FUzDjn''ewI A -> FUzDjn''ewI A.
Arguments H12KOEaMC7K96sRkH {A}.
Arguments u9jYZOr82l7QB {A} _ _ _.

Fixpoint blXKvIXIXlURcMCM {A} (l : list A) : FUzDjn''ewI A :=
  match l with
  | nil => H12KOEaMC7K96sRkH
  | cons x xs => u9jYZOr82l7QB x (blXKvIXIXlURcMCM xs) H12KOEaMC7K96sRkH
  end.

Fixpoint adJTB7c2XYmc9 {A} (t : FUzDjn''ewI A) : nat :=
  match t with
  | H12KOEaMC7K96sRkH => 0
  | u9jYZOr82l7QB _ l r => S (max (adJTB7c2XYmc9 l) (adJTB7c2XYmc9 r))
  end.

Theorem GudZKpfNtaqSNjSI {A} (t : FUzDjn''ewI A) : adJTB7c2XYmc9 t >= 0.
Proof.
  induction t.
  - simpl; econstructor.
  - simpl.
    assert (adJTB7c2XYmc9 t1 >= adJTB7c2XYmc9 t2 \/ adJTB7c2XYmc9 t2 >= adJTB7c2XYmc9 t1) as [H|H] by lia;
    [ erewrite max_l | erewrite max_r ]; lia.
Qed.

Theorem hjhEsWq {A} (t : FUzDjn''ewI A) : adJTB7c2XYmc9 t = 0 <-> t = H12KOEaMC7K96sRkH.
Proof.
  destruct t; simpl in *; intuition;
  try congruence.
Qed.

Theorem RwwF'laxl : forall {A} (l1 : list A),
  adJTB7c2XYmc9 (blXKvIXIXlURcMCM l1) = length l1.
Proof.
  induction l1; simpl in *; eauto; subst; lia.  Qed.

Definition qV4JC_xOAhmov5fdL {A} (x : pVqM5RLOUCDma3IoM A) : bool :=
  match x with
  | VGeaXYabEnsvxS _ => true
  | bOWGLYJX   => false
  end.

                                                        
Definition ONJx8XKPxznr5 : FUzDjn''ewI nat := u9jYZOr82l7QB 0 H12KOEaMC7K96sRkH H12KOEaMC7K96sRkH.

                                      
                                               
