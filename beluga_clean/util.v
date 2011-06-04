Require Export worlds.

 Definition cdot {A} : name ∅ -> A := fun n => match (empty_is_empty n) with end.
 Notation "·" := cdot.

 Definition maybe {A C} (f:A -> C) (c:C) (x:A + unit) : C := match x with | inl a => f a | inr _ => c end.  

Definition compose {A B C:Set} (f:A -> B) (g:B -> C) (a:A) : C
 := g (f a). 

Notation "f ○ g" := (compose g f) (at level 10).

Notation "Γ ,, ( y , t )" := ((maybe Γ t) ○ (export y)) (at level 90).