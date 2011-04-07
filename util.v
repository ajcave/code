(*Section star.
 Hypotheses (A:Set) (Rel:A -> A -> Set).
 Inductive star (a:A) : A -> Set :=
  | s_nil : star a a
  | s_cons : forall b c, star a b -> Rel b c -> star a c.
End star.
 Implicit Arguments star.
 Implicit Arguments s_nil.
 Implicit Arguments s_cons.
 Print Implicit s_cons.
 Implicit Arguments s_nil [A Rel a]. *)
 Require Import worlds.
 Require Import Coq.Logic.FunctionalExtensionality.
 Definition cdot {A} : name empty -> A := fun n => match (empty_is_empty n) with end.
 Notation "·" := cdot.

 Definition maybe {A C} (f:A -> C) (c:C) (x:A + unit) : C := match x with | inl a => f a | inr _ => c end.  

Definition compose
  {A:Set}
  {B:Set}
  {C:Set}
  (f:A -> B)
  (g:B -> C)
  (a:A) : C
 := g (f a). 
 Notation "f ○ g" := (compose g f) (at level 10).

 Notation "Γ ,, ( y , t )" := ((maybe Γ t) ○ (export y)) (at level 90).

Lemma compose_assoc {A B C D:Set} (f:A -> B) (g:B -> C) (h:C -> D) : (h ○ g) ○ f = h ○ (g ○ f).
extensionality x. unfold compose. reflexivity.
Qed.

Lemma f_maybe {A B C:Set} (f:B -> C) (Γ:A -> B) (t:B) :
 f ○ (maybe Γ t) = maybe (f ○ Γ) (f t).  
extensionality x. unfold compose.
destruct x; simpl; reflexivity.
Qed.

Lemma compose_comma {α β} {x:α↪β} {B C:Set} (f:B -> C)
 (Γ:name α -> B) (b:B) :
 f ○ (Γ,, (x,b)) = (f ○ Γ,, (x,f b)). 
erewrite <- compose_assoc.
erewrite f_maybe. reflexivity.
Qed.
