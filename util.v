 Require Import worlds.
 Require Import Coq.Logic.FunctionalExtensionality.
 Definition cdot {A} : name ∅ -> A := fun n => match (empty_is_empty n) with end.
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
Definition id {A:Set} := fun x:A => x.
Lemma compose_id_left {A B:Set} (f:A -> B) : id ○ f = f.
extensionality x. unfold compose. unfold id.
reflexivity.
Qed.
Lemma compose_id_right {A B:Set} (f:A -> B) : f ○ id = f.
extensionality x. unfold compose. unfold id.
reflexivity.
Qed.

Open Scope type_scope.
Definition linkassign (A:Set) := 
 star (fun α β => (α↪β)*A).
Notation "α ↝ β 〈 A 〉" := (linkassign A α β) (at level 90).