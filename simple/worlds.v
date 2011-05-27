Require Import Coq.Program.Equality.
Parameter world : Set.
Parameter empty : world.
Notation "∅" := empty.
Parameter name : world -> Set.
Parameter link : world -> world -> Set.
Notation "α ↪ β" := (link α β) (at level 90).
Parameter weaken : forall {α β}, α↪β -> name β.
Coercion weaken : link >-> name.
Parameter import : forall {α β}, α↪β -> name α -> name β.
Parameter next_world : world -> world.
Parameter next_link : forall α, α↪(next_world α).
Definition next α : {β:world & α↪β}. 
exists (next_world α).
apply next_link.
Defined.
Parameter export : forall {α β} (y:α↪β) (n:name β), name α + unit.
Axiom empty_is_empty : name ∅ -> False.
Axiom export_self : forall {α β} (y:α↪β), export y y = inr _ tt.
Axiom export_import_inv : forall {α β} (y:α↪β) x, export y (import y x) = inl _ x.

Definition maybe {A C} (f:A -> C) (c:C) (x:A + unit) : C :=
match x with
| inl a => f a
| inr _ => c
end.
Definition compose {A B C:Set} (f:A -> B) (g:B -> C) (a:A) : C
 := g (f a). 
Notation "f ○ g" := (compose g f) (at level 10).

Definition cdot {A} : name ∅ -> A :=
fun n => match (empty_is_empty n) with end.

Notation "·" := cdot.

(* Γ : name α -> tp *)
Notation "Γ ,, ( x , T )" := ((maybe Γ T) ○ (export x)) (at level 90).
(* i.e.
  (Γ ,, (x,T)) y :=
    match (export x y) with 
     | inl n => Γ n
     | inr _ => T
    end
*)

Tactic Notation "nice_inversion" hyp(H) := inversion H; subst; simpl_existTs; subst.
Tactic Notation "nice_inversion" integer(N) := inversion N; subst; simpl_existTs; subst.