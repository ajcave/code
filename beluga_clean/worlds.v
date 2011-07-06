Parameter world : Set.
Parameter empty : world.
Notation "∅" := empty.
Parameter name : world -> Set.
Axiom empty_is_empty : name ∅ -> False.
Parameter link : world -> world -> Set.
Notation "α ↪ β" := (link α β) (at level 90).

Parameter toName : forall {α β}, α↪β -> name β.
Coercion toName : link >-> name.
Definition name_subst α β := name α -> name β.
Axiom import : forall {α β}, α↪β -> name_subst α β.
Notation "↑ x" := (import x) (at level 90).
Parameter succ_world : world -> world.
Parameter succ_link : forall α, α↪(succ_world α).
Notation "₁" := (succ_link ∅).
Axiom export : forall {α β} (y:α↪β) (n:name β), name α + unit.
Axiom export_self : forall {α β} (y:α↪β), export y y = inr _ tt.
Axiom export_import_inv : forall {α β} (y:α↪β) (n:name α), export y (import y n) = inl _ n.

Definition empty_initial : forall (C : Set), name ∅ -> C
 := fun C x => match (empty_is_empty x) with end.
