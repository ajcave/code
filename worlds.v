Parameter world : Set.
Parameter empty : world.
Notation "∅" := empty.
Parameter name : world -> Set.
Axiom empty_is_empty : name ∅ -> False.
Parameter link : world -> world -> Set.
Notation "α ↪ β" := (link α β) (at level 90).
Parameter weaken : forall {α β}, α↪β -> name β.
Coercion weaken : link >-> name.
Parameter import : forall {α β}, α↪β -> name α -> name β.
Parameter next' : forall a, {b:world & a↪b}.
Definition next a : {b:world & a↪b} := existT _ (projT1 (next' a)) (projT2 (next' a)).

Parameter export : forall {α β} (y:α↪β) (n:name β), name α + unit.

Axiom export_self : forall {α β} (y:α↪β), export y y = inr _ tt.

Lemma export_exclusive : forall {α β} {y:α↪β} {n:name α}, inl _ n = export y y -> False.
intros.
erewrite export_self in H.
discriminate.
Qed.

Axiom export_import_inv : forall {α β} (y:α↪β) (n:name α), export y (import y n) = inl _ n.
 