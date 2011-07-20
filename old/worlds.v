
Section star.
 Hypotheses (A:Set) (Rel:A -> A -> Set).
 Inductive star (a:A) : A -> Set :=
  | s_nil : star a a
  | s_cons : forall b c, star a b -> Rel b c -> star a c.
End star.
Implicit Arguments star.
Implicit Arguments s_cons.
Implicit Arguments s_nil [A Rel a].

Parameter world : Set.
Parameter empty : world.
Notation "∅" := empty.
Parameter name : world -> Set.
Axiom empty_is_empty : name ∅ -> False.
Parameter link : world -> world -> Set.
Notation "α ↪ β" := (link α β) (at level 90).

Definition link_star := star link.
Notation "α ↪* β" := (link_star α β) (at level 90).
Parameter weaken : forall {α β}, α↪β -> name β.
Coercion weaken : link >-> name.
Axiom import : forall {α β}, α↪β -> name α -> name β.
Parameter next' : forall a, {b:world & a↪b}.
Definition next a : {b:world & a↪b} := existT _ (projT1 (next' a)) (projT2 (next' a)).

Axiom export : forall {α β} (y:α↪β) (n:name β), name α + unit.

Axiom export_self : forall {α β} (y:α↪β), export y y = inr _ tt.

Lemma export_exclusive : forall {α β} {y:α↪β} {n:name α}, inl _ n = export y y -> False.
intros.
erewrite export_self in H.
discriminate.
Qed.

Axiom export_import_inv : forall {α β} (y:α↪β) (n:name α), export y (import y n) = inl _ n.

Axiom empty_initial : forall α, ∅↪*α.

Fixpoint import_star {α β} (y:α↪*β) (n:name α) : name β :=
match y in star _ _ β return name β with
 | s_nil => n
 | s_cons _ _ ys y => import y (import_star ys n)
end.