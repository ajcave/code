
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
Parameter name' : world -> world -> Set.
Definition name := name' ∅.
Axiom self_empty : forall α, name' α α -> False.
Lemma empty_is_empty : name ∅ -> False.
eapply self_empty.
Qed.
Parameter link : world -> world -> Set.
Notation "α ↪ β" := (link α β) (at level 90).

Definition link_star := star link.
Notation "α ↪* β" := (link_star α β) (at level 90).
Axiom weaken' : forall {α β γ}, α↪*β -> β↪γ -> name' α γ.
Parameter weaken : forall {α β}, α↪β -> name β.
Coercion weaken : link >-> name.
Axiom import' : forall {α β γ}, β↪γ -> name' α β -> name' α γ.
Corollary import : forall {α β}, α↪β -> name α -> name β.
eapply (@import' ∅).
Qed.
Parameter next' : forall a, {b:world & a↪b}.
Definition next a : {b:world & a↪b} := existT _ (projT1 (next' a)) (projT2 (next' a)).

Axiom export' : forall {α β γ} (y:β↪γ) (n:name' α γ),
 name' α β + unit.

Lemma export : forall {α β} (y:α↪β) (n:name β), name α + unit.
eapply (@export' ∅).
Qed.

Axiom export_self : forall {α β} (y:α↪β), export y y = inr _ tt.

Lemma export_exclusive : forall {α β} {y:α↪β} {n:name α}, inl _ n = export y y -> False.
intros.
erewrite export_self in H.
discriminate.
Qed.

Axiom export_import_inv : forall {α β} (y:α↪β) (n:name α), export y (import y n) = inl _ n.
 