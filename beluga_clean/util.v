Require Export worlds.
Require Import Coq.Logic.FunctionalExtensionality.

Definition cdot {A} : name ∅ -> A := fun n => match (empty_is_empty n) with end.
Notation "·" := cdot.

Definition maybe {A C} (f:A -> C) (c:C) (x:A + unit) : C := match x with | inl a => f a | inr _ => c end.  

Definition compose {A B C:Set} (f:A -> B) (g:B -> C) (a:A) : C
 := g (f a). 

Notation "f ○ g" := (compose g f) (at level 10).

Definition id {A:Set} := fun x:A => x.

Notation "Γ ,, ( y , t )" := ((maybe Γ t) ○ (export y)) (at level 90).

Lemma compose_assoc {A B C D:Set} (f:A -> B) g (h:C -> D) :
 h ○ (g ○ f) = (h ○ g) ○ f.
apply functional_extensionality.
unfold compose. reflexivity.
Qed.

Lemma compose_def {A B C:Set} (f:A->B) (g:B -> C) :
 g ○ f = fun x => g (f x).
reflexivity.
Qed.
Lemma compose_def' {A B C:Set} (f:A->B) (g:B -> C) x :
 g (f x) = (g ○ f) x.
reflexivity.
Qed.

Lemma id_unit_left {A B:Set} (f:A -> B) : id ○ f = f.
apply functional_extensionality. unfold compose. reflexivity.
Qed.

Lemma id_unit_right {A B:Set} (f:A -> B) : f ○ id = f.
apply functional_extensionality. unfold compose. reflexivity.
Qed.

Lemma eta {A B:Set} (f:A -> B) : (fun x => f x) = f.
apply functional_extensionality. reflexivity.
Qed.


Set Implicit Arguments.
Inductive vec (T:Set) : nat -> Set :=
| snil : vec T 0
| scons : forall n, vec T n -> T -> vec T (S n).

Fixpoint smap {A B:Set} {n} (f:A -> B) (xs:vec A n) : vec B n :=
match xs with
| snil => snil _
| scons _ xs t => scons (smap f xs) (f t)
end.

Fixpoint wplus α (n:nat) : world :=
match n with
| 0 => α
| S m => succ_world (α + m)
end
where "α + xs" := (wplus α xs).

Fixpoint ctx_times {α n} {T:Set} (Γ:name α -> T) (Δ:vec T n) : name (α + n) -> T :=
match Δ in vec _ n return name (α + n) -> T with
| snil => Γ
| scons _ Δ' t => (Γ * Δ'),,(succ_link _,t)
end
where "Γ * Δ" := (ctx_times Γ Δ).
