Parameter world : Set.
Parameter empty : world.
Notation "∅" := empty.
Parameter name : world -> Set.
Parameter link : world -> world -> Set.
Notation "α ↪ β" := (link α β) (at level 90).
Parameter weaken : forall {α β}, α↪β -> name β.
Coercion weaken : link >-> name.
Parameter import : forall {α β}, α↪β -> name α -> name β.
Parameter next' : forall a, {b:world & a↪b}.
Definition next a : {b:world & a↪b} := existT _ (projT1 (next' a)) (projT2 (next' a)).
Parameter export : forall {α β} (y:α↪β) (n:name β), name α + unit.

Definition maybe {A C} (f:A -> C) (c:C) (x:A + unit) : C :=
match x with
| inl a => f a
| inr _ => c
end.
Definition compose {A B C:Set} (f:A -> B) (g:B -> C) (a:A) : C
 := g (f a). 
Notation "f ○ g" := (compose g f) (at level 10).

Inductive tp :=
| one : tp
| arrow : tp -> tp -> tp
| prod : tp -> tp -> tp.

Set Implicit Arguments.
Inductive exp (α:world) : Set :=
| tt : exp α
| lam : forall β, α↪β -> tp -> exp β -> exp α
| app : exp α -> exp α -> exp α
| fst : exp α -> exp α
| snd : exp α -> exp α
| pair : exp α -> exp α -> exp α.
Implicit Arguments tt [α].

Definition ctx γ := name γ -> tp.

Notation "Γ ,, ( x , T )" := ((maybe Γ T) ○ (export x)) (at level 90).

Reserved Notation "Γ ⊢ E ⇐ T" (at level 90).

Inductive of {γ} (Γ:ctx γ) : exp γ -> tp -> Prop :=
| tt_of : Γ ⊢ tt ⇐ one
| lam_of : forall γ' (x:γ↪γ') T S M,
          Γ,,(x,T) ⊢ M ⇐ S
        (*============================== *) ->
          Γ ⊢ lam x T M ⇐ arrow T S
| app_of : forall T S M N,
          Γ ⊢ M ⇐ arrow T S ->
          Γ ⊢ N ⇐ T 
        (*===============================*) ->
          Γ ⊢ app M N ⇐ S
| fst_of : forall T S M,
          Γ ⊢ M ⇐ prod T S
        (*===============================*) ->
          Γ ⊢ fst M ⇐ T
| snd_of : forall T S M,
          Γ ⊢ M ⇐ prod T S
        (*===============================*) ->
          Γ ⊢ snd M ⇐ S
| pair_of : forall T S M N,
          Γ ⊢ M ⇐ T ->
          Γ ⊢ N ⇐ S
        (*===============================*) ->
          Γ ⊢ pair M N ⇐ prod T S
where "Γ ⊢ E ⇐ T" := (@of _ Γ E T).

