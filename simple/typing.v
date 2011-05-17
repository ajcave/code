Require Import worlds.

Inductive tp :=
| one : tp
| arrow : tp -> tp -> tp
| sum : tp -> tp -> tp.

Set Implicit Arguments.
Inductive exp (α:world) : Set :=
| tt : exp α
| var : name α -> exp α
| lam : forall β, α↪β -> tp -> exp β -> exp α
| app : exp α -> exp α -> exp α
| inl : tp -> exp α -> exp α
| inr : tp -> exp α -> exp α
| case : exp α -> forall β, (α↪β) -> exp β ->
         forall γ, (α↪γ) -> exp γ -> exp α.
Implicit Arguments tt [α].
Coercion var : name >-> exp.

Definition tp_ctx γ := name γ -> tp.

Reserved Notation "Γ ⊢ E ⇐ T" (at level 90).

Inductive of {γ} (Γ:tp_ctx γ) : exp γ -> tp -> Prop :=
| tt_of : Γ ⊢ tt ⇐ one
| var_of : forall x T,
          Γ x = T
        (*===============================*) ->
          Γ ⊢ x ⇐ T
| lam_of : forall γ' (x:γ↪γ') T S M,
          Γ,,(x,T) ⊢ M ⇐ S
        (*===============================*) ->
          Γ ⊢ lam x T M ⇐ arrow T S
| app_of : forall T S M N,
          Γ ⊢ M ⇐ arrow T S ->
          Γ ⊢ N ⇐ T 
        (*===============================*) ->
          Γ ⊢ app M N ⇐ S
| inl_of : forall T S M,
          Γ ⊢ M ⇐ T
        (*===============================*) ->
          Γ ⊢ inl S M ⇐ (sum T S)
| inr_of : forall T S M,
          Γ ⊢ M ⇐ S
        (*===============================*) ->
          Γ ⊢ inr T M ⇐ (sum T S)
| case_of : forall α β(x:γ↪α)(y:γ↪β)T S U M N1 N2,
          Γ ⊢ M ⇐ (sum T S) ->
          Γ,,(x,T) ⊢ N1 ⇐ U ->
          Γ,,(y,S) ⊢ N2 ⇐ U
        (*===============================*) ->
          Γ ⊢ (case M x N1 y N2) ⇐ U
where "Γ ⊢ E ⇐ T" := (@of _ Γ E T).
Hint Constructors of.