Require Export util.
Set Implicit Arguments.

Axiom mtype : world -> Set.
Axiom meta_term : world -> Set.
Axiom m_var : forall δ, name δ -> meta_term δ.
Coercion m_var : name >-> meta_term.

Definition mtype_assign δ := name δ -> mtype δ.

Axiom m_oft : forall {δ:world} (Δ:mtype_assign δ), meta_term δ -> mtype δ -> Prop.
Notation "D ⊨ t ∷ U" := (m_oft D t U) (at level 90).

Definition msubst δ δ' := name δ -> meta_term δ'.

Axiom app_msubst : forall {δ δ'}, (msubst δ δ') -> meta_term δ -> meta_term δ'.
Axiom app_msubst_assoc : forall {δ} (t:meta_term δ)
 {δ'} (θ:msubst δ δ') {δ''} (θ':msubst δ' δ''),
 app_msubst θ' (app_msubst θ t) =
 app_msubst (app_msubst θ' ○ θ) t.

Class substitutable (A:world -> Set) := {
   app_subst : forall {α β}, msubst α β -> A α -> A β ;
   assoc : forall {α} (t:A α) {β} (θ:msubst α β) {γ} (θ':msubst β γ), app_subst θ' (app_subst θ t) = app_subst (app_msubst θ' ○ θ) t
 }.
Notation "〚 θ 〛" := (app_subst θ).

Axiom app_msubst_mtype : forall {δ δ'}, msubst δ δ' -> mtype δ -> mtype δ'.
Axiom app_msubst_mtype_assoc : forall {δ} (U:mtype δ)
 {δ'} (θ:msubst δ δ') {δ''} (θ':msubst δ' δ''),
  app_msubst_mtype θ' (app_msubst_mtype θ U) =
  app_msubst_mtype (app_msubst θ' ○ θ) U. 

Instance meta_term_substitutable : substitutable meta_term := {
   app_subst := @app_msubst;
   assoc := @app_msubst_assoc
 }.
Instance mtype_substitutable : substitutable mtype := {
  app_subst := @app_msubst_mtype;
  assoc := @app_msubst_mtype_assoc
 }.

Definition single_subst {γ γ'} (x:γ↪γ') {T} `{H:substitutable T} (N:meta_term γ) (M:T γ') :=
 〚@m_var γ,,(x,N)〛 M.

(* TODO: This may cause me trouble later *)
Definition msubst_oft {α} (Δ:mtype_assign α) {β} (Δ':mtype_assign β) θ := forall x, Δ' ⊨ (θ x) ∷ 〚θ〛(Δ x).
Notation "Δ' ⊩ θ ∷ Δ" := (@msubst_oft _ Δ _ Δ' θ) (at level 90).
