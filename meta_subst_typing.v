Require Import util.
Require Import worlds.
Require Import meta_subst.
Require Import meta_term.
Require Import meta_subst_meta_type.
 Reserved Notation "D ⊩ T ∷ D2" (at level 90).
 Notation "T ;  t // y " := (msubst_cons T (y,t)) (at level 90).
 Notation "D ; y ∷ U" := (m_cons D (y,U)) (at level 90).
 Notation "·" := (s_nil).

 Inductive msubst_typ' {α}(Δ:mtype_assign α) : forall {β}(Δ':mtype_assign β), msubst β α ->Prop :=
  | m_subst_typ_nil :
           Δ ⊩ · ∷ ·
  | m_subst_typ_cons : forall β Δ' γ (y:β ↪ γ) U t θ,
           Δ ⊩ θ ∷ Δ' 
        -> Δ ⊨ t ∷ (⟦θ⟧ U)
        -> Δ ⊩ (θ; t//y) ∷ (Δ'; y∷U)
  where "D ⊩ T ∷ D2" := (@msubst_typ' _ D _ D2 T).
 
Definition msubst_typ {α} (Δ:mtype_assign α) {β} (Δ':mtype_assign β) θ := msubst_typ' Δ' Δ θ.