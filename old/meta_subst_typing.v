Require Import util.
Require Import worlds.
Require Import meta_subst.
Require Import meta_term.
Require Import meta_subst_meta_type.
 Reserved Notation "D ⊩ T ∷ D2" (at level 90).
(* TODO: Write this directly... forall x, Delta |- theta x :: Delta' x *) 
 Inductive msubst_typ' {α}(Δ:mtype_assign α) : forall {β}(Δ':mtype_assign β), msubst β α ->Prop :=
  | m_subst_typ_nil :
           Δ ⊩ · ∷ ·
  | m_subst_typ_cons : forall β γ (Δ':mtype_assign β) (y:β ↪ γ) (U:mtype β) (t:meta_term α) (θ:msubst β α),
           Δ ⊩ θ ∷ Δ' 
        -> Δ ⊨ t ∷ (⟦θ⟧ U)
        -> Δ ⊩ (θ,, (y,t)) ∷ (import_mtype y ○ (Δ',,(y,U)))
  where "D ⊩ T ∷ D2" := (@msubst_typ' _ D _ D2 T).
 
Definition msubst_typ {α} (Δ:mtype_assign α) {β} (Δ':mtype_assign β) θ := msubst_typ' Δ' Δ θ.