Require Import List.
Require Import util.
Require Import worlds.
Require Import meta_term.
Require Import meta_subst.
Require Import meta_subst_typing.
Require Import type_assign.
Require Import comp_expr.
Require Import meta_subst_type.
Require Import meta_subst_type_assign.
Require Import meta_subst_meta_type.

Reserved Notation "D1 ; G1 ⊢ t1 ⇐ T1" (at level 90).
Reserved Notation "D1 ; G1 ⊢ t1 ⇒ T2" (at level 90).

Inductive s_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign γ δ}
                   : synth_exp δ γ -> tp δ -> Prop :=
  | var_s : forall x T,
             Γ x = T
           -> Δ;Γ ⊢ (var _ x) ⇒ T
  | app_s : forall I T1 E T2,
              Δ;Γ ⊢ I ⇒ (arr T1 T2)
           -> Δ;Γ ⊢ E ⇐ T1
           -> Δ;Γ ⊢ (app I E) ⇒ T2
  | mapp_s : forall I δ' (X:δ↪δ') U C T,
              Δ;Γ ⊢ I ⇒ (pi X U T)
           -> Δ ⊨ C ∷ U
           -> Δ;Γ ⊢ (mapp I C) ⇒ (msubst_single_t X C T)
  | coerce_s : forall E T,
              Δ;Γ ⊢ E ⇐ T
           -> Δ;Γ ⊢ (coercion E T) ⇒ T
  | unfold_c : forall I δ' (X:δ↪δ') ψ (Z:∅↪ψ) U C T,
              Δ;Γ ⊢ I ⇒ (tapp (mu Z X U T) C) 
           -> Δ;Γ ⊢ unfold I ⇒ (app_tp_subst_single
                          (mu Z X U T) 
                          (msubst_single_t' X C T))
 with c_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign γ δ}
                   : checked_exp δ γ -> tp δ -> Prop :=
  | synth_c : forall I T,
              Δ;Γ ⊢ I ⇒ T
           -> Δ;Γ ⊢ I ⇐ T
  | meta_c : forall C U,
              Δ ⊨ C ∷ U 
           -> Δ;Γ ⊢ (meta γ C) ⇐ U
  | fn_c : forall γ' (y:γ↪γ') E T1 T2,
             Δ;(Γ,, (y,T1)) ⊢ E ⇐ T2
          -> Δ;Γ ⊢ (fn y E) ⇐ (arr T1 T2)
  | mlam_c : forall δ' (X:δ↪δ') E U T,
             (import_mtype X ○ (Δ,, (X,U)));(import_tp_assign X Γ) ⊢ E ⇐ T
          -> Δ;Γ ⊢ (mlam X E) ⇐ (pi X U T)
  | case_i_c : forall I U Bs T,
             Δ;Γ ⊢ I ⇒ U
          -> (forall B, In B Bs -> br_tp B (arr U T))
          -> Δ;Γ ⊢ (case_i I Bs) ⇐ T
  | rec_c : forall γ' (f:γ↪γ') E T,
             Δ;(Γ,, (f,T)) ⊢ E ⇐ T
          -> Δ;Γ ⊢ (rec f E) ⇐ T
  | inl_c : forall E T S,
             Δ;Γ ⊢ E ⇐ T
          -> Δ;Γ ⊢ (inl E) ⇐ (sum T S)
  | inr_c : forall E T S,
             Δ;Γ ⊢ E ⇐ S
          -> Δ;Γ ⊢ (inr E) ⇐ (sum T S)
  | pair_c : forall E1 E2 T S,
             Δ;Γ ⊢ E1 ⇐ T
          -> Δ;Γ ⊢ E2 ⇐ S
          -> Δ;Γ ⊢ (pair E1 E2) ⇐ (prod T S)
  | pack_c : forall E δ' (X:δ↪δ') U C T,
              Δ ⊨ C ∷ U
           -> Δ;Γ ⊢ E ⇐ (msubst_single_t X C T) 
           -> Δ;Γ ⊢ (pack C E) ⇐ (sigma X U T)
  | fold_c : forall E δ' (X:δ↪δ') ψ (Z:∅↪ψ) U C T,
              Δ;Γ ⊢ E ⇐ (app_tp_subst_single
                          (mu Z X U T) 
                          (msubst_single_t' X C T))
           -> Δ;Γ ⊢ fold E ⇐ (tapp (mu Z X U T) C)
  | tt_c : Δ;Γ ⊢ tt ⇐ unit
 with br_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign γ δ}
                     : branch δ γ -> tp δ -> Prop :=
  | br_c : forall δi (C:meta_term δi) (θi:msubst δ δi)
                  (E:checked_exp δi γ) (U T:mtype δ)
                  (Δi:mtype_assign δi),
             Δi ⊨ C ∷ ⟦θi⟧ U
          -> Δi ⊩ θi ∷ Δ
          -> Δi;(⟦θi⟧ Γ) ⊢ E ⇐ ⟦θi⟧T
          -> br_tp (br C θi E) (arr (m_tp' U) (m_tp' T))
  where "D1 ; G1 ⊢ t1 ⇒ T1" := (@s_tp _ _ D1 G1 t1 T1)
  and   "D1 ; G1 ⊢ t1 ⇐ T1" := (@c_tp _ _ D1 G1 t1 T1).
 
Implicit Arguments c_tp.