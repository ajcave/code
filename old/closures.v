Require Import meta_term.
Require Import worlds.
Require Import comp_expr.
Require Import comp_expr_typing.
Require Import type_assign.
Require Import util.
Require Import meta_subst_typing.
Require Import meta_subst.

 Inductive closure : Set :=
  | meta_term_closure : meta_term ∅ -> closure
  | comp_term_closure : forall δ γ, checked_exp δ γ -> msubst δ ∅ -> (name γ -> closure) -> closure.
 Definition env γ := name γ -> closure.
 Implicit Arguments comp_term_closure.

 Notation "E [ θ ;; ρ ]" := (comp_term_closure E θ ρ) (at level 80).

 Reserved Notation "E ∷∷ T" (at level 90).

Definition env_tp {γ} (ρ:env γ) (Γ:tp_assign γ ∅)
  (oft:closure -> tp ∅ -> Prop) :=
  forall y, oft (ρ y) (Γ y).
Lemma env_tp_cons {γ} (ρ:env γ) (Γ:tp_assign γ ∅)
 oft V T γ' (x:γ↪γ'):
     env_tp ρ Γ oft
  -> oft V T
  -> env_tp (ρ,,(x,V)) (Γ,,(x,T)) oft.
unfold env_tp. intros. unfold compose.
destruct (export x y); firstorder.
Qed.

 Inductive closure_typ : closure -> tp ∅ -> Prop :=
  | meta_term_closure_typ : forall C U,
              (· ⊨ C ∷ U)
           -> (meta_term_closure C) ∷∷ U
  | comp_term_closure_typ : forall δ γ (Δ:mtype_assign δ) (Γ:tp_assign γ δ) E (T:tp δ) (θ:msubst δ ∅) (ρ:env γ),
                 · ⊩ θ ∷ Δ
              -> env_tp ρ (⟦θ⟧Γ) closure_typ
              -> Δ;Γ ⊢ E ⇐ T
              -> (E [θ ;; ρ]) ∷∷ (⟦θ⟧  T)
  where "E ∷∷ T" := (closure_typ E T).