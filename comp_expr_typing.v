Require Import List.
Require Import worlds.
Require Import meta_term.
Require Import meta_subst.
Require Import meta_subst_typing.
Require Import type_assign.
Require Import comp_expr.
Require Import meta_subst_type.
Require Import meta_subst_type_assign.
Require Import meta_subst_meta_type.

(* TODO. Is this even possible? Should it produce a world D2 and link? *)
 Axiom import_tp : forall {D1 D2:world} (y:slink D1 D2) (T:tp D1), tp D2.

 Definition weaken_ctx : forall {D1 D2 G}, slink D1 D2 -> tp_assign D1 G -> tp_assign D2 G.
 intros. induction H0.
 constructor.
 econstructor.
 eexact IHstar.
 destruct r.
 constructor.
 exact s.
 eapply import_tp.
 eexact H.
 exact t.
 Defined.

Reserved Notation "D1 ; G1 ⊢ t1 ⇐ T1" (at level 90).
Reserved Notation "D1 ; G1 ⊢ t1 ⇒ T2" (at level 90).

Inductive s_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign δ γ}
                   : synth_exp δ γ -> tp δ -> Prop :=
  | var_s : forall x T,
             var_assigned Γ x T
           -> Δ;Γ ⊢ (var _ x) ⇒ T
  | app_s : forall I T1 E T2,
              Δ;Γ ⊢ I ⇒ (arr T1 T2)
           -> Δ;Γ ⊢ E ⇐ T1
           -> Δ;Γ ⊢ (app I E) ⇒ T2
  | mapp_s : forall I δ' (X:wlink δ δ') U C T,
              Δ;Γ ⊢ I ⇒ (prod X U T)
           -> Δ ⊨ C ∷ U
           -> Δ;Γ ⊢ (mapp I C) ⇒ (msubst_single_t X C T)
  | coerce_s : forall E T,
              Δ;Γ ⊢ E ⇐ T
           -> Δ;Γ ⊢ (coercion E T) ⇒ T
 with c_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign δ γ}
                   : checked_exp δ γ -> tp δ -> Prop :=
  | synth_c : forall I T,
              Δ;Γ ⊢ I ⇒ T
           -> Δ;Γ ⊢ I ⇐ T
  | meta_c : forall C U,
              Δ ⊨ C ∷ U 
           -> Δ;Γ ⊢ (meta γ C) ⇐ U
  | fn_c : forall γ' (y:slink γ γ') E T1 T2,
             Δ;(v_cons Γ (y,T1)) ⊢ E ⇐ T2
          -> Δ;Γ ⊢ (fn y E) ⇐ (arr T1 T2)
  | mlam_c : forall δ' (X:slink δ δ') E U T,
             (m_cons Δ (X,U));(weaken_ctx X Γ) ⊢ E ⇐ T
          -> Δ;Γ ⊢ (mlam X E) ⇐ (prod X U T)
  | case_i_c : forall I U Bs T,
             Δ;Γ ⊢ I ⇒ U
          -> (forall B, In B Bs -> br_tp B (arr U T))
          -> Δ;Γ ⊢ (case_i I Bs) ⇐ T
  | rec_c : forall γ' (f:slink γ γ') E T,
             Δ;(v_cons Γ (f,T)) ⊢ E ⇐ T
          -> Δ;Γ ⊢ (rec f E) ⇐ T
 with br_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign δ γ}
                     : branch δ γ -> tp δ -> Prop :=
  | br_c : forall δi (C:meta_term δi) (θi:msubst δ δi)
                  (E:checked_exp δi γ) (U T:mtype δ)
                  (Δi:mtype_assign δi),
             Δi ⊨ C ∷ ⟦θi⟧ U
          -> Δi ⊩ θi ∷ Δ
          -> Δi;(app_msubst_tp_assign θi Γ) ⊢ E ⇐ (app_msubst_t θi T)
          -> br_tp (br C θi E) (arr U T)
  where "D1 ; G1 ⊢ t1 ⇒ T1" := (@s_tp _ _ D1 G1 t1 T1)
  and   "D1 ; G1 ⊢ t1 ⇐ T1" := (@c_tp _ _ D1 G1 t1 T1).
 
Implicit Arguments c_tp.