Require Import util.
Require Import worlds.
Require Import closures.
Require Import meta_term.
Require Import meta_subst.
Require Import comp_expr.
Require Import unification.

Reserved Notation "E ⇓ V" (at level 90).

Inductive val : closure -> Prop :=
 | fn_val : forall γ δ δ' (θ:msubst γ empty) (y:δ↪δ') E ρ,
      env_val ρ -> val ((fn y E)[θ;;ρ])
 | mlam_val : forall γ γ' δ θ (X:γ↪γ') E (ρ:env δ),
      env_val ρ -> val ((mlam X E)[θ;;ρ])
 | meta_term_val : forall C, val (meta_term_closure C)
with env_val : forall {δ}, env δ -> Prop :=
 | env_val_nil : env_val ·
 | env_val_cons : forall γ (ρ:env γ) γ' (y:γ↪γ') V,
      val V -> env_val (ρ,,(y,V))
.

Inductive eval : closure -> closure -> Prop :=
 | ev_val : forall V, val V -> eval V V 
 | ev_coerce : forall δ θ γ ρ (E:checked_exp δ γ) T V,
             E [θ ;; ρ] ⇓ V
          -> (coercion E T) [θ ;; ρ] ⇓ V
 | ev_app : forall δ θ γ ρ (I1:synth_exp δ γ) γ'
  (y:γ ↪ γ')
  (E:checked_exp δ γ') θ' ρ' (E2:checked_exp δ γ) V2 V,
             I1 [θ ;; ρ] ⇓ (fn y E) [θ' ;; ρ']
          -> E2 [θ ;; ρ] ⇓ V2
          -> E [θ' ;; (ρ' ,, (y,V2))] ⇓ V
          -> (app I1 E2) [θ ;; ρ] ⇓ V
 | ev_mapp : forall δ θ γ ρ (I:synth_exp δ γ) δ'
  (X:δ ↪ δ') (E:checked_exp δ' γ) θ' ρ' C V,
             I [θ ;; ρ] ⇓ (mlam X E) [θ';; ρ']
          -> E [(θ' ,, (X, (⟦θ⟧ C))) ;; ρ'] ⇓ V
          -> (mapp I C) [θ ;; ρ] ⇓ V
 | ev_case1 : forall δ θ γ ρ (I:synth_exp δ γ) δi
  (θk:msubst δ δi) Bs Ck Ek V,
            (θ /≐ θk)
         -> case_i I Bs [θ ;; ρ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V
 | ev_case2 : forall δ θ γ ρ (I:synth_exp δ γ) δi
  (θk:msubst δ δi) θ' Bs (C:meta_term empty) Ek V Ck,
            (θ ≐ θk // θ')
         -> I [θ ;; ρ] ⇓ meta_term_closure C
         -> (C /≑ ⟦θ'⟧ Ck)
         -> case_i I Bs [θ ;; ρ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V
 | ev_case3 : forall δ θ γ ρ (I:synth_exp δ γ) δi
 (θk:msubst δ δi) θ' θ'' Bs (C:meta_term empty) Ek V Ck,
            (θ ≐ θk // θ')
         -> I [θ ;; ρ] ⇓ meta_term_closure C
         -> (C ≑ ⟦θ'⟧ Ck // θ'')
         -> Ek [ ⟦θ''⟧ θ' ;; ρ ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V 
 | ev_var : forall δ (θ:msubst δ empty) γ ρ (y:name γ) V1 V,
            ρ y = V1
         -> V1 ⇓ V
         -> (var _ y) [θ ;; ρ] ⇓ V
 | ev_rec : forall δ θ γ ρ γ' (f:γ↪γ') (E:checked_exp δ γ') V,
       E [ θ ;; ρ ,, (f, (rec f E)[θ;;ρ]) ] ⇓ V
    -> rec f E [θ ;; ρ] ⇓ V
where "E1 ⇓ V1" := (eval E1 V1).

Theorem eval_val L V : L ⇓ V -> val V.
induction 1; assumption.
Qed.