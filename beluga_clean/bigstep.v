Require Export comp.

Reserved Notation "E ⇓ V" (at level 90).
Inductive eval : checked_exp ∅ ∅ -> checked_exp ∅ ∅ -> Prop :=
 | ev_coerce : forall δ θ γ ρ (E:checked_exp δ γ) T V,
             E [θ ;; ρ] ⇓ V
          -> (coercion E T) [θ ;; ρ] ⇓ V
 | ev_app : forall δ θ γ ρ (I1:synth_exp δ γ) γ' γ''
  (y:γ' ↪ γ'')
  (E:checked_exp δ γ'') θ' ρ' (E2:checked_exp δ γ) V2 V,
             I1 [θ ;; ρ] ⇓ (fn y E) [θ' ;; ρ']
          -> E2 [θ ;; ρ] ⇓ V2
          -> E [θ' ;; (ρ' ,, (y,V2))] ⇓ V
          -> (app I1 E2) [θ ;; ρ] ⇓ V
 | ev_mapp : forall δ θ γ ρ (I:synth_exp δ γ) δ'
  (X:δ ↪ δ') (E:checked_exp δ' γ) θ' ρ' C V,
             I [θ ;; ρ] ⇓ (mlam X E) [θ';; ρ']
          -> E [(θ' ,, (X, (〚θ〛 C))) ;; ρ'] ⇓ V
          -> (mapp I C) [θ ;; ρ] ⇓ V
(* | ev_case1 : forall δ θ γ ρ (I:synth_exp δ γ) δi
  (θk:msubst δ δi) Bs Ck Ek V,
            (θ /≐ θk)
         -> case_i I Bs [θ ;; ρ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V
 | ev_case2 : forall δ θ γ ρ (I:synth_exp δ γ) δi
  (θk:msubst δ δi) θ' Bs (C:meta_term ∅) Ek V Ck,
            (θ ≐ θk // θ')
         -> I [θ ;; ρ] ⇓ meta_term_closure C
         -> (C /≑ ⟦θ'⟧ Ck)
         -> case_i I Bs [θ ;; ρ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V
 | ev_case3 : forall δ θ γ ρ (I:synth_exp δ γ) δi
 (θk:msubst δ δi) θ' θ'' Bs (C:meta_term ∅) Ek V Ck,
            (θ ≐ θk // θ')
         -> I [θ ;; ρ] ⇓ meta_term_closure C
         -> (C ≑ ⟦θ'⟧ Ck // θ'')
         -> Ek [ ⟦θ''⟧ θ' ;; ρ ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V *)
 | ev_var : forall δ (θ:msubst δ ∅) γ ρ (y:name γ) V1 V,
            ρ y = V1
         -> V1 ⇓ V
         -> (var _ y) [θ ;; ρ] ⇓ V
 | ev_rec : forall δ θ γ ρ γ' (f:γ↪γ') (E:checked_exp δ γ') V,
       E [ θ ;; ρ ,, (f, (rec f E)[θ;;ρ]) ] ⇓ V
    -> (rec f E) [θ ;; ρ] ⇓ V
 | ev_inl : forall δ (θ:msubst δ ∅) γ (ρ:env γ) E V,
            E[θ;;ρ] ⇓ V
         -> (inl E)[θ;;ρ] ⇓ (inl V)
 | ev_inr : forall δ (θ:msubst δ ∅) γ (ρ:env γ) E V,
            E[θ;;ρ] ⇓ V
         -> (inr E)[θ;;ρ] ⇓ (inr V)
 | ev_pair : forall δ (θ:msubst δ ∅) γ (ρ:env γ) E1 E2 V1 V2,
            E1[θ;;ρ] ⇓ V1
         -> E2[θ;;ρ] ⇓ V2
         -> (pair E1 E2)[θ;;ρ] ⇓ pair V1 V2
 | ev_pack : forall δ (θ:msubst δ ∅) γ (ρ:env γ) C E V,
            E[θ;;ρ] ⇓ V
         -> (pack C E)[θ;;ρ] ⇓ pack (〚θ〛C) V
where "E1 ⇓ V1" := (eval E1 V1).
