Require Export bigstep.

Set Implicit Arguments.
Reserved Notation "E [ θ ;; ρ ] ⇑" (at level 0).
CoInductive div {δ γ} (θ:msubst δ ∅) (ρ:env γ) : checked_exp δ γ -> Prop :=
 | div_coerce : forall (E:checked_exp δ γ) T,
             E [θ ;; ρ] ⇑
          -> (coercion E T) [θ ;; ρ] ⇑
 | div_app1 : forall (I1:synth_exp δ γ)
  (E2:checked_exp δ γ),
             I1 [θ ;; ρ] ⇑
          -> (app I1 E2) [θ ;; ρ] ⇑
 | div_app2 : forall (I1:synth_exp δ γ) (E2:checked_exp δ γ) V,
             I1 [θ ;; ρ] ⇓ V
          -> E2 [θ ;; ρ] ⇑ 
          -> (app I1 E2) [θ ;; ρ] ⇑
 | div_app3 : forall (I1:synth_exp δ γ) γ' γ'' (y:γ' ↪ γ'') δ'
  (E:checked_exp δ' γ'') θ' ρ' (E2:checked_exp δ γ) V2,
             I1 [θ ;; ρ] ⇓ (vfn y E θ' ρ')
          -> E2 [θ ;; ρ] ⇓ V2
          -> E [θ' ;; (ρ' ,, (y,V2))] ⇑
          -> (app I1 E2) [θ ;; ρ] ⇑
 | div_mapp1 : forall (I:synth_exp δ γ) C,
             I [θ ;; ρ] ⇑
          -> (mapp I C) [θ ;; ρ] ⇑
 | div_mapp2 : forall (I:synth_exp δ γ) δ' δ'' γ'
  (X:δ' ↪ δ'') (E:checked_exp δ'' γ') θ' ρ' C,
             I [θ ;; ρ] ⇓ (vmlam X E θ' ρ')
          -> E [(θ' ,, (X, (〚θ〛 C))) ;; ρ'] ⇑
          -> (mapp I C) [θ ;; ρ] ⇑
 | div_caseI : forall (I:synth_exp δ γ) Bs,
            I [θ ;; ρ] ⇑
         -> (case_i I Bs) [θ ;; ρ] ⇑
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
 | div_var : forall (y:name γ) δ' γ' γ'' (E:checked_exp δ' γ'') (f:γ'↪γ'')
                    (θ':msubst δ' ∅) ρ',
            ρ y = (evrec f E θ' ρ')
         -> (rec f E)[θ';;ρ'] ⇑
         -> (var _ y) [θ ;; ρ] ⇑
 | div_rec : forall γ' (f:γ↪γ') (E:checked_exp δ γ'),
       E [ θ ;; ρ ,, (f, (evrec f E θ ρ)) ] ⇑
    -> (rec f E) [θ ;; ρ] ⇑
 | div_inl : forall E,
            E[θ;;ρ] ⇑
         -> (inl E)[θ;;ρ] ⇑
 | div_inr : forall E,
            E[θ;;ρ] ⇑
         -> (inr E)[θ;;ρ] ⇑
 | div_pair1 : forall E1 E2,
            E1[θ;;ρ] ⇑
         -> (pair E1 E2)[θ;;ρ] ⇑
 | div_pair2 : forall E1 E2 V1,
            E1[θ;;ρ] ⇓ V1
         -> E2[θ;;ρ] ⇑
         -> (pair E1 E2)[θ;;ρ] ⇑
 | div_pack : forall C E,
            E[θ;;ρ] ⇑
         -> (pack C E)[θ;;ρ] ⇑
 | div_fold : forall E,
            E[θ;;ρ] ⇑
         -> (fold E)[θ;;ρ] ⇑
 | ev_unfold : forall I,
            (synth I)[θ;;ρ] ⇑
         -> (unfold I)[θ;;ρ] ⇑ 
where "E [ θ ;; ρ ] ⇑" := (@div _ _ θ ρ E).