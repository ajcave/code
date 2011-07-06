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
 | div_case_coverage : forall (I:synth_exp δ γ) V,
            I [θ ;; ρ] ⇓ V
         -> (case_i I nil) [θ ;; ρ] ⇑
 | div_case3 : forall n (I:synth_exp δ γ) δi Δi Γi (ρ':vec val n)
 (θi:msubst δ δi) {δi'} θ' Bs pa Ei V1 (Δi':mtype_assign δi') θ'' ,
            (mgu Δi θ θi θ' Δi')
         -> I [θ ;; ρ] ⇓ V1
         -> (pmatch Δi' (· * (smap 〚θ'〛 Γi)) V1 (〚θ'〛pa) (· * ρ') θ'')
         -> Ei [ (〚θ''〛 ○ θ') ;; ρ * (smap evval ρ') ] ⇑
         -> (case_i I ((br _ Δi Γi pa θi Ei)::Bs)) [θ ;; ρ] ⇑
 | div_case1 : forall n (I:synth_exp δ γ) δi Δi Γi
 (θi:msubst δ δi) Bs (pa:pat (∅ + n) δi) Ei V1 ,
            (~(exists δi', exists θ', exists Δi' : mtype_assign δi', mgu Δi θ θi θ' Δi'))
         -> I [θ ;; ρ] ⇓ V1
         -> (case_i I Bs) [θ ;; ρ] ⇑
         -> (case_i I ((br _ Δi Γi pa θi Ei)::Bs)) [θ ;; ρ] ⇑
 | div_case2 : forall n (I:synth_exp δ γ) δi Δi Γi
 (θi:msubst δ δi) {δi'} θ' (Δi':mtype_assign δi') Bs (pa:pat (∅ + n) δi) Ei V1,
            (mgu Δi θ θi θ' Δi')
         -> I [θ ;; ρ] ⇓ V1
         -> (~(exists ρ', exists θ'', pmatch Δi' (· * (smap 〚θ'〛 Γi)) V1 (〚θ'〛pa) (· * ρ') θ''))
         -> (case_i I Bs) [θ ;; ρ] ⇑
         -> (case_i I ((br _ Δi Γi pa θi Ei)::Bs)) [θ ;; ρ] ⇑
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
where "E [ θ ;; ρ ] ⇑" := (@div _ _ θ ρ E).