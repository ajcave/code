Require Export comp.

Definition mgu {δ δi δi'} (Δi : mtype_assign δi) 
 (θ : msubst δ ∅) (θi : msubst δ δi) (θ' : msubst δi δi') (Δi' : mtype_assign δi') : Prop
 := (〚empty_initial _〛 ○ θ = 〚θ'〛 ○ θi) /\ (Δi' ⊩ θ' ∷ Δi).
(* TODO: This is missing the MGU part, which is important for progress *)

Definition pmatch {δ γ} (Δ : mtype_assign δ) (Γ : tp_assign γ δ)(V : val) pa (ρ:name γ -> val)
 (θ : msubst δ ∅) : Prop
 := (V = psubst ρ (〚θ〛 pa)) /\ (⊪ ρ ⇐ (〚θ〛 ○ Γ)).

Reserved Notation "E [ θ ;; ρ ] ⇓ V" (at level 0).
Inductive eval  {δ γ} (θ:msubst δ ∅) (ρ:name γ -> extended_val) : checked_exp δ γ -> val -> Prop :=
 | ev_coerce : forall (E:checked_exp δ γ) T V,
             E [θ ;; ρ] ⇓ V
          -> (coercion E T) [θ ;; ρ] ⇓ V
 | ev_app : forall (I1:synth_exp δ γ) γ' γ''
  (y:γ' ↪ γ'') δ'
  (E:checked_exp δ' γ'') θ' ρ' (E2:checked_exp δ γ) V2 V,
             I1 [θ ;; ρ] ⇓ (vfn y E θ' ρ')
          -> E2 [θ ;; ρ] ⇓ V2
          -> E [θ' ;; (ρ' ,, (y,V2))] ⇓ V
          -> (app I1 E2) [θ ;; ρ] ⇓ V
 | ev_mapp : forall (I:synth_exp δ γ) δ' δ'' γ'
  (X:δ' ↪ δ'') (E:checked_exp δ'' γ') θ' ρ' C V,
             I [θ ;; ρ] ⇓ (vmlam X E θ' ρ')
          -> E [(θ' ,, (X, (〚θ〛 C))) ;; ρ'] ⇓ V
          -> (mapp I C) [θ ;; ρ] ⇓ V
 | ev_var1 : forall (y:name γ) δ' γ' γ'' (f:γ'↪γ'') (E:checked_exp δ' γ'') θ' ρ' V,
            ρ y = (evrec f E θ' ρ')
         -> (rec f E)[θ';;ρ'] ⇓ V
         -> (var _ y) [θ ;; ρ] ⇓ V
 | ev_var2 : forall (y:name γ) V1,
            ρ y = (evval V1)
         -> (var _ y) [θ ;; ρ] ⇓ V1
 | ev_rec : forall γ' (f:γ↪γ') (E:checked_exp δ γ') V,
       E [ θ ;; ρ ,, (f, (evrec f E θ ρ))] ⇓ V
    -> (rec f E) [θ ;; ρ] ⇓ V
 | ev_inl : forall E V,
            E[θ;;ρ] ⇓ V
         -> (inl E)[θ;;ρ] ⇓ (vinl V)
 | ev_inr : forall E V,
            E[θ;;ρ] ⇓ V
         -> (inr E)[θ;;ρ] ⇓ (vinr V)
 | ev_pair : forall E1 E2 V1 V2,
            E1[θ;;ρ] ⇓ V1
         -> E2[θ;;ρ] ⇓ V2
         -> (pair E1 E2)[θ;;ρ] ⇓ (vpair V1 V2)
 | ev_pack : forall C E V,
            E[θ;;ρ] ⇓ V
         -> (pack C E)[θ;;ρ] ⇓ (vpack (〚θ〛C) V)
 | ev_fold : forall E V,
            E[θ;;ρ] ⇓ V
         -> (fold E)[θ;;ρ] ⇓ (vfold V)
 | ev_meta : forall (C:meta_term δ),
            (meta γ C)[θ;;ρ] ⇓ (vmeta (〚θ〛C))
 | ev_fn : forall γ' (y:γ↪γ') (E:checked_exp δ γ'), 
            (fn y E)[θ;;ρ] ⇓ (vfn y E θ ρ)
 | ev_mlam : forall δ' (X:δ↪δ') (E:checked_exp δ' γ),
            (mlam X E)[θ;;ρ] ⇓ (vmlam X E θ ρ)
 | ev_tt : tt[θ;;ρ] ⇓ vtt 
 | ev_case3 : forall n (I:synth_exp δ γ) δi Δi Γi (ρ':vec val n)
 (θi:msubst δ δi) {δi'} θ' Bs pa Ei V1 V (Δi':mtype_assign δi') θ'' ,
            (mgu Δi θ θi θ' Δi')
         -> I [θ ;; ρ] ⇓ V1
         -> (pmatch Δi' (· * (smap 〚θ'〛 Γi)) V1 (〚θ'〛pa) (· * ρ') θ'')
         -> Ei [ (〚θ''〛 ○ θ') ;; ρ * (smap evval ρ') ] ⇓ V
         -> (case_i I ((br _ Δi Γi pa θi Ei)::Bs)) [θ ;; ρ] ⇓ V
 | ev_case1 : forall n (I:synth_exp δ γ) δi Δi Γi
 (θi:msubst δ δi) Bs (pa:pat (∅ + n) δi) Ei V1 V ,
            (~exists θ', θ = 〚θ'〛 ○ θi)
         -> I [θ ;; ρ] ⇓ V1
         -> (case_i I Bs) [θ ;; ρ] ⇓ V
         -> (case_i I ((br _ Δi Γi pa θi Ei)::Bs)) [θ ;; ρ] ⇓ V
 | ev_case2 : forall n (I:synth_exp δ γ) δi Δi Γi
 (θi:msubst δ δi) θ' Bs (pa:pat (∅ + n) δi) Ei V1 V,
           (θ = 〚θ'〛 ○ θi)
         -> I [θ ;; ρ] ⇓ V1
         -> (~exists ρ', V1 = psubst (· * ρ') (〚θ'〛 pa))
         -> (case_i I Bs) [θ ;; ρ] ⇓ V
         -> (case_i I ((br _ Δi Γi pa θi Ei)::Bs)) [θ ;; ρ] ⇓ V
where "E [ θ ;; ρ ] ⇓ V" := (@eval _  _ θ ρ E V).

(* TODO: We can simplify this definition by making it a 3 (4) place predicate, so we don't have to quantify over θ and ρ every time *)
