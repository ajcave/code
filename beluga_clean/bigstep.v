Require Export comp.

Inductive extended_val : checked_exp ∅ ∅ -> Prop :=
| ext_val_val : forall V, val V -> extended_val V
| ext_val_rec : forall δ γ γ' (f:γ↪γ') (E:checked_exp δ γ') θ ρ,
       val_env ρ -> src_lang E -> extended_val ((rec f E)[θ;;ρ])
with val_env : forall {γ} (ρ:env γ), Prop :=
| is_val_env : forall γ (ρ:env γ),
               (forall x, extended_val (ρ x))
            -> val_env ρ
with val : checked_exp ∅ ∅ -> Prop :=
| val_tt : val tt
| val_fold : forall E, val E -> val (fold E)
| val_inl : forall E, val E -> val (inl E)
| val_inr : forall E, val E -> val (inr E)
| val_pair : forall E1 E2, val E1 -> val E2 -> val (pair E1 E2)
| val_pack : forall E C, val E -> val (pack C E)
| val_fn : forall δ' γ' γ'' (y:γ'↪γ'') (E:checked_exp δ' γ'') θ ρ,
           val_env ρ -> src_lang E -> val ((fn y E)[θ;;ρ])
| val_mlam : forall δ' δ'' γ' (X:δ'↪δ'')(E:checked_exp δ'' γ') θ ρ,
           val_env ρ -> src_lang E -> val ((mlam X E)[θ;;ρ])
| val_meta : forall C, val (meta _ C)
.
Reserved Notation "E [ θ ;; ρ ] ⇓ V" (at level 0).
Inductive eval  {δ γ} (θ:msubst δ ∅) (ρ:name γ -> checked_exp ∅ ∅) : checked_exp δ γ -> checked_exp ∅ ∅ -> Prop :=
 | ev_coerce : forall (E:checked_exp δ γ) T V,
             E [θ ;; ρ] ⇓ V
          -> (coercion E T) [θ ;; ρ] ⇓ V
 | ev_app : forall (I1:synth_exp δ γ) γ' γ''
  (y:γ' ↪ γ'') δ'
  (E:checked_exp δ' γ'') θ' ρ' (E2:checked_exp δ γ) V2 V,
             I1 [θ ;; ρ] ⇓ ((fn y E) [θ' ;; ρ'])
          -> E2 [θ ;; ρ] ⇓ V2
          -> E [θ' ;; (ρ' ,, (y,V2))] ⇓ V
          -> (app I1 E2) [θ ;; ρ] ⇓ V
 | ev_mapp : forall (I:synth_exp δ γ) δ' δ'' γ'
  (X:δ' ↪ δ'') (E:checked_exp δ'' γ') θ' ρ' C V,
             I [θ ;; ρ] ⇓ ((mlam X E) [θ';; ρ'])
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
 | ev_var1 : forall (y:name γ) δ' γ' (W:checked_exp δ' γ') θ' ρ' V,
            ρ y = (W[θ';;ρ'])
         -> W[θ';;ρ'] ⇓ V
         -> (var _ y) [θ ;; ρ] ⇓ V
 | ev_var2 : forall (y:name γ) V1,
            ρ y = V1
         -> val V1
         -> (var _ y) [θ ;; ρ] ⇓ V1
 | ev_rec : forall γ' (f:γ↪γ') (E:checked_exp δ γ') V,
       E [ θ ;; ρ ,, (f, (rec f E)[θ;;ρ]) ] ⇓ V
    -> (rec f E) [θ ;; ρ] ⇓ V
 | ev_inl : forall E V,
            E[θ;;ρ] ⇓ V
         -> (inl E)[θ;;ρ] ⇓ (inl V)
 | ev_inr : forall E V,
            E[θ;;ρ] ⇓ V
         -> (inr E)[θ;;ρ] ⇓ (inr V)
 | ev_pair : forall E1 E2 V1 V2,
            E1[θ;;ρ] ⇓ V1
         -> E2[θ;;ρ] ⇓ V2
         -> (pair E1 E2)[θ;;ρ] ⇓ (pair V1 V2)
 | ev_pack : forall C E V,
            E[θ;;ρ] ⇓ V
         -> (pack C E)[θ;;ρ] ⇓ (pack (〚θ〛C) V)
 | ev_fold : forall E V,
            E[θ;;ρ] ⇓ V
         -> (fold E)[θ;;ρ] ⇓ (fold V)
 | ev_unfold : forall I V,
            (synth I)[θ;;ρ] ⇓ (fold V)
         -> (unfold I)[θ;;ρ] ⇓ V
 | ev_meta : forall (C:meta_term δ),
            (meta γ C)[θ;;ρ] ⇓ (meta ∅ (〚θ〛C))
 | ev_fn : forall γ' (y:γ↪γ') (E:checked_exp δ γ'), 
            (fn y E)[θ;;ρ] ⇓ ((fn y E)[θ;;ρ])
 | ev_mlam : forall δ' (X:δ↪δ') (E:checked_exp δ' γ),
            (mlam X E)[θ;;ρ] ⇓ ((mlam X E)[θ;;ρ])
 | ev_tt : tt[θ;;ρ] ⇓ tt 
where "E [ θ ;; ρ ] ⇓ V" := (@eval _  _ θ ρ E V).

(* TODO: We can simplify this definition by making it a 3 (4) place predicate, so we don't have to quantify over θ and ρ every time *)
