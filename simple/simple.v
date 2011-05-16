Require Import Coq.Program.Equality.
Require Import worlds.
Require Import typing.
Set Implicit Arguments.
Inductive closure : Set :=
| clos : forall γ, exp γ -> (name γ -> closure) -> closure.
Definition env γ := name γ -> closure.
Notation "E [ ρ ]" := (clos E ρ) (at level 80).

Reserved Notation "C ∷ T" (at level 90).
Inductive closure_of : closure -> tp -> Prop :=
| clos_of : forall γ (M:exp γ) (Γ:tp_ctx γ) (ρ:env γ) T,
            (forall x, (ρ x) ∷ (Γ x)) ->
            Γ ⊢ M ⇐ T ->
          (*==============================*)
            M [ρ] ∷ T
where "C ∷ T" := (closure_of C T).

Lemma env_tp_cons {γ} (ρ:env γ) (Γ:tp_ctx γ) V T γ' (x:γ↪γ'):
     (forall y, ρ y ∷ Γ y)
  -> V ∷ T
  -> (forall y, (ρ,,(x,V)) y ∷ (Γ,,(x,T)) y).
intros. unfold compose.
destruct (export x y); firstorder.
Qed.

Inductive val : closure -> Prop :=
 | fn_val : forall γ γ' (x:γ↪γ') M T ρ,
      env_val ρ -> val ((lam x T M)[ρ])
 | tt_val : forall γ (ρ:env γ),
      env_val ρ -> val (tt[ρ])
 | inl_val : forall γ (ρ:env γ) M S,
      env_val ρ -> val (M[ρ])
   -> val ((inl S M)[ρ])
 | inr_val : forall γ (ρ:env γ) M T,
      env_val ρ -> val (M[ρ])
   -> val ((inr T M)[ρ])
with env_val : forall {γ}, env γ -> Prop :=
 | env_val_nil : env_val ·
 | env_val_cons : forall γ (ρ:env γ) γ' (x:γ↪γ') V,
      val V -> env_val (ρ,,(x,V)).

Reserved Notation "C ⇓ V" (at level 90).
Inductive eval : closure -> closure -> Prop :=
| val_eval : forall V,
          val V
        (*======*) ->
          V ⇓ V 
| var_eval : forall γ (ρ:env γ) x V V1,
          ρ x = V ->
          V ⇓ V1
        (*=========*) ->
          x[ρ] ⇓ V1
| app_eval : forall γ γ' γ'' (ρ:env γ) ρ' (x:γ'↪γ'') T M N M' V1 V2,
          M[ρ] ⇓ (lam x T M')[ρ'] ->
          N[ρ] ⇓ V1 ->
          M'[ρ',,(x,V1)] ⇓ V2
        (*========================*) ->
          (app M N)[ρ] ⇓ V2  
| inl_eval : forall γ γ' (ρ:env γ) (ρ':env γ') M V S,
          M[ρ] ⇓ V[ρ']
        (*========================*) ->
          (inl S M)[ρ] ⇓ (inl S V)[ρ']
| inr_eval : forall γ γ' (ρ:env γ) (ρ':env γ') M V T,
          M[ρ] ⇓ V[ρ']
        (*========================*) ->
          (inr T M)[ρ] ⇓ (inr T V)[ρ']
where "C ⇓ V" := (eval C V).

Tactic Notation "nice_inversion" hyp(H) := inversion H; subst; simpl_existTs; subst.
Tactic Notation "nice_inversion" integer(N) := inversion N; subst; simpl_existTs; subst.

Hint Constructors eval val closure_of.

Lemma val_env_val γ (ρ:env γ) V
 (H:val (V[ρ])) : env_val ρ.
nice_inversion H; eauto.
Qed.
Hint Resolve val_env_val.

Lemma eval_to_val C V : eval C V -> val V.
induction 1; eauto.
Qed.

Theorem subject_reduction C V : C ⇓ V -> forall T, C ∷ T -> V ∷ T.
induction 1; nice_inversion 1.
assumption.
nice_inversion H7.
apply IHeval. auto.
nice_inversion H8.
assert (lam x T M' [ρ'] ∷ (arrow T1 T0)); eauto.
nice_inversion H3.
nice_inversion H13.
apply IHeval3.
econstructor; eauto.
eapply env_tp_cons; eauto.
nice_inversion H6.
assert (V [ρ'] ∷ T0); eauto.
nice_inversion H1.
eauto.
nice_inversion H6.
assert (V [ρ'] ∷ S); eauto.
nice_inversion H1.
eauto.
Qed.