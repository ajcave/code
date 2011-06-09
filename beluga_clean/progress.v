Require Import divergence.
Require Import subj_red.
Set Implicit Arguments.

Inductive val {δ γ} : checked_exp δ γ -> Prop :=
| val_var : forall x, val (var δ x)
| val_tt : val tt
| val_fold : forall E, val E -> val (fold E)
| val_inl : forall E, val E -> val (inl E)
| val_inr : forall E, val E -> val (inr E)
| val_pair : forall E1 E2, val E1 -> val E2 -> val (pair E1 E2)
| val_pack : forall E C, val E -> val (pack C E)
| val_fn : forall δ' γ' γ'' (y:γ'↪γ'') (E:checked_exp δ' γ'') θ ρ,
           val ((fn y E)[θ;;ρ])
| val_mlam : forall δ' δ'' γ' (X:δ'↪δ'')(E:checked_exp δ'' γ') θ ρ,
           val ((mlam X E)[θ;;ρ])
| val_meta : forall C, val (meta _ C)
.

Hint Constructors val.
Lemma eval_to_val E V : E ⇓ V -> val V.
induction 1; eauto. inversion IHeval. eauto.
Qed.

Inductive canonical : checked_exp ∅ ∅ -> tp ∅ -> Prop :=
| canon_fn : forall δ γ γ' (y:γ↪γ') (E:checked_exp δ γ') θ ρ T S,
                 canonical ((fn y E)[θ;;ρ]) (arr T S)
| canon_mlam : forall δ δ' γ (X:δ↪δ') (E:checked_exp δ' γ) θ ρ U T,
                 canonical ((mlam X E)[θ;;ρ]) (pi ₁ U T)
| canon_fold : forall ψ δ (Z:∅↪ψ) (X:∅↪δ) E C U T,
                 canonical (fold E) (tapp (mu Z X U T) C)
| canon_tt : canonical tt unit
| canon_inl : forall E T S, canonical (inl E) (sum T S)
| canon_inr : forall E T S, canonical (inr E) (sum T S)
| canon_pair : forall E1 E2 T S, canonical (pair E1 E2) (prod T S)
| canon_pack : forall δ (X:∅↪δ) C E U T,
                  canonical (pack C E) (sigma X U T)
| canon_meta : forall C U, canonical (meta _ C) (m_tp' U)
.

Hint Constructors canonical.

Lemma canonical_forms V T : val V -> ·;· ⊢ V ⇐ T -> canonical V T.
intros. nice_inversion H; invert_typing; simpl; eauto.
edestruct empty_is_empty; eauto.
Qed.

Lemma canonical_forms' δ γ θ ρ (E:checked_exp δ γ) V :
   E[θ;;ρ] ⇓ V
-> forall Δ Γ, (· ⊩ θ ∷ Δ)
-> (·;· ⊪ ρ ⇐ (〚θ〛 ○ Γ))
-> forall T, Δ;Γ ⊢ E ⇐ T
-> canonical V (〚θ〛T).
intros.
eapply canonical_forms.
eapply eval_to_val; eauto.
eapply subj_red; eauto.
Qed.
Hint Resolve canonical_forms'.

Axiom classical : forall P, P \/ ~P.

Hint Constructors eval div.

Ltac doesItConverge E :=
 let V := fresh "V" in
 let H := fresh "H" in
 destruct (classical (exists V, E ⇓ V)) as [ (V, H) | H ].

Ltac canonical :=
match goal with
| [ H : ?E[?θ;;_] ⇓ ?V,
    H0 : _;_ ⊢ ?E ⇐ ?T |- _] =>
     assert (·;· ⊢ V ⇐ (〚θ〛T)) by eauto using subj_red; 
     assert (canonical V (〚θ〛T)) by eauto; clear H0
| [ H : (synth ?I)[?θ;;_] ⇓ ?V,
    H0 : _;_ ⊢ ?I ⇒ ?T |- _] =>
     assert (·;· ⊢ V ⇐ (〚θ〛T)) by eauto using subj_red;
     assert (canonical V (〚θ〛T)) by eauto; clear H0
end.

Theorem progress : forall {δ γ} θ ρ (E:checked_exp δ γ) T,
   ·;· ⊢ E[θ;;ρ] ⇐ T
-> (forall V, ~ (E[θ;;ρ] ⇓ V))
-> E[θ;;ρ] ⇑.
cofix. intros. invert_typing. nice_inversion H7.

(* synth *)
nice_inversion H.

(* var *)
clear progress.
admit. (* TODO *)

(* app *)
doesItConverge (I0[θ;;ρ]).
doesItConverge (E[θ;;ρ]).
repeat canonical. nice_inversion H10. invert_typing.
nice_inversion H16.
doesItConverge (E0[θ0;;(ρ0,,(y,V0))]).
edestruct H0. by eauto.
eapply div_app3; eauto. 
eapply progress.
econstructor. eauto.  eauto.
erewrite compose_cons.
eapply env_tp_cons.
eauto.
rewrite H1. by eauto.
by eauto.
eapply div_app2; eauto 7.
eapply div_app1; eauto 7.

(* mapp *)
doesItConverge (I0[θ;;ρ]).
canonical. nice_inversion H5. invert_typing. nice_inversion H14.
doesItConverge (E[θ0,,(X0,〚θ〛C);;ρ0]).
edestruct H0; eauto.
eapply div_mapp2; eauto.
eapply progress. econstructor.
by eauto. by eauto. erewrite cons_import_mvar. by eauto.
by eauto.
eapply div_mapp1; eauto 7.

(* coercion *)
econstructor.
eapply progress; eauto.
intros v Hy.
eapply H0; eauto.

(* unfold *)
econstructor.
eapply progress; eauto.
intros v Hy.
assert (canonical v (〚θ〛(tapp (mu Z X U T) C))) as Hy0 by eauto. (* TODO: Auto *)
  nice_inversion Hy0.
eapply H0; by eauto.

(* meta *)
edestruct H0; by eauto.

(* fn *)
edestruct H0; by eauto.

(* mlam *)
edestruct H0; by eauto.

(* rec *)
doesItConverge (E0 [θ;; ρ,, (f, (rec f E0) [θ;; ρ])]).
edestruct H0; by eauto.
econstructor.
eapply progress.
econstructor; eauto.
erewrite compose_cons.
by eauto.
by eauto.

(* inl *)
econstructor.
eapply progress; eauto.
intros v Hy.
eapply H0; by eauto.

(* inr *)
econstructor.
eapply progress; eauto.
intros v Hy.
eapply H0; by eauto.

(* pair *)
doesItConverge (E1[θ;;ρ]).
eapply div_pair2; eauto.
eapply progress; eauto.
intros v Hy. eapply H0; by eauto.
eapply div_pair1; eauto.
eapply progress; by eauto.

(* pack *)
econstructor.
eapply progress; eauto.
intros v Hy. 
eapply H0; by eauto.

(* fold *)
econstructor.
eapply progress; eauto.
intros v Hy.
eapply H0; by eauto.

(* tt *)
edestruct H0; by eauto.

clear progress.
admit.
Qed.