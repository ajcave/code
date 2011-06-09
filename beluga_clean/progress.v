Require Import divergence.
Require Import subj_red.
Require Import Coq.Program.Equality.
Set Implicit Arguments.

Hint Constructors extended_val val.

Lemma val_env_cons {γ γ'} (y:γ↪γ') (ρ:env γ) V :
   val_env ρ
-> extended_val V
-> val_env (ρ,,(y,V)).
intros.
nice_inversion H.
econstructor. intro.
unfold compose. destruct (export y x); unfold maybe; eauto.
Qed.
Hint Resolve @val_env_cons.

Inductive is_closure : checked_exp ∅ ∅ -> Prop :=
| is_clos : forall δ γ (E:checked_exp δ γ) θ ρ,
                 val_env ρ -> is_closure (E[θ;;ρ]).

Lemma only_closures_eval V1 V2 :
   extended_val V1
-> V1 ⇓ V2
-> is_closure V1. 
intros.
nice_inversion H0; nice_inversion H;
try match goal with 
| [ H : val (_[_;;_]) |- _] => nice_inversion H
end; eauto using is_clos.
Qed.

Lemma eval_to_val {γ δ} (E:checked_exp δ γ) θ ρ V :
val_env ρ -> E[θ;;ρ] ⇓ V -> val V.
intros.
dependent induction H0; eauto.

(* fn *)
assert (val (fn y E0)[θ';;ρ']) by eauto.
nice_inversion H0.
eapply IHeval3.
eapply val_env_cons. eexact H2.
econstructor.
eapply IHeval2.
eexact H.
eapply @refl_equal.
eapply @refl_equal.

(* mlam *)
assert (val (mlam X E0)[θ';;ρ']) by eauto.
nice_inversion H0. by eauto.

(* var *)
nice_inversion H.
specialize (H4 y).
pose proof (only_closures_eval H4 H0). nice_inversion H1.
by eauto.

(* rec *)
eapply IHeval.
eapply val_env_cons.
eexact H.
econstructor 2; eexact H.
by eapply @refl_equal.

(* fold *)
assert (val (fold V)) by eauto.
nice_inversion H1. by assumption.
Qed.
Hint Resolve @eval_to_val.

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
Qed.

Lemma canonical_forms' δ γ θ ρ (E:checked_exp δ γ) V :
   val_env ρ
-> E[θ;;ρ] ⇓ V
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
     assert (canonical V (〚θ〛T)) by eauto;
     assert (val V) by eauto; clear H0
| [ H : (synth ?I)[?θ;;_] ⇓ ?V,
    H0 : _;_ ⊢ ?I ⇒ ?T |- _] =>
     assert (·;· ⊢ V ⇐ (〚θ〛T)) by eauto using subj_red;
     assert (canonical V (〚θ〛T)) by eauto;
     assert (val V) by eauto; clear H0
end.

Theorem progress : forall {δ γ} θ ρ (Hyp:val_env ρ)
(E:checked_exp δ γ) T,
   ·;· ⊢ E[θ;;ρ] ⇐ T
-> (forall V, ~ (E[θ;;ρ] ⇓ V))
-> E[θ;;ρ] ⇑.
cofix. intros. invert_typing. nice_inversion H7.

(* synth *)
nice_inversion H.

(* var *)
nice_inversion Hyp. specialize (H3 x). inversion H3.
edestruct H0. eauto.
econstructor; eauto.
eapply progress; eauto.
rewrite H1. by eauto.
intros v Hy. eapply H0; by eauto.

(* app *)
doesItConverge (I0[θ;;ρ]).
doesItConverge (E[θ;;ρ]).
repeat canonical. nice_inversion H11. invert_typing.
nice_inversion H18.
doesItConverge (E0[θ0;;(ρ0,,(y,V0))]).
edestruct H0. by eauto.
eapply div_app3; eauto. 
eapply progress.
nice_inversion H12. by eauto.
econstructor; eauto.
erewrite compose_cons.
eapply env_tp_cons; eauto.
rewrite H1. by eauto.
by eauto.
eapply div_app2; by eauto 7.
eapply div_app1; by eauto 7.

(* mapp *)
doesItConverge (I0[θ;;ρ]).
canonical. nice_inversion H5. invert_typing. nice_inversion H15.
doesItConverge (E[θ0,,(X0,〚θ〛C);;ρ0]).
edestruct H0; eauto.
eapply div_mapp2; eauto.
eapply progress; eauto.
nice_inversion H6. by eauto.
econstructor; eauto.
erewrite cons_import_mvar. by assumption.
eapply div_mapp1; by eauto 7.

(* coercion *)
econstructor.
eapply progress; eauto.
intros v Hy.
eapply H0; by eauto.

(* unfold *)
econstructor.
eapply progress; eauto.
intros v Hy.
canonical. nice_inversion H3.
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
by eauto.
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

clear progress. admit. (* TODO *)
Qed.

Lemma dot_val_env : val_env ·.
econstructor. intro. edestruct (empty_is_empty x).
Qed.

Lemma dot_subst_typing : · ⊩ · ∷ ·.
intro. edestruct (empty_is_empty x).
Qed.

Lemma dot_env_typing Δ : ·; · ⊪ · ⇐ Δ.
intro. edestruct (empty_is_empty x).
Qed.
Hint Resolve dot_val_env dot_subst_typing dot_env_typing.

Theorem progress' : forall E T,
   ·;· ⊢ E ⇐ T
-> (exists V, E[·;;·] ⇓ V) \/ E[·;;·] ⇑.
intros.
destruct (classical (exists V, E[·;;·] ⇓ V)); eauto.
right. eapply progress; eauto.
Qed.