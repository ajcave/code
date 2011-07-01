Require Import divergence.
Require Import subj_red.
Require Import Coq.Program.Equality.
Set Implicit Arguments.

Hint Constructors extended_val val.

Axiom classical : forall P, P \/ ~P.

Hint Constructors eval div.

Ltac doesItConverge E θ ρ :=
 let V := fresh "V" in
 let H := fresh "H" in
 destruct (classical (exists V, E[θ;;ρ] ⇓ V)) as [ (V, H) | H ].

Theorem progress : forall {δ γ} θ ρ
(E:checked_exp δ γ) T,
   clos_tp E θ ρ T
-> (forall V, (E[θ;;ρ] ⇓ V) -> False)
-> E[θ;;ρ] ⇑.
cofix. intros. invert_typing. nice_inversion H6;
try (econstructor; by eauto);
try (edestruct H0; by eauto).

(* synth *)
nice_inversion H. nice_inversion H1.

(* var *)
pose proof (env_tp_app x H8).
remember (ρ x).
destruct e.
edestruct H0. eauto.
nice_inversion H3. nice_inversion H15. nice_inversion H13.
econstructor; by eauto.

(* app *)
doesItConverge I0 θ ρ.
doesItConverge E θ ρ.

assert (V ∈ (〚θ〛(arr T1 (add_eq Cs T0)))) by eauto using @subj_red.
assert (V0 ∈ (〚θ〛T1)) by eauto using @subj_red.
nice_inversion_clear H5; invert_typing; try discriminate.
nice_inversion H17.
eapply div_app3; eauto.
eapply progress; eauto.
econstructor; eauto.
erewrite compose_cons.
eapply env_tp_cons; eauto.
rewrite H5.
econstructor.
firstorder.
eapply div_app2; by eauto 7.
eapply div_app1. eapply progress; by eauto.

(* mapp *)
doesItConverge I0 θ ρ.
assert (V ∈ (〚θ〛(pi X U T))) by eauto using @subj_red.
nice_inversion_clear H4; invert_typing; try discriminate.
eapply div_mapp2; eauto.
nice_inversion H17.
eapply progress; eauto.
econstructor; eauto.
erewrite cons_import_mvar. by eauto.
eapply div_mapp1; eapply progress; by eauto 7.

(* coercion *)
econstructor. by eauto. 

(* unfold *)
econstructor.
eapply progress; eauto.
intros v Hy.
assert (v ∈ (〚θ〛(tapp (mu Z X U T) C))) by eauto using @subj_red.
nice_inversion_clear H2; invert_typing; try discriminate.
by eauto.

(* rec *)
econstructor.
eapply progress; eauto.
econstructor; eauto.
erewrite compose_cons.
by eauto.

(* pair *)
doesItConverge E1 θ ρ.
eapply div_pair2; by eauto.
eapply div_pair1; by eauto.

(* case *)
doesItConverge I θ ρ.
clear progress. admit. (* TODO: Coverage *)
eapply div_caseI. eapply progress; eauto.
Qed.

Lemma dot_subst_typing : · ⊩ · ∷ ·.
intro. edestruct (empty_is_empty x).
Qed.

Lemma dot_env_typing Δ : ⊪ · ⇐ Δ.
econstructor. intro. edestruct (empty_is_empty x).
Qed.
Hint Resolve dot_subst_typing dot_env_typing.

Theorem progress' : forall E T,
   ·;· ⊢ E ⇐ T
-> (exists V, E[·;;·] ⇓ V) \/ E[·;;·] ⇑.
intros.
destruct (classical (exists V, E[·;;·] ⇓ V)); eauto.
right. eapply progress; eauto.
Qed.
Print Assumptions progress'.
