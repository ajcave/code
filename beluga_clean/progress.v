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
nice_inversion H3.
assert (V0 ∈ (〚θ〛T)) by eauto using @subj_red.
nice_inversion_clear H9; nice_inversion H12; nice_inversion H18; try discriminate. nice_inversion H16.
nice_inversion H17.
eapply div_app3; eauto.
eapply progress; eauto.
econstructor; eauto.
erewrite compose_cons.
eapply env_tp_cons; eauto.
rewrite H14. erewrite simpl_subst_add_eq'.
econstructor. eapply blah2.
by assumption.
nice_inversion H3. eapply div_app2; by eauto 7.
nice_inversion H3. eapply div_app1. eapply progress; by eauto.

(* mapp *)
doesItConverge I0 θ ρ. nice_inversion H3.
assert (V ∈ (〚θ〛(pi X U T))) by eauto using @subj_red.
nice_inversion_clear H10; nice_inversion H11; nice_inversion H17; nice_inversion H16.
eapply div_mapp2; eauto.
nice_inversion H15.
eapply progress; eauto.
econstructor; eauto.
erewrite cons_import_mvar. by eauto.
eapply div_mapp1; eapply progress; by eauto 7.

(* coercion *)
nice_inversion H2. econstructor; by eauto.

(* rec *)
nice_inversion H.
econstructor.
eapply progress; eauto.
econstructor; eauto.
erewrite compose_cons.
by eauto.

(* inl *)
nice_inversion H. econstructor; by eauto.

(* inr *)
nice_inversion H. econstructor; by eauto.

(* pair *)
nice_inversion H. nice_inversion H1.
doesItConverge E1 θ ρ.
eapply div_pair2; by eauto.
eapply div_pair1; by eauto.

(* pack *)
nice_inversion H1. econstructor; by eauto.

(* fold *)
nice_inversion H. econstructor; by eauto.

(* case *)
nice_inversion H.
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
intros. nice_inversion H.
destruct (classical (exists V, E[·;;·] ⇓ V)); eauto.
right. eapply progress; eauto.
Qed.
Print Assumptions progress'.
