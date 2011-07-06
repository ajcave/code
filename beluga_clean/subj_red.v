Require Import ssreflect.
Require Export bigstep.
Require Import Coq.Program.Equality.
Set Implicit Arguments.

Ltac nice_inversion_clear H := nice_inversion H; clear H.

Ltac invert_typing_1 :=
match goal with
| [ H : _;_ ⊢ _ ⇐ _ |- _ ] => nice_inversion_clear H; [idtac]
| [ H : _;_ ⊢ _ ⇒ _ |- _ ] => nice_inversion_clear H; [idtac]
| [ H : clos_tp _ _ _ _ |- _] => nice_inversion_clear H; [idtac]
| [ H : _ ∈ _ |- _] => nice_inversion_clear H; [idtac] 
| [ H : branch_tp _ _ _ _ _ |- _] => nice_inversion_clear H; [idtac]
| [ H : extended_val_tp _ _ |- _] => nice_inversion_clear H; [idtac]
| [ H : checks_tp' _ _ _ _ |- _] => nice_inversion_clear H; [idtac]
| [ H : synth_tp' _ _ _ _ |- _] => nice_inversion_clear H; [idtac]
end.
Ltac invert_typing := repeat invert_typing_1.

Ltac normalize_subst := repeat (match goal with
| [ |- context f [@app_subst tp tp_substitutable ?δ ?δ' ?θ ?T] ] =>
 replace (@app_subst tp tp_substitutable δ δ' θ T) with
         (@app_subst (tp' ∅) (@tp_substitutable' ∅) δ δ' θ T) by reflexivity
| [ H : context f [@app_subst tp tp_substitutable ?δ ?δ' ?θ ?T] |- _ ] =>
 replace (@app_subst tp tp_substitutable δ δ' θ T) with
         (@app_subst (tp' ∅) (@tp_substitutable' ∅) δ δ' θ T) in H by reflexivity
end).

Hint Constructors synth_tp checks_tp synth_tp' checks_tp'.
Hint Resolve @subst_lemma.
Hint Resolve @subst_cons_typing @meta_type_eq @env_tp_cons.

Lemma blah2 V Cs T : V ∈ T -> V ∈ (add_eq Cs T).
intros.
induction Cs. assumption.
econstructor. eapply IHCs.
Qed.
Lemma blah3 V Cs T : V ∈ (add_eq Cs T) -> V ∈ T.
intros.
induction Cs. assumption.
nice_inversion H.
invert_typing. nice_inversion H6. 
invert_typing. nice_inversion H6.
by eauto.
Qed.
Lemma blah V Cs0 Cs1 T0 T1 : V ∈ T0 -> add_eq Cs0 T0 = add_eq Cs1 T1 -> V ∈ T1.
intros.
pose proof (blah2 Cs0 H).
rewrite H0 in H1.
eapply blah3; eauto.
Qed.
Lemma simpl_subst_add_eq {δ δ'} (θ:msubst δ δ') Cs (T:tp' ∅ δ) :
(@app_subst tp (@tp_substitutable) δ δ' θ (add_eq Cs T))
= add_eq (map 〚θ〛 Cs) (〚θ〛T).
induction Cs; simpl in *; congruence.
Qed.
Lemma simpl_subst_add_eq' {δ δ'} (θ:msubst δ δ') Cs (T:tp' ∅ δ) :
(@app_subst (@tp' empty) (@tp_substitutable' empty) δ δ' θ (add_eq Cs T))
= add_eq (map 〚θ〛 Cs) (〚θ〛T).
induction Cs; simpl in *; congruence.
Qed.
(*Hint Resolve blah blah2 blah3.*)

Theorem subj_red {δ γ} (L:checked_exp δ γ) θ ρ V :
L[θ;;ρ] ⇓ V -> forall T, (clos_tp L θ ρ T) -> (V ∈ T).
induction 1; intros; invert_typing.

(* Coercion *)
assert (V ∈ 〚θ〛T).
eapply IHeval. econstructor. eexact H2. eauto. eauto.
assert (〚θ〛(add_eq Cs0 T) = 〚θ〛(add_eq Cs T1)) by congruence.
repeat erewrite simpl_subst_add_eq' in H3.
eapply blah; by eauto.

(* app *)
assert (V2 ∈ 〚θ〛T) by eauto.
assert ((vfn y E θ' ρ') ∈ 〚θ〛(arr (add_eq Cs0 T) (add_eq Cs T0))) by eauto.
invert_typing.  nice_inversion H12.
assert (V ∈ 〚θ'〛T1).
eapply IHeval3. econstructor; eauto.
erewrite compose_cons. eapply env_tp_cons. by eassumption.
econstructor.
rewrite H7. erewrite simpl_subst_add_eq'. eapply blah2. by eauto.
repeat erewrite simpl_subst_add_eq' in H8.
eapply blah; by eauto.

(* mapp *)
assert ((vmlam X E θ' ρ') ∈ 〚θ〛(pi X0 U T)) by eauto.
invert_typing.
nice_inversion H11.
assert (V ∈ (〚θ',, (X,〚θ〛C) 〛 (add_eq Cs1 T1))).
erewrite simpl_subst_add_eq.
eapply blah2.
eapply IHeval2.
econstructor; eauto.
erewrite cons_import_mvar. by eassumption.
normalize_subst.
rewrite -> (common_var (〚θ〛C) H3) in H7.
erewrite <- msubst_over_single in H7.
erewrite <- assoc in H7.
erewrite H4 in H7.
normalize_subst.
erewrite simpl_subst_add_eq' in H7.
eapply blah3; by eauto.

(* Var (extended value) *)
unfold compose in *.
pose proof (env_tp_app' y H9 H).
invert_typing.
erewrite H3 in H7.
assert (V ∈ 〚θ'〛 (add_eq Cs0 T1)) by eauto.
normalize_subst.
repeat erewrite simpl_subst_add_eq' in H7, H2.
erewrite simpl_subst_add_eq' in H7.
eapply blah. eapply blah3. eexact H2. by eauto.

(* Var (value) *)
unfold compose in *.
pose proof (env_tp_app' y H8 H).
invert_typing.
rewrite H2 in H3.
normalize_subst. erewrite simpl_subst_add_eq' in H3.
eapply blah3; by eauto.

(* Rec *)
normalize_subst. erewrite simpl_subst_add_eq'. eapply blah2.
eapply IHeval.
econstructor; eauto.
erewrite compose_cons.
eapply env_tp_cons;
by eauto.

(* Inl *)
change (〚θ〛(sum (add_eq Cs T0) S)) with (sum (〚θ〛(add_eq Cs T0)) (〚θ〛S)).
econstructor.
erewrite simpl_subst_add_eq'. eapply blah2.
by eauto.

(* Inr *)
change (〚θ〛(sum T (add_eq Cs T0))) with (sum (〚θ〛T) (〚θ〛(add_eq Cs T0))).
econstructor.
erewrite simpl_subst_add_eq'. eapply blah2.
by eauto.

(* Pair *)
change (〚θ〛(prod (add_eq Cs0 T1) (add_eq Cs T0))) with (prod (〚θ〛(add_eq Cs0 T1)) (〚θ〛(add_eq Cs T0))).
econstructor; erewrite simpl_subst_add_eq'; eapply blah2; by eauto.

(* pack *)
change (〚θ〛(sigma X U T)) with (sigma ₁ (〚θ〛U) (〚θ × (₁//X)〛T)).
econstructor. by eauto.
erewrite single_subst_commute'.
erewrite <- H0. erewrite simpl_subst_add_eq. eapply blah2.
by eauto.

(* fold *)
change (〚θ〛(tapp (mu Z X U T) C)) with (tapp (mu (ψ:=empty) Z ₁ (〚θ〛 U) (〚θ ×  (₁ // X) 〛 T))
       (〚θ〛 C)).
econstructor.
erewrite single_subst_commute'.
change (mu Z ₁ (〚θ 〛 U) (〚θ ×  (₁ // X) 〛 T)) with (〚θ〛(mu (ψ:=empty) Z X U T)).
erewrite <- tp_subst_commute.
erewrite <- H0.
erewrite simpl_subst_add_eq. eapply blah2.
eapply IHeval.
by eauto.

(* meta *)
simpl. econstructor.
eapply subst_lemma; by eauto.

(* fn *)
econstructor. econstructor; by eauto.

(* mlam *)
econstructor. econstructor; by eauto.

(* tt *)
econstructor.

(* case. happy case *)
destruct H. destruct H1. subst.
assert ((psubst (· * ρ') (〚θ''〛 (〚θ'〛 pa))) ∈ 〚θ''〛 (〚〚θ'〛 ○ θi〛 U)).
eapply IHeval1. erewrite <- H. erewrite assoc. erewrite compose_assoc.
erewrite <- assoc''.
erewrite (empty_is_initial (〚θ'' 〛 ○ (empty_initial (meta_term δi'))) (@m_var _)).
erewrite mvar_left_unit. by eauto.

assert (branch_tp Δ Γ (br _ Δi Γi pa θi Ei) U T0) by firstorder.
invert_typing.
assert (〚〚θ''〛 ○ θ'〛 (add_eq Cs0 T) = 〚〚θ''〛 ○ θ'〛(〚θi〛 T0)) by congruence.
erewrite assoc in H8. change (〚(app_msubst (〚θ''〛 ○ θ') ○ θi) 〛 T0) with (〚〚〚θ''〛 ○ θ'〛 ○ θi 〛 T0) in H8. 
erewrite subst_assoc in H8. erewrite <- H in H8. erewrite compose_assoc in H8.
erewrite <- assoc' in H8.
erewrite (empty_is_initial (〚θ'' 〛 ○ (empty_initial (meta_term δi'))) (@m_var _)) in H8.
erewrite mvar_left_unit in H8.
erewrite <- H8.

erewrite simpl_subst_add_eq. eapply blah2.
eapply IHeval2.
destruct H5.
econstructor.
by eauto.
intro.
erewrite subst_assoc. unfold compose. eapply subst_lemma. eapply H4. by eauto.
erewrite compose_prod.
eapply env_tp_prod.

erewrite subst_assoc. rewrite (compose_assoc Γ 〚θi〛 〚θ'〛). erewrite <- assoc'. erewrite <- H.
erewrite <- subst_assoc. erewrite compose_assoc. erewrite <- assoc'.
erewrite (empty_is_initial (〚θ'' 〛 ○ (empty_initial (meta_term δi'))) (@m_var _)).
erewrite mvar_left_unit. by assumption.
erewrite assoc'. erewrite smap_functorial.
do 2 erewrite smap_coerce_functorial.
eexact H5.

(* case *)
eapply IHeval2.
econstructor; eauto.
econstructor; eauto. intros.
eapply H6; by firstorder.

(* case *)
eapply IHeval2.
econstructor; eauto.
econstructor; eauto. intros.
eapply H7; by firstorder.
Qed.

