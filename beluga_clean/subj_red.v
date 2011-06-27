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
(* | [ H : ⊪ _ ⇐ _ |- _] => nice_inversion_clear H; [idtac] *)
| [ H : extended_val_tp _ _ |- _] => nice_inversion_clear H; [idtac]
end.
Ltac invert_typing := repeat invert_typing_1.

Hint Constructors synth_tp checks_tp.
Hint Resolve @subst_lemma.
Hint Resolve @subst_cons_typing @meta_type_eq @env_tp_cons.


Theorem subj_red {δ γ} (L:checked_exp δ γ) θ ρ V :
L[θ;;ρ] ⇓ V -> forall T, (clos_tp L θ ρ T) -> (V ∈ T).
induction 1; intros; invert_typing; try by eauto.

(* app *)
assert (V2 ∈ 〚θ〛T1) by eauto.
assert ((vfn y E θ' ρ') ∈ 〚θ〛(arr T1 T0)) by eauto.
invert_typing.
change (arr (〚θ'〛T2) (〚θ'〛T3) = arr (〚θ〛T1) (〚θ〛T0)) in H12. (* TODO *) nice_inversion H12. (* Combine with this? *)

erewrite <- H6.
eapply IHeval3.
econstructor; eauto.
erewrite compose_cons. (* TODO: This is part of normalization *)
rewrite H4.
by eauto.

(* mapp *)
assert ((vmlam X E θ' ρ') ∈ 〚θ〛(pi X0 U T)) by eauto.
invert_typing.
nice_inversion H10.
erewrite assoc. erewrite msubst_over_single.
rewrite <- (common_var (〚θ〛C) H1).

eapply IHeval2.
econstructor; eauto.
erewrite cons_import_mvar.
by eauto.

(* Var (extended value) *)
unfold compose in *.
pose proof (env_tp_app' y H9 H).
invert_typing.
erewrite <- H6.
by eauto.

(* Var (value) *)
unfold compose in *.
pose proof (env_tp_app' y H8 H).
invert_typing.
by assumption.

(* Rec *)
eapply IHeval.
econstructor; eauto.
erewrite compose_cons. (* TODO: Part of normalizing *)
eapply env_tp_cons;
by eauto.

(* Inl *)
change (〚θ〛(sum T S)) with (sum (〚θ〛T) (〚θ〛S)). (* TODO: Should be together with a tactic for the arr case *)
by eauto.

(* Inr *)
change (〚θ〛(sum T S)) with (sum (〚θ〛T) (〚θ〛S)).
by eauto.

(* Pair *)
change (〚θ〛(prod T S)) with (prod (〚θ〛T) (〚θ〛S)).
econstructor; by eauto.

(* pack *)
change (〚θ〛(sigma X U T)) with (sigma ₁ (〚θ〛U) (〚θ × (₁//X)〛T)).
econstructor; eauto.
erewrite single_subst_commute'.
by eauto.

(* fold *)
change (〚θ〛(tapp (mu Z X U T) C)) with (tapp (mu (ψ:=empty) Z ₁ (〚θ〛 U) (〚θ ×  (₁ // X) 〛 T))
       (〚θ〛 C)).
econstructor.
apply IHeval.
pose proof (clos_c H1 H7 H8).
erewrite single_subst_commute'.
erewrite tp_subst_commute in H0.
exact H0.

(* unfold *)
assert ((vfold V) ∈ (〚θ〛 (tapp (mu Z X U T) C))) by eauto.
invert_typing.
erewrite tp_subst_commute.
erewrite single_subst_commute' in H4.
exact H4.

(* meta *)
simpl. econstructor.
eapply subst_lemma; by eauto.

(* case. happy case *)
assert (psubst (· * ρ') (〚θ'〛 pa) ∈ (〚〚θ'〛 ○ θi〛U)) by eauto.
assert (branch_tp Δ Γ (br _ Δi Γi pa θi Ei) U T0) by firstorder.
invert_typing.
eapply IHeval2.
erewrite <- assoc.
econstructor.
eauto.
admit. (* TODO *)
erewrite compose_prod.
admit. (* TODO *)

(* case *)
eapply IHeval2.
econstructor; eauto.
econstructor; eauto. intros.
eapply H6; by firstorder.

(* case *)
eapply IHeval2.
econstructor; eauto.
econstructor; eauto. intros.
eapply H6; by firstorder.
Qed.

(* Notes:
Focus on simultaneous substitutions means proofs and
intermediate results are very algebraic.
*)