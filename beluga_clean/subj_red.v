Require Import ssreflect.
Require Export bigstep.
Require Import Coq.Program.Equality.
Set Implicit Arguments.

Ltac clean_substs :=
(match goal with
 | [ H : context f [tp_substitutable ?w1 ?w2 ?s1 ?t1] |- ?g ] =>
   replace (tp_substitutable w1 w2 s1 t1)
    with (〚 s1 〛 t1) in H; try reflexivity 
 | [ H : context f [app_msubst_mtype ?t ?w] |- ?g ] =>
   replace (app_msubst_mtype t w) with (〚 t 〛 w) in H;
   try reflexivity
 | [ H : _ |- context f [app_msubst_tp ?t ?T] ] =>
   replace (app_msubst_tp t T) with (〚 t 〛 T);
   try reflexivity
 | [ H : context f [app_msubst_tp ?t ?T] |- _ ] =>
   replace (app_msubst_tp t T) with (〚 t 〛 T) in H;
   try reflexivity
 | [ H : context f [app_msubst ?t ?T] |- _ ] =>
   replace (app_msubst t T) with (〚 t 〛 T) in H;
   try reflexivity
 | _ => fail
end).
Ltac clean_inversion := subst; simpl_existTs; subst; repeat clean_substs.

Tactic Notation "nice_inversion" integer(H) := inversion H; clean_inversion.

Tactic Notation "nice_inversion" hyp(H) := inversion H; clean_inversion.

Ltac nice_inversion_clear H := nice_inversion H; clear H.

Ltac invert_typing_1 :=
match goal with
| [ H : _;_ ⊢ synth _ ⇐ _ |- _ ] => nice_inversion_clear H
| [ H : _;_ ⊢ coercion _ _ ⇒ _ |- _] => nice_inversion_clear H
| [ H : _;_ ⊢ clos _ _ _ ⇐ _ |- _] => nice_inversion_clear H
| [ H : _;_ ⊢ app _ _ ⇒ _ |- _] => nice_inversion_clear H
| [ H : _;_ ⊢ fn _ _ ⇐ _ |- _] => nice_inversion_clear H
| [ H : _;_ ⊢ mapp _ _ ⇒ _ |- _] => nice_inversion_clear H
| [ H : _;_ ⊢ mlam _ _ ⇐ _ |- _] => nice_inversion_clear H
| [ H : _;_ ⊢ var _ _ ⇒ _ |- _] => nice_inversion_clear H
| [ H : _;_ ⊢ rec _ _ ⇐ _ |- _] => nice_inversion_clear H
| [ H : _;_ ⊢ inl _ ⇐ _ |- _ ] => nice_inversion_clear H
| [ H : _;_ ⊢ inr _ ⇐ _ |- _ ] => nice_inversion_clear H
| [ H : _;_ ⊢ pair _ _ ⇐ _ |- _ ] => nice_inversion_clear H
| [ H : _;_ ⊢ pack _ _ ⇐ _ |- _ ] => nice_inversion_clear H
| [ H : _;_ ⊢ fold _ ⇐ _ |- _ ] => nice_inversion_clear H
| [ H : _;_ ⊢ unfold _ ⇒ _ |- _ ] => nice_inversion_clear H
| [ H : _;_ ⊢ meta _ _ ⇐ _ |- _ ] => nice_inversion_clear H
| [ H : _;_ ⊢ tt ⇐ _ |- _] => nice_inversion_clear H
end.
Ltac invert_typing := repeat invert_typing_1.

Hint Constructors synth_tp checks_tp.
Hint Resolve @subst_lemma.
Hint Resolve @subst_cons_typing @meta_type_eq @env_tp_cons.

Theorem subj_red {δ γ} (L:checked_exp δ γ) θ ρ V :
L[θ;;ρ] ⇓ V -> forall T, (·;· ⊢ L[θ;;ρ] ⇐ T) -> (·;· ⊢ V ⇐ T).
induction 1; intros; invert_typing; try by eauto.

(* app *)
assert (·;· ⊢ V2 ⇐ 〚θ〛T1) by eauto.
assert (·;· ⊢ (fn y E)[θ';;ρ'] ⇐ 〚θ〛(arr T1 T0)) by eauto.
invert_typing.
change (arr (〚θ'〛T2) (〚θ'〛T3) = arr (〚θ〛T1) (〚θ〛T0)) in H14. (* TODO *) nice_inversion H14. (* Combine with this? *)

erewrite <- H6.
eapply IHeval3.
econstructor; eauto.
erewrite compose_cons. (* TODO: This is part of normalization *)
rewrite H4.
by eauto.

(* mapp *)
assert (·;· ⊢ (mlam X E)[θ';;ρ'] ⇐ 〚θ〛(pi X0 U T)) by eauto.
invert_typing.
nice_inversion H12.
erewrite assoc. erewrite msubst_over_single.
rewrite <- (common_var (〚θ〛C) H1).

eapply IHeval2.
econstructor; eauto.
erewrite cons_import_mvar.
by assumption.

(* Var (extended value) *)
specialize (H10 y). rewrite H in H10. 
by firstorder.

(* Var (value) *)
by firstorder.

(* Rec *)
eapply IHeval.
econstructor; eauto.
erewrite compose_cons. (* TODO: Part of normalizing *)
by eauto.

(* Inl *)
change (〚θ〛(sum T S)) with (sum (〚θ〛T) (〚θ〛S)). (* TODO: Should be together with a tactic for the arr case *)
by eauto.

(* Inr *)
change (〚θ〛(sum T S)) with (sum (〚θ〛T) (〚θ〛S)).
by eauto.

(* Pair *)
change (〚θ〛(prod T S)) with (prod (〚θ〛T) (〚θ〛S)).
by eauto 6.

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
pose proof (clos_c H1 H8 H9).
erewrite single_subst_commute'.
erewrite tp_subst_commute in H0.
exact H0.

(* unfold *)
assert (·;· ⊢ (fold V) ⇐ (〚θ〛 (tapp (mu Z X U T) C))) by eauto.
invert_typing.
erewrite tp_subst_commute.
erewrite single_subst_commute' in H4.
exact H4.

(* meta *)
simpl. econstructor.
eapply subst_lemma; by eauto.

(* unit *)
simpl. eauto.
Qed.

(* Notes:
Focus on simultaneous substitutions means proofs and
intermediate results are very algebraic.
*)