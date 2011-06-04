Require Import ssreflect.
Require Export bigstep.
Require Import Coq.Program.Equality.

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
 | [ H : context f [app_msubst ?t] |- _ ] =>
   replace (app_msubst t) with (〚 t 〛) in H;
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
end.
Ltac invert_typing := repeat invert_typing_1.

Hint Constructors synth_tp checks_tp.

Theorem subj_red (L:checked_exp ∅ ∅) V :
L ⇓ V -> forall T, (·;· ⊢ L ⇐ T) -> (·;· ⊢ V ⇐ T).
induction 1; intros; invert_typing.
by eauto. (* Coercion *)

(* app *)
assert (·;· ⊢ V2 ⇐ 〚θ〛T1) by eauto.
assert (·;· ⊢ (fn y E)[θ';;ρ'] ⇐ 〚θ〛(arr T1 T0)) by eauto.
invert_typing.
change (arr (〚θ'〛T2) (〚θ'〛T3) = arr (〚θ〛T1) (〚θ〛T0)) in H14. (* TODO *) nice_inversion H14. (* Combine with this? *)
admit. (*TODO: by eauto *)

assert (·;· ⊢ (mlam X E)[θ';;ρ'] ⇐ 〚θ〛(pi X0 U T)) by eauto.
invert_typing.
nice_inversion H12.
unfold single_subst.
erewrite assoc.
(* Ah! Use the × combine result *)