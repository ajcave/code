Require Import List.
Require Import Eqdep.
Require Import util.
Require Import worlds.
Require Import meta_term.
Require Import meta_subst.
Require Import meta_subst_meta_term.
Require Import meta_subst_meta_type.
Require Import meta_subst_typing.
Require Import meta_subst_type.
Require Import type_assign.
Require Import comp_expr.
Require Import meta_subst_type_assign.
Require Import meta_subst_meta_subst.
Require Import comp_expr_typing.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import unification.
Require Import closures.
Require Import meta_subst_misc.
Require Import tactics.
Require Import bigstep.
Require Import Coq.Program.Equality.

Hint Constructors closure_typ c_tp s_tp br_tp msubst_typ'.
Hint Resolve @env_tp_cons.

Theorem subj_red L V : L ⇓ V -> forall T, L ∷∷ T -> V ∷∷ T.
Proof.
induction 1; auto; nice_inversion 1.

(* Case: coercion *)
nice_inversion H9.
nice_inversion H2; eauto.
  
(* Case: app *)
nice_inversion H11.
nice_inversion H4.
assert (V2 ∷∷ (⟦θ⟧ T1)); eauto.     
assert ((fn y E)[θ';;ρ'] ∷∷ (⟦θ⟧ (arr T1 T0))); eauto.
   
nice_inversion H5.
nice_inversion H19.
nice_inversion H17.
rewrite <- H13.
apply IHeval3.
econstructor; eauto.
unfold app_subst in H18 |- *; unfold tp_assign_substitutable in *; erewrite compose_comma.
eapply env_tp_cons; eauto.
erewrite H12. assumption.

(* Case: meta application *)
nice_inversion H10.
nice_inversion H3.
assert ((mlam X E)[θ';;ρ'] ∷∷ (⟦θ⟧ (pi X0 U T))); eauto.
   
nice_inversion H2.
nice_inversion H17.
nice_inversion H15.
apply IHeval2.
rewrite <- subst_combine.
   
erewrite <- msubst_ext; eauto.
econstructor; eauto.
econstructor; eauto.
erewrite H6.
eapply subst_lemma; eauto. 
erewrite <- cons_wkn_inv; eauto.
  
(* case expression 1 *)
eapply IHeval.
nice_inversion H10.
constructors firstorder.

(* case expression 2 *)
eapply IHeval2.
nice_inversion H12.
constructors firstorder.

(* case expression 3 *)
nice_inversion H12.
assert ((meta_term_closure C) ∷∷  ⟦θ⟧ U); eauto.
nice_inversion H4.
   
assert (@br_tp _ _ Δ Γ (br Ck θk Ek) (arr U T0)); firstorder.
   
nice_inversion H5.
pose proof (hop1a H10 H20 H).
assert (· ⊩ θ'' ∷ ·).
eapply hop2a; [idtac | idtac | eexact H1]; eauto.
eapply subst_lemma; eauto; fail.

rewrite (hop1b H10 H20 H) in *. 
nice_inversion H14.
eapply IHeval2.
rewrite subst_assoc3.
rewrite subst_id.
econstructor; eauto.
erewrite assoc. eauto; fail.
destruct (empty_is_empty y); fail.  

(* var *)
nice_inversion H10.
nice_inversion H2.
unfold env_tp in H9.
eapply IHeval.
eapply H9.
   
(* rec *)
nice_inversion H9.
eapply IHeval; eauto.
econstructor; eauto.
unfold app_subst; unfold tp_assign_substitutable; erewrite compose_comma.
eauto; fail.
Qed.

Print Assumptions subj_red.
