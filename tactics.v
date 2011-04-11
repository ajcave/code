Require Import meta_subst.
Require Import meta_subst_type.
Require Import meta_term.
Require Import meta_subst_type_assign.
Require Import meta_subst_meta_subst.
Require Import Coq.Program.Equality.
Ltac clean_substs :=
      (match goal with
        | [ H : context f [tp_substitutable ?w1 ?w2 ?s1 ?t1] |- ?g ] =>
          replace (tp_substitutable w1 w2 s1 t1) with (⟦ s1 ⟧ t1) in H; try reflexivity 
        | [ H : context f [app_msubst_mtype ?t ?w] |- ?g ] =>
          replace (app_msubst_mtype t w) with (⟦ t ⟧ w) in H; try reflexivity
        | [ H : _ |- context f [tp_assign_substitutable ?w1 ?w2 ?w3 ?s1 ?t1] ] =>
          replace (tp_assign_substitutable w1 w2 w3 s1 t1) with  (⟦ s1 ⟧ t1); try reflexivity 
        | [ H : _ |- context f [app_msubst_tp ?t ?T] ] =>
          replace (app_msubst_tp t T) with (⟦ t ⟧ T); try reflexivity
        | [ H : context f [app_msubst_tp ?t ?T] |- _ ] =>
          replace (app_msubst_tp t T) with (⟦ t ⟧ T) in H; try reflexivity
        | [ H : _ |- context f [msubst_substitutable ?w1 ?w2 ?t1 ?t2] ] =>
          replace (msubst_substitutable w1 w2 t1 t2) with (⟦ t1 ⟧ t2); try reflexivity 
        | _ => fail
     end).

   Ltac clean_inversion := subst; simpl_existTs; subst; repeat clean_substs.
   Tactic Notation "nice_inversion" integer(H) := inversion H; clean_inversion.
   Tactic Notation "nice_inversion" hyp(H) := inversion H; clean_inversion.
   Ltac simpl_subst := unfold app_subst; simpl;repeat clean_substs.
   Tactic Notation "constructors" tactic(t) := repeat (econstructor; eauto); t; repeat clean_substs.