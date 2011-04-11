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

 Reserved Notation "E ⇓ V" (at level 90).
 

 Inductive val : closure -> Prop :=
  | fn_val : forall γ δ δ' (θ:msubst γ empty) (y:δ↪δ') E ρ,
       env_val ρ -> val ((fn y E)[θ;;ρ])
  | mlam_val : forall γ γ' δ θ (X:γ↪γ') E (ρ:env δ),
       env_val ρ -> val ((mlam X E)[θ;;ρ])
  | meta_term_val : forall C, val (meta_term_closure C)
 with env_val : forall {δ}, env δ -> Prop :=
  | env_val_nil : env_val ·
  | env_val_cons : forall γ (ρ:env γ) γ' (y:γ↪γ') V,
       val V -> env_val (ρ,,(y,V))
 .

 Inductive eval : closure -> closure -> Prop :=
  | ev_val : forall V, val V -> eval V V 
  | ev_coerce : forall δ θ γ ρ (E:checked_exp δ γ) T V,
             E [θ ;; ρ] ⇓ V
          -> (coercion E T) [θ ;; ρ] ⇓ V
  | ev_app : forall δ θ γ ρ (I1:synth_exp δ γ) γ' (y:γ ↪ γ')
             (E:checked_exp δ γ') θ' ρ' (E2:checked_exp δ γ) V2 V,
             I1 [θ ;; ρ] ⇓ (fn y E) [θ' ;; ρ']
          -> E2 [θ ;; ρ] ⇓ V2
          -> E [θ' ;; (ρ' ,, (y,V2))] ⇓ V
          -> (app I1 E2) [θ ;; ρ] ⇓ V
  | ev_mapp : forall δ θ γ ρ (I:synth_exp δ γ) δ' (X:δ ↪ δ')
            (E:checked_exp δ' γ) θ' ρ' C V,
             I [θ ;; ρ] ⇓ (mlam X E) [θ';; ρ']
          -> E [(θ' ,, (X, (⟦θ⟧ C))) ;; ρ'] ⇓ V
          -> (mapp I C) [θ ;; ρ] ⇓ V
  | ev_case1 : forall δ θ γ ρ (I:synth_exp δ γ) δi
            (θk:msubst δ δi) Bs Ck Ek V,
            (θ /≐ θk)
         -> case_i I Bs [θ ;; ρ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V
  | ev_case2 : forall δ θ γ ρ (I:synth_exp δ γ) δi
            (θk:msubst δ δi) θ' Bs (C:meta_term empty) Ek V Ck,
            (θ ≐ θk // θ')
         -> I [θ ;; ρ] ⇓ meta_term_closure C
         -> (C /≑ ⟦θ'⟧ Ck)
         -> case_i I Bs [θ ;; ρ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V
  | ev_case3 : forall δ θ γ ρ (I:synth_exp δ γ) δi
            (θk:msubst δ δi) θ' θ'' Bs (C:meta_term empty) Ek V Ck,
            (θ ≐ θk // θ')
         -> I [θ ;; ρ] ⇓ meta_term_closure C
         -> (C ≑ ⟦θ'⟧ Ck // θ'')
         -> Ek [ ⟦θ''⟧ θ' ;; ρ ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V 
  | ev_var : forall δ (θ:msubst δ empty) γ ρ (y:name γ) V1 V,
            ρ y = V1
         -> V1 ⇓ V
         -> (var _ y) [θ ;; ρ] ⇓ V
  | ev_rec : forall δ θ γ ρ γ' (f:γ↪γ') (E:checked_exp δ γ') V,
       E [ θ ;; ρ ,, (f, (rec f E)[θ;;ρ]) ] ⇓ V
    -> rec f E [θ ;; ρ] ⇓ V
    where "E1 ⇓ V1" := (eval E1 V1).

  Theorem eval_val L V : L ⇓ V -> val V.
  induction 1; assumption.
  Qed.

   Require Import Coq.Program.Equality.
   Notation "[[ C1 // X1 ]]" := (msubst_single_t X1 C1) (at level 90). 
   Lemma subst_combine : forall {γ δ δ'} (θ:msubst δ γ) (X:δ ↪ δ') C T,
     ⟦ θ ,, (X, ⟦θ⟧ C) ⟧ T = ⟦θ⟧ ([[ C // X ]] T).
   Admitted.

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

   Theorem subst_lemma : forall {δ δ':world} C U θ (Δ:mtype_assign δ) (Δ':mtype_assign δ'),
     Δ' ⊩ θ ∷ Δ
  -> Δ  ⊨ C ∷ U
  -> Δ' ⊨ ⟦θ⟧ C ∷ ⟦θ⟧ U.
   Admitted.

Theorem cons_wkn_inv {δ δ' δ'' γ } (θ:msubst δ δ') (X:δ ↪ δ'') (Γ:tp_assign γ δ) C :
 ⟦θ⟧Γ = ⟦θ ,, (X,C)⟧(import_tp_assign X Γ).
unfold import_tp_assign.
erewrite assoc.
(* TODO: I think there's a nice lemma here... *)
f_equal.
unfold compose.
extensionality y.
erewrite app_msubst_mvar_result.
erewrite export_import_inv.
simpl.
reflexivity.
Qed.
Print import_tp_assign.
(* Theorem cons_wkn_inv' {δ δ' δ''} (θ:msubst δ δ') (X:δ ↪ δ'') C :  ⟦θ⟧ = ⟦θ ,, (X,C)⟧ ○ ⟦import X⟧.
*)

  Theorem msubst_ext : forall {δ δ' δ'0 α β} (θ : msubst δ β)
   (X : δ ↪ δ') (θ' : msubst δ β)
    m  
   (X0 : δ ↪ δ'0) (T:tp δ'0) (T1:tp δ')  (X' : β ↪ α),
    ⟦import_msubst X' θ' ,, (X,m_var  X') ⟧ T1 =
    ⟦import_msubst X' θ ,, (X0, m_var X') ⟧ T ->
    ⟦θ' ,, (X,m) ⟧ T1 = ⟦θ ,, (X0,m)  ⟧ T.
   Admitted.

Lemma subst_id {δ} (θ:msubst δ empty) : ⟦·⟧ θ = θ.
unfold app_subst.
unfold msubst_substitutable.
unfold app_subst.
unfold meta_term_substitutable.
erewrite app_msubst_id.
erewrite compose_id_left. reflexivity.
eexact θ.
Qed.
Lemma subst_assoc3 {δ} (T:tp δ) : forall {δ' δ''}
 (θ:msubst δ δ') (θ':msubst δ' δ''),
 ⟦⟦θ'⟧θ⟧ T = ⟦θ'⟧(⟦θ⟧T).
intros. erewrite assoc. reflexivity.
Qed.

   Hint Constructors closure_typ c_tp s_tp br_tp msubst_typ'.
   Hint Resolve @env_tp_cons.
   Ltac clean_inversion := subst; simpl_existTs; subst; repeat clean_substs.
   Tactic Notation "nice_inversion" integer(H) := inversion H; clean_inversion.
   Tactic Notation "nice_inversion" hyp(H) := inversion H; clean_inversion.
   Ltac simpl_subst := unfold app_subst; simpl;repeat clean_substs.
   Tactic Notation "constructors" tactic(t) := repeat (econstructor; eauto); t; repeat clean_substs.

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
   destruct (next empty) as [α X']. simpl in *.
   apply IHeval2. repeat clean_substs.
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
   destruct (empty_fst y); fail.  

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
