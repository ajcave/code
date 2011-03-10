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
 
  (* TODO: Compare our use of strong links and imports to the paper's example of
     typing derivations. It's possible that they do contravariant stuff to avoid
     the import *)
(* TODO: Consider just having eval relate closures, and
   proving after the fact that the rhs is always a value *)
 
 Inductive closure : Set :=
  | meta_term_closure : meta_term empty -> closure
  | comp_term_closure : forall D G, checked_exp D G -> msubst D empty -> env G -> closure
 with env : world -> Set :=
  | e_nil : env empty
  | e_cons : forall γ γ', env γ -> (γ↪γ')*closure -> env γ'.
 Implicit Arguments comp_term_closure.
 Implicit Arguments e_nil.
 Implicit Arguments e_cons.

Inductive env_assigned : forall {γ}, env γ -> name γ -> closure -> Prop :=
  | env_assigned_here   : forall γ γ' (ρ:env γ') (y:γ'↪γ) V,
                      env_assigned (e_cons ρ (y,V)) y V
  | env_assigned_before : forall γ γ' (ρ:env γ') (y:γ'↪γ) V x U,
                      env_assigned ρ x U
                   -> env_assigned (e_cons ρ (y,V)) (import y x) U.

 Notation "E [ θ ;; ρ ]" := (comp_term_closure E θ ρ) (at level 80).

 Reserved Notation "E ∷∷ T" (at level 90).
(* Definition a {δ δ'} (θ:msubst δ δ') (T1: tp δ) := ⟦ θ ⟧  T1. *)

 Inductive closure_typ : closure -> tp empty -> Prop :=
  | meta_term_closure_typ : forall C U,
              (· ⊨ C ∷ U)
           -> (meta_term_closure C) ∷∷ U
  | comp_term_closure_typ : forall δ γ (Δ:mtype_assign δ) (Γ:tp_assign γ δ) E (T:tp δ) (θ:msubst δ empty) (ρ:env γ),
                 · ⊩ θ ∷ Δ
              -> env_tp ρ (⟦θ⟧ Γ)
              -> Δ;Γ ⊢ E ⇐ T
              -> (E [θ ;; ρ]) ∷∷ (⟦θ⟧  T)
  with env_tp : forall {γ}, env γ -> tp_assign γ empty -> Prop :=
   | env_tp_nil : env_tp e_nil ·
   | env_tp_cons : forall γ (ρ:env γ) Γ V T γ' (y:γ ↪ γ'),
              env_tp ρ Γ
              -> V ∷∷ T
              -> env_tp (e_cons ρ (y,V)) (v_cons Γ (y,T))
  where "E ∷∷ T" := (closure_typ E T).
 Reserved Notation "E ⇓ V" (at level 90).
 

 Axiom unify : forall {δ δ' δ''} (θ:msubst δ δ') (θk:msubst δ δ'')
  (θ':msubst δ'' δ'), Prop. (* θ = θ'(θk) *)
 Axiom unify2 : forall {δ δ'} (C:meta_term δ) (D:meta_term δ')
  (θ:msubst δ' δ), Prop. (* C = θ(D) *) 
 Print branch.
 Notation "θ /≐ θ'" :=(forall θ'', ~unify θ θ' θ'') (at level 90).
 Notation "θ ≐ θk // θ'" := (unify θ θk θ') (at level 90). 
 Notation "C /≑ D" :=(forall θ, ~unify2 C D θ) (at level 90).
 Notation "C ≑ D // θ" := (unify2 C D θ) (at level 90).

 Inductive val : closure -> Prop :=
  | fn_val : forall γ δ δ' (θ:msubst γ empty) (y:δ↪δ') E ρ,
       env_val ρ -> val ((fn y E)[θ;;ρ])
  | mlam_val : forall γ γ' δ θ (X:γ↪γ') E (ρ:env δ),
       env_val ρ -> val ((mlam X E)[θ;;ρ])
  | meta_term_val : forall C, val (meta_term_closure C)
 with env_val : forall {δ}, env δ -> Prop :=
  | env_val_nil : env_val e_nil
  | env_val_cons : forall γ (ρ:env γ) γ' (y:γ↪γ') V,
       val V -> env_val (e_cons ρ (y,V))
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
          -> E [θ' ;; (e_cons ρ' (y,V2))] ⇓ V
          -> (app I1 E2) [θ ;; ρ] ⇓ V
  | ev_mapp : forall δ θ γ ρ (I:synth_exp δ γ) δ' (X:δ ↪ δ')
            (E:checked_exp δ' γ) θ' ρ' C V,
             I [θ ;; ρ] ⇓ (mlam X E) [θ';; ρ']
          -> E [(θ' ; (⟦θ⟧ C) // X) ;; ρ'] ⇓ V
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
            env_assigned ρ y V1
         -> V1 ⇓ V
         -> (var _ y) [θ ;; ρ] ⇓ V
  | ev_rec : forall δ θ γ ρ γ' (f:γ↪γ') (E:checked_exp δ γ') V,
       E [ θ ;; e_cons ρ (f, (rec f E)[θ;;ρ]) ] ⇓ V
    -> rec f E [θ ;; ρ] ⇓ V
    where "E1 ⇓ V1" := (eval E1 V1).

  Theorem eval_val L V : L ⇓ V -> val V.
  induction 1; assumption.
  Qed.

   Require Import Coq.Program.Equality.
   Implicit Arguments env_tp_cons.
   Notation "[[ C1 // X1 ]]" := (msubst_single_t X1 C1) (at level 90). 
   Axiom subst_combine : forall {γ δ δ'} (θ:msubst δ γ) (X:δ ↪ δ') C T,
     ⟦ θ ; ⟦θ⟧ C // X ⟧ T = ⟦θ⟧ ([[ C // X ]] T).

    Ltac clean_substs :=
      (match goal with
        | [ H : context f [tp_substitutable ?w1 ?w2 ?s1 ?t1] |- ?g ] =>
          replace (tp_substitutable w1 w2 s1 t1) with (⟦ s1 ⟧ t1) in H; try reflexivity 
        | [ H : context f [app_msubst_t ?t ?w] |- ?g ] =>
          replace (app_msubst_t t w) with (⟦ t ⟧ w) in H; try reflexivity
        | _ => fail
     end).

   Axiom subst_lemma : forall {δ δ':world} C U θ (Δ:mtype_assign δ) (Δ':mtype_assign δ'),
     Δ' ⊩ θ ∷ Δ
  -> Δ  ⊨ C ∷ U
  -> Δ' ⊨ ⟦θ⟧ C ∷ ⟦θ⟧ U.

   Theorem cons_wkn_inv {δ δ' δ'' γ } (θ:msubst δ δ') (X:δ ↪ δ'') (Γ:tp_assign γ δ) C :
     ⟦θ⟧Γ = ⟦θ; C // X⟧(weaken_ctx X Γ).
   Admitted.

  Theorem msubst_ext : forall {δ δ' δ'0 α β} (θ : msubst δ β) 
                      (X : δ ↪ δ') (θ' : msubst δ β)
                      m  
                      (X0 : δ ↪ δ'0) (T:tp δ'0) (T1:tp δ')  (X' : β ↪ α),
                    ⟦theta_weaken θ' X';  m_var X' // X ⟧ T1 =
                    ⟦theta_weaken θ X';  m_var X' // X0 ⟧ T ->
                    ⟦θ';  m // X ⟧ T1 = ⟦θ;  m // X0 ⟧ T.
   Admitted.
  Set Implicit Arguments.
  Section hop1.
   Variables (δ δ' δ'':world)
   (θ:msubst δ δ') (θ':msubst δ δ'') (θ'':msubst δ'' δ')
   (Δ:mtype_assign δ) (Δ':mtype_assign δ') (Δ'':mtype_assign δ'').
   Theorem hop1a :
       Δ' ⊩ θ ∷ Δ
    -> Δ'' ⊩ θ' ∷ Δ
    -> θ ≐ θ' // θ''
    -> Δ' ⊩ θ'' ∷ Δ''.
   Admitted.
   Theorem hop1b :
       Δ' ⊩ θ ∷ Δ
    -> Δ'' ⊩ θ' ∷ Δ
    -> θ ≐ θ' // θ''
    -> θ = ⟦θ''⟧ θ'.
   Admitted.
  End hop1.
 
  Section hop2.
   Variables (δ δ':world)
   (θ:msubst δ δ')
   (Δ:mtype_assign δ) (Δ':mtype_assign δ')
   (T:mtype δ') (C:meta_term δ')
   (U:mtype δ)  (D:meta_term δ).
   Theorem hop2a :
       Δ' ⊨ C ∷ T
    -> Δ  ⊨ D ∷ U
    -> C ≑ D // θ
    -> Δ' ⊩ θ ∷ Δ.
   Admitted.
   Theorem hop2b :
       Δ' ⊨ C ∷ T
    -> Δ  ⊨ D ∷ U
    -> C ≑ D // θ
    -> C = ⟦θ⟧ D.
   Admitted.
  End hop2.
   Hint Unfold app_subst meta_term_substitutable
     msubst_substitutable mtype_substitutable : subst.
   Lemma subst_id1 : forall (C:meta_term empty), ⟦·⟧ C = C.
   Admitted.
   Lemma subst_id2 : forall (U:mtype empty),  ⟦·⟧ U = U.
   Admitted.
   Lemma subst_id {δ} (θ:msubst δ empty) : ⟦·⟧ θ = θ.
   induction θ.
   reflexivity.  destruct r.
   autounfold with subst in *. simpl.
   rewrite IHθ. rewrite (subst_id1 m). reflexivity.
   Qed.
   Lemma subst_assoc {δ δ' δ''} (T:mtype δ)
    (θ:msubst δ δ') (θ':msubst δ' δ'') :
    ⟦⟦θ'⟧θ⟧ T = ⟦θ'⟧(⟦θ⟧T).
   Admitted.
   Lemma subst_assoc3 {δ δ' δ''} (T:tp δ)
    (θ:msubst δ δ') (θ':msubst δ' δ'') :
    ⟦⟦θ'⟧θ⟧ T = ⟦θ'⟧(⟦θ⟧T).
   Admitted.
   Lemma subst_assoc2 {δ δ' δ'' γ} (Γ:tp_assign γ δ)
    (θ:msubst δ δ') (θ':msubst δ' δ'') :
    ⟦⟦θ'⟧θ⟧ Γ = ⟦θ'⟧(⟦θ⟧ Γ).
   generalize dependent δ'.
   generalize dependent δ''.
   induction Γ; intros.
   reflexivity. destruct r.
   unfold app_subst. unfold tp_assign_substitutable. simpl.
   f_equal.
   apply IHΓ.
   f_equal.
   apply subst_assoc3.
   Admitted.

 Lemma env_tp1 : forall γ ρ y V1 T0 (Γ : tp_assign γ empty),
                    env_assigned ρ y V1 ->
                    env_tp ρ Γ -> var_assigned Γ y T0 -> V1 ∷∷ T0.
 intros. dependent induction H0.
 inversion H1.   
 inversion H1; subst; simpl_existTs; subst.
 inversion H; subst; simpl_existTs; subst.  
 auto.
 contradict H3.
 apply import_img.
 inversion H; subst; simpl_existTs; subst.
 symmetry in H3.
 contradict H3.
 apply import_img.
 eapply IHenv_tp.
 eauto.
 pose proof (import_inj H3).
 subst.
 auto.
 Qed.

 Lemma env_tp2 : forall δ γ (Γ : tp_assign γ δ) δ' (θ:msubst δ δ') y T0,
                    var_assigned Γ y T0
                 -> var_assigned (⟦θ⟧ Γ) y (app_msubst_t2 θ T0).
 induction Γ; intros. 
 inversion H. 
 inversion H; subst; simpl_existTs; subst.
 econstructor. 
 econstructor.
 apply IHΓ.
 auto.
 Qed.


   Theorem subj_red L V : L ⇓ V -> forall T, L ∷∷ T -> V ∷∷ T.
   Proof.
   induction 1; try (destruct V; auto; fail);
   inversion 1; subst; simpl_existTs; subst.
   inversion H9; subst.
   inversion H2; subst.
   apply IHeval.
   econstructor.
   eexact H7.
   eexact H8.
   eexact H5.
  
   (* Case: app *)
   inversion H11; subst.
   inversion H4; subst.
   assert (V2 ∷∷ (⟦θ⟧ T1)).
   apply IHeval2.
   econstructor.
   eexact H9.
   eexact H10.
   eexact H8.
   
   assert ((fn y E)[θ';;ρ'] ∷∷ (⟦θ⟧ (arr T1 T0))).
   apply IHeval1.
   econstructor.
   eexact H9.
   eexact H10.
   constructor.
   eexact H6.

   inversion H5. subst. simpl_existTs. subst.
   destruct T; try discriminate. inversion H17.
   inversion H19. subst. simpl_existTs. subst. repeat clean_substs.
    rewrite <- H13.
   pose proof (env_tp_cons y H18 H3).
   
   apply IHeval3.
   Print closure_typ. 
   econstructor.
   eexact H14.
   instantiate (1 := (v_cons Γ0 (y,T2))).
   rewrite <- H12 in H7.
   eexact H7. assumption.

   (* Case: meta application *)
   inversion H10. subst.
   inversion H3. simpl_existTs. subst.
   assert ((mlam X E)[θ';;ρ'] ∷∷ (⟦θ⟧ (prod X0 U T))).
   apply IHeval1.
   econstructor.
   eexact H8. eexact H9. constructor. eexact H5.
   
   inversion H2. subst. simpl_existTs. subst.
   inversion H17. subst. simpl_existTs. subst.
   inversion H15. simpl_existTs. unfold weaken1 in *.
   repeat clean_substs.
   destruct (next empty) as [α X']. simpl in *.
   apply IHeval2.
   rewrite <- subst_combine.
   unfold msubst.
   
   erewrite <- msubst_ext.
   Focus 2. eexact H4.
   econstructor.
   econstructor.
   eexact H12.
   instantiate (1:= U0).
   erewrite H6.
   eapply subst_lemma.   
   eauto.
   eauto.
   Focus 2.
   eexact H14.
   rewrite <- (cons_wkn_inv θ' X Γ0 (⟦θ⟧ C)). 
   exact H16.
  
   (* case expression 1 *)
   eapply IHeval.
   econstructor.
   eexact H8.
   eexact H9.
   inversion H10. subst.
   econstructor.
   eexact H4.      
   intros.
   apply H6.
   constructor 2.
   auto.

   (* case expression 2 *)
   eapply IHeval2.
   econstructor.
   eexact H10.
   eexact H11.
   inversion H12. subst.
   econstructor.   
   eexact H6.
   intros. apply H8.
   constructor 2. auto.

   (* case expression 3 *)
   inversion H12. subst.
   assert ((meta_term_closure C) ∷∷  ⟦θ⟧ U).
   eapply IHeval1.
   econstructor.
   eexact H10.
   eexact H11.
   constructor. auto.
   inversion H4. subst.
   
   assert (@br_tp _ _ Δ Γ (br Ck θk Ek) (arr U T0)).
   eapply H8.
   constructor.
   reflexivity.
   inversion H5. subst. simpl_existTs. subst.
   pose proof (hop1a H10 H20 H).
   assert (· ⊩ θ'' ∷ ·).
   eapply hop2a.
   Focus 3. eexact H1.
   eexact H9.
   eapply subst_lemma.   
   eexact H13.
   eexact H16.
   pose proof (hop1b H10 H20 H). 
   subst.
   inversion H14. simpl_existTs. subst.
   eapply IHeval2.
   rewrite subst_assoc3.
   rewrite subst_id.
   econstructor.
   eexact H13.   
   pose proof (subst_assoc2 Γ θk θ').
   rewrite H15 in H11.
   eexact H11.
   auto.

   (* var *)
   inversion H10. subst. inversion H3. subst.
   apply IHeval. 
   eapply env_tp1; eauto.
   apply env_tp2. auto. 
   
   (* rec *)
   inversion H9. subst. simpl_existTs. subst.
   eapply IHeval.
   econstructor.
   eauto.
   Focus 2. eexact H5.
   unfold app_subst. simpl. econstructor; eauto.
  Qed.

  Print Assumptions subj_red.
