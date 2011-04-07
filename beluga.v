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

 Inductive closure : Set :=
  | meta_term_closure : meta_term empty -> closure
  | comp_term_closure : forall D G, checked_exp D G -> msubst D empty -> star (fun γ γ' => (γ↪γ')*closure) empty G -> closure.
 Definition env := star (fun γ γ' => (γ↪γ')*closure) empty.
 Implicit Arguments comp_term_closure.

Inductive env_assigned : forall {γ}, env γ -> name γ -> closure -> Prop :=
  | env_assigned_here   : forall γ γ' (ρ:env γ') (y:γ'↪γ) V,
                      env_assigned (ρ,, (y,V)) y V
  | env_assigned_before : forall γ γ' (ρ:env γ') (y:γ'↪γ) V x U,
                      env_assigned ρ x U
                   -> env_assigned (ρ,, (y,V)) (import y x) U.

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
   | env_tp_nil : env_tp s_nil ·
   | env_tp_cons : forall γ (ρ:env γ) Γ V T γ' (y:γ ↪ γ'),
              env_tp ρ Γ
              -> V ∷∷ T
              -> env_tp (ρ,,(y,V)) (Γ,,(y,T))
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
  | env_val_nil : env_val s_nil
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
       E [ θ ;; ρ ,, (f, (rec f E)[θ;;ρ]) ] ⇓ V
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
        | [ H : _ |- context f [tp_assign_substitutable ?w1 ?w2 ?w3 ?s1 ?t1] ] =>
          replace (tp_assign_substitutable w1 w2 w3 s1 t1) with  (⟦ s1 ⟧ t1); try reflexivity 
        | [ H : _ |- context f [app_msubst_t2 ?t ?T] ] =>
          replace (app_msubst_t2 t T) with (⟦ t ⟧ T); try reflexivity
        | [ H : context f [app_msubst_t2 ?t ?T] |- _ ] =>
          replace (app_msubst_t2 t T) with (⟦ t ⟧ T) in H; try reflexivity
        | [ H : _ |- context f [msubst_substitutable ?w1 ?w2 ?t1 ?t2] ] =>
          replace (msubst_substitutable w1 w2 t1 t2) with (⟦ t1 ⟧ t2); try reflexivity 
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
                    ⟦import_msubst X' θ';  m_var  X' // X ⟧ T1 =
                    ⟦import_msubst X' θ;  m_var X' // X0 ⟧ T ->
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
   Admitted. (* TODO: This should be part of the typeclass *)
   Axiom subst_assoc4 : forall {δ δ' δ''} (C:meta_term δ)
    (θ:msubst δ δ') (θ':msubst δ' δ''),
     ⟦⟦θ'⟧θ⟧ C = ⟦θ'⟧(⟦θ⟧C).
   Lemma subst_assoc3 {δ} (T:tp δ) : forall {δ' δ''}
    (θ:msubst δ δ') (θ':msubst δ' δ''),
    ⟦⟦θ'⟧θ⟧ T = ⟦θ'⟧(⟦θ⟧T).
   induction T; intros;
   unfold app_subst at 1 3 4;
   unfold tp_substitutable in *;
   simpl; repeat clean_substs;
   try (rewrite subst_assoc);
   try (f_equal);
   try (eapply IHT1);
   try (eapply IHT2);
   try (eapply IHT);
   try (eapply subst_assoc4).
   unfold app_subst in *.
   unfold tp_substitutable in *.
   erewrite <- IHT.
   repeat clean_substs.
   remember ((next' δ'')) as X.
   remember (next' δ'0) as X'.
   destruct X.
   destruct X'. simpl.
   f_equal.
   repeat (match goal with | [ H : _ |- _] => clear H end).
   generalize dependent δ''.
   generalize δ' s x x0 s1.
   clear δ' s x x0 s1.
   induction θ; intros.
   unfold app_subst.
   simpl.
   Admitted.
   
  (* TODO: Remove extraneous definitions! 
     Define substitution directly where we declare it an
     instance of the typeclass! Then less unfolding *)
   
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
   Qed.

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

 Lemma env_tp2 : forall δ γ (Γ:tp_assign γ δ) δ' (θ:msubst δ δ') y T0,
                    var_assigned Γ y T0
                 -> var_assigned (⟦θ⟧ Γ) y (⟦θ⟧ T0).
 induction Γ; intros. 
 inversion H. 
 inversion H; subst; simpl_existTs; subst.
 econstructor. 
 econstructor.
 apply IHΓ.
 auto.
 Qed.


   Hint Constructors closure_typ c_tp s_tp br_tp msubst_typ' env_tp.
   Hint Resolve env_tp1 env_tp2.
   Ltac clean_inversion := subst; simpl_existTs; subst; repeat clean_substs.
   Tactic Notation "nice_inversion" integer(H) := inversion H; clean_inversion.
   Tactic Notation "nice_inversion" hyp(H) := inversion H; clean_inversion.
   Ltac simpl_subst := unfold app_subst; simpl;repeat clean_substs.
   Tactic Notation "constructors" tactic(t) := repeat (econstructor; simpl_subst; eauto); t; repeat clean_substs.

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
   unfold app_subst in *. 
   rewrite <- H13.
   apply IHeval3.
   constructors congruence.

   (* Case: meta application *)
   nice_inversion H10.
   nice_inversion H3.
   assert ((mlam X E)[θ';;ρ'] ∷∷ (⟦θ⟧ (pi X0 U T))); eauto.
   
   nice_inversion H2.
   nice_inversion H17.
   nice_inversion H15.
   destruct (next empty) as [α X']. simpl in *.
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
   eapply subst_lemma; eauto.

   rewrite (hop1b H10 H20 H) in *. 
   nice_inversion H14.
   eapply IHeval2.
   rewrite subst_assoc3.
   rewrite subst_id.
   econstructor; eauto.
   erewrite subst_assoc2 in H11; eauto.

   (* var *)
   nice_inversion H10.
   nice_inversion H3.
   eauto.
   
   (* rec *)
   nice_inversion H9.
   eapply IHeval; eauto.
   constructors idtac.
  Qed.

  Print Assumptions subj_red.
