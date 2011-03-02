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

 (* TODO. Is this even possible? Should it produce a world D2 and link? *)
 Axiom import_tp : forall {D1 D2:world} (y:slink D1 D2) (T:tp D1), tp D2.

 
 Definition weaken_ctx : forall {D1 D2 G}, slink D1 D2 -> tp_assign D1 G -> tp_assign D2 G.
 intros. induction H0.
 constructor.
 econstructor.
 eexact IHstar.
 destruct r.
 constructor.
 exact s.
 eapply import_tp.
 eexact H.
 exact t.
 Defined.
 
 Check @app_subst.
 Reserved Notation "D1 ; G1 ⊢ t1 ⇐ T1" (at level 90).
 Reserved Notation "D1 ; G1 ⊢ t1 ⇒ T2" (at level 90).
 Inductive s_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign δ γ}
                   : synth_exp δ γ -> tp δ -> Prop :=
  | var_s : forall x T,
             var_assigned Γ x T
           -> Δ;Γ ⊢ (var _ x) ⇒ T
  | app_s : forall I T1 E T2,
              Δ;Γ ⊢ I ⇒ (arr T1 T2)
           -> Δ;Γ ⊢ E ⇐ T1
           -> Δ;Γ ⊢ (app I E) ⇒ T2
  | mapp_s : forall I δ' (X:wlink δ δ') U C T,
              Δ;Γ ⊢ I ⇒ (prod X U T)
           -> Δ ⊨ C ∷ U
           -> Δ;Γ ⊢ (mapp I C) ⇒ (msubst_single_t X C T)
  | coerce_s : forall E T,
              Δ;Γ ⊢ E ⇐ T
           -> Δ;Γ ⊢ (coercion E T) ⇒ T
 with c_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign δ γ}
                   : checked_exp δ γ -> tp δ -> Prop :=
  | synth_c : forall I T,
              Δ;Γ ⊢ I ⇒ T
           -> Δ;Γ ⊢ I ⇐ T
  | meta_c : forall C U,
              Δ ⊨ C ∷ U 
           -> Δ;Γ ⊢ (meta γ C) ⇐ U
  | fn_c : forall γ' (y:slink γ γ') E T1 T2,
             Δ;(v_cons Γ (y,T1)) ⊢ E ⇐ T2
          -> Δ;Γ ⊢ (fn y E) ⇐ (arr T1 T2)
  | mlam_c : forall δ' (X:slink δ δ') E U T,
             (m_cons Δ (X,U));(weaken_ctx X Γ) ⊢ E ⇐ T
          -> Δ;Γ ⊢ (mlam X E) ⇐ (prod X U T)
  | case_i_c : forall I U Bs T,
             Δ;Γ ⊢ I ⇒ U
          -> (forall B, In B Bs -> br_tp B (arr U T))
          -> Δ;Γ ⊢ (case_i I Bs) ⇐ T
  | rec_c : forall γ' (f:slink γ γ') E T,
             Δ;(v_cons Γ (f,T)) ⊢ E ⇐ T
          -> Δ;Γ ⊢ (rec f E) ⇐ T
 with br_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign δ γ}
                     : branch δ γ -> tp δ -> Prop :=
  | br_c : forall δi (C:meta_term δi) (θi:msubst δ δi)
                  (E:checked_exp δi γ) (U T:mtype δ)
                  (Δi:mtype_assign δi),
             Δi ⊨ C ∷ ⟦θi⟧ U
          -> Δi ⊩ θi ∷ Δ
          -> Δi;(app_msubst_tp_assign θi Γ) ⊢ E ⇐ (app_msubst_t θi T)
          -> br_tp (br C θi E) (arr U T)
  where "D1 ; G1 ⊢ t1 ⇒ T1" := (@s_tp _ _ D1 G1 t1 T1)
  and   "D1 ; G1 ⊢ t1 ⇐ T1" := (@c_tp _ _ D1 G1 t1 T1).
 
 Implicit Arguments c_tp.
 Print s_tp.
  (* TODO: Compare our use of strong links and imports to the paper's example of
     typing derivations. It's possible that they do contravariant stuff to avoid
     the import *)

 Inductive is_val (D G:world) : checked_exp D G -> Prop :=
  | fn_is_val : forall G2 (y:wlink G G2) E, is_val D G (fn y E)
  | mlam_is_val : forall D2 (X:wlink D D2) E, is_val D G (mlam X E).
 Implicit Arguments fn_is_val.
 Implicit Arguments mlam_is_val.

 Inductive is_exval (D G:world) : checked_exp D G -> Prop :=
  | rec_is_val : forall G2 (f:wlink G G2) E, is_exval D G (rec f E).
 Implicit Arguments rec_is_val.
 Definition closed_mterm := meta_term empty.
 Inductive env : world -> Set :=
  | e_nil : env empty
  | e_cons : forall G1 G2, env G1 -> (slink G1 G2)*exval -> env G2
 with val : Set :=
  | v_meta2 : closed_mterm -> val
  | v_val2 : forall D G E, is_val D G E -> msubst D empty -> env G -> val
 with exval : Set :=
  | v_val1 : val -> exval
  | v_rec1 : forall D G E, is_exval D G E -> msubst D empty -> env G -> exval.
 Implicit Arguments v_val2.
 Implicit Arguments v_rec1.
 Implicit Arguments e_nil.
 Implicit Arguments e_cons.
 Coercion v_meta2 : closed_mterm >-> val.

 Inductive env_assigned : forall {γ}, env γ -> name γ -> exval -> Prop :=
  | env_assigned_here   : forall γ γ' (ρ:env γ') (y:γ'↪γ) V,
                        env_assigned (e_cons ρ (y,V)) y V
  | env_assigned_before : forall γ γ' (ρ:env γ') (y:γ'↪γ) V x U,
                        env_assigned ρ x U
                     -> env_assigned (e_cons ρ (y,V)) (import y x) U.
 
 Inductive closure : Set :=
  | meta_term_closure : meta_term empty -> closure
  | comp_term_closure : forall D G, checked_exp D G -> msubst D empty -> env G -> closure.
 Implicit Arguments comp_term_closure.

 Definition val_to_closure (v:val) : closure.
 destruct v. constructor 1. auto.
 set E.
 destruct E; try (elimtype False; inversion i; try inversion H; fail); econstructor 2.
 eexact c. eexact m. exact e.
 eexact c. eexact m. exact e.
 Defined.
 Coercion val_to_closure : val >-> closure.

 Definition exval_to_closure (v:exval) : closure.
 destruct v.
 apply val_to_closure. exact v.
 destruct E; try (elimtype False; inversion i; try inversion H; fail);
 econstructor 2.
 eexact (rec w E). eexact m. exact e.
 Defined.
 Coercion exval_to_closure : exval >-> closure.

 Notation "E [ θ ;; ρ ]" := (comp_term_closure E θ ρ) (at level 80).

 Reserved Notation "E ∷∷ T" (at level 90).
 Definition a {δ δ'} (θ:msubst δ δ') (T1: tp δ) := ⟦ θ ⟧  T1.

 Inductive closure_typ : closure -> tp empty -> Prop :=
  | meta_term_closure_typ : forall C U,
              (· ⊨ C ∷ U)
           -> (meta_term_closure C) ∷∷ U
  | comp_term_closure_typ : forall δ γ (Δ:mtype_assign δ) (Γ:tp_assign' γ δ) E (T:tp δ) (θ:msubst δ empty) (ρ:env γ),
                 · ⊩ θ ∷ Δ
              -> env_tp ρ (⟦θ⟧ Γ)
              -> c_tp Δ Γ E T
              -> (E [θ ;; ρ]) ∷∷ (a θ T)
  with env_tp : forall {γ}, env γ -> tp_assign empty γ -> Prop :=
   | env_tp_nil : env_tp e_nil ·
   | env_tp_cons : forall γ (ρ:env γ) Γ (V:exval) T γ' (y:γ ↪ γ'),
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
 Print fn_is_val.
 Print v_val2.
 Notation "θ /≐ θ'" :=(forall θ'', ~unify θ θ' θ'') (at level 90).
 Notation "θ ≐ θk // θ'" := (unify θ θk θ') (at level 90). 
 Notation "C /≑ D" :=(forall θ, ~unify2 C D θ) (at level 90).
 Notation "C ≑ D // θ" := (unify2 C D θ) (at level 90).
 Inductive eval : closure -> val -> Prop :=
  | ev_val : forall (V:val), eval V V 
  | ev_coerce : forall δ θ γ ρ (E:checked_exp δ γ) T V,
             E [θ ;; ρ] ⇓ V
          -> (coercion E T) [θ ;; ρ] ⇓ V
  | ev_app : forall δ θ γ ρ (I1:synth_exp δ γ) γ' (y:γ ↪ γ')
             (E:checked_exp δ γ') θ' ρ' (E2:checked_exp δ γ) V2 V,
             I1 [θ ;; ρ] ⇓ (v_val2 (fn_is_val y E) θ' ρ')
          -> E2 [θ ;; ρ] ⇓ V2
          -> E [θ' ;; (e_cons ρ' (y,v_val1 V2))] ⇓ V
          -> (app I1 E2) [θ ;; ρ] ⇓ V
  | ev_mapp : forall δ θ γ ρ (I:synth_exp δ γ) δ' (X:δ ↪ δ')
            (E:checked_exp δ' γ) θ' ρ' C V,
             I [θ ;; ρ] ⇓ (v_val2 (mlam_is_val X E) θ' ρ')
          -> E [(θ' ; (⟦θ⟧ C) // X) ;; ρ'] ⇓ V
          -> (mapp I C) [θ ;; ρ] ⇓ V
  | ev_case1 : forall δ θ γ ρ (I:synth_exp δ γ) δi
            (θk:msubst δ δi) Bs Ck Ek V,
            (θ /≐ θk)
         -> case_i I Bs [θ ;; ρ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V
  | ev_case2 : forall δ θ γ ρ (I:synth_exp δ γ) δi
            (θk:msubst δ δi) θ' Bs (C:closed_mterm) Ek V Ck,
            (θ ≐ θk // θ')
         -> I [θ ;; ρ] ⇓ C
         -> (C /≑ ⟦θ'⟧ Ck)
         -> case_i I Bs [θ ;; ρ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V
  | ev_case3 : forall δ θ γ ρ (I:synth_exp δ γ) δi
            (θk:msubst δ δi) θ' θ'' Bs (C:closed_mterm) Ek V Ck,
            (θ ≐ θk // θ')
         -> I [θ ;; ρ] ⇓ C
         -> (C ≑ ⟦θ'⟧ Ck // θ'')
         -> Ek [ ⟦θ''⟧ θ' ;; ρ ] ⇓ V
         -> case_i I ((br Ck θk Ek)::Bs) [θ ;; ρ] ⇓ V 
  | ev_var : forall δ (θ:msubst δ empty) γ ρ (y:name γ) V1 V,
            env_assigned ρ y V1
         -> V1 ⇓ V
         -> (var _ y) [θ ;; ρ] ⇓ V
  | ev_rec : forall δ θ γ ρ γ' (f:γ↪γ') (E:checked_exp δ γ') V,
       E [ θ ;; e_cons ρ (f, v_rec1 (rec_is_val f E) θ ρ) ] ⇓ V
    -> rec f E [θ ;; ρ] ⇓ V
    where "E1 ⇓ V1" := (eval E1 V1).
   Require Import Coq.Program.Equality.
   Implicit Arguments env_tp_cons.
   Notation "[[ C1 // X1 ]]" := (msubst_single_t X1 C1) (at level 90). 
   Axiom subst_combine : forall {γ δ δ'} (θ:msubst δ γ) (X:δ ↪ δ') C T,
     ⟦ θ ; ⟦θ⟧ C // X ⟧ T = ⟦θ⟧ ([[ C // X ]] T).

    Ltac clean_substs :=
      unfold a in *;
      (match goal with
        | [ H : context f [tp_substitutable ?w1 ?w2 ?s1 ?t1] |- ?g ] =>
        replace (tp_substitutable w1 w2 s1 t1) with (⟦ s1 ⟧ t1) in H 
     end).

   Axiom subst_lemma : forall {δ δ':world} C U θ (Δ:mtype_assign δ) (Δ':mtype_assign δ'),
     Δ' ⊩ θ ∷ Δ
  -> Δ  ⊨ C ∷ U
  -> Δ' ⊨ ⟦θ⟧ C ∷ ⟦θ⟧ U.

   Theorem cons_wkn_inv {δ δ' δ'' γ } (θ:msubst δ δ') (X:δ ↪ δ'') (Γ:tp_assign' γ δ) C :
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
   Lemma subst_assoc2 {δ δ' δ'' γ} (Γ:tp_assign δ γ)
    (θ:msubst δ δ') (θ':msubst δ' δ'') :
    app_msubst_tp_assign (⟦θ'⟧θ) Γ =
     app_msubst_tp_assign θ' (app_msubst_tp_assign θ Γ).
   generalize dependent δ'.
   generalize dependent δ''.
   induction Γ; intros.
   reflexivity. destruct r.
   simpl.
   f_equal.
   apply IHΓ.
   f_equal.
   apply subst_assoc3.
   Admitted.

 Lemma env_tp1 : forall γ ρ y V1 T0 (Γ : tp_assign' γ empty),
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

 Lemma env_tp2 : forall δ γ (Γ : tp_assign' γ δ) δ' (θ:msubst δ δ') y T0,
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
   
   assert ((v_val2 (fn_is_val y E) θ' ρ') ∷∷ (⟦θ⟧ (arr T1 T0))).
   apply IHeval1.
   econstructor.
   eexact H9.
   eexact H10.
   constructor.
   eexact H6.

   inversion H5. subst. simpl_existTs. subst.
   destruct T; try discriminate. inversion H17.
   inversion H19. subst. simpl_existTs. subst.
   clean_substs. clean_substs.
    rewrite <- H13.
   pose proof (env_tp_cons (v_val1 V2) y H18 H3).
   
   apply IHeval3.
   Print closure_typ. 
   econstructor.
   eexact H14.
   instantiate (1 := (v_cons Γ0 (y,T2))).
   rewrite <- H12 in H7.
   eexact H7.
   exact H15.
   reflexivity.
   reflexivity.   

   (* Case: meta application *)
   unfold a in *. inversion H10. subst.
   inversion H3. simpl_existTs. subst.
   assert ((v_val2 (mlam_is_val X E) θ' ρ') ∷∷ (⟦θ⟧ (prod X0 U T))).
   apply IHeval1.
   econstructor.
   eexact H8. eexact H9. constructor. eexact H5.
   
   inversion H2. subst. simpl_existTs. subst.
   inversion H17. subst. simpl_existTs. subst.
   inversion H15. simpl_existTs. unfold weaken1 in *.
   clean_substs. Focus 2. reflexivity.
   destruct (next empty) as [α X']. simpl in *.
   apply IHeval2.
   rewrite <- subst_combine.
   unfold msubst.
   change (s_cons δ' (theta_weaken θ' X') (X, m_var X'))
     with  ((theta_weaken θ' X') ; (m_var X') // X) in H4.
   change (s_cons δ'0 (theta_weaken θ X') (X0, m_var X'))
     with  ((theta_weaken θ X') ; (m_var X') // X0) in H4.
   change (app_msubst_t θ' U0) with (⟦θ'⟧ U0) in H6. 
   change (app_msubst_t θ U) with (⟦θ⟧ U) in H6.
   replace (⟦θ ; ⟦θ⟧ C // X0⟧ T) with (⟦θ'; ⟦θ⟧ C // X⟧ T1).
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
   eapply msubst_ext.
   eauto.
  
   (* case statement 1 *)
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

   (* case statement 2 *)
   eapply IHeval2.
   econstructor.
   eexact H10.
   eexact H11.
   inversion H12. subst.
   econstructor.   
   eexact H6.
   intros. apply H8.
   constructor 2. auto.

   (* case statement 3 *)
   inversion H12. subst.
   assert (C ∷∷ a θ U).
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
   inversion H14. simpl_existTs. subst. (* We diverge here *)
   eapply IHeval2.
   simpl.
   rewrite subst_assoc.
   rewrite subst_id.
   change (Ek [θ';; ρ] ∷∷ a θ' (app_msubst_t θk T)).
   econstructor.
   eexact H13.   
   pose proof (subst_assoc2 Γ θk θ').
   unfold app_subst in H11 at 1.
   unfold tp_assign_substitutable in H11.
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
   unfold app_subst. unfold tp_assign_substitutable.
   simpl.
   econstructor; eauto.
  Qed.
  Print Assumptions subj_red.
