Require Import List.

Section foo.
 Parameter world : Set.
 Parameter empty : world.
 Parameter name : world -> Set.
 Parameter wlink : world -> world -> Set.
 Definition slink := wlink. (* ??? *)
 Definition weaken1 {a b} (x:slink a b) : wlink a b := x.
 Axiom weaken1_inj : forall {W W'} {y y':slink W W'}, weaken1 y = weaken1 y' -> y = y'.
 Parameter weaken : forall {a b}, slink a b -> name b.
 Coercion weaken : slink >-> name.
 Parameter import : forall {a b}, slink a b -> name a -> name b.
 Parameter next : forall a, {b:world & slink a b}.
 
 Inductive meta_term (D:world) :=
  | m_z
  | m_succ : meta_term D -> meta_term D
  | m_var : name D -> meta_term D.
 Inductive mtype (D:world) :=
  | m_nat : mtype D
  | m_vec : meta_term D -> mtype D.
 Coercion m_var : name >-> meta_term.
 	       	 
 Implicit Arguments m_nat [D].
 Implicit Arguments m_vec [D].
 Implicit Arguments m_z [D].
 Implicit Arguments m_succ [D].
 Implicit Arguments m_var [D].

 Fixpoint import_meta_term {D1 D2:world} (y:slink D1 D2) (t:meta_term D1) := 
 match t with
  | m_z => m_z
  | m_succ t => m_succ (import_meta_term y t)
  | m_var x => m_var (import y x)
 end.

 Fixpoint import_mtype {D1 D2:world} (y:slink D1 D2) (T:mtype D1) :=
 match T with
  | m_nat => m_nat
  | m_vec t => m_vec (import_meta_term y t)
 end.

 Section star.
 Hypotheses (A:Set) (Rel:A -> A -> Set).
 Inductive star (a:A) : A -> Set :=
  | s_nil : star a a
  | s_cons : forall b c, star a b -> Rel b c -> star a c.
 End star.
 Implicit Arguments star.
 Implicit Arguments s_nil.
 Implicit Arguments s_cons.
 Print Implicit s_cons.

 Open Scope type_scope.
 Definition var_mtp D1 D2 := (slink D1 D2)*(mtype D1).
 Definition mtype_assign := star var_mtp empty.
 Definition m_cons := @s_cons _ var_mtp empty.
 Implicit Arguments m_cons.
 Print Implicit m_cons.
 
 (* This is basically the "In" predicate, except that we import things to the end *)
 Inductive m_assigned D : mtype_assign D -> name D -> mtype D -> Prop :=
  | m_asn_top : forall D' (A:mtype_assign D') T x,
                    m_assigned D (m_cons A (x,T)) x (import_mtype x T)
  | m_asn_else : forall D' T A x (y:slink D' D) U,
                 m_assigned D' A x T
                 -> m_assigned D (m_cons A (y,U)) (import y x) (import_mtype y T). 
 Implicit Arguments m_assigned.
 Implicit Arguments m_asn_top.
 Implicit Arguments m_asn_else.

 Inductive m_oft {D':world} {D:mtype_assign D'} : meta_term D' -> mtype D' -> Prop :=
  | m_z_tp : m_oft m_z m_nat
  | m_succ_tp : forall n, m_oft n m_nat -> m_oft (m_succ n) m_nat
  | m_var_tp : forall y T, m_assigned D y T -> m_oft y T
 .

 Implicit Arguments m_oft.

 Notation "D ⊨ t ∷ U" := (m_oft D t U) (at level 90).
 (* wf_mtype A T if T is a well-formed meta-type in the context A *)
   
 Inductive wf_mtype {D:world} {A:mtype_assign D} : mtype D -> Prop :=
  | m_nat_tp : wf_mtype m_nat
  | m_vec_tp : forall t, m_oft A t m_nat -> wf_mtype (m_vec t).
 Implicit Arguments wf_mtype.

 (* Well formed meta-contexts *)
 (* Inductive wf_mctx {D:world} : mtype_assign D -> Prop := . *)
 (* TODO: Do we need to make wf_mtype depend on wf_mctx?
    Can we to inforce this invariant? Should we just quantify all our theorems
    with the assumptions that wf_mctx and wf_mtype, etc...? *)

 Inductive tp (D:world) :=
  | m_tp : mtype D -> tp D
  | arr : tp D -> tp D -> tp D
  | prod : forall D2, wlink D D2 -> mtype D -> tp D2 -> tp D
 .
 Coercion m_tp : mtype >-> tp.
 Implicit Arguments m_tp.
 Implicit Arguments arr.
 Implicit Arguments prod.

 (* TODO. Is this even possible? Should it produce a world D2 and link? *)
 Axiom import_tp : forall {D1 D2:world} (y:slink D1 D2) (T:tp D1), tp D2.

 Definition mbind D D1 D2 := (slink D1 D2)*(meta_term D).
 Definition msubst D R := star (mbind R) empty D.
 Definition msubst_cons D R := @s_cons _ (mbind R) empty D.
 Implicit Arguments msubst_cons.

 Inductive synth_exp (D G:world) : Set :=
  | var : name G -> synth_exp D G
  | app :  synth_exp D G -> checked_exp D G -> synth_exp D G
  | mapp : synth_exp D G -> meta_term D -> synth_exp D G
  | coercion : checked_exp D G -> tp D -> synth_exp D G
 with checked_exp (D G:world) : Set := 
  | synth : synth_exp D G -> checked_exp D G
  | meta : meta_term D -> checked_exp D G
  | fn : forall G2, wlink G G2 -> checked_exp D G2 -> checked_exp D G
  | mlam : forall D2, wlink D D2 -> checked_exp D2 G -> checked_exp D G
  | case_i :  synth_exp D G -> list (branch D G) -> checked_exp D G
  | case_c : meta_term D -> list (branch D G) -> checked_exp D G
  | rec : forall G2, wlink G G2 -> checked_exp D G2 -> checked_exp D G
 with branch (D G:world) : Set :=
  | br : forall Di, meta_term Di -> msubst D Di -> checked_exp Di G -> branch D G.
 Coercion synth : synth_exp >-> checked_exp.
 Implicit Arguments var.
 Implicit Arguments app.
 Implicit Arguments mapp.
 Implicit Arguments coercion.
 Implicit Arguments synth.
 Implicit Arguments meta.
 Implicit Arguments fn.
 Implicit Arguments mlam.
 Implicit Arguments case_i.
 Implicit Arguments case_c.
 Implicit Arguments rec.
 Implicit Arguments br.

 Definition var_tp D G1 G2 := (slink G1 G2)*(tp D).
 Definition tp_assign D := star (var_tp D) empty.
 Definition tp_assign_nil D := @s_nil _ (var_tp D).
 Definition v_cons D := @s_cons _ (var_tp D) empty.
 Implicit Arguments v_cons.
 Print Implicit v_cons.

 (* TODO: We could eliminate the duplication between this and the other one *)
 Inductive var_assigned D G : tp_assign D G -> name G -> tp D -> Prop :=
  | v_asn_top : forall G' (A:tp_assign D G') T x,
                    var_assigned D G (v_cons A (x,T)) x T
  | v_asn_else : forall G' T A x (y:slink G' G) U,
                 var_assigned D G' A x T
                 -> var_assigned D G (v_cons A (y,U)) (import y x) T.
 Implicit Arguments var_assigned.
 
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
 
 Axiom msubst_single_t : forall {D D'} (X:wlink D D'), meta_term D -> tp D' -> tp D.
 (* Write this in terms of a simultaneous substitution: (id,C/X) ? *)
 Axiom app_msubst : forall W W', msubst W W' -> meta_term W -> meta_term W'.
 Axiom app_msubst_t : forall W W', msubst W W' -> mtype W -> mtype W'.
 Implicit Arguments app_msubst.
 Implicit Arguments app_msubst_t.
 Class substitutable (A:world -> Set) := 
   app_subst : forall {α β}, msubst α β -> A α -> A β.
 
 Instance meta_term_substitutable : substitutable meta_term := app_msubst.
 Instance mtype_substitutable : substitutable mtype := app_msubst_t. 
 (* Termination of these is going to be tricky, since it depends on their typing, which
    we define in terms of application. Maybe it's better to state it as a relation
    and prove total separately
  *)

 Axiom theta_weaken : forall {D R} (theta:msubst D R) {R'} (X:wlink R R'), msubst D R'.
 Definition app_msubst_t2' : forall {W} (T:tp W) {W'} (theta:msubst W W'), tp W'.
 induction 1; intros.
 apply m_tp.
 eapply app_msubst_t. eexact theta. exact m.
 apply arr. apply IHT1. exact theta. apply IHT2. exact theta.
 Print Implicit prod.
 Print projT1.
 apply (prod (projT2 (next W'))).
 eapply app_msubst_t. eexact theta. eexact m.
 apply IHT.
 econstructor. eapply theta_weaken. eexact theta.
 eexact (projT2 (next W')).
 split. eexact w. constructor 3. eapply (weaken (projT2 (next W'))).
 Defined.
 Definition app_msubst_t2 {W W'} (theta:msubst W W') (T:tp W) : tp W' := app_msubst_t2' T theta.
 
 Fixpoint app_msubst_tp_assign' {W G'} (G:tp_assign W G') : forall {W'} (theta:msubst W W'), tp_assign W' G' :=
  match G in star _ _ G' return forall {W'} (theta:msubst W W'), star (var_tp W') empty G' with
   | s_nil => fun W' theta => s_nil (var_tp W') _
   | s_cons _ _ a (b,c) => fun W' theta => s_cons _ (app_msubst_tp_assign' a _ theta) (b,app_msubst_t2 theta c)
  end.
 
 Definition app_msubst_tp_assign {G' W W'} (theta:msubst W W') (G:tp_assign W G') : tp_assign W' G' := app_msubst_tp_assign' G _ theta.
 Definition tp_assign' δ γ := tp_assign γ δ.
 Instance tp_assign_substitutable γ : substitutable (tp_assign' γ) := (@app_msubst_tp_assign γ).

 Instance tp_substitutable : substitutable tp := @app_msubst_t2.

 Axiom app_msubst_msubst : forall {δ δ' δ''} (θ':msubst δ' δ'') (θ':msubst δ δ'), msubst δ δ''.
 Instance msubst_substitutable {δ} : substitutable (msubst δ)
  := @app_msubst_msubst δ.

 Implicit Arguments app_msubst.
 Implicit Arguments app_msubst_t.
 Implicit Arguments app_msubst_t2.
 Implicit Arguments app_msubst_tp_assign.
 Notation "⟦ θ ⟧" := (app_subst θ). 
 Notation "α ↪ β" := (slink α β) (at level 90).

 Implicit Arguments s_nil [A Rel a].
 Reserved Notation "D ⊩ T ∷ D2" (at level 90).
 Notation "T ;  t // y " := (msubst_cons T (y,t)) (at level 90).
 Notation "D ; y ∷ U" := (m_cons D (y,U)) (at level 90).
 Notation "·" := (s_nil).
 Inductive msubst_typ' {α}(Δ:mtype_assign α) : forall {β}(Δ':mtype_assign β), msubst β α ->Prop :=
  | m_subst_typ_nil :
           Δ ⊩ · ∷ ·
  | m_subst_typ_cons : forall β Δ' γ (y:β ↪ γ) U t θ,
           Δ ⊩ θ ∷ Δ' 
        -> Δ ⊨ t ∷ (⟦θ⟧ U)
        -> Δ ⊩ (θ; t//y) ∷ (Δ'; y∷U)
  where "D ⊩ T ∷ D2" := (@msubst_typ' _ D _ D2 T).
 
Definition msubst_typ {α} (Δ:mtype_assign α) {β} (Δ':mtype_assign β) θ := msubst_typ' Δ' Δ θ.
 Check @app_subst.
 Reserved Notation "D1 ; G1 ⊢ t1 ⇐ T1" (at level 90).
 Reserved Notation "D1 ; G1 ⊢ t1 ⇒ T2" (at level 90).
 Inductive s_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign δ γ}
                   : synth_exp δ γ -> tp δ -> Prop :=
  | var_s : forall x T,
             var_assigned Γ x T
           -> Δ;Γ  ⊢ (var _ x) ⇒ T
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
  (* | case_i | case_c ... TODO *)
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
 
 Inductive env : world -> Set :=
  | e_nil : env empty
  | e_cons : forall G1 G2, env G1 -> (slink G1 G2)*exval -> env G2
 with val : Set :=
  | v_meta2 : meta_term empty -> val
  | v_val2 : forall D G E, is_val D G E -> msubst D empty -> env G -> val
 with exval : Set :=
  | v_val1 : val -> exval
  | v_rec1 : forall D G E, is_exval D G E -> msubst D empty -> env G -> exval.
 Implicit Arguments v_val2.
 Implicit Arguments e_nil.
 Implicit Arguments e_cons.

 Inductive closure : Set :=
  | meta_term_closure : meta_term empty -> closure
  | comp_term_closure : forall D G, checked_exp D G -> msubst D empty -> env G -> closure.
 Implicit Arguments comp_term_closure.

 Definition val_to_closure (v:val) : closure.
 destruct v. constructor 1. exact m.
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
 

 Definition unify {δ δ' δ''} (θ:msubst δ δ') (θk:msubst δ δ'')
  (θ':msubst δ'' δ') := θ = ⟦θ'⟧ θk.

 Definition unify2 {δ δ' δ''} (θ:msubst δ δ') 
   Inductive eval : closure -> val -> Prop :=
    | ev_val : forall (V:val), eval V V
    | ev_coerce : forall δ θ γ ρ (E:checked_exp δ γ) T V,
               E [θ ;; ρ] ⇓ V
            -> (coercion E T) [θ ;; ρ] ⇓ V
    | ev_app : forall δ θ γ ρ (I1:synth_exp δ γ) γ' (y:γ ↪ γ')
               (E:checked_exp γ γ') θ' ρ' (E2:checked_exp δ γ) V2 V,
               I1 [θ ;; ρ] ⇓ (v_val2 (fn_is_val y E) θ' ρ')
            -> E2 [θ ;; ρ] ⇓ V2
            -> E [θ' ;; (e_cons ρ' (y,v_val1 V2))] ⇓ V
            -> (app I1 E2) [θ ;; ρ] ⇓ V
    | ev_mapp : forall δ θ γ ρ (I:synth_exp δ γ) δ' (X:δ ↪ δ')
               (E:checked_exp δ' γ) θ' ρ' C V,
               I [θ ;; ρ] ⇓ (v_val2 (mlam_is_val X E) θ' ρ')
            -> E [(θ' ; (⟦θ⟧ C) // X) ;; ρ'] ⇓ V
            -> (mapp I C) [θ ;; ρ] ⇓ V
    | ev_
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
   Qed.
   
End foo.