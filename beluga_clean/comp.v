Require Export meta.
Require Export List.
Set Implicit Arguments.

(* Note we only allow one type variable at a time.
   Hmm. Why is this OK again? *)
Inductive tp' ψ (δ:world):=
  | m_tp : mtype δ -> tp' ψ δ
  | arr : tp' ψ δ -> tp' ψ δ -> tp' ψ δ
  | pi : forall δ', δ↪δ' -> mtype δ -> tp' ψ δ' -> tp' ψ δ
  | sigma : forall δ', δ↪δ' -> mtype δ -> tp' ψ δ' -> tp' ψ δ
  | unit : tp' ψ δ
  | prod : tp' ψ δ -> tp' ψ δ -> tp' ψ δ
  | sum : tp' ψ δ -> tp' ψ δ -> tp' ψ δ
  | tapp : neutral_tp ψ δ -> meta_term δ -> tp' ψ δ
  | eq_constraint : meta_term δ -> meta_term δ -> tp' ψ δ -> tp' ψ δ
with neutral_tp ψ (δ:world) :=
  | tvar : name ψ -> neutral_tp ψ δ
  | mu : forall ψ' δ', ∅↪ψ' -> δ↪δ' ->
       mtype δ -> tp' ψ' δ' -> neutral_tp ψ δ
.
Implicit Arguments mu [ψ δ ψ' δ'].
Implicit Arguments unit [ψ δ].
Definition tp δ := tp' ∅ δ.
Definition m_tp' {δ} := @m_tp ∅ δ : mtype δ -> tp δ.
Coercion m_tp' : mtype >-> tp.


Section app_msubst_tp_sect.

Reserved Notation "[ θ ] T" (at level 90).
Fixpoint app_msubst_tp {ψ} {δ δ'} (θ:msubst δ δ') (T:tp' ψ δ) : tp' ψ δ' :=
match T  with
 | m_tp U     =>
   m_tp _ (〚θ〛 U)
 | arr T1 T2  =>
   arr ([θ] T1) ([θ] T2)
 | pi _ X U T0 =>
   let X' := succ_link δ' in
   pi X' (〚θ〛 U) ([ θ × (X' // X ) ] T0)
 | sigma _ X U T0 =>
   let X' := succ_link δ' in
   sigma X' (〚θ〛 U) ([ θ × (X' // X ) ] T0)
 | unit =>
   unit
 | prod T1 T2 =>
   prod ([θ] T1) ([θ] T2)
 | sum T1 T2 =>
   sum ([θ] T1) ([θ] T2)
 | tapp N C =>
   tapp (app_msubst_neutral_tp θ N) (〚θ〛 C)
 | eq_constraint C1 C2 T0 =>
   eq_constraint (〚θ〛 C1) (〚θ〛 C2) ([θ] T0)
 
end
with app_msubst_neutral_tp {ψ} {δ δ'} (θ:msubst δ δ') (N:neutral_tp ψ δ) : neutral_tp ψ δ' :=
match N with
 | tvar n => tvar _ n
 | mu ψ' ε Z X U T0 =>
    let X' := succ_link δ' in
    mu Z X' (〚θ〛 U) ([ θ × (X' // X) ] T0)
end
where "[ θ ] T" := (app_msubst_tp θ T).

End app_msubst_tp_sect.

Instance tp_substitutable' {ψ} : substitutable (tp' ψ) := {
  app_subst := @app_msubst_tp ψ
}.
admit.
Defined.

Instance neutral_tp_substitutable' {ψ} : substitutable (neutral_tp ψ) := {
  app_subst := @app_msubst_neutral_tp ψ
}.
admit.
Defined.

Instance tp_substitutable : substitutable tp := {
  app_subst := @app_subst _ tp_substitutable';
  assoc := @assoc _ tp_substitutable'
}.

Section app_tp_subst_sec.
Reserved Notation "[ θ ] T" (at level 90).

Definition app_tp_subst_neutral {ψ ψ'} {δ} (θ:name ψ -> neutral_tp ψ' δ) (N:neutral_tp ψ δ) : neutral_tp ψ' δ :=
match N with
 | tvar n => θ n
 | mu ψ'' ε Z X U T0 =>
   mu Z X U T0
end.
Fixpoint app_tp_subst {ψ ψ'} {δ} (θ:name ψ -> neutral_tp ψ' δ) (T:tp' ψ δ) : tp' ψ' δ :=
match T  with
 | m_tp U     =>
   m_tp _ U
 | arr T1 T2  =>
   arr ([θ] T1) ([θ] T2)
 | pi _ X U T0 =>
   pi X U ([app_msubst_neutral_tp (↑X) ○ θ] T0)
 | sigma _ X U T0 =>
   sigma X U ([app_msubst_neutral_tp (↑X) ○ θ] T0)
 | unit =>
   unit
 | prod T1 T2 =>
   prod ([θ] T1) ([θ] T2)
 | sum T1 T2 =>
   sum ([θ] T1) ([θ] T2)
 | tapp N C =>
   tapp (app_tp_subst_neutral θ N) C
 | eq_constraint C1 C2 T0 =>
   eq_constraint C1 C2 ([θ] T0)
end
where "[ θ ] T" := (app_tp_subst θ T).
Definition app_tp_subst_single {ψ δ}
(N:neutral_tp ∅ δ) (T:tp' ψ δ) : tp' ∅ δ :=
app_tp_subst (fun n => N) T.
End app_tp_subst_sec.

Inductive synth_exp (δ γ:world) : Set :=
  | var : name γ -> synth_exp δ γ
  | app :  synth_exp δ γ -> checked_exp δ γ -> synth_exp δ γ
  | mapp : synth_exp δ γ -> meta_term δ -> synth_exp δ γ
  | coercion : checked_exp δ γ -> tp δ -> synth_exp δ γ
  | unfold : synth_exp δ γ -> synth_exp δ γ
 with checked_exp (δ γ:world) : Set := 
  | synth : synth_exp δ γ -> checked_exp δ γ
  | meta : meta_term δ -> checked_exp δ γ
  | fn : forall γ', γ↪γ' -> checked_exp δ γ' -> checked_exp δ γ
  | mlam : forall δ', δ↪δ' -> checked_exp δ' γ -> checked_exp δ γ
  | rec : forall γ', γ↪γ' -> checked_exp δ γ' -> checked_exp δ γ
  | fold : checked_exp δ γ -> checked_exp δ γ
  | inl : checked_exp δ γ -> checked_exp δ γ
  | inr : checked_exp δ γ -> checked_exp δ γ
  | pack : meta_term δ -> checked_exp δ γ -> checked_exp δ γ
  | pair : checked_exp δ γ -> checked_exp δ γ -> checked_exp δ γ
  | tt : checked_exp δ γ
  | clos : forall δ' γ', checked_exp δ' γ' -> msubst δ' δ -> (name γ' -> checked_exp δ γ) -> checked_exp δ γ
  | case_i :  synth_exp δ γ -> list (branch δ γ) -> checked_exp δ γ
 with branch (δ γ:world) : Set :=
  | br : forall δi γi, checked_exp δi γi -> msubst δ δi -> checked_exp δi γ -> branch δ γ.
Implicit Arguments tt [δ γ].
Coercion synth : synth_exp >-> checked_exp.
Definition env γ := name γ -> checked_exp ∅ ∅.
Notation "E [ θ ;; ρ ]" := (clos E θ ρ) (at level 0).

Reserved Notation "D1 ; G1 ⊢ t1 ⇐ T1" (at level 90).
Reserved Notation "D1 ; G1 ⊢ t1 ⇒ T2" (at level 90).

Definition tp_assign γ δ := name γ -> tp δ.


Definition env_tp {δ γ γ'} (Δ:mtype_assign δ) (Γ:tp_assign γ δ) ρ (Γ':tp_assign γ' δ) (tp_rel:checked_exp δ γ -> tp δ -> Prop) :=
forall x, tp_rel (ρ x) (Γ' x).
Reserved Notation "Δ ; Γ ⊪ ρ ⇐ Γ'" (at level 90).

Inductive synth_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign γ δ}
                   : synth_exp δ γ -> tp δ -> Prop :=
  | var_s : forall x T,
             Γ x = T
           -> Δ;Γ ⊢ (var _ x) ⇒ T
  | app_s : forall I T1 E T2,
              Δ;Γ ⊢ I ⇒ (arr T1 T2)
           -> Δ;Γ ⊢ E ⇐ T1
           -> Δ;Γ ⊢ (app I E) ⇒ T2
  | mapp_s : forall I δ' (X:δ↪δ') U C T,
              Δ;Γ ⊢ I ⇒ (pi X U T)
           -> Δ ⊨ C ∷ U
           -> Δ;Γ ⊢ (mapp I C) ⇒ (〚single_subst X C〛 T)
  | coerce_s : forall E T,
              Δ;Γ ⊢ E ⇐ T
           -> Δ;Γ ⊢ (coercion E T) ⇒ T
  | unfold_c : forall I δ' (X:δ↪δ') ψ (Z:∅↪ψ) U C T,
              Δ;Γ ⊢ I ⇒ (tapp (mu Z X U T) C) 
           -> Δ;Γ ⊢ unfold I ⇒ (app_tp_subst_single
                          (mu Z X U T) 
                          (〚single_subst X C〛 T))
 with checks_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign γ δ}
                   : checked_exp δ γ -> tp δ -> Prop :=
  | synth_c : forall I T,
              Δ;Γ ⊢ I ⇒ T
           -> Δ;Γ ⊢ I ⇐ T
  | meta_c : forall C U,
              Δ ⊨ C ∷ U 
           -> Δ;Γ ⊢ (meta γ C) ⇐ U
  | fn_c : forall γ' (y:γ↪γ') E T1 T2,
             Δ;(Γ,, (y,T1)) ⊢ E ⇐ T2
          -> Δ;Γ ⊢ (fn y E) ⇐ (arr T1 T2)
  | mlam_c : forall δ' (X:δ↪δ') E U T,
             (* TODO: Clean this up *)
             (〚@m_var _ ○ ↑X〛 ○ (Δ,, (X,U)));(〚@m_var _ ○ ↑X〛 ○ Γ) ⊢ E ⇐ T
          -> Δ;Γ ⊢ (mlam X E) ⇐ (pi X U T)
  | rec_c : forall γ' (f:γ↪γ') E T,
             Δ;(Γ,, (f,T)) ⊢ E ⇐ T
          -> Δ;Γ ⊢ (rec f E) ⇐ T
  | inl_c : forall E T S,
             Δ;Γ ⊢ E ⇐ T
          -> Δ;Γ ⊢ (inl E) ⇐ (sum T S)
  | inr_c : forall E T S,
             Δ;Γ ⊢ E ⇐ S
          -> Δ;Γ ⊢ (inr E) ⇐ (sum T S)
  | pair_c : forall E1 E2 T S,
             Δ;Γ ⊢ E1 ⇐ T
          -> Δ;Γ ⊢ E2 ⇐ S
          -> Δ;Γ ⊢ (pair E1 E2) ⇐ (prod T S)
  | pack_c : forall E δ' (X:δ↪δ') U C T,
              Δ ⊨ C ∷ U
           -> Δ;Γ ⊢ E ⇐ (〚single_subst X C〛 T) 
           -> Δ;Γ ⊢ (pack C E) ⇐ (sigma X U T)
  | fold_c : forall E δ' (X:δ↪δ') ψ (Z:∅↪ψ) U C T,
              Δ;Γ ⊢ E ⇐ (app_tp_subst_single
                          (mu Z X U T) 
                          (〚single_subst X C〛 T))
           -> Δ;Γ ⊢ fold E ⇐ (tapp (mu Z X U T) C)
  | tt_c : Δ;Γ ⊢ tt ⇐ unit
  | clos_c : forall δ' γ' Δ' Γ' (E:checked_exp δ' γ') T ρ θ,
              Δ';Γ' ⊢ E ⇐ T
           -> Δ ⊩ θ ∷ Δ'
           -> Δ;Γ ⊪ ρ ⇐ (〚θ〛 ○ Γ')
           -> Δ;Γ ⊢ E[θ;;ρ] ⇐ 〚θ〛T
 (* | case_i_c : forall I U Bs T,
             Δ;Γ ⊢ I ⇒ U
          -> (forall B, In B Bs -> branch_tp B (arr U T))
          -> Δ;Γ ⊢ (case_i I Bs) ⇐ T 
 with branch_tp {δ γ:world} {Δ:mtype_assign δ} {Γ:tp_assign γ δ}
                     : branch δ γ -> tp δ -> Prop :=
  | br_c : forall δi (C:meta_term δi) (θi:msubst δ δi)
                  (E:checked_exp δi γ) (U T:mtype δ)
                  (Δi:mtype_assign δi),
             Δi ⊨ C ∷ 〚θi〛 U
          -> Δi ⊩ θi ∷ Δ
          -> Δi;(〚θi〛 ○ Γ) ⊢ E ⇐ 〚θi〛T
          -> branch_tp (br C θi E) (arr (m_tp' U) (m_tp' T)) *)
  where "D1 ; G1 ⊢ t1 ⇒ T1" := (@synth_tp _ _ D1 G1 t1 T1)
  and   "D1 ; G1 ⊢ t1 ⇐ T1" := (@checks_tp _ _ D1 G1 t1 T1)
  and   "Δ ; Γ ⊪ ρ ⇐ Γ'" := (env_tp Δ Γ ρ Γ' (@checks_tp _ _ Δ Γ)).

Lemma tp_subst_commute {δ ψ δ'} (T:neutral_tp ∅ δ) (U:tp' ψ δ) : forall  (θ:msubst δ δ'),
〚θ〛 (app_tp_subst_single T U) = app_tp_subst_single (〚θ〛T) (〚θ〛 U).
induction U; intros; simpl.
admit. (* TODO *)
unfold app_tp_subst_single.
simpl.
f_equal.
apply IHU1.
apply IHU2.
Admitted. (* TODO *)

Lemma env_tp_cons {δ γ γ'} (Δ:mtype_assign δ) (Γ:tp_assign γ δ) (Γ':tp_assign γ' δ) ρ {γ''} (y:γ'↪γ'') V T:
   Δ;Γ ⊪ ρ ⇐ Γ'
-> Δ;Γ ⊢ V ⇐ T
-> Δ;Γ ⊪ (ρ,, (y, V)) ⇐ (Γ',, (y, T)).
intros. intro.
unfold compose.
destruct (export y x); simpl; eauto.
Qed.

Lemma env_typing_eq {δ γ γ'} (Δ:mtype_assign δ) (Γ:tp_assign γ δ)
(Γ' Γ'':tp_assign γ' δ) ρ :
   Γ'' = Γ' 
-> Δ;Γ ⊪ ρ ⇐ Γ'
-> Δ;Γ ⊪ ρ ⇐ Γ''.
intros. subst. assumption.
Qed.