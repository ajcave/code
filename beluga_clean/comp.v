Require Export meta.
Require Export List.
Require Export Coq.Program.Equality.
Set Implicit Arguments.

(* Note we only allow one type variable at a time.
   Hmm. Why is this OK again? *)
(* Note that we only index by a single meta_term in tapp,
   unlike the general theory. *)
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

Reserved Notation "[ θ ]" (at level 90).
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
where "[ θ ]" := (app_msubst_tp θ).
Scheme tp'_ind2 := Induction for tp' Sort Prop
with neutral_tp_ind2 := Induction for neutral_tp Sort Prop.

Require Import Coq.Logic.FunctionalExtensionality.
Lemma app_msubst_tp_hom : forall ψ δ (T:tp' ψ δ) {δ' δ''} (θ2:msubst δ' δ'') (θ1:msubst δ δ'),
[θ2]([θ1]T) = [〚θ2〛 ○ θ1]T.
eapply (tp'_ind2
 (fun ψ δ T => forall {δ' δ''} (θ2:msubst δ' δ'') (θ1:msubst δ δ'),
    [θ2]([θ1]T) = [〚θ2〛 ○ θ1]T)
 (fun ψ δ T => forall {δ' δ''} (θ2:msubst δ' δ'') (θ1:msubst δ δ'),
    app_msubst_neutral_tp θ2 (app_msubst_neutral_tp θ1 T) = app_msubst_neutral_tp (〚θ2〛 ○ θ1) T)); intros.
unfold app_msubst_tp. erewrite assoc. reflexivity.
simpl. f_equal.
erewrite H. reflexivity.
erewrite H0. reflexivity.
simpl. f_equal.
erewrite app_msubst_mtype_assoc. reflexivity.
erewrite H.
f_equal. erewrite compose_product. reflexivity.
simpl. f_equal.
erewrite app_msubst_mtype_assoc. reflexivity.
erewrite H.
f_equal. erewrite compose_product. reflexivity.
reflexivity.
simpl. f_equal.
erewrite H. reflexivity.
erewrite H0. reflexivity.
simpl. f_equal.
erewrite H. reflexivity.
erewrite H0. reflexivity.
simpl. f_equal.
erewrite H. reflexivity.
erewrite app_msubst_assoc. reflexivity.
simpl. f_equal.
erewrite app_msubst_assoc. reflexivity.
erewrite app_msubst_assoc. reflexivity.
erewrite H. reflexivity.
reflexivity.
simpl. f_equal.
erewrite app_msubst_mtype_assoc. reflexivity.
erewrite H. f_equal.
erewrite compose_product. reflexivity.
Qed.
End app_msubst_tp_sect.

Instance tp_substitutable' {ψ} : substitutable (tp' ψ) := {
  app_subst := @app_msubst_tp ψ
}.
intros. eapply app_msubst_tp_hom.
Defined.

Instance neutral_tp_substitutable' {ψ} : substitutable (neutral_tp ψ) := {
  app_subst := @app_msubst_neutral_tp ψ
}.
intros.
destruct t. simpl. reflexivity.
simpl. f_equal. erewrite app_msubst_mtype_assoc. reflexivity.
erewrite app_msubst_tp_hom. f_equal.
erewrite compose_product. reflexivity.
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
Notation "〈 T 〉" := (app_tp_subst_single T) (at level 0).


Inductive pat (γ δ:world) : Set :=
  | pvar : name γ -> pat γ δ
  | pmeta : meta_term δ -> pat γ δ
  | pfold : pat γ δ -> pat γ δ
  | pinl : pat γ δ -> pat γ δ
  | pinr : pat γ δ -> pat γ δ
  | ppack : meta_term δ -> pat γ δ -> pat γ δ
  | ppair : pat γ δ -> pat γ δ -> pat γ δ
  | ptt : pat γ δ.
Implicit Arguments ptt [γ δ].

Fixpoint add_eq {ψ δ} (constraints:list (meta_term δ)) (T:tp' ψ δ) : tp' ψ δ :=
match constraints with
| nil => T
| cons C Cs => eq_constraint C C (add_eq Cs T)
end.

Definition tp_assign γ δ := name γ -> tp δ.
Inductive synth_exp (δ γ:world) : Set :=
  | var : name γ -> synth_exp δ γ
  | app :  synth_exp δ γ -> checked_exp δ γ -> synth_exp δ γ
  | mapp : synth_exp δ γ -> meta_term δ -> synth_exp δ γ
  | coercion : checked_exp δ γ -> tp δ -> synth_exp δ γ
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
  | case_i :  synth_exp δ γ -> list (branch δ γ) -> checked_exp δ γ
 with branch (δ γ:world) : Set :=
  | br : forall δi (Δi:mtype_assign δi) n (Γi:vec (tp δi) n), pat (∅ + n) δi -> msubst δ δi
    -> checked_exp δi (γ + n) -> branch δ γ.
Implicit Arguments tt [δ γ].
Coercion synth : synth_exp >-> checked_exp.

Inductive val : Set :=
  | vmeta : meta_term ∅ -> val
  | vfn : forall δ γ γ', γ↪γ' -> checked_exp δ γ'
      -> msubst δ ∅ -> (name γ -> extended_val) -> val
  | vmlam : forall δ δ' γ, δ↪δ' -> checked_exp δ' γ
      -> msubst δ ∅ -> (name γ -> extended_val) -> val
  | vfold : val -> val
  | vinl : val -> val
  | vinr : val -> val
  | vpack : meta_term ∅ -> val -> val
  | vpair : val -> val -> val
  | vtt : val
with extended_val : Set :=
| evval : val -> extended_val
| evrec : forall δ γ γ' (f:γ↪γ') (E:checked_exp δ γ') (θ:msubst δ ∅)
           (ρ:name γ -> extended_val), extended_val.
Coercion evval : val >-> extended_val.
Definition env γ := name γ -> extended_val.

Reserved Notation "Δ ; Γ ⊢ t ⇐ T" (at level 90).
Reserved Notation "Δ ; Γ ⊢ t ⇒ T" (at level 90).

Inductive pat_tp {δ γ:world} (Δ:mtype_assign δ) (Γ:tp_assign γ δ)
                   : pat γ δ -> tp δ -> Prop :=
  | pvar_c : forall x T,
             Γ x = T
           -> pat_tp Δ Γ (pvar _ x) T
  | pmeta_c : forall C U,
              Δ ⊨ C ∷ U 
           -> pat_tp Δ Γ (pmeta γ C) U
  | pinl_c : forall E T S,
             pat_tp Δ Γ E T
          -> pat_tp Δ Γ (pinl E) (sum T S)
  | pinr_c : forall E T S,
             pat_tp Δ Γ E S
          -> pat_tp Δ Γ (pinr E) (sum T S)
  | ppair_c : forall E1 E2 T S,
             pat_tp Δ Γ E1 T
          -> pat_tp Δ Γ E2 S
          -> pat_tp Δ Γ (ppair E1 E2) (prod T S)
  | ppack_c : forall E δ' (X:δ↪δ') U C T,
              Δ ⊨ C ∷ U
           -> pat_tp Δ Γ E (〚single_subst X C〛 T) 
           -> pat_tp Δ Γ (ppack C E) (sigma X U T)
  | pfold_c : forall E δ' (X:δ↪δ') ψ (Z:∅↪ψ) U C T,
              pat_tp Δ Γ E (〈mu Z X U T〉 (〚single_subst X C〛 T))
           -> pat_tp Δ Γ (pfold E) (tapp (mu Z X U T) C)
  | ptt_c : pat_tp Δ Γ ptt unit.

Inductive synth_tp' {δ γ:world} (Δ:mtype_assign δ) (Γ:tp_assign γ δ)
                   : synth_exp δ γ -> tp δ -> Set :=
  | var_s : forall x T,
             Γ x = T
           -> synth_tp' Δ Γ (var _ x) T
  | app_s : forall I T1 E T2,
              Δ;Γ ⊢ I ⇒ (arr T1 T2)
           -> Δ;Γ ⊢ E ⇐ T1
           -> synth_tp' Δ Γ (app I E) T2
  | mapp_s : forall I δ' (X:δ↪δ') U C T,
              Δ;Γ ⊢ I ⇒ (pi X U T)
           -> Δ ⊨ C ∷ U
           -> synth_tp' Δ Γ (mapp I C) (〚single_subst X C〛 T)
  | coerce_s : forall E T,
              Δ;Γ ⊢ E ⇐ T
           -> synth_tp' Δ Γ (coercion E T) T
 with synth_tp {δ γ:world} (Δ:mtype_assign δ) (Γ:tp_assign γ δ)
                   : synth_exp δ γ -> tp δ -> Set :=
  | eq_constraint_s : forall I T Cs,
              synth_tp' Δ Γ I (add_eq Cs T)
           -> Δ;Γ ⊢ I ⇒ T
 with checks_tp' {δ γ:world} (Δ:mtype_assign δ) (Γ:tp_assign γ δ)
                   : checked_exp δ γ -> tp δ -> Set :=
  | synth_c : forall I T,
              Δ;Γ ⊢ I ⇒ T
           -> checks_tp' Δ Γ I T
  | meta_c : forall C U,
              Δ ⊨ C ∷ U 
           -> checks_tp' Δ Γ (meta γ C) U
  | fn_c : forall γ' (y:γ↪γ') E T1 T2,
             Δ;(Γ,, (y,T1)) ⊢ E ⇐ T2
          -> checks_tp' Δ Γ (fn y E) (arr T1 T2)
  | mlam_c : forall δ' (X:δ↪δ') E U T,
             (* TODO: Clean this up *)
             (〚@m_var _ ○ ↑X〛 ○ (Δ,, (X,U)));(〚@m_var _ ○ ↑X〛 ○ Γ) ⊢ E ⇐ T
          -> checks_tp' Δ Γ (mlam X E) (pi X U T)
  | rec_c : forall γ' (f:γ↪γ') E T,
             Δ;(Γ,, (f,T)) ⊢ E ⇐ T
          -> checks_tp' Δ Γ (rec f E) T
  | inl_c : forall E T S,
             Δ;Γ ⊢ E ⇐ T
          -> checks_tp' Δ Γ (inl E) (sum T S)
  | inr_c : forall E T S,
             Δ;Γ ⊢ E ⇐ S
          -> checks_tp' Δ Γ (inr E) (sum T S)
  | pair_c : forall E1 E2 T S,
             Δ;Γ ⊢ E1 ⇐ T
          -> Δ;Γ ⊢ E2 ⇐ S
          -> checks_tp' Δ Γ (pair E1 E2) (prod T S)
  | pack_c : forall E δ' (X:δ↪δ') U C T,
              Δ ⊨ C ∷ U
           -> Δ;Γ ⊢ E ⇐ (〚single_subst X C〛 T) 
           -> checks_tp' Δ Γ (pack C E) (sigma X U T)
  | fold_c : forall E δ' (X:δ↪δ') ψ (Z:∅↪ψ) U C T,
              Δ;Γ ⊢ E ⇐ 〈mu Z X U T〉 (〚single_subst X C〛 T)
           -> checks_tp' Δ Γ (fold E) (tapp (mu Z X U T) C)
  | tt_c : checks_tp' Δ Γ tt unit
  | case_i_c : forall I U Bs T,
             Δ;Γ ⊢ I ⇒ U
          -> (forall B, In B Bs -> branch_tp Δ Γ B U T)
          -> checks_tp' Δ Γ (case_i I Bs) T 
 with checks_tp {δ γ:world} (Δ:mtype_assign δ) (Γ:tp_assign γ δ)
                   : checked_exp δ γ -> tp δ -> Set :=
  | eq_constraint_c : forall E T Cs,
             checks_tp' Δ Γ E T
          -> Δ;Γ ⊢ E ⇐ (add_eq Cs T)
 with branch_tp {δ γ:world} (Δ:mtype_assign δ) (Γ:tp_assign γ δ)
                     : branch δ γ -> tp δ -> tp δ -> Set :=
  | br_c : forall δi n (θi:msubst δ δi) U T
                  (Δi:mtype_assign δi) (Γi:vec (tp δi) n) (p:pat (∅ + n) δi) E,
             pat_tp Δi (· * Γi) p (〚θi〛 U)
          -> Δi ⊩ θi ∷ Δ
          -> Δi;((〚θi〛 ○ Γ)*Γi) ⊢ E ⇐ 〚θi〛T
          -> branch_tp Δ Γ (br _ Δi Γi p θi E) U T
  where "D1 ; G1 ⊢ t1 ⇒ T1" := (@synth_tp _ _ D1 G1 t1 T1)
  and   "D1 ; G1 ⊢ t1 ⇐ T1" := (@checks_tp _ _ D1 G1 t1 T1).

Reserved Notation "V ∈ T" (at level 90).
Reserved Notation "⊪ ρ ⇐ Γ" (at level 90). 
Inductive val_tp : val -> tp ∅ -> Prop :=
  | vmeta_c : forall C U,
              · ⊨ C ∷ U 
           -> (vmeta C) ∈ U
  | vfn_c : forall δ γ γ' (y:γ↪γ') (E:checked_exp δ γ') (θ:msubst δ ∅) (ρ:env γ) T,
              clos_tp (fn y E) θ ρ T 
           -> (vfn y E θ ρ) ∈ T
  | vmlam_c : forall γ δ δ' (X:δ↪δ') (E:checked_exp δ' γ) (θ:msubst δ ∅) (ρ:env γ) T,
              clos_tp (mlam X E) θ ρ T 
           -> (vmlam X E θ ρ) ∈ T
  | vinl_c : forall E T S,
             E ∈ T
          -> (vinl E) ∈ (sum T S)
  | vinr_c : forall E T S,
             E ∈ S
          -> (vinr E) ∈ (sum T S)
  | vpair_c : forall V1 V2 T S,
             V1 ∈ T
          -> V2 ∈ S
          -> (vpair V1 V2) ∈ (prod T S)
  | vpack_c : forall V δ' (X:∅↪δ') U C T,
              · ⊨ C ∷ U
           -> V ∈ (〚single_subst X C〛 T) 
           -> (vpack C V) ∈ (sigma X U T)
  | vfold_c : forall V δ (X:∅↪δ) ψ (Z:∅↪ψ) U C T,
              V ∈ 〈mu Z X U T〉 (〚single_subst X C〛 T)
           -> vfold V ∈ (tapp (mu Z X U T) C)
  | vtt_c : vtt ∈ unit
  | veq_constr : forall V T C, V ∈ T -> V ∈ (eq_constraint C C T)
with extended_val_tp : extended_val -> tp ∅ -> Prop :=
  | evval_c : forall V T, V ∈ T -> extended_val_tp V T
  | evrec_c : forall δ γ γ' (f:γ↪γ') (E:checked_exp δ γ') (θ:msubst δ ∅) (ρ:env γ) T,
              clos_tp (rec f E) θ ρ T 
           -> extended_val_tp (evrec f E θ ρ) T
with env_tp : forall {γ'} (ρ:env γ') (Γ':tp_assign γ' ∅), Prop :=
  | env_c : forall γ' (ρ:env γ') Γ', (forall x, extended_val_tp (ρ x) (Γ' x)) -> ⊪ ρ ⇐ Γ'
with clos_tp : forall {δ γ} (E:checked_exp δ γ) (θ:msubst δ ∅) (ρ:env γ), tp ∅ -> Prop :=
  | clos_c : forall δ γ (E:checked_exp δ γ) θ ρ Δ Γ T,
              checks_tp' Δ Γ E T
           -> · ⊩ θ ∷ Δ
           -> ⊪ ρ ⇐ (〚θ〛 ○ Γ)
           -> clos_tp E θ ρ (〚θ〛T)
  where "V ∈ T" := (@val_tp V T)
  and "⊪ ρ ⇐ Γ" := (env_tp ρ Γ).

Ltac simpl_tp_subst_single :=
match goal with
| [ |- context f [〈?T〉 (arr ?U1 ?U2)] ] =>
 replace (〈T〉 (arr U1 U2)) with (arr (〈T〉 U1) (〈T〉 U2)) by reflexivity
| [ |- context f [〈?T〉 (pi ?X ?U1 ?U2)] ] =>
 replace (〈T〉 (pi X U1 U2)) with (pi X U2 (〈app_msubst_neutral_tp (↑X) ○ T〉 U2)) by reflexivity
end.

Ltac simpl_app_subst_tp :=
match goal with
| [ |- context f [〚?θ〛 (arr ?T ?U)] ] =>
 replace (〚θ〛(arr T U)) with (arr (〚θ〛 T) (〚θ〛 U)) by reflexivity
end.

(* TODO: Clean this up *)
Lemma tp_subst_commute' {δ ψ} (U:tp' ψ δ) : forall (T:name ψ -> neutral_tp ∅ δ) {δ'} (θ:msubst δ δ'),
〚θ〛 (app_tp_subst T U) = app_tp_subst (〚θ〛○T) (〚θ〛 U).
induction U; intros;
unfold app_subst in *; unfold tp_substitutable in *;
unfold app_subst in *;
unfold tp_substitutable' in *;
unfold neutral_tp_substitutable' in *;
simpl; f_equal; firstorder.

(* pi *)
specialize (IHU ((app_msubst_neutral_tp (fun x : name δ => (↑l) x)) ○ T) _ (θ × (succ_link δ'0 // l))).
erewrite IHU.
f_equal.
extensionality x.
unfold compose.
pose proof (@assoc _ (@neutral_tp_substitutable' ∅)).
unfold app_subst in H. unfold neutral_tp_substitutable' in H.
erewrite H. erewrite H.
f_equal.
extensionality y. unfold compose.
erewrite app_msubst_mvar.
unfold context_mult.  unfold compose at 1.
erewrite export_import_inv. simpl.
reflexivity.

(* sigma *)
specialize (IHU ((app_msubst_neutral_tp (fun x : name δ => (↑l) x)) ○ T) _ (θ × (succ_link δ'0 // l))).
erewrite IHU.
f_equal.
extensionality x.
unfold compose.
pose proof (@assoc _ (@neutral_tp_substitutable' ∅)).
unfold app_subst in H. unfold neutral_tp_substitutable' in H.
erewrite H. erewrite H.
f_equal.
extensionality y. unfold compose.
erewrite app_msubst_mvar.
unfold context_mult.  unfold compose at 1.
erewrite export_import_inv. simpl.
reflexivity.

(* neutral *)
destruct n.
reflexivity.
reflexivity.
Qed.

Lemma tp_subst_commute {δ ψ} (T:neutral_tp ∅ δ) (U:tp' ψ δ) : forall  {δ'} (θ:msubst δ δ'),
〚θ〛 (〈T〉 U) = 〈〚θ〛T〉 (〚θ〛 U).
intros. eapply tp_subst_commute'.
Qed.


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
 | [ H : context f [(app_msubst_tp ?t) ○ ?Γ] |- _ ] =>
   replace ((app_msubst_tp t) ○ Γ) with (〚 t 〛 ○ Γ) in H;
   try reflexivity
 | [ H : context f [app_msubst ?t ?T] |- _ ] =>
   replace (app_msubst t T) with (〚 t 〛 T) in H;
   try reflexivity
 | _ => fail
end).
Ltac clean_inversion := subst; simpl_existTs; subst; repeat clean_substs.

Tactic Notation "nice_inversion" integer(H) := inversion H; clean_inversion.

Tactic Notation "nice_inversion" hyp(H) := inversion H; clean_inversion.

Hint Constructors clos_tp env_tp extended_val_tp val_tp.
Lemma env_tp_cons {γ'} (Γ':tp_assign γ' ∅) ρ {γ''} (y:γ'↪γ'') W T:
   ⊪ ρ ⇐ Γ'
-> extended_val_tp W T
-> ⊪ (ρ,, (y, W)) ⇐ (Γ',, (y, T)).
intros. econstructor. nice_inversion H. intro.
unfold compose.
destruct (export y x); simpl; eauto.
Qed.

Lemma env_typing_eq {γ'}
(Γ' Γ'':tp_assign γ' ∅) ρ :
   Γ'' = Γ' 
-> ⊪ ρ ⇐ Γ'
-> ⊪ ρ ⇐ Γ''.
intros. subst. assumption.
Qed.

Lemma env_tp_app γ (ρ:env γ) Γ x : ⊪ ρ ⇐ Γ -> extended_val_tp (ρ x) (Γ x).
intro. nice_inversion H. by eauto.
Qed.
Hint Resolve @env_tp_app.

Lemma env_tp_app' γ (ρ:env γ) Γ x E : ⊪ ρ ⇐ Γ -> ρ x = E -> extended_val_tp E (Γ x).
intros. subst. by eauto.
Qed.
Hint Resolve @env_tp_app'.

Section app_msubst_pat_sect.
Reserved Notation "[ θ ]" (at level 90).

Fixpoint app_msubst_pat {γ δ δ'} (θ:msubst δ δ') (p:pat γ δ) : pat γ δ' :=
match p with
| pvar y => pvar _ y 
| pmeta C => pmeta _ (〚θ〛C)
| pfold E => pfold ([θ] E)
| pinl E => pinl ([θ] E)
| pinr E => pinr ([θ] E)
| ppair E1 E2 => ppair ([θ] E1) ([θ] E2)
| ppack C E => ppack (〚θ〛C) ([θ] E)
| ptt => ptt
end
where "[ θ ]" := (@app_msubst_pat _ _ _ θ).
End app_msubst_pat_sect.

Instance pat_substitutable {γ} : substitutable (pat γ) :=
{
 app_subst := @app_msubst_pat γ
}.
intros. induction t; simpl; try congruence; erewrite app_msubst_assoc; congruence.
Defined.

Section app_subst_pat_sect.
Reserved Notation "[ ρ ]" (at level 90).
Fixpoint psubst {γ} (ρ:name γ -> val) (p:pat γ ∅) : val :=
match p with
| pvar x => ρ x
| pmeta C => vmeta C
| pfold E => vfold ([ρ] E)
| pinl E => vinl ([ρ] E)
| pinr E => vinr ([ρ] E)
| ppair E1 E2 => vpair ([ρ] E1) ([ρ] E2)
| ppack C E => vpack C ([ρ] E)
| ptt => vtt
end
where "[ ρ ]" := (psubst ρ).
End app_subst_pat_sect.

Scheme checks_synth_ind := Induction for checks_tp Sort Prop
 with synth_checks_ind := Induction for synth_tp Sort Prop
 with br_tp_ind := Induction for branch_tp Sort Prop.
(* Combined Scheme checks_synth_multind from checks_synth_ind,
 synth_checks_ind, br_tp_ind. *)

Require Import Coq.Program.Equality.

Lemma env_tp_prod {γ} {n} (ρ1:env γ) ρ2 (Γ1 : tp_assign γ ∅) (Γ2 : vec (tp ∅) n)
 : ⊪ ρ1 ⇐ Γ1 -> ⊪ (· * ρ2) ⇐ (· * Γ2) -> ⊪ ρ1 * ρ2 ⇐ Γ1 * Γ2.
induction ρ2; intros; dependent destruction Γ2; simpl in *.
by assumption.
econstructor. intro. unfold compose.
nice_inversion H0.
assert (⊪ · * ρ2 ⇐ · * Γ2).  econstructor. intro.
pose proof (H4 (import (succ_link (∅ + n)) x0)).
unfold compose in H1. erewrite export_import_inv in H1. simpl in *.
assumption.

specialize (H4 (succ_link (∅ + n))).
unfold compose in H4. erewrite export_self in H4. simpl in *.

pose proof (IHρ2 _ H H1). nice_inversion H2.
destruct (export (succ_link (γ + n)) x); simpl in *; by eauto.
Qed.