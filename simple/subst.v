Require Import Coq.Program.Equality.
Require Import worlds.
Require Import typing.
Set Implicit Arguments.

Section rename_sect.
Reserved Notation "[ θ ] T " (at level 90).
Definition rn_cons {α β γ δ} (θ:name α -> name β) (z:β↪γ) (y:α↪δ) := ((import z) ○ θ,,(y,z)).
Notation "θ × ( y // x )" := (rn_cons θ y x) (at level 90).
Fixpoint rename {α β} (θ:name α -> name β) (M:exp α) : exp β := match M with
| var n => var (θ n)
| tt => tt
| app M N => app ([θ] M) ([θ] N)
| lam _ y T M => 
  let (_,z) := next β in
  lam z T ([θ × (z // y)] M)
| inl T M => inl T ([θ] M)
| inr T M => inr T ([θ] M)
| case M _ x N1 _ y N2 =>
  let (_,z) := next β in
  case ([θ] M)
         z ([θ × (z // x)] N1)
         z ([θ × (z // y)] N2)
end
where "[ θ ] M" := (rename θ M).

Lemma rn_cons_tp {γ γ0 γ1 γ'} (Γ:tp_ctx γ) (Γ0:tp_ctx  γ0) (θ:name γ -> name γ0) (y:γ0↪γ1) T (x:γ↪γ') :
 (forall z, Γ0 (θ z) = Γ z) ->
 forall z, (Γ0,, (y, T)) ((θ × (y // x)) z) = (Γ,,(x,T)) z.
intros.
unfold rn_cons.
unfold compose at 2 4.
case (export x z); simpl; intros; unfold compose.
erewrite export_import_inv. simpl. eauto.
erewrite export_self. reflexivity.
Qed.

Lemma rename_lemma : forall {δ} M T (Δ:tp_ctx δ),
  Δ ⊢ M ⇐ T ->
  forall {γ} θ (Γ:tp_ctx γ), (forall x, Γ (θ x) = Δ x)
(*===========================================*) ->
  Γ ⊢ rename θ M ⇐ T. 
induction 1; simpl; intros; subst; eauto.
econstructor.
set (next_link γ0).
eapply IHof.
eapply rn_cons_tp; eauto.
econstructor; eauto.
eapply IHof2.
eapply rn_cons_tp; eauto.
eapply IHof3.
eapply rn_cons_tp; eauto.
Qed.
End rename_sect.

Definition import_exp {α β} (x:α↪β) : exp α -> exp β :=
 rename (import x).

Reserved Notation "[ θ ]".
Definition subst_cons {α β γ δ} (θ:name α -> exp β) (y:β↪γ) (x:α↪δ) := ((import_exp y) ○ θ,,(x,y)).
Notation "θ × ( y // x )" := (subst_cons θ y x) (at level 90).
Fixpoint app_subst {α β} (θ:name α -> exp β) (M:exp α) : exp β :=
match M with
| var n => θ n
| tt => tt
| app M N => app ([θ] M) ([θ] N)
| lam _ x T M => 
  let (_,y) := next β in
  lam y T ([θ × (y // x)] M)
| inl T M => inl T ([θ] M)
| inr T M => inr T ([θ] M)
| case M _ x N1 _ y N2 =>
  let (_,z) := next β in
  case ([θ] M)
       z ([θ × (z // x)] N1)
       z ([θ × (z // y)] N2)      
end
where "[ θ ]" := (app_subst θ).


Notation "Γ ⊩ θ ⇐ Δ" := (forall x, Γ ⊢ θ x ⇐ Δ x) (at level 90).

Lemma subst_cons_tp  {γ γ0 γ1 γ'} (Γ:tp_ctx γ) (Γ0:tp_ctx  γ0) (θ:name γ -> exp γ0) (y:γ0↪γ1) T (x:γ↪γ') :
 Γ0 ⊩ θ ⇐ Γ ->
(Γ0,, (y, T)) ⊩ θ × (y // x) ⇐ (Γ,,(x,T)).
intros.
unfold subst_cons.
unfold compose at 2 4.
case (export x x0); intros; simpl.
eapply rename_lemma; eauto.
intros. unfold compose. erewrite export_import_inv.
reflexivity.
econstructor. unfold compose.
erewrite export_self.
reflexivity.
Qed.

Lemma subst_lemma : forall {δ} M T (Δ:tp_ctx δ),
   Δ ⊢ M ⇐ T   ->
   forall {γ} θ (Γ:tp_ctx γ), Γ ⊩ θ ⇐ Δ 
 (*=====================================*) ->
   Γ ⊢ [θ]M ⇐ T.
induction 1; simpl; intros; subst; eauto.
set (next_link γ0).
econstructor.
eapply IHof.
eapply subst_cons_tp; eauto.
econstructor; eauto.
eapply IHof2.
eapply subst_cons_tp; eauto.
eapply IHof3.
eapply subst_cons_tp; eauto.
Qed.

Definition single_subst {γ γ'} (x:γ↪γ') (M:exp γ') (N:exp γ) := [@var γ,,(x,N)] M. 

Lemma single_subst_lemma : forall {γ γ'} (x:γ↪γ') M N U T (Γ:tp_ctx γ),
  Γ,,(x,U) ⊢ M ⇐ T ->
  Γ ⊢ N ⇐ U 
(*====================*) ->
  Γ ⊢ single_subst x M N ⇐ T.
intros.
eapply subst_lemma.
eexact H.
intro. unfold compose.
case (export x x0); intros; simpl; eauto.
Qed.

Inductive val : exp ∅ -> Prop :=
| tt_val : val tt
| lam_val : forall {γ} {x:∅↪γ} M T, val (lam x T M)
| inl_val : forall M T, val M -> val (inl T M)
| inr_val : forall M T, val M -> val (inr T M).

Reserved Notation "M ⇓ V" (at level 90).
Inductive eval : exp ∅ -> exp ∅ -> Prop :=
| eval_val : forall V, val V -> eval V V
| eval_app : forall M {γ} T (x:∅↪γ) (M':exp γ) N V1 V2 ,
     M ⇓ (lam x T M') ->
     N ⇓ V1 ->
     (single_subst x M' V1) ⇓ V2
   (*==========================*) ->
     (app M N) ⇓ V2 
| eval_inl : forall M T V,
     M ⇓ V 
   (*==========================*) ->
     (inl T M) ⇓ (inl T V)
| eval_inr : forall M T V,
     M ⇓ V
   (*==========================*) ->
     (inr T M) ⇓ (inr T V)
| eval_case_l : forall M {α β} {x:∅↪α} N1 {y:∅↪β} N2 T U V,
     M ⇓ (inl T U) ->
     (single_subst x N1 U) ⇓ V
   (*==========================*) ->
     (case M x N1 y N2) ⇓ V
| eval_case_r : forall M {α β} {x:∅↪α} N1 {y:∅↪β} N2 T U V,
     M ⇓ (inr T U) ->
     (single_subst y N2 U) ⇓ V
   (*==========================*) ->
     (case M x N1 y N2) ⇓ V
where "M ⇓ V" := (eval M V).

Hint Constructors eval.
Theorem subject_reduction {M V} : M ⇓ V -> forall T, · ⊢ M ⇐ T -> · ⊢ V ⇐ T.
induction 1; intros; eauto.
nice_inversion H2.
eapply IHeval3.
eapply single_subst_lemma.
apply IHeval1 in H5.
nice_inversion H5.
eassumption.
apply IHeval2.
assumption.
nice_inversion H0. eauto.
nice_inversion H0. eauto.
nice_inversion H1.
eapply IHeval2.
eapply single_subst_lemma; eauto.
apply IHeval1 in H10.
nice_inversion H10. auto.
nice_inversion H1.
eapply IHeval2.
eapply single_subst_lemma; eauto.
apply IHeval1 in H10.
nice_inversion H10. auto.
Qed.

Reserved Notation "M ⇑" (at level 90).
CoInductive diverge : exp ∅ -> Prop :=
| app_div1 : forall M N,
     M ⇑ ->
     (app M N) ⇑ 
| app_div2 : forall M {γ} T (x:∅↪γ) (M':exp γ) N ,
     M ⇓ (lam x T M') ->
     N ⇑ ->
     (app M N) ⇑
| app_div3 : forall M {γ} T (x:∅↪γ) (M':exp γ) N V1,
     M ⇓ (lam x T M') ->
     N ⇓ V1 ->
     (single_subst x M' V1) ⇑ ->
     (app M N) ⇑ 
| inl_div : forall M T,
     M ⇑ ->
     (inl T M) ⇑
| inr_div : forall M T,
     M ⇑ ->
     (inr T M) ⇑
| case_div : forall M {α β} {x:∅↪α} N1 {y:∅↪β} N2,
     M ⇑
   (*==========================*) ->
     (case M x N1 y N2) ⇑
| case_l_div : forall M {α β} {x:∅↪α} N1 {y:∅↪β} N2 T U,
     M ⇓ (inl T U) ->
     (single_subst x N1 U) ⇑
   (*==========================*) ->
     (case M x N1 y N2) ⇑
| case_r_div : forall M {α β} {x:∅↪α} N1 {y:∅↪β} N2 T U,
     M ⇓ (inr T U) ->
     (single_subst y N2 U) ⇑
   (*==========================*) ->
     (case M x N1 y N2) ⇑
where "M ⇑" := (diverge M).

Hint Constructors val.

Inductive canonical : exp ∅ -> tp -> Prop :=
| tt_canon: canonical tt one
| lam_canon : forall U T {γ} (x:∅↪γ) (M:exp γ), canonical (lam x U M) (arrow U T)
| inl_canon : forall M T S, canonical (inl T M) (sum S T)
| inr_canon : forall M T S, canonical (inr S M) (sum S T).
Hint Constructors canonical.

Lemma canonical_forms {V T} : val V -> · ⊢ V ⇐ T -> canonical V T.
intros. nice_inversion H0; eauto.
destruct (empty_is_empty x).
nice_inversion H.
inversion H.
Qed.

Lemma eval_to_val {M V} : M ⇓ V -> val V.
induction 1; eauto.
Qed.
Hint Resolve @eval_to_val.

Axiom classical : forall P, P \/ ~P.
Theorem progress : forall M T, · ⊢ M ⇐ T -> 
 (forall V, ~ (M ⇓ V)) -> (M ⇑).
cofix. intros.
nice_inversion H.
destruct (H0 tt); eauto.
destruct (empty_is_empty x).
destruct (H0 (lam x T0 M0)); eauto.
destruct (classical (exists V, M0 ⇓ V)).
destruct H3.
pose proof (eval_to_val H3).
pose proof (subject_reduction H3 H1).
pose proof (canonical_forms H4 H5).
nice_inversion H6.
nice_inversion H5.
destruct (classical (exists V, N ⇓ V)).
destruct H7.
destruct (classical (exists V, single_subst x0 M x ⇓ V)).
destruct H9.
destruct (H0 x1); eauto.
eapply app_div3; eauto.
eapply progress.
eapply single_subst_lemma; eauto.
eapply subject_reduction; eauto.
intros. contradict H9.
exists V. auto.
eapply app_div2; eauto.
eapply app_div1; eauto.
econstructor.
destruct (classical (exists V, M0 ⇓ V)).
destruct H2.
destruct (H0 (inl S x)); eauto.
eapply progress; eauto.
econstructor.
destruct (classical (exists V, M0 ⇓ V)).
destruct H2.
destruct (H0 (inr T0 x)); eauto.
eapply progress; eauto.
destruct (classical (exists V, M0 ⇓ V)).
destruct H4 as [V Hy].
pose proof (subject_reduction Hy H1).
pose proof (eval_to_val Hy).
pose proof (canonical_forms H5 H4).
nice_inversion H6.
destruct (classical (exists V, (single_subst x N1 M) ⇓ V)).
destruct H7 as [V1 Hy0].
edestruct H0.
eapply eval_case_l; eauto.
eapply case_l_div; eauto.
eapply progress; eauto.
nice_inversion H4.
eapply single_subst_lemma; eauto.
destruct (classical (exists V, (single_subst y N2 M) ⇓ V)).
destruct H7 as [V1 Hy0].
edestruct H0.
eapply eval_case_r; eauto.
eapply case_r_div; eauto.
eapply progress; eauto.
nice_inversion H4.
eapply single_subst_lemma; eauto.
eapply case_div.
eapply progress; eauto.
Qed.

Theorem progress' M T : · ⊢ M ⇐ T ->
(exists V, (M ⇓ V)) \/ (M ⇑).
intros.
destruct (classical (exists V, M ⇓ V)).
tauto.
right. eapply progress; eauto.
Qed.

Definition subst_compose {α β γ}
 (θ:name β -> exp γ)
 (θ':name α -> exp β)
:= [θ] ○ θ'.
Notation "θ ** θ'" := (subst_compose θ θ') (at level 40).

Require Import Coq.Logic.FunctionalExtensionality.

Definition subst α β := name α -> exp β.

Theorem rename_is_a_subst {α β} (θ : name α -> name β) : rename θ = [@var _ ○ θ].
Admitted.

Lemma hom_admitted : forall (α β : world) (l : α ↪ β),
  forall (γ γ' β0 β0' : world) (θ : subst α β0) (η : subst β0 γ)(l0:γ↪γ') (l1:β0↪β0'),
    ((η ** θ) ×  (l0 // l)) = (η ×  (l0 // l1)) ** (θ ×  (l1 // l)).
intros.
eapply functional_extensionality_dep. intros.
unfold subst_compose.
unfold subst_cons.
unfold compose at 1 4 5.
destruct (export l x); simpl.
unfold compose at 1 2 5.
Admitted.

Theorem hom {α β γ} (θ:subst α β) (η:subst β γ) :
 [η ** θ] = [η] ○ [θ].
eapply functional_extensionality_dep. intros.
generalize dependent β. generalize dependent γ.
induction x; intros.
Focus 3.
simpl.
unfold compose; simpl.
set (next_link γ). set (next_link β0).
f_equal.
unfold compose in IHx.
erewrite <- IHx.
f_equal.
eapply hom_admitted.
Admitted.

Theorem associativity {α β γ δ} (θ:subst α β) (η:subst β γ) (ζ:subst γ δ) :
 (ζ ** η) ** θ = ζ ** (η ** θ).
eapply functional_extensionality_dep. intros.
pose proof (hom η ζ).
unfold subst_compose in *.
unfold compose in *.
erewrite H.
reflexivity.
Qed.