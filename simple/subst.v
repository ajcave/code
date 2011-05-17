Require Import Coq.Program.Equality.
Require Import worlds.
Require Import typing.
Set Implicit Arguments.

Section rename_sect.
Reserved Notation "[ θ ] T " (at level 90).

Fixpoint rename {α β} (θ:name α -> name β) (M:exp α) : exp β := match M with
| var n => var (θ n)
| tt => tt
| app M N => app ([θ] M) ([θ] N)
| lam _ x T M => 
  let (_,x') := next β in
  lam x' T ([(import x') ○ θ,,(x,x')] M)
| inl T M => inl T ([θ] M)
| inr T M => inr T ([θ] M)
end
where "[ θ ] M" := (rename θ M).
End rename_sect.

Definition import_exp {α β} (x:α↪β) : exp α -> exp β :=
 rename (import x).

Reserved Notation "[ θ ] T" (at level 90).

Fixpoint app_subst {α β} (θ:name α -> exp β) (M:exp α) : exp β :=
match M with
| var n => θ n
| tt => tt
| app M N => app ([θ] M) ([θ] N)
| lam _ x T M => 
  let (β',x') := next β in
  lam x' T ([(import_exp x') ○ θ,,(x,x')] M)
| inl T M => inl T ([θ] M)
| inr T M => inr T ([θ] M)
end
where "[ θ ] M" := (app_subst θ M).

Lemma rename_lemma : forall {δ} M T (Δ:tp_ctx δ),
  Δ ⊢ M ⇐ T ->
  forall {γ} θ (Γ:tp_ctx γ), (forall x, Γ (θ x) = Δ x)
(*===========================================*) ->
  Γ ⊢ rename θ M ⇐ T. 
induction 1; simpl; intros; subst; eauto.
econstructor.
set (next_link γ0).
eapply IHof.
intros.
unfold compose at 2 4.
case (export x x0); simpl; intros.
unfold compose. erewrite export_import_inv.
simpl. eauto.
unfold compose. erewrite export_self.
reflexivity.
Qed.

Notation "Γ ⊩ θ ⇐ Δ" := (forall x, Γ ⊢ θ x ⇐ Δ x) (at level 90).

Lemma subst_lemma : forall {δ} M T (Δ:tp_ctx δ),
   Δ ⊢ M ⇐ T   ->
   forall {γ} θ (Γ:tp_ctx γ), Γ ⊩ θ ⇐ Δ 
 (*=====================================*) ->
   Γ ⊢ [θ]M ⇐ T.
induction 1; simpl; intros; subst; eauto.
set (next_link γ0).
econstructor.
eapply IHof.
intro.
unfold compose at 2 4.
case (export x x0); intros; simpl.
eapply rename_lemma; eauto.
intros. unfold compose. erewrite export_import_inv.
reflexivity.
econstructor.
unfold compose. erewrite export_self.
reflexivity.
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
     (single_subst x M' V1) ⇓ V2 ->
     (app M N) ⇓ V2 
| eval_inl : forall M T V,
     M ⇓ V ->
     (inl T M) ⇓ (inl T V)
| eval_inr : forall M T V,
     M ⇓ V ->
     (inr T M) ⇓ (inr T V)
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
Qed.

Theorem progress' M T : · ⊢ M ⇐ T ->
(exists V, (M ⇓ V)) \/ (M ⇑).
intros.
destruct (classical (exists V, M ⇓ V)).
tauto.
right. eapply progress; eauto.
Qed.