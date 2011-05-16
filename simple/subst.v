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
(*====================================================*) ->
  Γ ⊢ rename θ M ⇐ T. 
induction 1; simpl; intros; subst; eauto.
econstructor.
set (next_link γ0).
eapply IHof.
intros.
unfold compose.
case (export x x0); simpl; intros.
erewrite export_import_inv.
simpl. eauto.
erewrite export_self.
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
unfold import_exp.
unfold compose.
remember (export x x0).
destruct s.
simpl.
specialize (H0 n).
eapply rename_lemma.
eassumption.
intros. erewrite export_import_inv.
reflexivity.
econstructor.
erewrite export_self.
reflexivity.
Qed.

