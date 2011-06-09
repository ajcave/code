Require Export util.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid.
Require Import ssreflect.
Set Implicit Arguments.

Axiom mtype : world -> Set.
Axiom meta_term : world -> Set.
Axiom m_var : forall δ, name δ -> meta_term δ.
Coercion m_var : name >-> meta_term.

Definition mtype_assign δ := name δ -> mtype δ.

Axiom m_oft : forall {δ:world} (Δ:mtype_assign δ), meta_term δ -> mtype δ -> Prop.
Notation "D ⊨ t ∷ U" := (m_oft D t U) (at level 90).

Definition msubst δ δ' := name δ -> meta_term δ'.

Axiom app_msubst : forall {δ δ'}, (msubst δ δ') -> meta_term δ -> meta_term δ'.
Axiom app_msubst_assoc : forall {δ} (t:meta_term δ)
 {δ'} (θ:msubst δ δ') {δ''} (θ':msubst δ' δ''),
 app_msubst θ' (app_msubst θ t) =
 app_msubst (app_msubst θ' ○ θ) t.
Axiom app_msubst_mvar : forall {δ δ'} (θ:msubst δ δ')
  (n:name δ), app_msubst θ (m_var n) = θ n.
Axiom mvar_unit : forall δ, app_msubst (@m_var δ) = id.

Class substitutable (A:world -> Set) := {
   app_subst : forall {α β}, msubst α β -> A α -> A β ;
   assoc : forall {α} (t:A α) {β} (θ:msubst α β) {γ} (θ':msubst β γ), app_subst θ' (app_subst θ t) = app_subst (app_msubst θ' ○ θ) t
 }.
Notation "〚 θ 〛" := (app_subst θ).

Axiom app_msubst_mtype : forall {δ δ'}, msubst δ δ' -> mtype δ -> mtype δ'.
Axiom app_msubst_mtype_assoc : forall {δ} (U:mtype δ)
 {δ'} (θ:msubst δ δ') {δ''} (θ':msubst δ' δ''),
  app_msubst_mtype θ' (app_msubst_mtype θ U) =
  app_msubst_mtype (app_msubst θ' ○ θ) U. 

Instance meta_term_substitutable : substitutable meta_term := {
   app_subst := @app_msubst;
   assoc := @app_msubst_assoc
 }.
Instance mtype_substitutable : substitutable mtype := {
  app_subst := @app_msubst_mtype;
  assoc := @app_msubst_mtype_assoc
 }.

Definition single_subst {γ γ'} (x:γ↪γ') (N:meta_term γ) : msubst γ' γ :=
 (@m_var γ,,(x,N)).

(* TODO: This may cause me trouble later *)
Definition msubst_oft {α} (Δ:mtype_assign α) {β} (Δ':mtype_assign β) θ := forall x, Δ' ⊨ (θ x) ∷ ((〚θ〛 ○ Δ) x).
Notation "Δ' ⊩ θ ∷ Δ" := (@msubst_oft _ Δ _ Δ' θ) (at level 90).

Ltac clean_msubsts :=
(match goal with
 | [ H : _ |- context f [app_msubst ?t ?T]] =>
   replace (app_msubst t T) with (〚 t 〛 T);
   try reflexivity
 | _ => fail
end).

Definition context_mult {δ δ'} (θ:msubst δ δ') {δ'' δ'''} (y:δ'↪δ''') (x:δ↪δ'') := (〚@m_var _ ○ ↑y〛 ○ θ,, (x,y)).
Notation "θ × ( y // x )" := (context_mult θ y x) (at level 10).

(* TODO: Consistently name these variants. (See below) *)
(* TODO: This actually has nothing to do with substitutions *)
Lemma compose_cons' :
  forall δ δ' β γ
  (s : δ ↪ δ') {T} `{H:substitutable T}
  (θ : name δ -> T β) (θ' : msubst β γ) C x,
  (〚θ'〛 ((θ,, (s,C)) x)) =
   ((〚θ'〛 ○ θ),, (s,〚θ'〛C)) x.
intros.
unfold compose at 1 2 3.
destruct (export s x); reflexivity.
Qed.

Lemma compose_cons :
  forall δ δ' β γ
  (s : δ ↪ δ') {T} `{H:substitutable T}
  (θ : name δ -> T β) (θ' : msubst β γ) C,
  (〚θ'〛 ○ (θ,, (s,C))) =
   ((〚θ'〛 ○ θ),, (s,〚θ'〛C)).
intros. eapply functional_extensionality. 
eapply compose_cons'.
Qed.

Lemma compose_mvar {α β} (θ:msubst α β) : 〚θ〛○(@m_var _) = θ.
apply functional_extensionality.
apply app_msubst_mvar.
Qed.

Lemma subst_assoc {β γ δ} {T} `{H:substitutable T} {A:Set} (θ1:A  -> T β) θ2 (θ3:msubst γ δ) :
 〚〚θ3〛 ○ θ2〛 ○ θ1 = 〚θ3〛 ○ (〚θ2〛 ○ θ1).
apply functional_extensionality. intros.
unfold compose at 1 3 4.
erewrite assoc.
reflexivity.
Qed.

Lemma cons_import {α β γ} (θ:msubst α β) (x:α↪γ) C :
 (θ,,(x,C)) ○ (↑x) = θ.
apply functional_extensionality. intro.
unfold compose.
erewrite export_import_inv.
reflexivity.
Qed.

Lemma cons_self {α β γ} (θ:msubst α β) (x:α↪γ) C :
 (〚θ,,(x,C)〛 (m_var x)) = C.
erewrite app_msubst_mvar.
unfold compose. erewrite export_self. reflexivity.
Qed.

Lemma assoc' {α β γ} {T} `{H:substitutable T} (θ1:msubst α β)
(θ2:msubst β γ) :
 〚〚θ2〛 ○ θ1〛 = 〚θ2〛 ○ 〚θ1〛.
apply functional_extensionality. intro.
unfold compose.
erewrite assoc.
reflexivity.
Qed.

Lemma compose_product :
  forall δ δ' β γ x x0
  (s : δ ↪ δ')
  (θ : msubst δ β) (θ' : msubst β γ) 
  (s0 : γ ↪ x) (s1 : β ↪ x0),
  (〚(θ' ×  (s0 // s1))〛 ○ (θ ×  (s1 // s))) =
   (〚θ'〛 ○ θ) ×  (s0 // s).
intros.
unfold context_mult.
erewrite compose_cons.
erewrite cons_self.
f_equal.
f_equal.
erewrite <- subst_assoc.
erewrite compose_assoc.
erewrite compose_assoc.
f_equal.
erewrite compose_mvar.
erewrite cons_import.
apply assoc'.
Qed.

Lemma single_subst_mult {α α' β β'} (θ:msubst α β)
(z:β↪β') (y:α↪α') C :
 〚single_subst z C〛 ○ (θ × (z // y)) = (θ,, (y,C)).
unfold single_subst.
unfold context_mult.
erewrite compose_cons.
erewrite cons_self.
erewrite compose_assoc.
erewrite <- assoc'.
erewrite compose_assoc.
erewrite compose_mvar.
erewrite cons_import.
erewrite mvar_unit.
erewrite id_unit_left.
reflexivity.
Qed.

Lemma msubst_over_single {α β γ} (θ:msubst α β) (x:α↪γ) C :
 〚θ〛 ○ (single_subst x C) = (θ,, (x,〚θ〛C)). 
unfold single_subst.
erewrite compose_cons.
erewrite compose_mvar.
reflexivity.
Qed.

Lemma common_var {α α' β β' γ γ'} {θ:msubst α β} {θ':msubst γ β}
                 {x:α↪α'} {y:γ↪γ'} {z:β↪β'} {T}
                 `{H:substitutable T} {M:T γ'} {N:T α'} C :
   〚θ' × (z // y)〛 M = 〚θ × (z // x)〛 N
-> 〚θ',, (y,C)〛    M = 〚θ,, (x,C)〛    N.
intro.
assert (〚single_subst z C〛 (〚θ' × (z // y) 〛 M)
     = (〚single_subst z C〛 (〚θ  × (z // x) 〛 N)))
 by (f_equal; auto).
erewrite assoc in H1. erewrite single_subst_mult in H1.
erewrite assoc in H1. erewrite single_subst_mult in H1.
assumption.
Qed.


Lemma single_subst_commute {α α' β β'} (θ:msubst α β) (y:α↪α')
                           (z:β↪β') C :
  〚single_subst z (〚θ〛C)〛 ○ (θ × (z // y))
= 〚θ〛 ○ (single_subst y C).
erewrite single_subst_mult.
erewrite msubst_over_single.
reflexivity.
Qed.

Lemma single_subst_commute' {α α' β β'} (θ:msubst α β) (y:α↪α')
 (z:β↪β') C {T} `{H:substitutable T} M :
  〚single_subst z (〚θ〛C)〛 (〚θ × (z // y)〛 M)
= 〚θ〛 (〚single_subst y C〛 M).
erewrite assoc.
erewrite assoc.
erewrite single_subst_commute.
reflexivity.
Qed.

Axiom subst_lemma : forall {δ δ'} (θ:msubst δ' δ)
                   (Δ:mtype_assign δ) (Δ':mtype_assign δ') C U,
   Δ' ⊨ C ∷ U
-> Δ  ⊩ θ ∷ Δ'
-> Δ  ⊨ 〚θ〛C ∷ 〚θ〛U.

Lemma cons_import_mvar {δ δ' δ''} (X:δ↪δ') C (θ:msubst δ δ'')
{T} `{H:substitutable T} {A:Set} (M:A -> T δ):
〚θ,, (X,C)〛 ○ (〚@m_var _ ○ ↑ X〛 ○ M) = 〚θ〛 ○ M.
erewrite <- subst_assoc.
erewrite compose_assoc.
erewrite compose_mvar.
erewrite cons_import.
reflexivity.
Qed.

Lemma subst_cons_typing {δ δ'} (Δ:mtype_assign δ) (Δ':mtype_assign δ') (θ:msubst δ' δ) {δ''} (X:δ'↪δ'') C U :
   Δ ⊩ θ ∷ Δ'
-> Δ ⊨ C ∷ 〚θ〛U
-> Δ ⊩ θ,,(X,C) ∷ 〚@m_var _ ○ ↑X〛 ○ (Δ',,(X,U)).
intros. intro.
erewrite cons_import_mvar.
unfold compose.
destruct (export X x); unfold maybe at 1 2.
by firstorder.
assumption.
Qed.

Lemma meta_type_eq {δ} {Δ:mtype_assign δ} C U V:
   U = V
-> Δ ⊨ C ∷ U
-> Δ ⊨ C ∷ V.
intros. subst. assumption.
Qed.
