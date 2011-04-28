Require Import util.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import worlds.
Require Import meta_subst.
Require Import comp_expr.
Require Import meta_subst_meta_type.
Require Import meta_subst_meta_term.
Require Import meta_subst_typing.
Require Import meta_term.
Require Import meta_subst_meta_subst.
Require Import Setoid.


Section app_msubst_tp_sect.

Reserved Notation "[ θ ] T" (at level 90).
Definition context_mult {δ δ'} (θ:msubst δ δ') {δ'' δ'''} (y:δ'↪δ''') (x:δ↪δ'') := (import_msubst y θ,, (x,m_var y)).
Notation "θ × ( y // x )" := (context_mult θ y x) (at level 10).
Fixpoint comm {α β} δ (xs:α ↪* β):{δ':world & δ↪*δ'} := 
match xs with
 | s_nil => existT _ _ s_nil
 | s_cons γ _ xs' x => 
  let (δ'',ys) := comm δ xs' in
  let (δ',y) := next δ'' in
  existT _ δ' (s_cons δ' ys y)
end.

Definition comm_bijection {α β} δ (xs:α ↪* β) :
 name' α β -> name' δ (projT1 (comm δ xs)).
induction xs.
simpl.
intro.
destruct (self_empty _ H).
simpl. destruct (comm δ xs). simpl in *.
intro.
destruct (export' r H).
eapply import'.
destruct (next' x). simpl.
eexact l0. eapply IHxs.
eexact n.
destruct (next' x). simpl.
eapply weaken'.
eexact l.
exact l0.
Defined.
Definition comm_bijection' {α β} δ (xs:α↪*β) :
 name' δ (projT1 (comm δ xs)) -> name' α β.
induction xs.
intro.
destruct (self_empty _ H).
simpl. destruct (comm δ xs).
simpl in *.
intro.
destruct (next' x). simpl in *.
destruct (export' l0 H).
eapply import'.
eapply r.
eapply IHxs.
eexact n.
eapply weaken'.
eexact xs.
exact r.
Defined.

Fixpoint app_msubst_tp {ψ} {δ δ'} (θ:msubst δ δ') (T:tp' ψ δ) : tp' ψ δ' :=
match T  with
 | m_tp U     =>
   m_tp _ (⟦θ⟧ U)
 | arr T1 T2  =>
   arr ([θ] T1) ([θ] T2)
 | pi _ X U T0 =>
   let (_,X') := next δ' in
   pi X' (⟦θ⟧ U) ([ θ × (X' // X )] T0)
 | sigma _ X U T0 =>
   let (_,X') := next δ' in
   sigma X' (⟦θ⟧ U) ([ θ × (X' // X )] T0)
 | unit =>
   unit _ _
 | prod T1 T2 =>
   prod ([θ] T1) ([θ] T2)
 | sum T1 T2 =>
   sum ([θ] T1) ([θ] T2)
 | tvar n =>
   tvar _ n
 | tapp T0 C =>
   tapp ([θ] T0) (⟦θ⟧ C)
 | eq_constraint C1 C2 T0 =>
   eq_constraint (⟦θ⟧ C1) (⟦θ⟧ C2) ([θ] T0)
 | mu ψ' ε Z X U T0 =>
   let (δ'',X') := next δ' in
   mu Z X' (⟦θ⟧ U) ([ θ × (X' // X)] T0)
end
where "[ θ ] T" := (app_msubst_tp θ T).

(* TODO: Clean up these next two proofs *)
(* This lemma can be stated more generally as
   (θ × g) ○ (θ' × h) = (θ ○ θ') × (g ○ h)
   Generalize "name α" to "name α β" - slice of
   names between α and β. Then they compose. *)
Lemma compose_product_hom :
  forall δ δ' β γ x x0
  (s : δ ↪ δ')
  (θ : msubst δ β) (θ' : msubst β γ) 
  (s0 : γ ↪ x) (s1 : β ↪ x0),
  (⟦θ' ×  (s0 // s1)⟧ (θ ×  (s1 // s))) =
   (⟦θ'⟧ θ) ×  (s0 // s).
Admitted.

Instance tp_substitutable' {ψ} : substitutable (tp' ψ) := {
  app_subst := @app_msubst_tp ψ
}.
pose proof (@assoc _ mtype_substitutable).
pose proof (@assoc _ meta_term_substitutable).
unfold app_subst in *. unfold mtype_substitutable in *.
unfold meta_term_substitutable in *.

intros α T. induction T; intros;
simpl;
f_equal; firstorder.
remember (next' γ).
remember (next' β).
destruct s.
destruct s0.
simpl.

Ltac abstraction_case IHT H1 :=
 erewrite IHT; f_equal;
 pose proof compose_product_hom as H1;
 unfold app_subst in H1;
 unfold msubst_substitutable in H1;
 eapply H1.

abstraction_case IHT H1.
abstraction_case IHT H1.
abstraction_case IHT H1.
Defined.

End app_msubst_tp_sect.
Implicit Arguments app_msubst_tp.

Instance tp_substitutable : substitutable tp :=
{
  app_subst := @app_subst _ (@tp_substitutable' ∅);
  assoc := @assoc _ (@tp_substitutable' ∅)
}.

Definition msubst_single_t {δ δ'} (X:δ↪δ') (t:meta_term δ) : tp δ' -> tp δ :=
 ⟦ (maybe (@m_var _ ) t) ○ (export X) ⟧.


Definition import_tp {δ δ'} (y:δ↪δ') : tp δ -> tp δ' :=  ⟦import y⟧.