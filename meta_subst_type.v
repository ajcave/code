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

Definition import_msubst {δ δ' δ''} (X:δ'↪δ'')  (θ:msubst δ δ')  : msubst δ δ'' :=
 import_meta_term X ○ θ.

Section app_msubst_tp_sect.

Reserved Notation "[ θ ] T" (at level 90).
Definition context_mult {δ δ'} (θ:msubst δ δ') {δ'' δ'''} (y:δ'↪δ''') (x:δ↪δ'') := (import_msubst y θ,, (x,m_var y)).
Notation "θ × ( y // x )" := (context_mult θ y x) (at level 10).
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
intros.
extensionality n.
unfold app_subst at 1.
unfold msubst_substitutable.
unfold compose at 1.
unfold context_mult at 2 3.
unfold compose.
remember (export s n) as mn.
destruct mn.
unfold maybe.
unfold import_msubst.
unfold import_meta_term.
(* TODO: There's some nice property here we should prove *)
unfold compose.
unfold app_subst at 4.
erewrite assoc.
erewrite assoc.
f_equal.
extensionality n'.
unfold compose.
erewrite app_msubst_mvar_result.
unfold context_mult.
unfold compose.
erewrite export_import_inv.
reflexivity.

simpl.
erewrite app_msubst_mvar_result.
unfold context_mult.
unfold compose.
erewrite export_self.
reflexivity.
Qed.

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