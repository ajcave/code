Require Import util.
Require Import worlds.
Require Import meta_term.
Require Import meta_subst.
Require Import meta_subst_type.
Require Import meta_subst_typing.
Require Import meta_subst_meta_subst.
Require Import type_assign.
Require Import meta_subst_type_assign.
Require Import comp_expr.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Notation "[[ C1 // X1 ]]" := (msubst_single_t X1 C1) (at level 90). 

Lemma subst_combine : forall {γ δ δ'} (θ:msubst δ γ) (X:δ ↪ δ') C T,
  ⟦ θ ,, (X, ⟦θ⟧ C) ⟧ T = ⟦θ⟧ ([[ C // X ]] T).
Admitted.

Theorem subst_lemma : forall {δ δ':world} C U θ (Δ:mtype_assign δ) (Δ':mtype_assign δ'),
   Δ' ⊩ θ ∷ Δ
-> Δ  ⊨ C ∷ U
-> Δ' ⊨ ⟦θ⟧ C ∷ ⟦θ⟧ U.
Admitted.

Theorem cons_wkn_inv {δ δ' δ'' γ } (θ:msubst δ δ') (X:δ ↪ δ'') (Γ:tp_assign γ δ) C :
 ⟦θ⟧Γ = ⟦θ ,, (X,C)⟧(import_tp_assign X Γ).
unfold import_tp_assign.
erewrite assoc.
(* TODO: I think there's a nice lemma here... *)
f_equal.
unfold compose.
extensionality y.
erewrite app_msubst_mvar_result.
erewrite export_import_inv.
simpl.
reflexivity.
Qed.


Theorem msubst_ext : forall {δ δ' δ'0 α β}
 (θ:msubst δ β) (X : δ ↪ δ') (θ' : msubst δ β)
 m (X0 : δ ↪ δ'0) (T:tp δ'0) (T1:tp δ')  (X' : β ↪ α),
    ⟦import_msubst X' θ' ,, (X,m_var  X') ⟧ T1 =
    ⟦import_msubst X' θ ,, (X0, m_var X') ⟧ T ->
    ⟦θ' ,, (X,m) ⟧ T1 = ⟦θ ,, (X0,m)  ⟧ T.
Admitted.

Lemma subst_id {δ} (θ:msubst δ ∅) : ⟦·⟧ θ = θ.
unfold app_subst.
unfold msubst_substitutable.
unfold app_subst.
unfold meta_term_substitutable.
erewrite app_msubst_id.
erewrite compose_id_left. reflexivity.
eexact θ.
Qed.

Lemma subst_assoc3 {δ} (T:tp δ) : forall {δ' δ''}
 (θ:msubst δ δ') (θ':msubst δ' δ''),
 ⟦⟦θ'⟧θ⟧ T = ⟦θ'⟧(⟦θ⟧T).
intros. erewrite assoc. reflexivity.
Qed.

Lemma msubst_import_id {δ} (θ:msubst δ ∅)
 (y:∅↪*δ) : ⟦θ⟧ ○  ⟦import_star y⟧ = id.
Admitted.