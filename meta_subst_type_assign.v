Require Import util.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import worlds.
Require Import type_assign.
Require Import meta_subst.
Require Import comp_expr.
Require Import meta_term.
Require Import meta_subst_type.
 
 Instance tp_assign_substitutable γ : substitutable (tp_assign γ) := {
  app_subst := (fun {δ δ'} (θ:msubst δ δ') (Γ:tp_assign γ δ)  => ⟦θ⟧ ○ Γ : tp_assign γ δ')
 }.
intros.
extensionality x.
unfold compose at 1 2 3.
erewrite assoc. reflexivity.
Defined.


Definition import_tp_assign {δ δ' γ} (X:δ↪δ') : tp_assign γ δ -> tp_assign γ δ' := ⟦import X⟧.
 (* TODO: This is becoming a pattern.
    Define for the whole typeclass? *)
