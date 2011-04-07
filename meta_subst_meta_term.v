Require Import util.
Require Import worlds.
Require Import meta_subst.
Require Import meta_term.
Require Import meta_subst_typing.

Axiom app_msubst : forall W W', msubst W W' -> meta_term W -> meta_term W'.

Definition app_msubst_mvar {δ δ'} (θ:msubst δ δ') : name δ -> meta_term δ' := fun n => θ n.

Implicit Arguments app_msubst.
Instance meta_term_substitutable : substitutable meta_term :=
 app_msubst.

Axiom app_msubst_mvar_result : forall {δ δ'} (θ:msubst δ δ')
  (n:name δ), ⟦ θ ⟧ (m_var n) = app_msubst_mvar θ n.