Require Import util.
Require Import worlds.
Require Import meta_subst.
Require Import meta_term.
Require Import meta_subst_typing.

Axiom app_msubst : forall W W', msubst W W' -> meta_term W -> meta_term W'.

Fixpoint app_msubst_mvar {δ δ'} (θ:msubst δ δ') : name δ -> meta_term δ' := 
match θ in star _ _ δ return name δ -> meta_term δ' with
| · => fun n => match (empty_is_empty n) with end
| (θ',,(Y,t)) => fun n =>
  match (export Y n) with
   | inleft n0 => app_msubst_mvar θ' n0
   | inright _ => t
  end
end.

Implicit Arguments app_msubst.
Instance meta_term_substitutable : substitutable meta_term :=
 app_msubst.

Axiom app_msubst_mvar_result : forall {δ δ'} (θ:msubst δ δ')
  (n:name δ), ⟦ θ ⟧ (m_var n) = app_msubst_mvar θ n.