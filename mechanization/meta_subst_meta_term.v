Require Import worlds.
Require Import meta_subst.
Require Import meta_term.

Axiom app_msubst : forall W W', msubst W W' -> meta_term W -> meta_term W'.

Implicit Arguments app_msubst.
Instance meta_term_substitutable : substitutable meta_term :=
 app_msubst.
