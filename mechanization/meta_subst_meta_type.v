Require Import meta_subst.
Require Import meta_term.
Axiom app_msubst_t : forall W W', msubst W W' -> mtype W -> mtype W'.

Implicit Arguments app_msubst_t.

Instance mtype_substitutable : substitutable mtype := app_msubst_t. 