Require Import worlds.
Require Import meta_subst.
Require Import comp_expr.
Require Import meta_subst_meta_type.

Axiom theta_weaken : forall {D R} (theta:msubst D R) {R'} (X:wlink R R'), msubst D R'.

Definition app_msubst_t2' : forall {W} (T:tp W) {W'} (theta:msubst W W'), tp W'.
induction 1; intros.
apply m_tp.
eapply app_msubst_t. eexact theta. exact m.
apply arr. apply IHT1. exact theta. apply IHT2. exact theta.
Print Implicit prod.
Print projT1.
apply (prod (projT2 (next W'))).
eapply app_msubst_t. eexact theta. eexact m.
apply IHT.
econstructor. eapply theta_weaken. eexact theta.
eexact (projT2 (next W')).
split. eexact w. constructor 3. eapply (weaken (projT2 (next W'))).
Defined.

Definition app_msubst_t2 {W W'} (theta:msubst W W') (T:tp W) : tp W' := app_msubst_t2' T theta.
Implicit Arguments app_msubst_t2.
Require Import meta_term.

Axiom msubst_single_t : forall {D D'} (X:wlink D D'), meta_term D -> tp D' -> tp D.
(* TODO: Write this as a simultaneous substitution: (id,C/X) ? *)