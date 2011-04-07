Require Import worlds.
Require Import util.
 Axiom meta_term : world -> Set.
 Axiom m_var : forall δ, name δ -> meta_term δ.
 Axiom mtype : world -> Set.
 Coercion m_var : name >-> meta_term.
 Implicit Arguments m_var [δ].

 Open Scope type_scope.
 Definition mtype_assign δ := name δ -> mtype δ.

 Axiom m_oft : forall {δ:world} {Δ:mtype_assign δ}, meta_term δ -> mtype δ -> Prop.
 Implicit Arguments m_oft.

 Notation "D ⊨ t ∷ U" := (m_oft D t U) (at level 90).

Definition msubst δ δ' := name δ -> meta_term δ'.

Axiom app_msubst : forall {δ δ'}, (msubst δ δ') -> meta_term δ -> meta_term δ'.

Axiom app_msubst_assoc : forall {δ} (t:meta_term δ)
 {δ'} (θ:msubst δ δ') {δ''} (θ':msubst δ' δ''),
 app_msubst θ' (app_msubst θ t) =
 app_msubst (app_msubst θ' ○ θ) t.
Implicit Arguments app_msubst.
Axiom app_msubst_mtype : forall {δ δ'}, (msubst δ δ') -> mtype δ -> mtype δ'.
Axiom app_msubst_mtype_assoc : forall {δ} (U:mtype δ)
 {δ'} (θ:msubst δ δ') {δ''} (θ':msubst δ' δ''),
  app_msubst_mtype θ' (app_msubst_mtype θ U) =
  app_msubst_mtype (app_msubst θ' ○ θ) U.  

Implicit Arguments app_msubst_mtype.


Axiom app_msubst_mvar_result : forall {δ δ'} (θ:msubst δ δ')
  (n:name δ), app_msubst θ  (m_var n) = θ n.

