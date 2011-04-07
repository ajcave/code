Require Import worlds.
Require Import util.
 Axiom meta_term : world -> Set.
 Axiom m_var : forall δ, name δ -> meta_term δ.
 Axiom mtype : world -> Set.
 Coercion m_var : name >-> meta_term.
 Implicit Arguments m_var [δ].

 Axiom import_meta_term : forall {δ δ'}, δ↪δ' -> meta_term δ -> meta_term δ'.

 Axiom import_mtype : forall {δ δ'}, δ↪δ' -> mtype δ -> mtype δ'.

 Open Scope type_scope.
 Definition mtype_assign δ := name δ -> mtype δ.

 Axiom m_oft : forall {δ:world} {Δ:mtype_assign δ}, meta_term δ -> mtype δ -> Prop.
 Implicit Arguments m_oft.

 Notation "D ⊨ t ∷ U" := (m_oft D t U) (at level 90).

