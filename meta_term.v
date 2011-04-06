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
 Definition var_mtp D1 D2 := (slink D1 D2)*(mtype D1).
 Definition mtype_assign := star var_mtp empty.

 
 (* This is basically the "In" predicate, except that we import things to the end *)
 Inductive m_assigned D : mtype_assign D -> name D -> mtype D -> Prop :=
  | m_asn_top : forall D' (A:mtype_assign D') T x,
                    m_assigned D (A,,(x,T)) x (import_mtype x T)
  | m_asn_else : forall D' T A x (y:slink D' D) U,
                 m_assigned D' A x T
                 -> m_assigned D (A,,(y,U)) (import y x) (import_mtype y T). 
 Implicit Arguments m_assigned.
 Implicit Arguments m_asn_top.
 Implicit Arguments m_asn_else.

 Axiom m_oft : forall {D':world} {D:mtype_assign D'}, meta_term D' -> mtype D' -> Prop.
 (*  m_var_tp : forall y T, m_assigned D y T -> m_oft y T *)


 Implicit Arguments m_oft.

 Notation "D ⊨ t ∷ U" := (m_oft D t U) (at level 90).
 (* wf_mtype A T if T is a well-formed meta-type in the context A *)

