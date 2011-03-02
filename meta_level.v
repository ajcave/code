Require Import worlds.
Require Import util.
 Inductive meta_term (D:world) :=
  | m_z
  | m_succ : meta_term D -> meta_term D
  | m_var : name D -> meta_term D.
 Inductive mtype (D:world) :=
  | m_nat : mtype D
  | m_vec : meta_term D -> mtype D.
 Coercion m_var : name >-> meta_term.
 	       	 
 Implicit Arguments m_nat [D].
 Implicit Arguments m_vec [D].
 Implicit Arguments m_z [D].
 Implicit Arguments m_succ [D].
 Implicit Arguments m_var [D].

 Fixpoint import_meta_term {D1 D2:world} (y:slink D1 D2) (t:meta_term D1) := 
 match t with
  | m_z => m_z
  | m_succ t => m_succ (import_meta_term y t)
  | m_var x => m_var (import y x)
 end.

 Fixpoint import_mtype {D1 D2:world} (y:slink D1 D2) (T:mtype D1) :=
 match T with
  | m_nat => m_nat
  | m_vec t => m_vec (import_meta_term y t)
 end.

 

 Open Scope type_scope.
 Definition var_mtp D1 D2 := (slink D1 D2)*(mtype D1).
 Definition mtype_assign := star var_mtp empty.
 Definition m_cons := @s_cons _ var_mtp empty.
 Implicit Arguments m_cons.
 Print Implicit m_cons.
 
 (* This is basically the "In" predicate, except that we import things to the end *)
 Inductive m_assigned D : mtype_assign D -> name D -> mtype D -> Prop :=
  | m_asn_top : forall D' (A:mtype_assign D') T x,
                    m_assigned D (m_cons A (x,T)) x (import_mtype x T)
  | m_asn_else : forall D' T A x (y:slink D' D) U,
                 m_assigned D' A x T
                 -> m_assigned D (m_cons A (y,U)) (import y x) (import_mtype y T). 
 Implicit Arguments m_assigned.
 Implicit Arguments m_asn_top.
 Implicit Arguments m_asn_else.

 Inductive m_oft {D':world} {D:mtype_assign D'} : meta_term D' -> mtype D' -> Prop :=
  | m_z_tp : m_oft m_z m_nat
  | m_succ_tp : forall n, m_oft n m_nat -> m_oft (m_succ n) m_nat
  | m_var_tp : forall y T, m_assigned D y T -> m_oft y T
 .

 Implicit Arguments m_oft.

 Notation "D ⊨ t ∷ U" := (m_oft D t U) (at level 90).
 (* wf_mtype A T if T is a well-formed meta-type in the context A *)
   
 Inductive wf_mtype {D:world} {A:mtype_assign D} : mtype D -> Prop :=
  | m_nat_tp : wf_mtype m_nat
  | m_vec_tp : forall t, m_oft A t m_nat -> wf_mtype (m_vec t).
 Implicit Arguments wf_mtype.

 (* Well formed meta-contexts *)
 (* Inductive wf_mctx {D:world} : mtype_assign D -> Prop := . *)
 (* TODO: Do we need to make wf_mtype depend on wf_mctx?
    Can we to inforce this invariant? Should we just quantify all our theorems
    with the assumptions that wf_mctx and wf_mtype, etc...? *)
