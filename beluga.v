Require Import List.

Section foo.
 Parameter world : Set.
 Parameter empty : world.
 Parameter name : world -> Set.
 Parameter wlink : world -> world -> Set.
 Parameter slink : world -> world -> Set.
 Parameter weaken1 : forall {a b}, slink a b -> wlink a b.
 Parameter weaken : forall {a b}, slink a b -> name b.
 Parameter import : forall {a b}, slink a b -> name a -> name b.
 
 Inductive meta_term (D:world) :=
  | m_z
  | m_succ : meta_term D -> meta_term D
  | m_var : name D -> meta_term D.
 Inductive mtype (D:world) :=
  | m_nat : mtype D
  | m_vec : meta_term D -> mtype D.
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

 Section star.
 Hypotheses (A:Set) (Rel:A -> A -> Set).
 Inductive star (a:A) : A -> Set :=
  | s_nil : star a a
  | s_cons : forall b c, star a b -> Rel b c -> star a c.
 End star.
 Implicit Arguments star.
 Implicit Arguments s_nil.
 Implicit Arguments s_cons.
 Print Implicit s_cons.

 Open Scope type_scope.
 Definition var_mtp D1 D2 := (slink D1 D2)*(mtype D1).
 Definition mtype_assign := star var_mtp empty.
 Definition m_cons := @s_cons _ var_mtp empty.
 Implicit Arguments m_cons.
 Print Implicit m_cons.
 
 (* This is basically the "In" predicate, except that we import things to the end *)
 Inductive m_assigned D : mtype_assign D -> name D -> mtype D -> Prop :=
  | m_asn_top : forall D' (A:mtype_assign D') T x,
                    m_assigned D (m_cons A (x,T)) (weaken x) (import_mtype x T)
  | m_asn_else : forall D' T A x (y:slink D' D) U,
                 m_assigned D' A x T
                 -> m_assigned D (m_cons A (y,U)) (import y x) (import_mtype y T). 
 Implicit Arguments m_assigned.
 Implicit Arguments m_asn_top.
 Implicit Arguments m_asn_else.

 Inductive m_oft {D':world} {D:mtype_assign D'} : meta_term D' -> mtype D' -> Prop :=
  | m_z_tp : m_oft m_z m_nat
  | m_succ_tp : forall n, m_oft n m_nat -> m_oft (m_succ n) m_nat
  | m_var_tp : forall y T, m_assigned D y T -> m_oft (m_var y) T
 .
 Implicit Arguments m_oft.

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

 Inductive tp (D:world) :=
  | m_tp : mtype D -> tp D
  | arr : tp D -> tp D -> tp D
  | prod : forall D2, wlink D D2 -> mtype D -> tp D2 -> tp D
 .
 Implicit Arguments m_tp.
 Implicit Arguments arr.
 Implicit Arguments prod.

 (* TODO. Is this even possible? Should it produce a world D2 and link? *)
 Axiom import_tp : forall {D1 D2:world} (y:slink D1 D2) (T:tp D1), tp D2.

 Inductive subst (D:world) := id_subst. (* TODO *)
 Inductive synth_exp (D G:world) : Set :=
  | var : name G -> synth_exp D G
  | app :  synth_exp D G -> checked_exp D G -> synth_exp D G
  | mapp : synth_exp D G -> meta_term D -> synth_exp D G
  | coercion : checked_exp D G -> tp D -> synth_exp D G
 with checked_exp (D G:world) : Set := 
  | synth : synth_exp D G -> checked_exp D G
  | meta : meta_term D -> checked_exp D G
  | fn : forall G2, wlink G G2 -> checked_exp D G2 -> checked_exp D G
  | mlam : forall D2, wlink D D2 -> checked_exp D2 G -> checked_exp D G
  | case_i :  synth_exp D G -> list (branch D G) -> checked_exp D G
  | case_c : meta_term D -> list (branch D G) -> checked_exp D G
  | rec : forall G2, wlink G G2 -> checked_exp D G2 -> checked_exp D G
 with branch (D G:world) : Set :=
  | br : forall Di, meta_term Di -> subst Di -> checked_exp Di G -> branch D G.
 Implicit Arguments var.
 Implicit Arguments app.
 Implicit Arguments coercion.
 Implicit Arguments synth.
 Implicit Arguments meta.
 Implicit Arguments fn.
 Implicit Arguments mlam.
 Implicit Arguments case_i.
 Implicit Arguments case_c.
 Implicit Arguments rec.

 Definition var_tp D G1 G2 := (slink G1 G2)*(tp D).
 Definition tp_assign D := star (var_tp D) empty.
 Definition v_cons D := @s_cons _ (var_tp D) empty.
 Implicit Arguments v_cons.
 Print Implicit v_cons.

 (* TODO: We could eliminate the duplication between this and the other one *)
 Inductive var_assigned D G : tp_assign D G -> name G -> tp D -> Prop :=
  | v_asn_top : forall G' (A:tp_assign D G') T x,
                    var_assigned D G (v_cons A (x,T)) (weaken x) T
  | v_asn_else : forall G' T A x (y:slink G' G) U,
                 var_assigned D G' A x T
                 -> var_assigned D G (v_cons A (y,U)) (import y x) T.
 Implicit Arguments var_assigned.
 
 Definition weaken_ctx : forall {D1 D2 G}, slink D1 D2 -> tp_assign D1 G -> tp_assign D2 G.
 intros. induction H0.
 constructor.
 econstructor.
 eexact IHstar.
 destruct r.
 constructor.
 exact s.
 eapply import_tp.
 eexact H.
 exact t.
 Defined. 
 
 Inductive s_tp {D' G':world} {D:mtype_assign D'} {G:tp_assign D' G'}
                   : synth_exp D' G' -> tp D' -> Prop :=
  | var_s : forall x T, var_assigned G x T -> s_tp (var _ x) T
  | app_s : forall I T1 E T2, s_tp I (arr T1 T2) -> c_tp E T1 -> s_tp (app I E) T2
  (* | mapp : ... TODO *)
  | coerce_s : forall E T, c_tp E T -> s_tp (coercion E T) T
 with c_tp {D' G':world} {D:mtype_assign D'} {G:tp_assign D' G'}
                   : checked_exp D' G' -> tp D' -> Prop :=
  | synth_c : forall I T, s_tp I T -> c_tp (synth I) T
  | meta_c : forall C U, m_oft D C U -> c_tp (meta G' C) (m_tp U)
  | fn_c : forall G2' (y:slink G' G2') E T1 T2,
             @c_tp _ _ D (v_cons G (y,T1)) E T2
          -> c_tp (fn (weaken1 y) E) (arr T1 T2)
  | mlam_c : forall D2' (X:slink D' D2') E U T,
             @c_tp _ _ (m_cons D (X,U)) (weaken_ctx X G) E T
          -> c_tp (mlam (weaken1 X) E) (prod (weaken1 X) U T)
  (* | case_i | case_c ... TODO *)
  | rec_c : forall G2' (f:slink G' G2') E T,
             @c_tp _ _ D (v_cons G (f,T)) E T
          -> c_tp (rec (weaken1 f) E) T
 .
  (* TODO: Compare our use of strong links and imports to the paper's example of
     typing derivations. It's possible that they do contravariant stuff to avoid
     the import *)
 
 Inductive is_val (D G:world) : checked_exp D G -> Prop :=
  | fn_is_val : forall G2 (y:slink G G2) E, is_val D G (fn (weaken1 y) E)
  | mlam_is_val : forall D2 (X:slink D D2) E, is_val D G (mlam (weaken1 X) E)
  | rec_is_val : forall G2 (f:slink G G2) E, is_val D G (rec (weaken1 f) E).

 Definition mbind D D1 D2 := (slink D1 D2)*(meta_term D).
 Definition msubst D R := star (mbind R) empty D.
 Definition msubst_cons D R := @s_cons _ (mbind R) empty D.
 Implicit Arguments msubst_cons.

 Inductive env : world -> Set :=
  | e_nil : forall G, env G
  | e_cons : forall G1 G2 (y:slink G1 G2), env G1 -> val -> env G2
 with val : Set :=
  | v_meta : meta_term empty -> val
  | v_val : forall D G E, is_val D G E -> msubst D empty -> env G -> val.

 Inductive closure : Set :=
  | meta_term_closure : meta_term empty -> closure
  | comp_term_closure : forall D G, checked_exp D G -> msubst D empty -> env G -> closure.

 Inductive msubst_typ W (D:mtype_assign W) : forall W' (D':mtype_assign W'), msubst W' W -> Prop :=
  | m_subst_typ_nil : msubst_typ W D empty (s_nil _ _) (s_nil _ _)
  | m_subst_typ_cons : forall W' D' W'' (y:slink W' W'') U t T, msubst_typ W D W' D' T
        -> msubst_typ W D W'' (m_cons D' (y,U)) (msubst_cons T (y,t)).
 
 
End foo.