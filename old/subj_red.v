Require Import List.
Inductive tp :=
 | i : tp
 | arr : tp -> tp -> tp.
Notation "G ; X" := (X::G) (at level 50).
Inductive exp : list tp -> Set :=
 | var : forall G1 G2 T, exp (G1 ; T ++ G2)
 | lam : forall G T, exp (G ; T) -> exp G
 | app : forall G, exp G -> exp G -> exp G
 | unit : forall G, exp G
.
Implicit Arguments var [G1 G2 T].
Implicit Arguments lam [G T].
Implicit Arguments app [G].
Implicit Arguments unit [G].
Inductive oft : forall (G:list tp), exp G -> tp -> Prop :=
 | var_tp : forall G1 G2 T, oft _ (@var G1 G2 T) T
 | lam_tp : forall G T E S, oft (G ; T) E S -> oft _ (lam E) (arr T S)
 | app_tp : forall G M N T S, oft G M (arr T S) -> oft G N T -> oft _ (app M N) S
 | unit_tp : forall G, oft G unit i
.
Implicit Arguments oft.

Inductive val : forall G, exp G -> Prop :=
 | lam_val : forall G T M, val G (@lam G T M)
 | unit_val : forall G, val G unit
.
Definition subst {G T} (M : exp (G ; T)) (N:exp G) : exp G.
Admitted. (* TODO: Wrong *)
Theorem subst_lemma G T S (M : exp (G ; T)) (N : exp G) :
 oft N T -> oft M S -> oft (subst M N) S.
Admitted. (* TODO *)
Hint Resolve @subst_lemma.

Inductive step : exp nil -> exp nil -> Prop :=
 | step_app1 : forall M M' N, step M M' -> step (app M N) (app M' N)
 | step_app2 : forall T M N N', step N N' -> step (app (@lam _ T M) N) (app (@lam _ T M) N')
 | step_app3 : forall T M V, val nil V -> step (app (@lam _ T M) V) (subst M V)
.
Require Import Coq.Program.Equality.
Hint Constructors oft.

Theorem subj_red (M M':exp nil) : step M M' -> forall T, oft M T -> oft M' T.
induction 1; inversion 1; simpl_existTs; subst; eauto.
inversion H4. simpl_existTs. subst.
eauto.
Qed.





