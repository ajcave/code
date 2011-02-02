Require Import List.
Inductive Fin : nat -> Set :=
 | f_z : forall n, Fin (S n)
 | f_succ : forall n, Fin n -> Fin (S n).

Section foo.
 Parameter world : Set.
 Parameter name : world -> Set.
 Parameter wlink : world -> world -> Set.
 
 Inductive mtype (G:world) :=
  | m_unit : mtype G.

 Inductive tp (a:world) :=
  | m_tp : mtype a -> tp a
  | arr : tp a -> tp a -> tp a
  | prod : forall b, mtype a -> wlink a b -> tp b -> tp a
 .
 Inductive meta_term (D:world) := m_tt.
 Inductive subst (D:world) := id_subst. (* TODO *)
 Inductive synth_exp  : world -> world -> Set :=
  | var : forall D G, name G -> synth_exp D G
  | app : forall D G, synth_exp D G -> checked_exp D G -> synth_exp D G
  | mapp : forall D G, synth_exp D G -> meta_term D -> synth_exp D G
  | coercion : forall D G, synth_exp D G -> tp D -> synth_exp D G
 with checked_exp : world -> world -> Set := 
  | synth : forall D G, synth_exp D G -> checked_exp D G
  | meta : forall D G, meta_term D -> checked_exp D G
  | fn : forall D G1 G2, wlink G1 G2 -> checked_exp D G2 -> checked_exp D G1
  | mlam : forall D1 G D2, wlink D1 D2 -> checked_exp D2 G -> checked_exp D1 G
  | case_i : forall D G, synth_exp D G -> list (branch D G) -> checked_exp D G
  | case_c : forall D G, meta_term D -> list (branch D G) -> checked_exp D G
  | rec : forall D G1 G2, wlink G1 G2 -> checked_exp D G2 -> checked_exp D G1
 with branch : world -> world -> Set :=
  | br : forall D G Di, meta_term Di -> subst Di -> checked_exp Di G -> branch D G.
 .
End foo.