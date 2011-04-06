Require Import worlds.
Require Import util.
Require Import meta_term.
Require Import meta_subst.
 
 Set Implicit Arguments.
 Inductive tp' ψ (δ:world):=
  | m_tp : mtype δ -> tp' ψ δ
  | arr : tp' ψ δ -> tp' ψ δ -> tp' ψ δ
  | pi : forall δ', δ↪δ' -> mtype δ -> tp' ψ δ' -> tp' ψ δ
  | sigma : forall δ', δ↪δ' -> mtype δ -> tp' ψ δ' -> tp' ψ δ
  | unit : tp' ψ δ
  | prod : tp' ψ δ -> tp' ψ δ -> tp' ψ δ
  | sum : tp' ψ δ -> tp' ψ δ -> tp' ψ δ
(*  | mu : forall δ' ψ', star (fun δ1 δ2 => (mtype δ1)*(δ1↪δ2)) δ δ'
         ->  ψ↪ψ'
         -> tp' ψ' δ'
         -> tp' ψ δ *)
  | tvar : name ψ -> tp' ψ δ
  | tapp : tp' ψ δ -> meta_term δ -> tp' ψ δ
  | eq_constraint : meta_term δ -> meta_term δ -> tp' ψ δ -> tp' ψ δ
 .

 Definition tp δ := tp' empty δ.
 Unset Implicit Arguments.
 Definition m_tp' {δ} := @m_tp empty δ : mtype δ -> tp δ.
 Coercion m_tp' : mtype >-> tp.

 Inductive synth_exp (D G:world) : Set :=
  | var : name G -> synth_exp D G
  | app :  synth_exp D G -> checked_exp D G -> synth_exp D G
  | mapp : synth_exp D G -> meta_term D -> synth_exp D G
  | coercion : checked_exp D G -> tp D -> synth_exp D G
  | unfold : synth_exp D G -> synth_exp D G
 with checked_exp (D G:world) : Set := 
  | synth : synth_exp D G -> checked_exp D G
  | meta : meta_term D -> checked_exp D G
  | fn : forall G2, wlink G G2 -> checked_exp D G2 -> checked_exp D G
  | mlam : forall D2, wlink D D2 -> checked_exp D2 G -> checked_exp D G
  | case_i :  synth_exp D G -> list (branch D G) -> checked_exp D G
  | case_c : meta_term D -> list (branch D G) -> checked_exp D G
  | rec : forall G2, wlink G G2 -> checked_exp D G2 -> checked_exp D G
  | fold : checked_exp D G -> checked_exp D G
  | inl : checked_exp D G -> checked_exp D G
  | inr : checked_exp D G -> checked_exp D G
  | pack : meta_term D -> checked_exp D G -> checked_exp D G
  | pair : checked_exp D G -> checked_exp D G -> checked_exp D G
  | tt : checked_exp D G
 with branch (D G:world) : Set :=
  | br : forall Di, meta_term Di -> msubst D Di -> checked_exp Di G -> branch D G.
 Coercion synth : synth_exp >-> checked_exp.
 Implicit Arguments var.
 Implicit Arguments app.
 Implicit Arguments mapp.
 Implicit Arguments coercion.
 Implicit Arguments synth.
 Implicit Arguments meta.
 Implicit Arguments fn.
 Implicit Arguments mlam.
 Implicit Arguments case_i.
 Implicit Arguments case_c.
 Implicit Arguments rec.
 Implicit Arguments br.