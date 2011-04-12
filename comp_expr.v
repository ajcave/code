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
  | tvar : name ψ -> tp' ψ δ
  | tapp : tp' ψ δ -> meta_term δ -> tp' ψ δ
  | eq_constraint : meta_term δ -> meta_term δ -> tp' ψ δ -> tp' ψ δ
 (* | mu : forall ψ' δ', ψ↪ψ' -> δ↝δ'〈mtype δ〉 -> tp' ψ' δ' -> tp' ψ δ *)
.

Definition tp δ := tp' ∅ δ.
Definition m_tp' {δ} := @m_tp ∅ δ : mtype δ -> tp δ.
Coercion m_tp' : mtype >-> tp.

Inductive synth_exp (δ γ:world) : Set :=
  | var : name γ -> synth_exp δ γ
  | app :  synth_exp δ γ -> checked_exp δ γ -> synth_exp δ γ
  | mapp : synth_exp δ γ -> meta_term δ -> synth_exp δ γ
  | coercion : checked_exp δ γ -> tp δ -> synth_exp δ γ
  | unfold : synth_exp δ γ -> synth_exp δ γ
 with checked_exp (δ γ:world) : Set := 
  | synth : synth_exp δ γ -> checked_exp δ γ
  | meta : meta_term δ -> checked_exp δ γ
  | fn : forall γ', γ↪γ' -> checked_exp δ γ' -> checked_exp δ γ
  | mlam : forall δ', δ↪δ' -> checked_exp δ' γ -> checked_exp δ γ
  | case_i :  synth_exp δ γ -> list (branch δ γ) -> checked_exp δ γ
  | case_c : meta_term δ -> list (branch δ γ) -> checked_exp δ γ
  | rec : forall γ', γ↪γ' -> checked_exp δ γ' -> checked_exp δ γ
  | fold : checked_exp δ γ -> checked_exp δ γ
  | inl : checked_exp δ γ -> checked_exp δ γ
  | inr : checked_exp δ γ -> checked_exp δ γ
  | pack : meta_term δ -> checked_exp δ γ -> checked_exp δ γ
  | pair : checked_exp δ γ -> checked_exp δ γ -> checked_exp δ γ
  | tt : checked_exp δ γ
 with branch (δ γ:world) : Set :=
  | br : forall δi, meta_term δi -> msubst δ δi -> checked_exp δi γ -> branch δ γ.

Coercion synth : synth_exp >-> checked_exp.
