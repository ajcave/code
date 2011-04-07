Require Import util.
Require Import worlds.
Require Import type_assign.
Require Import meta_subst.
Require Import comp_expr.
Require Import meta_subst_type.
 
 (* TODO: Remove *)
 Definition app_msubst_tp_assign {γ δ δ'} (θ:msubst δ δ') (Γ:tp_assign γ δ)  : tp_assign γ δ' := ⟦θ⟧ ○ Γ.
 
 Instance tp_assign_substitutable γ : substitutable (tp_assign γ) := (fun {δ δ'} (θ:msubst δ δ') (Γ:tp_assign γ δ)  =>
  ⟦θ⟧ ○ Γ : tp_assign γ δ').


 Implicit Arguments app_msubst_tp_assign.