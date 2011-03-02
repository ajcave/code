Require Import util.
Require Import worlds.
Require Import type_assign.
Require Import meta_subst.
Require Import comp_expr.
Require Import meta_subst_type.
 Fixpoint app_msubst_tp_assign' {W G'} (G:tp_assign W G') : forall {W'} (theta:msubst W W'), tp_assign W' G' :=
  match G in star _ _ G' return forall {W'} (theta:msubst W W'), star (var_tp W') empty G' with
   | s_nil => fun W' theta => s_nil
   | s_cons _ _ a (b,c) => fun W' theta => s_cons _ (app_msubst_tp_assign' a _ theta) (b,app_msubst_t2 theta c)
  end.
 
 Definition app_msubst_tp_assign {G' W W'} (theta:msubst W W') (G:tp_assign W G') : tp_assign W' G' := app_msubst_tp_assign' G _ theta.
 Definition tp_assign' δ γ := tp_assign γ δ.
 Instance tp_assign_substitutable γ : substitutable (tp_assign' γ) := (@app_msubst_tp_assign γ).

 Instance tp_substitutable : substitutable tp := @app_msubst_t2.

 Implicit Arguments app_msubst_tp_assign.