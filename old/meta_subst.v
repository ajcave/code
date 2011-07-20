Require Import util.
Require Import worlds. 
Require Import meta_term.

Class substitutable (A:world -> Set) := {
   app_subst : forall {α β}, msubst α β -> A α -> A β ;
   assoc : forall {α} (t:A α) {β} (θ:msubst α β) {γ} (θ':msubst β γ), app_subst θ' (app_subst θ t) = app_subst (app_msubst θ' ○ θ) t
 }.
Notation "⟦ θ ⟧" := (app_subst θ). 

Instance meta_term_substitutable : substitutable meta_term := { app_subst := app_msubst;
   assoc := @app_msubst_assoc
 }.
Instance mtype_substitutable : substitutable mtype := {
  app_subst := app_msubst_mtype;
  assoc := @app_msubst_mtype_assoc
 }.

Definition import_meta_term {δ δ'} (y:δ↪δ') : meta_term δ -> meta_term δ' := ⟦import y⟧.
Definition import_mtype {δ δ'} (y:δ↪δ') : mtype δ -> mtype δ' := ⟦import y⟧.
Hint Transparent app_subst.
