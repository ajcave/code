Require Import util.
Require Import worlds.
Require Import meta_subst.
Require Import meta_subst_meta_term.
 
Instance msubst_substitutable {δ} : substitutable (msubst δ)
  := fun _ _ θ θ' => ⟦θ⟧ ○ θ'.
 