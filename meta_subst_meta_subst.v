Require Import util.
Require Import worlds.
Require Import meta_subst.
Require Import meta_subst_meta_term.

Fixpoint app6 {δ δ'} (θ':msubst δ δ') : forall {δ''}, msubst δ' δ'' -> msubst δ δ'' := 
match θ' in star _ _ δ return forall {δ''}, msubst δ' δ'' -> msubst δ δ'' with
 | s_nil => fun δ'' θ => s_nil
 | s_cons _ _ θ0 (y,w) => fun δ'' θ =>
     s_cons _ (app6 θ0 _ θ) (y,⟦ θ ⟧ w)
end.
 
Instance msubst_substitutable {δ} : substitutable (msubst δ)
  := fun _ _ θ θ' => app6 θ' _ θ.
 