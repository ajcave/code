Require Import util.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import worlds.
Require Import meta_term.
Require Import meta_subst.
Require Import meta_subst_meta_term.
 
Instance msubst_substitutable {δ} : substitutable (msubst δ)
  := {
  app_subst := fun _ _ θ θ' => ⟦θ⟧ ○ θ'
  }.
intros. 
pose proof (@assoc _ meta_term_substitutable).
unfold app_subst in *.
unfold meta_term_substitutable in *.
extensionality x.
unfold compose in *.
erewrite H.
reflexivity.
Defined.