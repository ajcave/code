Require Import util.
Require Import worlds. 
Require Import meta_term.

Definition msubst δ δ' := name δ -> meta_term δ'.
Class substitutable (A:world -> Set) := 
   app_subst : forall {α β}, msubst α β -> A α -> A β.
Notation "⟦ θ ⟧" := (app_subst θ). 
Typeclasses Transparent substitutable.
Typeclasses Transparent app_subst.

Hint Transparent app_subst.
