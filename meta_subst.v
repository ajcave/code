Require Import util.
Require Import worlds. 
Require Import meta_level.

Definition mbind D D1 D2 := (slink D1 D2)*(meta_term D).
Definition msubst D R := star (mbind R) empty D.
Definition msubst_cons D R := @s_cons _ (mbind R) empty D.
Implicit Arguments msubst_cons.
Class substitutable (A:world -> Set) := 
   app_subst : forall {α β}, msubst α β -> A α -> A β.
Notation "⟦ θ ⟧" := (app_subst θ). 
Typeclasses Transparent substitutable.
Typeclasses Transparent app_subst.