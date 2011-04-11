Require Import worlds.
Require Import meta_term.
Require Import meta_subst.
Require Import meta_subst_typing.
Require Import meta_subst_meta_subst.

Definition unify : forall {δ δ' δ''} (θ:msubst δ δ')
 (θk:msubst δ δ'') (θ':msubst δ'' δ'), Prop. 
Admitted. (* θ = θ'(θk) *)

Definition unify2 : forall {δ δ'} (C:meta_term δ)
 (D:meta_term δ') (θ:msubst δ' δ), Prop.
Admitted. (* C = θ(D) *) 

Notation "θ /≐ θ'" :=(forall θ'', ~unify θ θ' θ'') (at level 90).
Notation "θ ≐ θk // θ'" := (unify θ θk θ') (at level 90). 
Notation "C /≑ D" :=(forall θ, ~unify2 C D θ) (at level 90).
Notation "C ≑ D // θ" := (unify2 C D θ) (at level 90).

Set Implicit Arguments.

Section hop1.
 Variables (δ δ' δ'':world)
 (θ:msubst δ δ') (θ':msubst δ δ'') (θ'':msubst δ'' δ')
 (Δ:mtype_assign δ) (Δ':mtype_assign δ') (Δ'':mtype_assign δ'').
 Theorem hop1a :
    Δ' ⊩ θ ∷ Δ 
 -> Δ'' ⊩ θ' ∷ Δ
 -> θ ≐ θ' // θ''
 -> Δ' ⊩ θ'' ∷ Δ''.
 Admitted.
 Theorem hop1b :
    Δ' ⊩ θ ∷ Δ
 -> Δ'' ⊩ θ' ∷ Δ
 -> θ ≐ θ' // θ''
 -> θ = ⟦θ''⟧ θ'.
 Admitted.
End hop1.
 
Section hop2.
 Variables (δ δ':world)
   (θ:msubst δ δ')
   (Δ:mtype_assign δ) (Δ':mtype_assign δ')
   (T:mtype δ') (C:meta_term δ')
   (U:mtype δ)  (D:meta_term δ).
 Theorem hop2a :
    Δ' ⊨ C ∷ T
 -> Δ  ⊨ D ∷ U
 -> C ≑ D // θ
 -> Δ' ⊩ θ ∷ Δ.
 Admitted.
 Theorem hop2b :
    Δ' ⊨ C ∷ T
 -> Δ  ⊨ D ∷ U
 -> C ≑ D // θ
 -> C = ⟦θ⟧ D.
 Admitted.
End hop2.