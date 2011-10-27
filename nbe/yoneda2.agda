{-# OPTIONS --type-in-type #-}
open import Yoneda using (_×_; _≡_; Obj; HomI; _*_; Unit)
module yoneda2 (C : Yoneda.Cat)  where

open Yoneda.Cat (Yoneda.CatY C) using (Base; Hom; comp; pair; iden; π₁; π₂)

_∘_ : ∀ {X Y Z} (f : Hom Y Z) (g : Hom X Y) -> Hom X Z
_∘_ {X} {Y} {Z} f g = comp {X} {Y} {Z} f g

[_,_] : ∀ {X Y Z} (f : Hom X Y) (g : Hom X Z) -> Hom X (Y × Z)
[_,_] {X} {Y} {Z} f g = pair {X} {Y} {Z} f g

test1 : ∀ {Γ Δ T : Obj Base} (σ : Hom Δ T) (θ : Hom Γ Δ)-> Unit
test1 {Γ} {Δ} {T} σ θ = {!!}

test : ∀ (Γ Δ S T Z : Obj Base) (σ : Hom Δ Γ) (N : Hom Γ T) (M : Hom (Γ × T) S)
        -> (M ∘ ([ iden , N ] ∘ σ)) ≡ (M ∘ ([ σ ∘ π₁ , π₂ ] ∘ [ iden , (N ∘ σ) ]))
test Γ Δ S T Z σ N M = {!!}

