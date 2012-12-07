module ISetoidComplete where
open import Level

open import Categories.Support.Equivalence using (module I→R-Wrapper; setoid-i→r) renaming (Setoid to ISetoid; module Setoid to ISetoid)
open import Categories.Support.SetoidFunctions using (module _⟶_)
open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor
open import Categories.Agda
open import Categories.Colimit
open import Categories.Object.Initial
open import Categories.Cocones
open import Categories.Cocone

Limit : ∀ {o ℓ e} {o′ ℓ′ e′} {C : Category o ℓ e} {J : Category o′ ℓ′ e′} (F : Functor J C) -> Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′)
Limit F = Colimit (Functor.op F)

record Complete (o ℓ e : Level) {o′ ℓ′ e′} (C : Category o′ ℓ′ e′) : Set (suc o ⊔ suc ℓ ⊔ suc e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    limit : ∀ {J : Category o ℓ e} (F : Functor J C) → Limit F


module LimitCone {o ℓ e c ℓ′} {J : Category o ℓ e} (F : Functor J (ISetoids (c ⊔ (o ⊔ ℓ ⊔ e)) (c ⊔ ℓ′ ⊔ (o ⊔ ℓ ⊔ e)))) where
  c′ = c ⊔ (o ⊔ ℓ ⊔ e)
  ℓ″ = c ⊔ ℓ′ ⊔ (o ⊔ ℓ ⊔ e)
  C = ISetoids c′ ℓ″
  D = Cocones F
  module J = Category J
  open Functor F
  open ISetoid
  open _⟶_

  carrier = ∀ (x : J.Obj) -> Carrier (F₀ x)

  ⊥ : Cocone (Functor.op F)
  ⊥ = record { N = {!!}; ψ = {!!}; commute = {!!} }


ISetoidsComplete : ∀ {o ℓ e c ℓ′} → Complete o ℓ e (ISetoids (c ⊔ (o ⊔ ℓ ⊔ e)) (c ⊔ ℓ′ ⊔ (o ⊔ ℓ ⊔ e)))
ISetoidsComplete {o} {ℓ} {e} {c} {cℓ} = record { limit = limit }
  where
  c′ = c ⊔ (o ⊔ ℓ ⊔ e)
  ℓ′ = c ⊔ cℓ ⊔  (o ⊔ ℓ ⊔ e)
  C = ISetoids c′ ℓ′
  limit : ∀ {J : Category o ℓ e} (F : Functor J C) → Limit F
  limit {J} F = record { initial = my-initial-cocone }
    where
    module J = Category J
    open Functor F
    open ISetoid
    open _⟶_

    open LimitCone {c = c} {cℓ} {J} F

    {-
    .my-!-unique : (A : Cocone F) (φ : CoconeMorphism ⊥ A) (x : vertex-carrier) → (_≈_ (Cocone.N A) (CoconeMorphism.f (! {A}) ⟨$⟩ x) (CoconeMorphism.f φ ⟨$⟩ x))
    my-!-unique A φ (X , x) = sym (Cocone.N A) (CoconeMorphism.commute φ (refl (F₀ X))) -}

    my-initial-cocone : Initial (Cocones (Functor.op F))
    my-initial-cocone = record
      { ⊥ = ⊥
      ; ! = {!!}
      ; !-unique = {!!} 
      }