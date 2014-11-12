open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Vec

data tp (Δ : ℕ) : Set where
 unit : tp Δ
 _⇝_ : (T : tp zero) -> (S : tp Δ) -> tp Δ
 var : Fin Δ -> tp Δ
 μ : tp (suc Δ) -> tp Δ
 _⊕_ _⊗_ : tp Δ -> tp Δ -> tp Δ

data tp' (Δ : ℕ) : Set₁ where
 unit : tp' Δ
 _⇝_ : (T : Set) -> (S : tp' Δ) -> tp' Δ
 var : Fin Δ -> tp' Δ
 μ : tp' (suc Δ) -> tp' Δ
 _⊕_ _⊗_ : tp' Δ -> tp' Δ -> tp' Δ

ext : ∀ {A : Set₁} {Δ} -> (Fin Δ -> A) -> A -> Fin (suc Δ) -> A
ext f x zero = x
ext f x (suc y) = f y

mutual
 interp0 : ∀ {Δ} -> tp' Δ -> (Vec Set Δ) -> Set
 interp0 unit ρ = Unit
 interp0 (T ⇝ t) ρ = T → interp0 t ρ
 interp0 (var x) ρ = lookup x ρ
 interp0 (μ t) ρ = μ̂ t ρ
 interp0 (t ⊕ t₁) ρ = (interp0 t ρ) ⊎ (interp0 t₁ ρ)
 interp0 (t ⊗ t₁) ρ = interp0 t ρ × interp0 t₁ ρ

 data μ̂ {Δ} (F : tp' (suc Δ)) (ρ : Vec Set Δ) : Set where
  inj : interp0 F (μ̂ F ρ ∷ ρ) -> μ̂ F ρ

interp : ∀ {Δ} -> tp Δ -> tp' Δ
interp unit = unit
interp (t ⇝ t₁) = {!!} ⇝ (interp t₁)
interp (var x) = var x
interp (μ t) = μ (interp t)
interp (t ⊕ t₁) = interp t ⊕ interp t₁
interp (t ⊗ t₁) = interp t ⊗ interp t₁
