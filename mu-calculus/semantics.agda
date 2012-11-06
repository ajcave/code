{-# OPTIONS --no-positivity-check #-}
module semantics where
open import mu-ltl
open import Data.Sum
open import Data.Nat
open import FinMap
open import Coinduction
open import Product
open import Unit
open import Data.Empty

ωnat : Set
ωnat = ℕ ⊎ Unit

_≤ω_ : ωnat -> ωnat -> Set
inj₁ n ≤ω inj₁ m = n ≤ m
inj₁ n ≤ω inj₂ tt = Unit
inj₂ tt ≤ω inj₁ x = ⊥
inj₂ tt ≤ω inj₂ y = Unit

obj : Set₁
obj = ωnat -> Set

○⁺ : obj -> obj
○⁺ A (inj₁ zero) = Unit
○⁺ A (inj₁ (suc n)) = A (inj₁ n)
○⁺ A (inj₂ tt) = A (inj₂ tt)

_⊃⁺_ : obj -> obj -> obj
(A ⊃⁺ B) α = ∀ β → β ≤ω α → A β → B β

_∧⁺_ : obj -> obj -> obj
(A ∧⁺ B) α = A α × B α

_∨⁺_ : obj -> obj -> obj
(A ∨⁺ B) α = A α ⊎ B α

⊤⁺ : obj
⊤⁺ α = Unit

mutual
 data ν⁺ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) (α : ωnat) : Set where
  ⟨_⟩ : ∞ (⟦ F ⟧ (ρ , (ν⁺ F ρ)) α) -> ν⁺ F ρ α

 data μ⁺ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) (α : ωnat) : Set where
  ⟨_⟩ : ⟦ F ⟧ (ρ , (μ⁺ F ρ)) α -> μ⁺ F ρ α

 ⟦_⟧ : ∀ {Δ} -> functor Δ -> (f : gksubst Δ obj) -> obj
 ⟦_⟧ (▹ A) ρ = lookup ρ A
 ⟦_⟧ (μ F) ρ = μ⁺ F ρ
 ⟦_⟧ (ν F) ρ = ν⁺ F ρ
 ⟦_⟧ (○ A) ρ = ○⁺ (⟦ A ⟧ ρ)
 ⟦_⟧ (A ⊃ B) ρ = ⟦ A ⟧ tt ⊃⁺ ⟦ B ⟧ ρ
 ⟦_⟧ (A ∧ B) ρ = ⟦ A ⟧ ρ ∧⁺ ⟦ B ⟧ ρ
 ⟦_⟧ (A ∨ B) ρ = ⟦ A ⟧ ρ ∨⁺ ⟦ B ⟧ ρ
 ⟦_⟧ ⊤ ρ = ⊤⁺