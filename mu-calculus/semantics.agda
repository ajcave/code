module semantics where
open import mu-ltl
open import Data.Sum
open import Data.Unit hiding (⊤)
open import Data.Nat
open import FinMap
open import Coinduction

ωnat : Set
ωnat = ℕ ⊎ Unit

obj : Set₁
obj = ωnat -> Set

mutual
 data ν⁺ {Δ} (F : functor (Δ , #prop)) (f : gksubst Δ Set) : Set where
  ⟨_⟩ : ∞ (⟦ F ⟧ (f , (ν⁺ F f))) -> ν⁺ F f

 data μ⁺ {Δ} (F : functor (Δ , #prop)) (f : gksubst Δ Set) : Set where
  ⟨_⟩ : ⟦ F ⟧ (f , (μ⁺ F f)) -> μ⁺ F f

 ⟦_⟧ : ∀ {Δ} -> functor Δ -> (f : gksubst Δ Set) -> Set
 ⟦ T ⟧ f = ?