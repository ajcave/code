{-# OPTIONS --no-positivity-check #-}
module non-positive where
open import Data.Nat
open import Data.Fin

data functor (n : ℕ) : Set where
 ▹ : (X : Fin n) -> functor n
 μ : (F : functor (suc n)) -> functor n
 _⇒_ : (A : functor zero) (F : functor n) -> functor n

env : ℕ -> Set₁
env n = ∀ (X : Fin n) -> Set

extend : ∀ {n} -> env n -> Set -> env (suc n)
extend ρ A zero = A
extend ρ A (suc i) = ρ i

mutual
 data μ' {n} (F : functor (suc n)) (ρ : env n) : Set where
  ⟨_⟩ : ⟦ F ⟧ (extend ρ (μ' F ρ)) -> μ' F ρ

 ⟦_⟧ : ∀ {n} -> functor n -> (ρ : env n) -> Set
 ⟦ ▹ X ⟧ ρ = ρ X
 ⟦ μ F ⟧ ρ = μ' F ρ
 ⟦ A ⇒ F ⟧ ρ = ⟦ A ⟧ (λ ()) → ⟦ F ⟧ ρ