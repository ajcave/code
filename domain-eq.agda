module domain-eq where
open import Data.Nat
open import Data.Unit hiding (_≤_)
open import Data.Sum

Dom : Set₁
Dom = ℕ -> Set

_⇒_ : Dom -> Dom -> Set
A ⇒ B = (n : _) → A n → B n 

▸ : Dom -> Dom
▸ A zero = Unit
▸ A (suc n) = A n

iter : ∀ {C : Set₁} -> (C -> C) -> C -> ℕ -> C
iter f b zero = b
iter f b (suc n) = f (iter f b n)

1⁺ : Dom
1⁺ n = Unit

μ : (Dom -> Dom) -> Dom
μ F n = iter F 1⁺ (suc n) n

_⇛_ : Dom -> Dom -> Dom
(A ⇛ B) n = (k : _) → k ≤ n → A k → B k

_⊕_ : Dom -> Dom -> Dom
(A ⊕ B) n = A n ⊎ B n

G : Dom -> Dom
G D = 1⁺ ⊕ ((▸ D) ⇛ (▸ D))

roll▸ : ▸ (μ ▸) ⇒ μ ▸
roll▸ zero t = unit
roll▸ (suc n) t = t

unroll▸ : μ ▸ ⇒ ▸ (μ ▸)
unroll▸ zero t = unit
unroll▸ (suc n) t = t

roll : G (μ G) ⇒ μ G -- (∀ k ≤ n     -> (▸ (μ G)) k ⇛ (▸ (μ G)) k) -> μ G n
                     -- (∀ k ≤ suc m -> (▸ (μ G)) k ⇛ (▸ (μ G)) k) -> G (μ G)
roll n (inj₁ x) = inj₁ x
roll zero (inj₂ y) = inj₂ (λ k _ z → z)
roll (suc n) (inj₂ y) = inj₂ (λ k x x' → {!!})

unroll : μ G ⇒ G (μ G)
unroll n t = {!!}

open import Relation.Binary.PropositionalEquality

lem0 : ∀ n f -> unroll n (roll n f) ≡ f
lem0 n f = {!!}