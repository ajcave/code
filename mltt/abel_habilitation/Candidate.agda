module Candidate where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Model

⌈_⌉ : Val -> REL -> REL
⌈ A ⌉ U a1 a2 = ∀ {A₁ A₂} -> A₁ ≈ A ∈ U -> A₂ ≈ A ∈ U -> (↓[ A₁ ] a1 ≈ ↓[ A₂ ] a2 ∈ ⊤')

mutual
 reflect : ∀ {e e' A A'} -> (pA : A ≈ A' ∈ SetR) -> e ≈ e' ∈ ⊥' -> ↑[ A ] e ≈ ↑[ A' ] e' ∈ (El pA)
 reflect (Neu x) d = inj d
 reflect Nat d = {!!}
 reflect (Π pA x) d = {!!}

 reify : ∀ {a a' A A'} (pA : A ≈ A' ∈ SetR) -> a ≈ a' ∈ (El pA) -> ↓[ A ] a ≈ ↓[ A' ] a' ∈ ⊤'
 reify (Neu x) (inj d) = λ n → , (Neut (proj₁ (proj₂ (d n))) , Neut (proj₂ (proj₂ (d n))))
 reify Nat d = {!!}
 reify (Π pA x) d = {!!}