module Candidate where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Model

data ⌊_⌋ (A : Val) (U : REL) : REL where
 inj : ∀ {e₁ e₂ A₁ A₂}
        -> A₁ ≈ A ∈ U
        -> A₂ ≈ A ∈ U
        -> e₁ ≈ e₁ ∈ ⊥' -> (↑[ A₁ ] e₁) ≈ (↑[ A₂ ] e₂) ∈ (⌊ A ⌋ U)

⌈_⌉ : Val -> REL -> REL
⌈ A ⌉ U a1 a2 = ∀ {A₁ A₂} -> A₁ ≈ A ∈ U -> A₂ ≈ A ∈ U -> (↓[ A₁ ] a1 ≈ ↓[ A₂ ] a2 ∈ ⊤')