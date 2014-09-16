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
 reflect Nat d = neu d
 reflect (Π pA x) d = {!!}

 reify : ∀ {a a' A A'} (pA : A ≈ A' ∈ SetR) -> a ≈ a' ∈ (El pA) -> ↓[ A ] a ≈ ↓[ A' ] a' ∈ ⊤'
 reify (Neu x) (inj d) n = , (Neut (proj₁ (proj₂ (d n))) , Neut (proj₂ (proj₂ (d n))))
 reify Nat zero n = zero , (zero , zero)
 reify Nat (suc x) n with reify Nat x n
 ... | _ , (q1 , q2) = _ , ((suc q1) , (suc q2))
 reify Nat (neu x) n = _ , ((Neut (proj₁ (proj₂ (x n)))) , (Neut (proj₂ (proj₂ (x n)))))
 reify (Π pA x) d n = {!!}