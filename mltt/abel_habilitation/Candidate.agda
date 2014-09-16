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
 reflect (Π pA pF) d = foo
  where foo : _ ≈ _ ∈ ΠR (El pA) (λ p -> El (_·_≈_·_∈App_.rel (pF p)))
        foo p with pF p
        foo p | inj b1 b2 red1 red2 rel with reify pA p
        ... | q with reflect rel (λ n → , ((proj₁ (proj₂ (d n))) · (proj₁ (proj₂ (q n)))) , (proj₂ (proj₂ (d n)) · proj₂ (proj₂ (q n))))
        ... | q1 = inj _ _ (↑ red1) (↑ red2) q1

 reify : ∀ {a a' A A'} (pA : A ≈ A' ∈ SetR) -> a ≈ a' ∈ (El pA) -> ↓[ A ] a ≈ ↓[ A' ] a' ∈ ⊤'
 reify (Neu x) (inj d) n = , (Neut (proj₁ (proj₂ (d n))) , Neut (proj₂ (proj₂ (d n))))
 reify Nat zero n = zero , (zero , zero)
 reify Nat (suc x) n with reify Nat x n
 ... | _ , (q1 , q2) = _ , ((suc q1) , (suc q2))
 reify Nat (neu x) n = _ , ((Neut (proj₁ (proj₂ (x n)))) , (Neut (proj₂ (proj₂ (x n)))))
 reify (Π pA pF) d n with reflect pA (λ n₁ → , lvl n , lvl n)
 ... | q with pF q | d q
 reify (Π pA pF) d n | q | inj b1 b2 red1 red2 rel | inj b3 b4 red3 red4 rel₁ with reify rel rel₁
 ... | q1 = _ , ((Π red3 red1 (proj₁ (proj₂ (q1 _)))) , (Π red4 red2 (proj₂ (proj₂ (q1 _)))))