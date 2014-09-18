module Candidate where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Model
open import Data.Nat
open import WfNat

open SetF

reifyNat : ∀ {a a'} -> a ≈ a' ∈ NatR -> ↓[ Nat ] a ≈ ↓[ Nat ] a' ∈ ⊤'
reifyNat zero n = , zero , zero
reifyNat (suc x) n with reifyNat x n
reifyNat (suc x) n | _ , (q1 , q2) = , suc q1 , suc q2
reifyNat (neu x) n = , Neut (proj₁ (proj₂ (x n))) , Neut (proj₂ (proj₂ (x n)))

-- Types of reify and reflect, parameterized for convenience
-- Really these should just abstract over a universe U and an interpretation function ElU
Reflect : (k : ℕ) (acck : Acc k) -> Set
Reflect k acck = ∀ {e e' A A'} -> (pA : A ≈ A' ∈ (SetU' acck)) -> e ≈ e' ∈ ⊥' -> ↑[ A ] e ≈ ↑[ A' ] e' ∈ (ElU' acck pA)

Reify : (k : ℕ) (acck : Acc k) -> Set
Reify k acck = ∀ {a a' A A'} (pA : A ≈ A' ∈ (SetU' acck)) -> a ≈ a' ∈ (ElU' acck pA) -> ↓[ A ] a ≈ ↓[ A' ] a' ∈ ⊤'

ReifySet : (k : ℕ) (acck : Acc k) -> Set
ReifySet k acck = ∀ {a a'} -> a ≈ a' ∈ (SetU' acck) -> ↓[ Set* k ] a ≈ ↓[ Set* k ] a' ∈ ⊤'

ReflectSet : (k : ℕ) (acck : Acc k) -> Set
ReflectSet k acck = ∀ {E E'} -> E ≈ E' ∈ ⊥' -> ↑[ Set* k ] E ≈ ↑[ Set* k ] E' ∈ (SetU' acck)

-- To help the termination checker
module RRF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
           (reifySet<   : ∀ {j} -> (p : j < k) -> ReifySet   j (akf p))
           (reflectSet< : ∀ {j} -> (p : j < k) -> ReflectSet j (akf p)) where

 mutual
  reflect : Reflect k (inj akf)
  reflect (Neu x) d = inj d
  reflect Nat d = neu d
  reflect (Π pA pF) d = foo
   where foo : _ ≈ _ ∈ ΠR (ElU' _ pA) (λ p -> ElU' _ (App.rel (pF p)))
         foo p with pF p
         foo p | inj b1 b2 red1 red2 rel with reify pA p
         ... | q with reflect rel (λ n → , ((proj₁ (proj₂ (d n))) · (proj₁ (proj₂ (q n)))) , (proj₂ (proj₂ (d n)) · proj₂ (proj₂ (q n))))
         ... | q1 = inj _ _ (↑ red1) (↑ red2) q1
  reflect (Set* j<k) d = reflectSet< j<k d 

  reify : Reify k (inj akf)
  reify (Neu x) (inj d) n = , (Neut (proj₁ (proj₂ (d n))) , Neut (proj₂ (proj₂ (d n))))
  reify Nat p n = reifyNat p n
  reify (Π pA pF) d n with reflect pA (λ n₁ → , lvl n , lvl n)
  ... | q with pF q | d q
  reify (Π pA pF) d n | q | inj b1 b2 red1 red2 rel | inj b3 b4 red3 red4 rel₁ with reify rel rel₁
  ... | q1 = _ , ((Π red3 red1 (proj₁ (proj₂ (q1 _)))) , (Π red4 red2 (proj₂ (proj₂ (q1 _)))))
  reify (Set* j<k) d n = reifySet< j<k d n 

  reifySet : ReifySet k (inj akf)
  reifySet (Neu x) n = , Neut (proj₁ (proj₂ (x n))) , Neut (proj₂ (proj₂ (x n)))
  reifySet Nat n = , Nat , Nat
  reifySet (Π pA pF) n with pF (reflect pA (λ n₁ -> , lvl n , lvl n))
  reifySet (Π pA pF) n | inj b1 b2 red1 red2 rel with reifySet pA | reifySet rel
  ... | qA | q2 = , Fun (proj₁ (proj₂ (qA n))) red1 (proj₁ (proj₂ (q2 (suc n)))) , Fun (proj₂ (proj₂ (qA n))) red2 (proj₂ (proj₂ (q2 (suc n))))
  reifySet (Set* j<k) n = , SetZ , SetZ

-- There's nicer ways to factor this, but I can't be bothered at the moment.
mutual
 reflectω' : ∀ {k} (acck : Acc k) -> Reflect k acck
 reflectω' (inj akf) = RRF.reflect _ akf (λ j<k → reifySetω' (akf j<k)) (λ p → reflectSetω' (akf p))

 reifyω' : ∀ {k} (acck : Acc k) -> Reify k acck
 reifyω' (inj akf) = RRF.reify _ akf (λ j<k → reifySetω' (akf j<k)) (λ p → reflectSetω' (akf p))

 reifySetω' : ∀ {k} (acck : Acc k) -> ReifySet k acck
 reifySetω' (inj akf) = RRF.reifySet _ akf (λ j<k → reifySetω' (akf j<k)) (λ p → reflectSetω' (akf p))

 reflectSetω' : ∀ {k} (acck : Acc k) -> ReflectSet k acck
 reflectSetω' (inj akf) = Neu

reflectω : ∀ {k} {e e' A A'} -> (pA : A ≈ A' ∈ (SetU k)) -> e ≈ e' ∈ ⊥' -> ↑[ A ] e ≈ ↑[ A' ] e' ∈ (ElU k pA)
reflectω = reflectω' nat-acc

reifyω : ∀ {k} {a a' A A'} (pA : A ≈ A' ∈ (SetU k)) -> a ≈ a' ∈ (ElU k pA) -> ↓[ A ] a ≈ ↓[ A' ] a' ∈ ⊤'
reifyω = reifyω' nat-acc

