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
open import Relation.Binary.PropositionalEquality hiding ([_])

open SetF
open Clo

mutual
 reifyNat : ∀ {a a'} -> a ≈ a' ∈ NatR -> ↓[ Nat ] a ≈ ↓[ Nat ] a' ∈ ⊤'
 reifyNat p n = inj' (unbox (rd1 p) (rd1 (reifyNatV (rel p) n))) (unbox (rd2 p) (rd2 (reifyNatV (rel p) n))) (rel (reifyNatV (rel p) n))

 reifyNatV : ∀ {a a'} -> a ≈ a' ∈ NatV -> ∀ n -> a ≈ a' ∈ Clo (RnfNat_,_↘_ n) _≡_
 reifyNatV zero n = inj' zero zero refl
 reifyNatV (suc x) n =
   let q = reifyNatV x n in
   inj' (suc (rd1 q)) (suc (rd2 q)) (cong suc (rel q))
 reifyNatV (natneu x) n =
   let q = reifyNatNe x n in
   inj' (natneu (rd1 q)) (natneu (rd2 q)) (rel q)

 reifyNatNe : ∀ {a a'} -> a ≈ a' ∈ NatNe -> ∀ n -> a ≈ a' ∈ Clo (RneNat_,_↘_ n) _≡_
 reifyNatNe (x ⊕ x₁) n =
   let q = reifyNatV x₁ n in
   inj' ((rd1 (x n)) ⊕ (rd1 q)) ((rd2 (x n)) ⊕ (rd2 q)) (cong₂ _⊕_ (rel (x n)) (rel q))

-- Types of reify and reflect, parameterized for convenience
-- Really these should just abstract over a universe U and an interpretation function ElU
Reflect : (k : ℕ) (acck : Acc k) -> Set
Reflect k acck = ∀ {e e' A A'} -> (pA : A ≈ A' ∈ (SetU' acck)) -> e ≈ e' ∈ ⊥' -> ↑[ A ] e ≈ ↑[ A' ] e' ∈ (ElU' pA)

Reify : (k : ℕ) (acck : Acc k) -> Set
Reify k acck = ∀ {a a' A A'} (pA : A ≈ A' ∈ (SetU' acck)) -> a ≈ a' ∈ (ElU' pA) -> ↓[ A ] a ≈ ↓[ A' ] a' ∈ ⊤'

ReifySet : (k : ℕ) (acck : Acc k) -> Set
ReifySet k acck = ∀ {a a'} -> a ≈ a' ∈ (SetU' acck) -> ↓[ Set* k ] a ≈ ↓[ Set* k ] a' ∈ ⊤'

ReflectSet : (k : ℕ) (acck : Acc k) -> Set
ReflectSet k acck = ∀ {E E'} -> E ≈ E' ∈ ⊥' -> ↑[ Set* k ] E ≈ ↑[ Set* k ] E' ∈ (SetU' acck)

open Clo
-- To help the termination checker
module RRF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
           (reifySet<   : ∀ {j} -> (p : j < k) -> ReifySet   j (akf p))
           (reflectSet< : ∀ {j} -> (p : j < k) -> ReflectSet j (akf p)) where

 mutual
  reflect : Reflect k (inj akf)
  reflect (Neu x _) d = inj d
  reflect Nat d = inj (, neu) (, neu) (natneu (d ⊕ zero)) --neu d
  reflect (Π pA pF) d = λ p ->
    let q = reify pA p 
        q1 = reflect (rel (pF p))
                     (λ n → inj' (ap (rd1 (d n)) (rd1 (q n)))
                                  (ap (rd2 (d n)) (rd2 (q n)))
                                  (cong₂ _·_ (rel (d n)) (rel (q n))))
    in inj (, ↑ (rd1 (pF p))) (, ↑ (rd2 (pF p))) q1
  reflect (Set* j<k) d = reflectSet< j<k d 

  reify : Reify k (inj akf)
  reify (Neu x _) (inj d) n = inj' (Neut (rd1 (d n))) (Neut (rd2 (d n))) (rel (d n))
  reify Nat p n = reifyNat p n
  reify (Π pA pF) d n =
    let qA = reflect pA (λ n₁ → inj' (lvl n) (lvl n) refl)
        qF = pF qA
        dF = d qA
        q1 = reify (rel qF) (rel dF)
    in inj' (Π (rd1 dF) (rd1 qF) (rd1 (q1 _))) (Π (rd2 dF) (rd2 qF) (rd2 (q1 _))) (cong ƛ (rel (q1 _)))
  reify (Set* j<k) d n = reifySet< j<k d n 

 reifySet : ReifySet k (inj akf)
 reifySet (Neu x _) n = inj' (Neut (rd1 (x n))) (Neut (rd2 (x n))) (rel (x n))
 reifySet Nat n = inj' Nat Nat refl
 reifySet (Π pA pF) n =
   let q0 = pF (reflect pA (λ n₁ -> inj' (lvl n) (lvl n) refl))
       qA = reifySet pA
       q2 = reifySet (rel q0)
   in inj' (Fun (rd1 (qA n)) (rd1 q0) (rd1 (q2 (suc n))))
           (Fun (rd2 (qA n)) (rd2 q0) (rd2 (q2 (suc n))))
           (cong₂ Π (rel (qA n)) (cong ƛ (rel (q2 _))))
 reifySet (Set* j<k) n = inj' SetZ SetZ refl

-- There's nicer ways to factor this, but I can't be bothered at the moment.
mutual
 reflectω' : ∀ {k} (acck : Acc k) -> Reflect k acck
 reflectω' (inj akf) = RRF.reflect _ akf (λ j<k → reifySetω' (akf j<k)) (λ p → reflectSetω' (akf p))

 reifyω' : ∀ {k} (acck : Acc k) -> Reify k acck
 reifyω' (inj akf) = RRF.reify _ akf (λ j<k → reifySetω' (akf j<k)) (λ p → reflectSetω' (akf p))

 reifySetω' : ∀ {k} (acck : Acc k) -> ReifySet k acck
 reifySetω' (inj akf) = RRF.reifySet _ akf (λ j<k → reifySetω' (akf j<k)) (λ p → reflectSetω' (akf p))

 reflectSetω' : ∀ {k} (acck : Acc k) -> ReflectSet k acck
 reflectSetω' (inj akf) = λ x → Neu x ≤refl

reflectω : ∀ {k} {e e' A A'} -> (pA : A ≈ A' ∈ (SetU k)) -> e ≈ e' ∈ ⊥' -> ↑[ A ] e ≈ ↑[ A' ] e' ∈ (ElU k pA)
reflectω = reflectω' nat-acc

reifyω : ∀ {k} {a a' A A'} (pA : A ≈ A' ∈ (SetU k)) -> a ≈ a' ∈ (ElU k pA) -> ↓[ A ] a ≈ ↓[ A' ] a' ∈ ⊤'
reifyω = reifyω' nat-acc

