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

mutual
 reifyNat : ∀ {a a'} -> a ≈ a' ∈ NatR -> ↓[ Nat ] a ≈ ↓[ Nat ] a' ∈ ⊤'
 reifyNat (natval x) n = , (nat natval (proj₁ (proj₂ (reifyNatV x n)))) , (nat natval (proj₂ (proj₂ (reifyNatV x n))))
 reifyNat (neu x) n = , nat neu (natneu (neu (proj₁ (proj₂ (x n))))) , nat neu (natneu (neu (proj₂ (proj₂ (x n)))))

 reifyNatV : ∀ {a a'} -> a ≈ a' ∈ NatV -> ∀ n -> ∃ (λ v -> RnfNat n , a ↘ v × RnfNat n , a' ↘ v)
 reifyNatV zero n = , zero , zero
 reifyNatV (suc x) n = , (suc (proj₁ (proj₂ (reifyNatV x n)))) , (suc (proj₂ (proj₂ (reifyNatV x n))))
 reifyNatV (natneu x) n = , (natneu (proj₁ (proj₂ (reifyNatNe x n)))) , (natneu (proj₂ (proj₂ (reifyNatNe x n))))

 reifyNatNe : ∀ {a a'} -> a ≈ a' ∈ NatNe -> ∀ n -> ∃ (λ v -> RneNat n , a ↘ v × RneNat n , a' ↘ v)
 reifyNatNe (x ⊕ x₁) n = _ , (((proj₁ (proj₂ (x n))) ⊕ (proj₁ (proj₂ (reifyNatV x₁ n)))) , ((proj₂ (proj₂ (x n))) ⊕ (proj₂ (proj₂ (reifyNatV x₁ n)))))
 reifyNatNe (neu x) n = _ , ((neu (proj₁ (proj₂ (x n)))) , (neu (proj₂ (proj₂ (x n)))))

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
  reflect Nat d = neu d
  reflect (Π pA pF) d = λ p ->
    let q = reify pA p 
        q1 = reflect (rel (pF p))
                     (λ n → , (ap (proj₁ (proj₂ (d n))) (proj₁ (proj₂ (q n))))
                            , (ap (proj₂ (proj₂ (d n))) (proj₂ (proj₂ (q n)))))
    in inj (, ↑ (rd1 (pF p))) (, ↑ (rd2 (pF p))) q1
  reflect (Set* j<k) d = reflectSet< j<k d 

  reify : Reify k (inj akf)
  reify (Neu x _) (inj d) n = , (Neut (proj₁ (proj₂ (d n))) , Neut (proj₂ (proj₂ (d n))))
  reify Nat p n = reifyNat p n
  reify (Π pA pF) d n =
    let qA = reflect pA (λ n₁ → , lvl n , lvl n)
        qF = pF qA
        dF = d qA
        q1 = reify (rel qF) (rel dF)
    in , ((Π (rd1 dF) (rd1 qF) (proj₁ (proj₂ (q1 _)))) , (Π (rd2 dF) (rd2 qF) (proj₂ (proj₂ (q1 _)))))
  reify (Set* j<k) d n = reifySet< j<k d n 

 reifySet : ReifySet k (inj akf)
 reifySet (Neu x _) n = , Neut (proj₁ (proj₂ (x n))) , Neut (proj₂ (proj₂ (x n)))
 reifySet Nat n = , Nat , Nat
 reifySet (Π pA pF) n =
   let q0 = pF (reflect pA (λ n₁ -> , lvl n , lvl n))
       qA = reifySet pA
       q2 = reifySet (rel q0)
   in , Fun (proj₁ (proj₂ (qA n))) (rd1 q0) (proj₁ (proj₂ (q2 (suc n))))
      , Fun (proj₂ (proj₂ (qA n))) (rd2 q0) (proj₂ (proj₂ (q2 (suc n))))
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
 reflectSetω' (inj akf) = λ x → Neu x ≤refl

reflectω : ∀ {k} {e e' A A'} -> (pA : A ≈ A' ∈ (SetU k)) -> e ≈ e' ∈ ⊥' -> ↑[ A ] e ≈ ↑[ A' ] e' ∈ (ElU k pA)
reflectω = reflectω' nat-acc

reifyω : ∀ {k} {a a' A A'} (pA : A ≈ A' ∈ (SetU k)) -> a ≈ a' ∈ (ElU k pA) -> ↓[ A ] a ≈ ↓[ A' ] a' ∈ ⊤'
reifyω = reifyω' nat-acc

