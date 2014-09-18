module Transitivity where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat
open import WfNat
open import Model
open import Relation.Binary.PropositionalEquality
open SetF

TRANS : ∀ {A} -> PREL A -> Set
TRANS R = ∀ {a b c} -> R a b -> R b c -> R a c

trans-⊥' : TRANS ⊥'
trans-⊥' h1 h2 n = {!!} -- need Rne deterministic

NatR-trans : TRANS NatR
NatR-trans zero zero = zero
NatR-trans (suc x) (suc y) = suc (NatR-trans x y)
NatR-trans (neu x) (neu y) = neu (trans-⊥' x y)

module TransF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
            (set<trans : ∀ {j} (p : j < k) -> TRANS (SetU' (akf p))) where
 transEl : ∀ {A A' B B' C C' a b c}
      (pAB : A ≈ B ∈ (SetU' (inj akf)))
         (eqB : B ≡ B')
      (pBC : B' ≈ C ∈ (SetU' (inj akf)))
         (eqC : C ≡ C')
      (pAC : A' ≈ C' ∈ (SetU' (inj akf)))
         (eqA : A ≡ A')
   -> ElU' (inj akf) pAB a b
   -> ElU' (inj akf) pBC b c
   -> ElU' (inj akf) pAC a c
 transEl pAB refl pBC refl pAC refl t1 t2 = {!!}

 transSet : TRANS (SetU' (inj akf))
 transSet (Neu x) (Neu x₁) = Neu (trans-⊥' x x₁)
 transSet Nat Nat = Nat
 transSet (Π pA pF) (Π pA₁ pF₁) = {!!}
 transSet (Set* x) (Set* x₁) = {!!}