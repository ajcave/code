module Sym where
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

SYM : ∀ {A} -> PREL A -> Set
SYM R = ∀ {a b} -> R a b -> R b a

sym-⊥' : SYM ⊥'
sym-⊥' h n = , proj₂ (proj₂ (h n)) , proj₁ (proj₂ (h n))

-- symApp : ∀ {f a f' a' B} -> SYM B -> 
--     f · a ≈ f' · a' ∈App B
--  -> f' · a' ≈ f · a ∈App B
-- symApp sB h = inj _ _ (_·_≈_·_∈App_.red2 h) (_·_≈_·_∈App_.red1 h) (sB (_·_≈_·_∈App_.rel h))

AppDeter1 :  ∀ {f1 a1 f2 a2 f3 a3 B B'} 
    (p : f1 · a1 ≈ f2 · a2 ∈App B)
    (q : f2 · a2 ≈ f3 · a3 ∈App B')
   -> _·_≈_·_∈App_.b2 p ≡ _·_≈_·_∈App_.b1 q
AppDeter1 p q = {!!}

module Sym (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j) where
 mutual
  symSet : SYM (SetU' (inj akf))
  symSet (Neu y) = Neu (sym-⊥' y)
  symSet Nat = Nat
  symSet (Π pA y) = Π (symSet pA) (λ p →
    let q = y (symEl pA refl refl (symSet pA) p) in
    inj _ _ (_·_≈_·_∈App_.red2 q) (_·_≈_·_∈App_.red1 q) (symSet (_·_≈_·_∈App_.rel q)))
  symSet (Set* y) = Set* y

  symEl : ∀ {A A' B B'} (pA : A ≈ A' ∈ (SetU' (inj akf)))
                     (eqA : A ≡ B) (eqB : A' ≡ B')
                     (pA' : B' ≈ B ∈ (SetU' (inj akf)))
   {a a'} ->
   ElU' (inj akf) pA' a a' -> ElU' (inj akf) pA a' a
  symEl (Neu y) refl refl (Neu w) (inj y') = inj (sym-⊥' y')
  symEl Nat refl refl Nat h = {!!}
  symEl (Π pA y) refl refl (Π pA' y') h = λ p →
   let p' = symEl pA' refl refl pA p in
   let q = h p' in
   inj _ _ (_·_≈_·_∈App_.red2 q) (_·_≈_·_∈App_.red1 q)
   (symEl (_·_≈_·_∈App_.rel (y p)) {!!} {!!} (_·_≈_·_∈App_.rel (y' p')) (_·_≈_·_∈App_.rel q))
  symEl (Set* y) refl refl (Set* y') h = {!!}