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

NatR-sym : SYM NatR
NatR-sym zero = zero
NatR-sym (suc x) = suc (NatR-sym x)
NatR-sym (neu x) = neu (sym-⊥' x)

module SymF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
            (set<sym : ∀ {j} (p : j < k) -> SYM (SetU' (akf p))) where
 mutual
  symSet : SYM (SetU' (inj akf))
  symSet (Neu y) = Neu (sym-⊥' y)
  symSet Nat = Nat
  symSet (Π pA y) = Π (symSet pA) (λ p →
    let q = y (symEl pA refl refl (symSet pA) p) in
    inj _ _ (App.red2 q) (App.red1 q) (symSet (App.rel q)))
  symSet (Set* y) = Set* y

  -- This seems like a heterogenous version of symmetry?
  symEl : ∀ {A A' B B' a a'} (pA : A ≈ A' ∈ (SetU' (inj akf)))
                     (eqA : A ≡ B) (eqB : A' ≡ B')
                     (pA' : B' ≈ B ∈ (SetU' (inj akf))) ->
   ElU' (inj akf) pA' a a' -> ElU' (inj akf) pA a' a
  symEl (Neu y) refl refl (Neu w) (inj y') = inj (sym-⊥' y')
  symEl Nat refl refl Nat h = NatR-sym h
  symEl (Π pA y) refl refl (Π pA' y') h = λ p →
   let p' = symEl pA' refl refl pA p in
   let q = h p' in
   inj _ _ (App.red2 q) (App.red1 q)
   (symEl (App.rel (y p))
             (AppDeter2 (y' p') (y p))
             (AppDeter1 (y p) (y' p'))
          (App.rel (y' p'))
          (App.rel q))
  symEl (Set* y) refl refl (Set* y') h with ≤uniq y y'
  symEl (Set* y) refl refl (Set* .y) h | refl = set<sym y h

symSetω' : ∀ {k} (acck : Acc k) -> SYM (SetU' acck)
symSetω' (inj x) = SymF.symSet _ x (λ p → symSetω' (x p))

symSetω : ∀ {k} -> SYM (SetU k)
symSetω = symSetω' nat-acc

symElω' : ∀ {k} (acck : Acc k) -> ∀ {A A' B B' a a'} (pA : A ≈ A' ∈ (SetU' acck))
                     (eqA : A ≡ B) (eqB : A' ≡ B')
                     (pA' : B' ≈ B ∈ (SetU' acck)) ->
      ElU' acck pA' a a' -> ElU' acck pA a' a
symElω' (inj x) = SymF.symEl _ x (λ p → symSetω' (x p))

symElω : ∀ {k} {A A' a a'}
     (pA  : A  ≈ A' ∈ (SetU k))
  -> (pA' : A' ≈ A  ∈ (SetU k))
  -> ElU k pA' a a' -> ElU k pA a' a
symElω pA pA' h = symElω' nat-acc pA refl refl pA' h


