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
open import Util
open SetF

SYM : ∀ {A} -> PREL A -> Set
SYM R = ∀ {a b} -> R a b -> R b a

sym-⊥' : SYM ⊥'
sym-⊥' h n = , proj₂ (proj₂ (h n)) , proj₁ (proj₂ (h n))

NatR-sym : SYM NatR
NatR-sym zero = zero
NatR-sym (suc x) = suc (NatR-sym x)
NatR-sym (neu x) = neu (sym-⊥' x)

App-sym : ∀ {B : REL} -> SYM B -> SYM (App B)
App-sym f (inj b1 b2 red1 red2 rel) = inj _ _ red2 red1 (f rel)

module SymF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
            (set<sym : ∀ {j} (p : j < k) -> SYM (SetU' (akf p))) where
  K : Acc k
  K = inj akf

  -- This seems like a heterogenous version of symmetry? Is this really necessary?
  hsymEl : ∀ {A A' B B' a a'}
      (pA : A ≈ A' ∈ (SetU' (inj akf)))
         (eqA : A ≡ B) (eqB : A' ≡ B')
      (pA' : B' ≈ B ∈ (SetU' (inj akf)))
   -> ElU' (inj akf) pA' a a'
   -> ElU' (inj akf) pA a' a
  hsymEl (Neu _ y) refl refl (Neu _ w) (inj y') = inj (sym-⊥' y')
  hsymEl Nat refl refl Nat h = NatR-sym h
  hsymEl (Π pA y) refl refl (Π pA' y') h = λ p →
   let p' = hsymEl pA' refl refl pA p in
   let q = h p' in
   inj _ _ (App.red2 q) (App.red1 q)
   (hsymEl (App.rel (y p))
             (AppDeter2 (y' p') (y p))
             (AppDeter1 (y p) (y' p'))
          (App.rel (y' p'))
          (App.rel q))
  hsymEl (Set* y) refl refl (Set* y') h with ≤uniq y y'
  hsymEl (Set* y) refl refl (Set* .y) h | refl = set<sym y h

  symSet : SYM (SetU' (inj akf))
  symSet (Neu y p) = Neu (sym-⊥' y) p
  symSet Nat = Nat
  symSet (Π pA pF) = Π (symSet pA) (λ p →
    let q = pF (hsymEl pA refl refl (symSet pA) p) in
    inj _ _ (App.red2 q) (App.red1 q) (symSet (App.rel q)))
  symSet (Set* y) = Set* y

symSetω' : ∀ {k} (acck : Acc k) -> SYM (SetU' acck)
symSetω' (inj x) = SymF.symSet _ x (λ p → symSetω' (x p))

symSetω : ∀ {k} -> SYM (SetU k)
symSetω = symSetω' nat-acc

-- symElω' : ∀ {k} (acck : Acc k) -> ∀ {A A' B B' a a'} (pA : A ≈ A' ∈ (SetU' acck))
--                      (eqA : A ≡ B) (eqB : A' ≡ B')
--                      (pA' : B' ≈ B ∈ (SetU' acck)) ->
--       ElU' acck pA' a a' -> ElU' acck pA a' a
-- symElω' (inj x) = SymF.symEl _ x (λ p → symSetω' (x p))

-- symElω2' : ∀ {k} (acck : Acc k) -> ∀ {A A' a a'}
--                      (pA : A ≈ A' ∈ (SetU' acck)) ->
--       ElU' acck pA a a' -> ElU' acck (symSetω' acck pA) a' a
-- symElω2' acck pA = symElω' acck (symSetω' acck pA) refl refl pA

-- symElω : ∀ {k} {A A' a a'}
--      (pA  : A'  ≈ A ∈ (SetU k))
--   -> (pA' : A ≈ A'  ∈ (SetU k))
--   -> ElU k pA' a a' -> ElU k pA a' a
-- symElω pA pA' h = symElω' nat-acc pA refl refl pA' h



