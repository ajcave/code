module Sym where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Nat
open import WfNat
open import Model
open import Relation.Binary.PropositionalEquality hiding ([_])
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

mutual
  -- This seems like a heterogenous version of symmetry? Is this really necessary?
  hsymEl : ∀ {k n} (an : Acc k) (ak : Acc n) {A A' B B' a a'}
      (pA : A ≈ A' ∈ (SetU' ak))
         (eqA : A ≡ B) (eqB : A' ≡ B')
      (pA' : B' ≈ B ∈ (SetU' an))
   -> ElU' _ pA a a'
   -> ElU' _ pA' a' a
  hsymEl (inj akf) (inj anf) (Neu _ y) refl refl (Neu _ w) (inj y') = inj (sym-⊥' y')
  hsymEl (inj akf) (inj anf) Nat refl refl Nat h = NatR-sym h
  hsymEl (inj akf) (inj anf) (Π pA y) refl refl (Π pA' y') h = λ p →
   let p' = hsymEl (inj anf) (inj akf) pA' refl refl pA p in
   let q = h p' in
   inj _ _ (App.red2 q) (App.red1 q) (hsym* (y p') (y' p) (App.rel q))
  hsymEl (inj akf) (inj anf) (Set* y) refl refl (Set* y') h = symSet _ _ ≤refl h

  hsym* :  ∀ {k n A A'} {K : Acc k} {N : Acc n} (pA : A ≈ A' ∈ App (SetU' K)) (pA' : A' ≈ A ∈ App (SetU' N))
   -> ∀ {a b} -> a ≈ b ∈ ElU' _ (App.rel pA) -> b ≈ a ∈ ElU' _ (App.rel pA')
  hsym* pA pA' x = hsymEl _ _ (App.rel pA) (AppDeter2 pA' pA) (AppDeter1 pA pA') (App.rel pA') x

  symSet : ∀ {k n} (K : Acc k) (N : Acc n) -> k ≤ n -> ∀ {A A'} -> A ≈ A' ∈ SetU' K -> A' ≈ A ∈ SetU' N
  symSet (inj akf) (inj akn) kn (Neu y p) = Neu (sym-⊥' y) (≤trans p kn)
  symSet (inj akf) (inj akn) kn Nat = Nat
  symSet (inj akf) (inj akn) kn (Π pA pF) = Π (symSet (inj akf) (inj akn) kn pA) (λ p →
    let q = pF (hsymEl (inj akf) (inj akn) (symSet _ _ kn pA) refl refl pA p) in
    inj _ _ (App.red2 q) (App.red1 q) (symSet (inj akf) (inj akn) kn (App.rel q)))
  symSet (inj akf) (inj anf) kn (Set* y) = Set* (≤trans y kn)

symSetω' : ∀ {k} (K : Acc k) -> SYM (SetU' K)
symSetω' K = symSet K K ≤refl

symSetω : ∀ {k} -> SYM (SetU k)
symSetω = symSetω' nat-acc

-- hsymElω' : ∀ {k} {K : Acc k} {A A' B B' a a'}
--       (pA : A ≈ A' ∈ (SetU' K))
--          (eqA : A ≡ B) (eqB : A' ≡ B')
--       (pA' : B' ≈ B ∈ (SetU' K))
--    -> ElU' K pA' a a'
--    -> ElU' K pA a' a
-- hsymElω' {k} {inj x} = SymF.hsymEl _ x (λ p → symSetω' (x p))


--hsymω (n , pA) (m , pA') = SymF.hsymEl _ _ {!!} pA' refl refl pA

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



