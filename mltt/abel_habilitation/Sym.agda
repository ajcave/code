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
open import Function
open SetF

SYM : ∀ {A} -> PREL A -> Set
SYM R = ∀ {a b} -> R a b -> R b a

HSYM : ∀ {B A} (U1 : PREL A) (El1 : INTERP B U1) (U2 : PREL A) (El2 : INTERP B U2) -> Set
HSYM U1 El1 U2 El2 = ∀ {A A'} (pA : A ≈ A' ∈ U1) (pA' : A' ≈ A ∈ U2)
  -> ∀ {a a'} -> a ≈ a' ∈ (El1 pA) -> a' ≈ a ∈ (El2 pA')

sym-⊥' : SYM ⊥'
sym-⊥' h n = , proj₂ (proj₂ (h n)) , proj₁ (proj₂ (h n))

mutual
 NatR-sym : SYM NatR
 NatR-sym p = inj (NatR.red2 p) (NatR.red1 p) (NatV-sym (NatR.rel p))

 NatV-sym : SYM NatV
 NatV-sym zero = zero
 NatV-sym (suc x) = suc (NatV-sym x)
 NatV-sym (natneu x) = natneu (NatNe-sym x)
 
 NatNe-sym : SYM NatNe
 NatNe-sym (x ⊕ x₁) = (sym-⊥' x) ⊕ (NatV-sym x₁)
 --NatNe-sym (neu x) = neu (sym-⊥' x)


-- NatR-sym zero = zero
-- NatR-sym (suc x) = suc (NatR-sym x)
-- NatR-sym (neu x) = neu (sym-⊥' x)
-- NatR-sym (p ⊕ x) = (sym-⊥' p) ⊕ (NatR-sym x)
-- NatR-sym (idR p) = idL (sym-⊥' p)
-- NatR-sym (idL p) = idR (sym-⊥' p)

App-sym : ∀ {C V : Set} {B : PREL V} {r : C -> V -> Set}  -> SYM B -> SYM (Clo r B)
App-sym f (inj red1 red2 rel) = inj red2 red1 (f rel)

open Clo

mutual
  -- This seems like a heterogenous version of symmetry? Is this really necessary?
  hsymEl : ∀ {k n} (an : Acc k) (ak : Acc n) -> HSYM (SetU' ak) ElU' (SetU' an) ElU'
  hsymEl (inj akf) (inj anf) (Neu _ y) (Neu _ w) (inj y') = inj (sym-⊥' y')
  hsymEl (inj akf) (inj anf) Nat Nat h = NatR-sym h
  hsymEl (inj akf) (inj anf) (Π pA y) (Π pA' y') h = λ p →
   let p' = hsymEl (inj anf) (inj akf) pA' pA p in
   let q = h p' in
   inj (red2 q) (red1 q) (hsym* evala-deter (y p') (y' p) (rel q))
  hsymEl (inj akf) (inj anf) (Set* y) (Set* y') h = symSet _ _ ≤refl h

  hsym* :  ∀ {k n} {K : Acc k} {N : Acc n} {C} {r : C -> Val -> Set} (d : Deterministic r)
   -> HSYM (Clo r (SetU' K)) (ElU' ∘ rel) (Clo r (SetU' N)) (ElU' ∘ rel)
  hsym* d (inj (_ , red1) (_ , red2) rel) (inj (_ , red3) (_ , red4) rel₁) x
     with d red1 red4 | d red2 red3
  hsym* d (inj (_ , red1) (_ , red2) rel) (inj (._ , red3) (._ , red4) rel₁) x | refl | refl = hsymEl _ _ rel rel₁ x

  symSet : ∀ {k n} (K : Acc k) (N : Acc n) -> k ≤ n -> ∀ {A A'} -> A ≈ A' ∈ SetU' K -> A' ≈ A ∈ SetU' N
  symSet (inj akf) (inj akn) kn (Neu y p) = Neu (sym-⊥' y) (≤trans p kn)
  symSet (inj akf) (inj akn) kn Nat = Nat
  symSet (inj akf) (inj akn) kn (Π pA pF) = Π (symSet (inj akf) (inj akn) kn pA) (λ p →
    let q = pF (hsymEl (inj akf) (inj akn) (symSet _ _ kn pA) pA p) in
    inj (red2 q) (red1 q) (symSet (inj akf) (inj akn) kn (rel q)))
  symSet (inj akf) (inj anf) kn (Set* y) = Set* (≤trans y kn)

symSetω' : ∀ {k} (K : Acc k) -> SYM (SetU' K)
symSetω' K = symSet K K ≤refl

symSetω : ∀ {k} -> SYM (SetU k)
symSetω = symSetω' nat-acc

