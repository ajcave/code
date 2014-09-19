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
open import Util
open import ElIrrelevance
open Syn

TRANS : ∀ {A} -> PREL A -> Set
TRANS R = ∀ {a b c} -> R a b -> R b c -> R a c

TRANS' : ∀ {A} -> PREL A -> Set
TRANS' R = ∀ {a b b' c} -> R a b -> b ≡ b' -> R b' c -> R a c

trans-⊥' : TRANS ⊥'
trans-⊥' h1 h2 n = {!!} -- need Rne deterministic

NatR-trans : TRANS NatR
NatR-trans zero zero = zero
NatR-trans (suc x) (suc y) = suc (NatR-trans x y)
NatR-trans (neu x) (neu y) = neu (trans-⊥' x y)

App-trans : ∀ {B : REL} -> TRANS B -> TRANS (App B)
App-trans f (inj b1 b2 red1 red2 rel) (inj b3 b4 red3 red4 rel₁) with app-deter red2 red3
App-trans f (inj b1 b2 red1 red2 rel) (inj .b2 b4 red3 red4 rel₁) | refl = inj _ _ red1 red4 (f rel rel₁)

SYM : ∀ {A} -> PREL A -> Set
SYM R = ∀ {a b} -> R a b -> R b a

App-sym : ∀ {B : REL} -> SYM B -> SYM (App B)
App-sym f (inj b1 b2 red1 red2 rel) = inj _ _ red2 red1 (f rel)

sym-⊥' : SYM ⊥'
sym-⊥' h n = , proj₂ (proj₂ (h n)) , proj₁ (proj₂ (h n))

NatR-sym : SYM NatR
NatR-sym zero = zero
NatR-sym (suc x) = suc (NatR-sym x)
NatR-sym (neu x) = neu (sym-⊥' x)

module TransF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
      (set<trans : ∀ {j} (p : j < k) -> TRANS (SetU' (akf p)))
      (set<sym : ∀ {j} (p : j < k) -> SYM (SetU' (akf p)))
 where
  open IrrF k akf

  mutual
   transEl : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> TRANS (ElU' K pA)
   transEl (Neu y) (inj y') (inj y0) = inj (trans-⊥' y' y0)
   transEl Nat ab bc = NatR-trans ab bc
   transEl (Π pA pF) ab bc = λ p →
    let p' = symEl pA p in
    let pp' = transEl pA p p' in
    let q0 = ab pp' in
    let q1 = bc p in
    let q2 = App→ (irrL (App.rel (pF pp')) (AppDeter3 (pF pp') (pF p)) (App.rel (pF p))) q0 in
    App-trans (transEl (App.rel (pF p))) q2 q1
   transEl (Set* y) ab bc = set<trans y ab bc

   symEl : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> SYM (ElU' K pA)
   symEl (Neu y) (inj x) = inj (sym-⊥' x)
   symEl Nat ab = NatR-sym ab
   symEl (Π pA pF) ab = λ p → 
    let p' = symEl pA p in
    let pp' = transEl pA p p' in
    let q = App-sym (symEl (App.rel (pF p'))) (ab p') in
    let q0 = App→ (irrR (App.rel (pF p')) (AppDeter4 (pF p') (pF pp')) (App.rel (pF pp'))) q in
    let q1 = App→ (irrL (App.rel (pF pp')) (AppDeter3 (pF pp') (pF p)) (App.rel (pF p))) q0 in
    q1
   symEl (Set* y) ab = set<sym y ab

