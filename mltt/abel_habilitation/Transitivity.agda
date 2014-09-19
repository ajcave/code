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
trans-⊥' h1 h2 n with h1 n | h2 n
... | _ , (p1 , p2) | _ , (p3 , p4) with Rne-deter p2 p3
trans-⊥' h1 h2 n | proj₁ , (p1 , p2) | .proj₁ , (p3 , p4) | refl = , p1 , p4

NatR-trans : TRANS NatR
NatR-trans zero zero = zero
NatR-trans (suc x) (suc y) = suc (NatR-trans x y)
NatR-trans (neu x) (neu y) = neu (trans-⊥' x y)

App-trans : ∀ {B : REL} -> TRANS B -> TRANS (App B)
App-trans f (inj b1 b2 red1 red2 rel) (inj b3 b4 red3 red4 rel₁) with app-deter red2 red3
App-trans f (inj b1 b2 red1 red2 rel) (inj .b2 b4 red3 red4 rel₁) | refl = inj _ _ red1 red4 (f rel rel₁)

open import Sym

module TransF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
      (set<trans : ∀ {j} (p : j < k) -> TRANS (SetU' (akf p)))
      (set<sym : ∀ {j} (p : j < k) -> SYM (SetU' (akf p)))
  where
 open IrrF k akf

 mutual
  transEl : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> TRANS (ElU' K pA)
  transEl (Neu y _) (inj y') (inj y0) = inj (trans-⊥' y' y0)
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
  symEl (Neu y _) (inj x) = inj (sym-⊥' x)
  symEl Nat ab = NatR-sym ab
  symEl (Π pA pF) ab = λ p → 
   let p' = symEl pA p in
   let pp' = transEl pA p p' in
   let q = App-sym (symEl (App.rel (pF p'))) (ab p') in
   let q0 = App→ (irrR (App.rel (pF p')) (AppDeter4 (pF p') (pF pp')) (App.rel (pF pp'))) q in
   let q1 = App→ (irrL (App.rel (pF pp')) (AppDeter3 (pF pp') (pF p)) (App.rel (pF p))) q0 in
   q1
  symEl (Set* y) ab = set<sym y ab

 mutual
  transSet' : TRANS' (SetU' K)
  transSet' (Neu x p) refl (Neu x₁ _) = Neu (trans-⊥' x x₁) p
  transSet' Nat refl Nat = Nat
  transSet' (Π pA pF) refl (Π pA₁ pF₁) = Π (transSet pA pA₁) (λ aa'AA'' →
    let a'aAA'' = symEl (transSet pA pA₁) aa'AA'' in
    let aaAA'' = transEl (transSet pA pA₁) aa'AA'' a'aAA'' in 
    let aaAA' = irrLω' (transSet pA pA₁) pA aaAA'' in
    let aa'A'A'' = irrRω' (transSet pA pA₁) pA₁ aa'AA'' in
    let q = transSet' (App.rel (pF aaAA')) (AppDeter1 (pF aaAA') (pF₁ aa'A'A'')) (App.rel (pF₁ aa'A'A'')) in
    inj _ _ (App.red1 (pF aaAA')) (App.red2 (pF₁ aa'A'A'')) q
   )
  transSet' (Set* x) refl (Set* x₁) = Set* x

  transSet : TRANS (SetU' K)
  transSet pA pB = transSet' pA refl pB
 