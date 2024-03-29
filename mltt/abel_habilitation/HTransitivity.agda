module HTransitivity where
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
open import Relation.Binary.PropositionalEquality hiding ([_])
open SetF
open import Util
open import ElIrrelevance

TRANS : ∀ {A} -> PREL A -> Set
TRANS R = ∀ {a b c} -> R a b -> R b c -> R a c

TRANS' : ∀ {A} -> PREL A -> Set
TRANS' R = ∀ {a b b' c} -> R a b -> b ≡ b' -> R b' c -> R a c

SELFL : ∀ {A} -> PREL A -> Set
SELFL R = ∀ {a a'} -> R a a' -> R a a

trans-⊥' : TRANS ⊥'
trans-⊥' h1 h2 n with h1 n | h2 n
... | _ , (p1 , p2) | _ , (p3 , p4) with Rne-deter p2 p3
trans-⊥' h1 h2 n | proj₁ , (p1 , p2) | .proj₁ , (p3 , p4) | refl = , p1 , p4

NatR-trans : TRANS NatR
NatR-trans zero zero = zero
NatR-trans (suc x) (suc y) = suc (NatR-trans x y)
NatR-trans (neu x) (neu y) = neu (trans-⊥' x y)

App-trans : ∀ {B : REL} -> TRANS B -> TRANS (App B)
App-trans f (inj red1 (b2 , red2) rel) (inj (b3 , red3) b4 rel₁) with eval-deter red2 red3
App-trans f (inj red1 (b2 , red2) rel) (inj (.b2 , red3) red4 rel₁) | refl = inj red1 red4 (f rel rel₁)

open import Sym

module TransF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
      (set<trans : ∀ {j} (p : j < k) -> TRANS (SetU' (akf p)))
  where
 open IrrF k akf

 mutual
  transEl : ∀ {A B C} (pAB : A ≈ B ∈ SetU' K) (pBC : B ≈ C ∈ SetU' K) (pAC : A ≈ C ∈ SetU' K) ->
   ∀ {f g h} -> f ≈ g ∈ ElU' pAB -> g ≈ h ∈ ElU' pBC -> f ≈ h ∈ ElU' pAC
  transEl (Neu x x₂) (Neu x₁ x₃) (Neu x₄ x₅) (inj x₆) (inj x₇) = inj (trans-⊥' x₆ x₇)
  transEl Nat Nat Nat x1 x2 = NatR-trans x1 x2
  transEl (Π pA pF) (Π pA₁ pF₁) (Π pA₂ pF₂) fRg gRh = λ aRa'₂ →
    let aRa'₁ = irrR pA₂ refl pA₁ aRa'₂ in
    let gaRha' = gRh aRa'₁ in
    let aRa' = irrL pA₂ refl pA aRa'₂ in
    let a'Ra = hsymEl _ _ pA (symSetω' _ pA) aRa' in
    let aRa = transEl pA (symSetω' _ pA) {! (transSet pA (symSetω' _ pA)) !} aRa' a'Ra in
    {!!}
  transEl (Set* x) (Set* x₁) (Set* x₂) x1 x2 = set<trans x₂ {!!} {!!}

  symEl : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> SYM (ElU' pA)
  symEl = {!!} -- (Neu y _) (inj x) = inj (sym-⊥' x)
  -- symEl Nat ab = NatR-sym ab
  -- symEl (Π pA pF) ab = λ p → 
  --  let p' = symEl pA p in
  --  let pp' = transEl pA p p' in
  --  let q = App-sym (symEl (App.rel (pF p'))) (ab p') in
  --  let q0 = App→ (irrR (App.rel (pF p')) (AppDeter4 (pF p') (pF pp')) (App.rel (pF pp'))) q in
  --  let q1 = App→ (irrL (App.rel (pF pp')) (AppDeter3 (pF pp') (pF p)) (App.rel (pF p))) q0 in
  --  q1
  -- symEl (Set* y) ab = symSetω' (akf y) ab

  selfL : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> SELFL (ElU' pA)
  selfL pA p = {!!} --transEl pA p (symEl pA p)

 mutual
  transSet' : TRANS' (SetU' K)
  transSet' (Neu x p) refl (Neu x₁ _) = Neu (trans-⊥' x x₁) p
  transSet' Nat refl Nat = Nat
  transSet' (Π pA pF) refl (Π pA₁ pF₁) = Π (transSet pA pA₁) (λ aa'AA'' →
    let aaAA'' = selfL (transSet pA pA₁) aa'AA'' in 
    let aaAA' = irrLω' (transSet pA pA₁) pA aaAA'' in
    let aa'A'A'' = irrRω' (transSet pA pA₁) pA₁ aa'AA'' in
    let q = transSet' (App.rel (pF aaAA')) (AppDeter1 (pF aaAA') (pF₁ aa'A'A'')) (App.rel (pF₁ aa'A'A'')) in
    inj (App.red1 (pF aaAA')) (App.red2 (pF₁ aa'A'A'')) q
   )
  transSet' (Set* x) refl (Set* x₁) = Set* x

  transSet : TRANS (SetU' K)
  transSet pA pB = transSet' pA refl pB

transSetω' : ∀ {k} (acck : Acc k) -> TRANS (SetU' acck)
transSetω' (inj x) = TransF.transSet _ _ (λ p → transSetω' (x p))

symω' : ∀ {k} (acck : Acc k) -> ∀ {A A'} (pA : A ≈ A' ∈ SetU' acck) -> SYM (ElU' pA)
symω' (inj x) = TransF.symEl _ _ (λ p → transSetω' (x p))

symω : ∀ {A A'} (pA : A ≈ A' ∈ Type) -> SYM ([ pA ])
symω (k , pA) = symω' _ pA

-- transω' : ∀ {k} (K : Acc k) {A A'} (pA : A ≈ A' ∈ SetU' K) -> TRANS (ElU' pA)
-- transω' (inj x) = TransF.transEl _ _ (λ p → transSetω' (x p))

