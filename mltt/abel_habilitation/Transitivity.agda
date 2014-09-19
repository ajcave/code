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
open import Sym
open import Util
open import Irrelevance

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

-- App-trans : ∀ {B : REL} -> TRANS B -> TRANS (App B)
-- App-trans f (inj b1 b2 red1 red2 rel) (inj b3 b4 red3 red4 rel₁) with app-deter red2 red3
-- App-trans f (inj b1 b2 red1 red2 rel) (inj .b2 b4 red3 red4 rel₁) | refl = inj _ _ red1 red4 (f rel rel₁)

module TransF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
      (set<trans : ∀ {j} (p : j < k) -> TRANS (SetU' (akf p)))
 where
  K : Acc k
  K = inj akf

  transEl : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> TRANS (ElU' K pA)
  transEl (Neu y) (inj y') (inj y0) = inj (trans-⊥' y' y0)
  transEl Nat ab bc = NatR-trans ab bc
  transEl (Π pA pF) ab bc = λ p →
   let q : _ ≈ _ ∈ App (ElU' K (App.rel (pF p))) 
       q = ab p in
   {!!}
  transEl (Set* y) ab bc = set<trans y ab bc

  symEl : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> SYM (ElU' K pA)
  symEl (Neu y) ab = {!!}
  symEl Nat ab = {!!}
  symEl (Π pA pF) ab = λ p → 
   {!!}
  symEl (Set* y) ab = {!!}

  selfrel1 : ∀ {A a a'}
     (pAB : A ≈ A ∈ SetU' K)
     -- (pAC : A ≈ C ∈ SetU' K)
     -> a ≈ a' ∈ ElU' (inj akf) pAB
     -> a' ≈ a'  ∈ ElU' (inj akf) pAB
  selfrel1 pAB h = transEl pAB {!!} h

 -- transEl : ∀ {A A' B B' C C' a b c}
 --      (pAB : A ≈ B ∈ (SetU' (inj akf)))
 --         (eqB : B ≡ B')
 --      (pBC : B' ≈ C ∈ (SetU' (inj akf)))
 --         (eqC : C ≡ C')
 --      (pAC : A' ≈ C' ∈ (SetU' (inj akf)))
 --         (eqA : A ≡ A')
 --   -> a ≈ b ∈ ElU' (inj akf) pAB
 --   -> b ≈ c ∈ ElU' (inj akf) pBC
 --   -> a ≈ c ∈ ElU' (inj akf) pAC
 -- transEl pAB refl pBC refl pAC refl t1 t2 = {!!}

 -- mutual
 --  transSet : TRANS' (SetU' (inj akf))
 --  transSet (Neu x) refl (Neu x₁) = Neu (trans-⊥' x x₁)
 --  transSet Nat refl Nat = Nat
 --  transSet (Π pA pF) refl (Π pA₁ pF₁) = Π (transSet pA refl pA₁) (λ p →
 --    let p1 = resp (transSet pA refl pA₁) (selfrel1Set pA) (symSetω' (inj akf) pA₁) pA p in
 --    let p2 = resp (selfrel2Set (transSet pA refl pA₁)) (symSetω' (inj akf) pA₁) (selfrel2Set pA₁) pA₁ (selfrel2 (transSet pA refl pA₁) p) in
 --    let q1 = pF p1 in
 --    let q2 = pF₁ p2 in
 --    inj _ _ (App.red1 q1) (App.red2 q2) (transSet (App.rel q1) {!!} (App.rel q2))
 --    )
 --  transSet (Set* x) refl (Set* x₁) = Set* x₁

 --  resp : ∀ {A A' B' B}
 --    (pA : A  ≈ A'  ∈ SetU' (inj akf))
 --    (h : A ≈ B ∈ SetU' (inj akf))
 --    (h' : A' ≈ B' ∈ SetU' (inj akf))
 --    (pB : B ≈ B' ∈ SetU' (inj akf))
 --   -> (ElU' _ pA) →₂ (ElU' _ pB)
 --  resp (Neu x) (Neu x₂) (Neu x₁) (Neu x₃) r = r
 --  resp Nat Nat Nat Nat r = r
 --  resp (Π pA pF) (Π h h1) (Π h' h1') (Π pB pG) r = λ p →
 --   let p' : _ ≈ _ ∈ ElU' _ pA
 --       p' = resp pB (symSetω' (inj akf) h) (symSetω' (inj akf) h') pA p in
 --   let q : _ ≈ _ ∈ App (ElU' _ (App.rel (pF p')))
 --       q = r p' in
 --   inj _ _ (App.red1 q) (App.red2 q)
 --    (resp (App.rel (pF p')) {!transitivity...!} {!!} (App.rel (pG p)) (App.rel q))
 --  resp (Set* x) (Set* x₁) (Set* x₂) (Set* x₃) r with ≤uniq x x₃
 --  resp (Set* x) (Set* x₁) (Set* x₂) (Set* .x) r | refl = r

 --  selfrel1Set : ∀ {A A'} -> (pA : A ≈ A' ∈ SetU' (inj akf)) -> A ≈ A ∈ SetU' (inj akf)
 --  selfrel1Set pA = transSet pA refl (symSetω' (inj akf) pA)

 --  selfrel2Set : ∀ {A A'} -> (pA : A ≈ A' ∈ SetU' (inj akf)) -> A' ≈ A' ∈ SetU' (inj akf)
 --  selfrel2Set pA = symSetω' (inj akf) {!!} --transSet (symSetω' (inj akf) pA) refl pA

 --  selfrel1 : ∀ {A A' a a'} -> (pA : A ≈ A' ∈ (SetU' (inj akf)))
 --    -> a ≈ a' ∈ ElU' (inj akf) pA
 --    -> a ≈ a  ∈ ElU' (inj akf) (selfrel1Set pA)
 --  selfrel1 pA h = transEl pA refl (symSetω' (inj akf) pA) refl (selfrel1Set pA) refl
 --   h
 --   (symElω' (inj akf) (symSetω' (inj akf) pA) refl refl pA h)

 --  selfrel2 : ∀ {A A' a a'} -> (pA : A ≈ A' ∈ (SetU' (inj akf)))
 --    -> a ≈ a' ∈ ElU' (inj akf) pA
 --    -> a' ≈ a'  ∈ ElU' (inj akf) (selfrel2Set pA)
 --  selfrel2 pA h = transEl (symSetω' (inj akf) pA) refl pA refl (selfrel2Set pA) refl
 --   (symElω' (inj akf) (symSetω' (inj akf) pA) refl refl pA h)
 --   h