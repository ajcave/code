module Resp where
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
open import Sym

open SetF

_→₂_ : ∀ {A : Set} (P Q : PREL A) -> Set
P →₂ Q = ∀ {a b} -> P a b -> Q a b

-- AppResp : ∀ {f a f' a' B B'} -> B →₂ B' ->
--     (f · a) ≈ (f' · a') ∈ App B
--  -> (f · a) ≈ (f' · a') ∈ App B'
-- AppResp rB x = inj _ _ (App.red1 x) (App.red2 x) (rB (App.rel x))

-- El-resp : ∀ {k} {p : Acc k} {A A'} (pA : A ≈ A' ∈ (SetU' p)) -> ∀ {a1 a2 b1 b2}
--  -> a1 ≡ b1 -> a2 ≡ b2 -> ElU' _ pA a1 a2 -> ElU' _ pA b1 b2
-- El-resp pA refl refl x = x

module Resp (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j) where
 open SymF k akf

 resp : ∀ {A A' B' B}
   (pA : A  ≈ A'  ∈ SetU' (inj akf))
   (h : A ≈ B ∈ SetU' (inj akf))
   (h' : A' ≈ B' ∈ SetU' (inj akf))
   (pB : B ≈ B' ∈ SetU' (inj akf))
  -> (ElU' _ pA) →₂ (ElU' _ pB)
 resp (Neu x) (Neu x₂) (Neu x₁) (Neu x₃) r = r
 resp Nat Nat Nat Nat r = r
 resp (Π pA pF) (Π h h1) (Π h' h1') (Π pB pG) r = λ p →
  let p' : _ ≈ _ ∈ ElU' _ pA
      p' = resp pB (symSetω' (inj akf) h) (symSetω' (inj akf) h') pA p in
  let q : _ ≈ _ ∈ App (ElU' _ (App.rel (pF p')))
      q = r p' in
  inj _ _ (App.red1 q) (App.red2 q)
   (resp (App.rel (pF p')) {!transitivity...!} {!!} (App.rel (pG p)) (App.rel q))
 resp (Set* x) (Set* x₁) (Set* x₂) (Set* x₃) r with ≤uniq x x₃
 resp (Set* x) (Set* x₁) (Set* x₂) (Set* .x) r | refl = r
