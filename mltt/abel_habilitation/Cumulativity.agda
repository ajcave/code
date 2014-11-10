module Cumulativity where
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
open SetF
open import Util
open Syn

mutual
 cumul : ∀ {k n} (ak : Acc k) (an : Acc n) -> k ≤ n ->
    SetU' ak →₂ SetU' an
 cumul (inj x) (inj x₁) k≤n (Neu x₂ x₃) = Neu x₂ (≤trans x₃ k≤n)
 cumul (inj x) (inj x₁) k≤n Nat = Nat
 cumul (inj x) (inj x₁) k≤n (Π pA pF) = Π (cumul _ _ k≤n pA) (λ p →
   let p' = irrL (inj x₁) (inj x) (cumul _ _ k≤n pA) refl pA p in
   let q = cumul (inj x) (inj x₁) k≤n (App.rel (pF p')) in
   inj (App.red1 (pF p')) (App.red2 (pF p')) q)
 cumul (inj x) (inj x₁) k≤n (Set* x₂) = Set* (≤trans x₂ k≤n)

 -- TODO: Clean this up in the same way hsymEl was cleaned up
 irrL : ∀ {k k'} (ak1 : Acc k) (ak2 : Acc k') {A A' B B'}
   (pA1 : A ≈ A' ∈ SetU' ak1) (eq1 : A ≡ B) (pA2 : B ≈ B' ∈ SetU' ak2)
   -> ElU' pA1 →₂ ElU' pA2
 irrL (inj akf1) (inj akf2) (Neu x₁ x) refl (Neu x₂ x₃) p = p
 irrL (inj akf1) (inj akf2) Nat refl Nat p = p
 irrL (inj akf1) (inj akf2) (Π pA pF) refl (Π pA₁ pF₁) p = λ p₁ →
  let p₁' = irrL (inj akf2) (inj akf1) pA₁ refl pA p₁ in
  let r = p p₁' in
  App→ (irrL (inj akf1) (inj akf2) (App.rel (pF p₁'))
                  (AppDeter3 (pF p₁') (pF₁ p₁))
                 (App.rel (pF₁ p₁))) r
 irrL (inj akf1) (inj akf2) (Set* x) refl  (Set* x₁) p = cumul (akf1 x) (akf2 x₁) ≤refl p

irrLω : ∀ {A A'} (pA1 pA2 : A ≈ A' ∈ Type) -> [ pA1 ] →₂ [ pA2 ]
irrLω (n , pA1) (m , pA2) = irrL _ _ pA1 refl pA2

open import Sym
irrR : ∀ {k n} (K : Acc k) (N : Acc n) {A A' B C}
    (pAB : B ≈ A ∈ SetU' K)
    (eq : A ≡ A')
    (pAC : C ≈ A' ∈ SetU' N)
   -> ElU' pAB →₂ ElU' pAC
irrR K N pAB eq pAC f≈g =
  hsymEl _ _ (symSetω' _ pAC) pAC
  (irrL _ _ (symSetω' _ pAB) eq (symSetω' _ pAC)
  (hsymEl _ _ pAB (symSetω' _ pAB) f≈g))

irrLω' : ∀ {k} {K : Acc k} {A B C}
    (pAB : A ≈ B ∈ SetU' K)
    (pAC : A ≈ C ∈ SetU' K)
   -> ElU' pAB →₂ ElU' pAC
irrLω' {k} {inj ackf} pAB pAC = irrL _ _ pAB refl pAC

irrRω' : ∀ {k} {K : Acc k} {A B C}
    (pAB : B ≈ A ∈ SetU' K)
    (pAC : C ≈ A ∈ SetU' K)
   -> ElU' pAB →₂ ElU' pAC
irrRω' {k} {inj ackf} pAB pAC = irrR _ _ pAB refl pAC

AppIrr : ∀ {A A'} (p q : A ≈ A' ∈ Type) -> App ([ p ]) →₂ App ([ q ])
AppIrr p q (inj red1 red2 rel) = inj red1 red2 (irrLω p q rel)

⟦⟧tp'-irr : ∀ {c1 c2 k} (p q : c1 ≈ c2 ∈ App (SetU k)) -> ⟦ p ⟧tp' →₂ ⟦ q ⟧tp'
⟦⟧tp'-irr p q x = irrL _ _ (App.rel p) (AppDeter3 p q) (App.rel q) x

-- ⟦⟧tp-irr : ∀ {c1 c2} (p q : c1 ≈ c2 ∈ App Type) -> ⟦ p ⟧tp →₂ ⟦ q ⟧tp
-- ⟦⟧tp-irr p q x = irrL _ _ (proj₂ (App.rel p)) (AppDeter3 p q) (proj₂ (App.rel q)) x