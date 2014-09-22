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
open import Relation.Binary.PropositionalEquality
open SetF
open import Util
open import ElIrrelevance
open Syn

mutual
 cumul : ∀ {k n} (ak : Acc k) (an : Acc n) -> k ≤ n ->
    SetU' ak →₂ SetU' an
 cumul (inj x) (inj x₁) k≤n (Neu x₂ x₃) = Neu x₂ (≤trans x₃ k≤n)
 cumul (inj x) (inj x₁) k≤n Nat = Nat
 cumul (inj x) (inj x₁) k≤n (Π pA pF) = Π (cumul _ _ k≤n pA) (λ p →
   let p' = elIrrAcc (inj x₁) (inj x) (cumul _ _ k≤n pA) refl refl pA p in
   let q = cumul (inj x) (inj x₁) k≤n (App.rel (pF p')) in
   inj _ _ (App.red1 (pF p')) (App.red2 (pF p')) q)
 cumul (inj x) (inj x₁) k≤n (Set* x₂) = Set* (≤trans x₂ k≤n)

 elIrrAcc : ∀ {k k'} (ak1 : Acc k) (ak2 : Acc k') {A A' B B'}
   (pA1 : A ≈ A' ∈ SetU' ak1) (eq1 : A ≡ B) (eq2 : A' ≡ B') (pA2 : B ≈ B' ∈ SetU' ak2)
   -> ElU' _ pA1 →₂ ElU' _ pA2
 elIrrAcc (inj akf1) (inj akf2) (Neu x₁ x) refl refl (Neu x₂ x₃) p = p
 elIrrAcc (inj akf1) (inj akf2) Nat refl refl Nat p = p
 elIrrAcc (inj akf1) (inj akf2) (Π pA pF) refl refl (Π pA₁ pF₁) p = λ p₁ →
  let p₁' = elIrrAcc (inj akf2) (inj akf1) pA₁ refl refl pA p₁ in
  let r = p p₁' in
  App→ (elIrrAcc (inj akf1) (inj akf2) (App.rel (pF p₁'))
                  (AppDeter3 (pF p₁') (pF₁ p₁))
                  (AppDeter4 (pF p₁') (pF₁ p₁))
                 (App.rel (pF₁ p₁))) r
 elIrrAcc (inj akf1) (inj akf2) (Set* x) refl refl (Set* x₁) p = cumul (akf1 x) (akf2 x₁) ≤refl p