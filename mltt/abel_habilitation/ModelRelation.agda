module ModelRelation where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding (pred)
open import WfNat
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Model
open import SubsetModel
open SetF
open SetPF

module ForgetF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
 (reflEl< : ∀ {j} (p : j < k) -> ∀ {a} -> a ∈₁ SetU₁' (akf p) -> a ≈ a ∈ SetU' (akf p)) where
 K : Acc k
 K = inj akf
 mutual
  forgetSet1 : ∀ {A A'} -> A ≈ A' ∈ SetU' K  -> A ∈₁ SetU₁' K
  forgetSet1 (Neu x) = Neu (λ n → , proj₁ (proj₂ (x n)))
  forgetSet1 Nat = Nat
  forgetSet1 (Π pA pF) = Π (forgetSet1 pA) (λ p →
   let p' = reflEl (forgetSet1 pA) pA p in
   let q = pF p' in
   inj _ (App.red1 q) (forgetSet1 (App.rel q)))
  forgetSet1 (Set* x) = Set* x

  reflEl : ∀ {A A' a} (pA : A ∈₁ SetU₁' K) (rA : A ≈ A' ∈ SetU' K)
    -> a ∈₁ ElU₁' _ pA -> a ≈ a ∈ ElU' _ rA
  reflEl (Neu x) (Neu x₁) (inj x₂) = inj (λ n → , proj₂ (x₂ n) , proj₂ (x₂ n))
  reflEl Nat Nat zero = zero
  reflEl Nat Nat (suc x) = suc (reflEl Nat Nat x)
  reflEl Nat Nat (neu x) = neu (λ n → , proj₂ (x n) , proj₂ (x n))
  reflEl (Π pA pF) (Π pA₁ pF₁) p = λ p₁ →
   {!!}
  reflEl (Set* x) (Set* x₁) p with ≤uniq x x₁
  reflEl (Set* x) (Set* .x) p | refl = reflEl< x p

