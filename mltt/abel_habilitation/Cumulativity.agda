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

open Clo
mutual
 cumul : ∀ {k n} (ak : Acc k) (an : Acc n) -> k ≤ n ->
    SetU' ak →₂ SetU' an
 cumul (inj x) (inj x₁) k≤n (Neu x₂ x₃) = Neu x₂ (≤trans x₃ k≤n)
 cumul (inj x) (inj x₁) k≤n Nat = Nat
 cumul (inj x) (inj x₁) k≤n (Π pA pF) = Π (cumul _ _ k≤n pA) (λ p →
   let p' = irrL (inj x₁) (inj x) (cumul _ _ k≤n pA) refl pA p in
   let q = cumul (inj x) (inj x₁) k≤n (rel (pF p')) in
   inj (red1 (pF p')) (red2 (pF p')) q)
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
  App→ (irrL (inj akf1) (inj akf2) (rel (pF p₁'))
                  (evala-deter (rd1 (pF p₁')) (rd1 (pF₁ p₁)))
                 (rel (pF₁ p₁))) r
 irrL (inj akf1) (inj akf2) (Set* x) refl  (Set* x₁) p = cumul (akf1 x) (akf2 x₁) ≤refl p

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

irrLF' : ∀ {α β : Set} {k} {K : Acc k} {A F F'} {r : β × α -> Val -> Set} (d : Deterministic r)
    (pF : F ≈ F' ∈ (A ⇒[ r ] SetU' K))
 -> ∀ {a a' a''} (p : a ≈ a' ∈ A) (p' : a ≈ a'' ∈ A) -> (ElU' (rel (pF p))) →₂ (ElU' (rel (pF p')))
irrLF' d pF p p' x = irrL _ _ (rel (pF p)) (d (rd1 (pF p)) (rd1 (pF p'))) (rel (pF p')) x

irrLF : ∀ {k} {K : Acc k} {A F F'}
    (pF : F ≈ F' ∈ (A ⇒R SetU' K))
 -> ∀ {a a' a''} (p : a ≈ a' ∈ A) (p' : a ≈ a'' ∈ A) -> (ElU' (rel (pF p))) →₂ (ElU' (rel (pF p')))
irrLF = irrLF' evala-deter

irrRF' : ∀ {α β : Set} {k} {K : Acc k} {A F F'} {r : β × α -> Val -> Set} (d : Deterministic r)
    (pF : F ≈ F' ∈ (A ⇒[ r ] SetU' K))
 -> ∀ {a a' a''} (p : a' ≈ a ∈ A) (p' : a'' ≈ a ∈ A) -> (ElU' (rel (pF p))) →₂ (ElU' (rel (pF p')))
irrRF' d pF p p' x = irrR _ _ (rel (pF p)) (d (rd2 (pF p)) (rd2 (pF p'))) (rel (pF p')) x

irrLRF' :  ∀ {α β : Set} {k} {K : Acc k} {A F F'} {r : β × α -> Val -> Set} (d : Deterministic r)
    (pF : F ≈ F' ∈ (A ⇒[ r ] SetU' K))
 -> ∀ {a1 a2 b1 b2} {p : a1 ≈ a2 ∈ A} {p' : b1 ≈ b2 ∈ A}
 -> a1 ≈ b2 ∈ A
 -> (ElU' (rel (pF p))) →₂ (ElU' (rel (pF p')))
irrLRF' d pF q x =
 let q0 = irrLF' d pF _ q x
     q1 = irrRF' d pF q _ q0
 in q1

irrRF : ∀ {k} {K : Acc k} {A F F'}
    (pF : F ≈ F' ∈ (A ⇒R SetU' K))
 -> ∀ {a a' a''} (p : a' ≈ a ∈ A) (p' : a'' ≈ a ∈ A) -> (ElU' (rel (pF p))) →₂ (ElU' (rel (pF p')))
irrRF = irrRF' evala-deter

irrRω' : ∀ {k} {K : Acc k} {A B C}
    (pAB : B ≈ A ∈ SetU' K)
    (pAC : C ≈ A ∈ SetU' K)
   -> ElU' pAB →₂ ElU' pAC
irrRω' {k} {inj ackf} pAB pAC = irrR _ _ pAB refl pAC

⟦⟧tp'-irr : ∀ {c1 c2 k} (p q : c1 ≈ c2 ∈ App (SetU k)) -> ⟦ p ⟧tp →₂ ⟦ q ⟧tp
⟦⟧tp'-irr p q x = irrL _ _ (rel p) (evala-deter (rd1 p) (rd1 q)) (rel q) x

