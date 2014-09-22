module ElIrrelevance where
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
open Syn

mutual
 irrAcc : ∀ {k} (ak1 ak2 : Acc k)
  -> SetU' ak1 →₂ SetU' ak2
 irrAcc (inj akf1) (inj akf2) (Neu x x₁) = Neu x x₁
 irrAcc (inj akf1) (inj akf2) Nat = Nat
 irrAcc (inj akf1) (inj akf2) (Π pA pF) = Π (irrAcc (inj akf1) (inj akf2) pA) (λ p →
   let p' = elIrrAcc (inj akf2) (inj akf1) (irrAcc _ _ pA) refl refl pA p in
   inj _ _ (App.red1 (pF p')) (App.red2 (pF p')) (irrAcc (inj akf1) (inj akf2) (App.rel (pF p'))))
 irrAcc (inj akf1) (inj akf2) (Set* x) = Set* x

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
 elIrrAcc (inj akf1) (inj akf2) (Set* x) refl refl (Set* x₁) p = irrAcc (akf1 x) (akf2 x₁) p

module IrrF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
   where
  K : Acc k
  K = inj akf
  
  irrL : ∀ {A A' B C}
    (pAB : A ≈ B ∈ SetU' K)
    (eq : A ≡ A')
    (pAC : A' ≈ C ∈ SetU' K)
   -> ElU' K pAB →₂ ElU' K pAC
  irrL (Neu _ y) refl (Neu _ y') ab = ab
  irrL Nat refl Nat ab = ab
  irrL (Π pA pF) refl (Π pA' pF') ab = λ p' →
   let p = irrL pA' refl pA p' in
   let q = irrL (App.rel (pF p)) (AppDeter3 (pF p) (pF' p')) (App.rel (pF' p')) (App.rel (ab p)) in
   inj _ _ (App.red1 (ab p)) (App.red2 (ab p)) q
  irrL (Set* y) refl (Set* y') ab with ≤uniq y y'
  irrL (Set* .y') refl (Set* y') ab | refl = ab

  irrR : ∀ {A A' B C}
    (pAB : B ≈ A ∈ SetU' K)
    (eq : A ≡ A')
    (pAC : C ≈ A' ∈ SetU' K)
   -> ElU' K pAB →₂ ElU' K pAC
  irrR (Neu _ y) refl (Neu _ y') ab = ab
  irrR Nat refl Nat ab = ab
  irrR (Π pA pF) refl (Π pA' pF') ab = λ p' →
   let p = irrR pA' refl pA p' in
   let q = irrR (App.rel (pF p)) (AppDeter4 (pF p) (pF' p')) (App.rel (pF' p')) (App.rel (ab p)) in
   inj _ _ (App.red1 (ab p)) (App.red2 (ab p)) q
  irrR (Set* y) refl (Set* y') ab with ≤uniq y y'
  irrR (Set* .y') refl (Set* y') ab | refl = ab

irrLω' : ∀ {k} {K : Acc k} {A B C}
    (pAB : A ≈ B ∈ SetU' K)
    (pAC : A ≈ C ∈ SetU' K)
   -> ElU' K pAB →₂ ElU' K pAC
irrLω' {k} {inj ackf} pAB pAC = IrrF.irrL k ackf pAB refl pAC

irrRω' : ∀ {k} {K : Acc k} {A B C}
    (pAB : B ≈ A ∈ SetU' K)
    (pAC : C ≈ A ∈ SetU' K)
   -> ElU' K pAB →₂ ElU' K pAC
irrRω' {k} {inj ackf} pAB pAC = IrrF.irrR k ackf pAB refl pAC

irrLω : ∀ {k} {A B C}
    (pAB : A ≈ B ∈ SetU k)
    (pAC : A ≈ C ∈ SetU k)
   -> ElU k pAB →₂ ElU k pAC
irrLω = irrLω' {_} {nat-acc}

irrRω : ∀ {k} {A B C}
    (pAB : B ≈ A ∈ SetU k)
    (pAC : C ≈ A ∈ SetU k)
   -> ElU k pAB →₂ ElU k pAC
irrRω = irrRω' {_} {nat-acc}