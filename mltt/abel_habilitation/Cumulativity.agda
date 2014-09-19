module Cumulativity where
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

module IrrLvlF  (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
                (n : ℕ) (anf : ∀ {j} -> j < n -> Acc j) where
 mutual
  ElIrrLvl : ∀ {A A'} (pAk : A ≈ A' ∈ SetU' (inj akf)) (pAn : A ≈ A' ∈ SetU' (inj anf))
             -> ElU' _ pAk →₂ ElU' _ pAn
  ElIrrLvl (Neu x x₁) (Neu x₂ x₃) p = p
  ElIrrLvl Nat Nat p = p
  ElIrrLvl (Π pA pF) (Π pA₁ pF₁) p = λ p₁ →
   let p₁' = ElIrrLvl' pA pA₁ p₁ in
   App→ (ElIrrLvl (App.rel (pF p₁')) {!App.rel (pF₁ p₁)!}) (p p₁')
  ElIrrLvl (Set* x) (Set* x₁) p = {!!} -- Need that the precise proof of Acc doesn't matter (actually, they're unique, given function extensionality... we could also use a Seq based definition so that we could actually prove it...

  ElIrrLvl' : ∀ {A A'} (pAk : A ≈ A' ∈ SetU' (inj akf)) (pAn : A ≈ A' ∈ SetU' (inj anf))
             -> ElU' _ pAn →₂ ElU' _ pAk
  ElIrrLvl' (Neu x x₁) (Neu x₂ x₃) p = p
  ElIrrLvl' Nat Nat p = p
  ElIrrLvl' (Π pA pF) (Π pA₁ pF₁) p = λ p₁ →
   let p₁' = ElIrrLvl pA pA₁ p₁ in
   {!!}
  ElIrrLvl' (Set* x) (Set* x₁) p = {!!}

module CumulF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
  where
 open IrrF k akf
 
 cumul : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> A ≈ A' ∈ SetU' (inj (suc-acc' akf))
 cumul (Neu x p) = Neu x (≤suc p)
 cumul Nat = Nat
 cumul (Π pA pF) = Π (cumul pA) (λ p →
   let p' = IrrLvlF.ElIrrLvl _ _ _ _ (cumul pA) pA p in
   let q = cumul (App.rel (pF p')) in
   inj _ _ (App.red1 (pF p')) (App.red2 (pF p')) q)
 cumul (Set* x) = Set* (≤suc x)