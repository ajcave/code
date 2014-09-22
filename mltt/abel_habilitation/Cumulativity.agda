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

module CumulF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
  where
 open IrrF k akf
 
 cumul : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> A ≈ A' ∈ SetU' (inj (suc-acc' akf))
 cumul (Neu x p) = Neu x (≤suc p)
 cumul Nat = Nat
 cumul (Π pA pF) = Π (cumul pA) (λ p →
   let p' = elIrrAcc _ _ (cumul pA) refl refl pA p in
   let q = cumul (App.rel (pF p')) in
   inj _ _ (App.red1 (pF p')) (App.red2 (pF p')) q)
 cumul (Set* x) = Set* (≤suc x)