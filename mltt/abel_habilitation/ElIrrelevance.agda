module ElIrrelevance where
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
open Syn
open import Cumulativity

-- module IrrF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
--    where
--   K : Acc k
--   K = inj akf
-- mutual  
--   irrL : ∀ {k n} (K : Acc k) (N : Acc n) {A A' B C}
--     (pAB : A ≈ B ∈ SetU' K)
--     (eq : A ≡ A')
--     (pAC : A' ≈ C ∈ SetU' N)
--    -> ElU' pAB →₂ ElU' pAC
--   irrL (inj akf) (inj anf) (Neu _ y) refl (Neu _ y') ab = ab
--   irrL (inj akf) (inj anf) Nat refl Nat ab = ab
--   irrL (inj akf) (inj anf) (Π pA pF) refl (Π pA' pF') ab = λ p' →
--    let p = irrL (inj anf) (inj akf) pA' refl pA p' in
--    let q = irrL (inj akf) (inj anf) (App.rel (pF p)) (AppDeter3 (pF p) (pF' p')) (App.rel (pF' p')) (App.rel (ab p)) in
--    inj (App.red1 (ab p)) (App.red2 (ab p)) q
--   irrL (inj akf) (inj anf) (Set* y) refl (Set* y') ab = cumul (akf y) (anf y') ≤refl ab 

--   irrR : ∀ {k n} (K : Acc k) (N : Acc n) {A A' B C}
--     (pAB : B ≈ A ∈ SetU' K)
--     (eq : A ≡ A')
--     (pAC : C ≈ A' ∈ SetU' N)
--    -> ElU' pAB →₂ ElU' pAC
--   irrR (inj akf) (inj anf) (Neu _ y) refl (Neu _ y') ab = ab
--   irrR (inj akf) (inj anf) Nat refl Nat ab = ab
--   irrR (inj akf) (inj anf) (Π pA pF) refl (Π pA' pF') ab = λ p' →
--    let p = irrR (inj anf) (inj akf) pA' refl pA p' in
--    let q = irrR (inj akf) (inj anf) (App.rel (pF p)) (AppDeter4 (pF p) (pF' p')) (App.rel (pF' p')) (App.rel (ab p)) in
--    inj (App.red1 (ab p)) (App.red2 (ab p)) q
--   irrR (inj akf) (inj anf) (Set* y) refl (Set* y') ab = cumul (akf y) (anf y') ≤refl ab

-- irrLω' : ∀ {k} {K : Acc k} {A B C}
--     (pAB : A ≈ B ∈ SetU' K)
--     (pAC : A ≈ C ∈ SetU' K)
--    -> ElU' pAB →₂ ElU' pAC
-- irrLω' {k} {inj ackf} pAB pAC = irrL _ _ pAB refl pAC

-- irrRω' : ∀ {k} {K : Acc k} {A B C}
--     (pAB : B ≈ A ∈ SetU' K)
--     (pAC : C ≈ A ∈ SetU' K)
--    -> ElU' pAB →₂ ElU' pAC
-- irrRω' {k} {inj ackf} pAB pAC = irrR _ _ pAB refl pAC

-- irrLω : ∀ {k} {A B C}
--     (pAB : A ≈ B ∈ SetU k)
--     (pAC : A ≈ C ∈ SetU k)
--    -> ElU k pAB →₂ ElU k pAC
-- irrLω = irrLω' {_} {nat-acc}

-- irrRω : ∀ {k} {A B C}
--     (pAB : B ≈ A ∈ SetU k)
--     (pAC : C ≈ A ∈ SetU k)
--    -> ElU k pAB →₂ ElU k pAC
-- irrRω = irrRω' {_} {nat-acc}