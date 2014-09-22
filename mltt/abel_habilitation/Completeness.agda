module Completeness where
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
open SetF
open import Util
open import ElIrrelevance
open import Typing
open import Sym
open import Transitivity
open Syn
open import ModelProperties
open import Function

-- Copatterns would be useful to do all of this at once, even the record stuff...
mutual
 fundc' : ∀ {Γ} -> Γ ⊢ctx -> ⊨ Γ ctx
 fundc' ⊡ = tt
 fundc' (_,_ x) = fundt' x , {!!}

 fundt' : ∀ {Γ T} -> Γ ⊢ T type -> ⊨ Γ ctx
 fundt' (inj x) = fundc x

 fundc : ∀ {Γ t t' T} -> Γ ⊢ t ≈ t' ∶ T -> ⊨ Γ ctx
 fundc (sym d) = fundc d
 fundc (trans d d₁) = fundc d
 fundc (Nat x) = fundc' x
 fundc (zero x) = fundc' x
 fundc (suc d) = fundc d
 fundc (Set* x) = fundc' x
 fundc (idx x₁ x₂) = fundc' x₁
 fundc _ = {!!}
 -- fundc (rec d d₁ d₂ d₃) = {!!}
 -- fundc (d · d₁) = {!!}
 -- fundc (ƛ d) = {!!}
 -- fundc (Π d d₁) = {!!}
 -- fundc (d [ x ]) = {!!}
 -- fundc (conv d d₁) = {!!}
 -- fundc (sub d x) = {!!}
 -- fundc (funβ d d₁) = {!!}
 -- fundc (funη d) = {!!}
 -- fundc (rec-zero d d₁ d₂) = {!!}
 -- fundc (rec-suc d d₁ d₂ d₃) = {!!}
 -- fundc (sub-id d) = {!!}
 -- fundc (sub-comp d x x₁) = {!!}
 -- fundc (sub-zero x) = {!!}
 -- fundc (sub-suc x d) = {!!}
 -- fundc (sub-Nat x) = {!!}
 -- fundc (sub-Set x) = {!!}
 -- fundc (sub-ƛ x d) = {!!}
 -- fundc (sub-rec d d₁ d₂ d₃ x) = {!!}
 -- fundc (sub-idx-top x) = {!!}
 -- fundc (sub-idx-pop x₁ x₂) = {!!}
 -- fundc (sub-· x d d₁) = {!!}
 -- fundc (sub-Π x d d₁) = {!!}

 fundt : ∀ {Γ t t' T} (d : Γ ⊢ t ≈ t' ∶ T) -> Γ ⊨' T type[ fundc d ]
 fundt (sym d) vρ = fundt d vρ
 fundt (trans d d₁) vρ = fundt d vρ
 fundt (Nat {i} x) vρ = record { red1 = , Set*; red2 = , Set*; rel = suc i , Set* (s≤s ≤refl) }
 fundt (zero x) vρ = record { red1 = , Nat; red2 = , Nat; rel = 0 , Nat }
 fundt _ vρ = {!!}
 -- fundt (suc d) vρ = {!!}
 -- fundt (Set* x) vρ = {!!}
 -- fundt (idx x₁ x₂) vρ = {!!}
 -- fundt (rec d d₁ d₂ d₃) vρ = {!!}
 -- fundt (d · d₁) vρ = {!!}
 -- fundt (ƛ d) vρ = {!!}
 -- fundt (Π d d₁) vρ = {!!}
 -- fundt (d [ x ]) vρ = {!!}
 -- fundt (conv d d₁) vρ = {!!}
 -- fundt (sub d x) vρ = {!!}
 -- fundt (funβ d d₁) vρ = {!!}
 -- fundt (funη d) vρ = {!!}
 -- fundt (rec-zero d d₁ d₂) vρ = {!!}
 -- fundt (rec-suc d d₁ d₂ d₃) vρ = {!!}
 -- fundt (sub-id d) vρ = {!!}
 -- fundt (sub-comp d x x₁) vρ = {!!}
 -- fundt (sub-zero x) vρ = {!!}
 -- fundt (sub-suc x d) vρ = {!!}
 -- fundt (sub-Nat x) vρ = {!!}
 -- fundt (sub-Set x) vρ = {!!}
 -- fundt (sub-ƛ x d) vρ = {!!}
 -- fundt (sub-rec d d₁ d₂ d₃ x) vρ = {!!}
 -- fundt (sub-idx-top x) vρ = {!!}
 -- fundt (sub-idx-pop x₁ x₂) vρ = {!!}
 -- fundt (sub-· x d d₁) vρ = {!!}
 -- fundt (sub-Π x d d₁) vρ = {!!}

 fund : ∀ {Γ t t' T} (d : Γ ⊢ t ≈ t' ∶ T) -> Γ ⊨' t ≈ t' ∶ T [ fundc d , fundt d ]
 fund (sym d) vρ = hsymωt (fundt d (⟦,⟧ctx-sym vρ)) (fundt d vρ) (fund d (⟦,⟧ctx-sym vρ))
 fund (trans d d₁) vρ = {!!}
 fund (Nat x) vρ = {!!}
 fund (zero x) vρ = {!!}
 fund _ vρ = {!!}
 -- fund (suc d) vρ = {!!}
 -- fund (Set* x) vρ = {!!}
 -- fund (idx x₁ x₂) vρ = {!!}
 -- fund (rec d d₁ d₂ d₃) vρ = {!!}
 -- fund (d · d₁) vρ = {!!}
 -- fund (ƛ d) vρ = {!!}
 -- fund (Π d d₁) vρ = {!!}
 -- fund (d [ x ]) vρ = {!!}
 -- fund (conv d d₁) vρ = {!!}
 -- fund (sub d x) vρ = {!!}
 -- fund (funβ d d₁) vρ = {!!}
 -- fund (funη d) vρ = {!!}
 -- fund (rec-zero d d₁ d₂) vρ = {!!}
 -- fund (rec-suc d d₁ d₂ d₃) vρ = {!!}
 -- fund (sub-id d) vρ = {!!}
 -- fund (sub-comp d x x₁) vρ = {!!}
 -- fund (sub-zero x) vρ = {!!}
 -- fund (sub-suc x d) vρ = {!!}
 -- fund (sub-Nat x) vρ = {!!}
 -- fund (sub-Set x) vρ = {!!}
 -- fund (sub-ƛ x d) vρ = {!!}
 -- fund (sub-rec d d₁ d₂ d₃ x) vρ = {!!}
 -- fund (sub-idx-top x) vρ = {!!}
 -- fund (sub-idx-pop x₁ x₂) vρ = {!!}
 -- fund (sub-· x d d₁) vρ = {!!}
 -- fund (sub-Π x d d₁) vρ = {!!}