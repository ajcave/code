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
 fundc (trans d d₁) = fundc d₁
 fundc (Nat x) = fundc' x
 fundc (zero x) = fundc' x
 fundc (suc d) = fundc d
 fundc (Set* x) = fundc' x
 fundc (idx x₁ x₂) = fundc' x₁
 fundc (rec d d₁ d₂ d₃) = {!!}
 fundc (d · d₁) = fundc d
 fundc (ƛ d) = proj₁ (fundc d)
 fundc (Π d d₁) = fundc d
 fundc (d [ x ]) = {!!}
 fundc (conv d d₁) = fundc d
 fundc (sub d x) = fundc d
 fundc (funβ d d₁) = fundc d₁
 fundc (funη d) = fundc d
 fundc _ = {!!}
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

 fundlvl : ∀ {Γ t t' T} (d : Γ ⊢ t ≈ t' ∶ T) -> ℕ
 fundlvl (sym d) = fundlvl d
 fundlvl (trans d d₁) = fundlvl d₁
 fundlvl (Nat {i} x) = suc i
 fundlvl (zero x) = 0
 fundlvl (suc d) = 0
 fundlvl (Set* {i} x) = suc (suc i)
 fundlvl (idx x₁ x₂) = {!!}
 fundlvl (rec d d₁ d₂ d₃) = {!!}
 fundlvl (d · d₁) = {!!}
 fundlvl (ƛ d) = {!!}
 fundlvl (Π d d₁) = {!!}
 fundlvl (d [ x ]) = {!!}
 fundlvl (conv d d₁) = {!!}
 fundlvl (sub d x) = {!!}
 fundlvl (funβ d d₁) = {!!}
 fundlvl (funη d) = {!!}
 fundlvl _ = {!!}
 -- fundlvl (rec-zero d d₁ d₂) = {!!}
 -- fundlvl (rec-suc d d₁ d₂ d₃) = {!!}
 -- fundlvl (sub-id d) = {!!}
 -- fundlvl (sub-comp d x x₁) = {!!}
 -- fundlvl (sub-zero x) = {!!}
 -- fundlvl (sub-suc x d) = {!!}
 -- fundlvl (sub-Nat x) = {!!}
 -- fundlvl (sub-Set x) = {!!}
 -- fundlvl (sub-ƛ x d) = {!!}
 -- fundlvl (sub-rec d d₁ d₂ d₃ x) = {!!}
 -- fundlvl (sub-idx-top x) = {!!}
 -- fundlvl (sub-idx-pop x₁ x₂) = {!!}
 -- fundlvl (sub-· x d d₁) = {!!}
 -- fundlvl (sub-Π x d d₁) = {!!}

 fundt : ∀ {Γ t t' T} (d : Γ ⊢ t ≈ t' ∶ T) -> Γ ⊨' T type[ fundc d , fundlvl d ]
 fundt (sym d) vρ = fundt d vρ
 fundt (trans d d₁) vρ = fundt d₁ vρ
 fundt (Nat {i} x) vρ = record { red1 = , Set*; red2 = , Set*; rel = Set* ≤refl }
 fundt (zero x) vρ = record { red1 = , Nat; red2 = , Nat; rel = Nat }
 fundt (suc d) vρ = inj (, Nat) (, Nat) (Nat)
 fundt (Set* {i} x) vρ = inj (, Set*) (, Set*) (Set* ≤refl)
 fundt (idx x₁ x₂) vρ = {!!}
 fundt (rec d d₁ d₂ d₃) vρ = {!!}
 fundt (d · d₁) vρ = {!!}
 fundt (ƛ d) vρ with proj₂ (fundc d) vρ 
 ... | inj (A , red1) (A' , red2) (n , rel) = {!!} --inj (, Π red1 ƛ) (, Π red2 ƛ) (Π rel (λ a≈a' → {!!})) -- TODO: This may not be n! Do I need to mutually extract the level?
 fundt (Π d d₁) vρ = {!!}
 fundt (d [ x ]) vρ = {!!}
 fundt (conv d d₁) vρ = {!!}
 fundt (sub d x) vρ = {!!}
 fundt (funβ d d₁) vρ = {!!}
 fundt (funη d) vρ = {!!}
 fundt _ vρ = {!!}
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

 fund : ∀ {Γ t t' T} (d : Γ ⊢ t ≈ t' ∶ T) -> Γ ⊨' t ≈ t' ∶ T [ (fundc d , (fundlvl d , fundt d)) ]
 fund (sym d) vρ = hsymωt (fundt d (⟦,⟧ctx-sym vρ)) (fundt d vρ) (fund d (⟦,⟧ctx-sym vρ))
 fund (trans d d₁) vρ =
   let vρ' = ⟦,⟧ctx-irr (⟦,⟧ctx-self vρ) in
   htransω' (fundt d vρ') (fundt d₁ vρ) (fundt d₁ vρ) (fund d vρ') (fund d₁ vρ)
 fund (Nat x) vρ = inj (, Nat) (, Nat) Nat
 fund (zero x) vρ = inj (, zero) (, zero) zero
 fund (suc d) vρ with fund d vρ
 fund (suc d) vρ | inj (_ , red1) (_ , red2) rel with fundt d vρ
 fund (suc d) vρ | inj (_ , red1) (_ , red2) rel' | inj (._ , Nat) (._ , Nat) (Nat) = inj (, suc red1) (, suc red2) (suc rel')
 fund (Set* x) vρ = inj (, Set*) (, Set*) (Set* ≤refl)
 fund (idx x₁ x₂) vρ = {!!}
 fund (rec d d₁ d₂ d₃) vρ = {!!}
 fund (d · d₁) vρ = {!!}
 fund (ƛ d) vρ = {!!}
 fund (Π d d₁) vρ = {!!}
 fund (d [ x ]) vρ = {!!}
 fund (conv d d₁) vρ = {!!}
 fund (sub d x) vρ = {!!}
 fund (funβ d d₁) vρ = {!!}
 fund (funη d) vρ = {!!}
 fund _ vρ = {!!}
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