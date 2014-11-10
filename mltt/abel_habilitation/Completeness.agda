{-# OPTIONS --copatterns #-}
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
open import ModelProperties
open import Function as F
open import Relation.Binary.PropositionalEquality hiding ([_]; sym; trans)
open import Cumulativity

_⋆_ : ∀ {c d} -> (∀ {v} -> c ↘ v -> d ↘ v) -> Red c -> Red d
f ⋆ r = , f (proj₂ r)

com : ∀ {B c1 c2 d1 d2}
 -> (∀ {v} -> c1 ↘ v -> d1 ↘ v) -- Like the CBPV stack proof...
 -> (∀ {v} -> c2 ↘ v -> d2 ↘ v)
 -> c1 ≈ c2 ∈ App B -> d1 ≈ d2 ∈ App B
com F1 F2 x = inj (F1 ⋆ (App.red1 x)) (F2 ⋆ App.red2 x) (App.rel x)

com2 : ∀ {B c1 c2 d1 d2} {f1 f2 : Val -> Val} {C : ∀ {v1 v2} (p : B v1 v2) -> REL}
 -> (∀ {v} -> c1 ↘ v -> d1 ↘ f1 v)
 -> (∀ {v} -> c2 ↘ v -> d2 ↘ f2 v)
 -> (p : c1 ≈ c2 ∈ App B)
 -> (∀ {v1 v2} -> (p : B v1 v2) -> C p (f1 v1) (f2 v2))
 -> d1 ≈ d2 ∈ App (C (App.rel p))
com2 F1 F2 x F3 = inj (, F1 (proj₂ (App.red1 x))) (, F2 (proj₂ (App.red2 x))) (F3 (App.rel x))


-- Do something like Applicative for 2-argument version of com?
-- Combine reductions into "product model", so dealing with 2 is as easy as one?
-- Outrageous but Meaninful Coincidences: S and K applicative instance...

-- Πs1 : ∀ {γ a b k} {Γ : ⊨ γ ctx} {ρ₁ ρ₂} (ρ₁≈ρ₂ : ρ₁ ≈ ρ₂ ∈ ⟦ Γ ⟧ctx)
--  -> (A : ⟦ a ⟧ ρ₁ ≈ ⟦ a ⟧ ρ₂ ∈ App (SetU k))
--  -> (∀ {a₁ a₂} -> a₁ ≈ a₂ ∈ ElU _ (App.rel A) -> ⟦ b ⟧ (ρ₁ , a₁) ≈ ⟦ b ⟧ (ρ₂ , a₂) ∈ App (SetU k))
--  -> ⟦ Π a (ƛ b) ⟧ ρ₁ ≈ ⟦ Π a (ƛ b) ⟧ ρ₂ ∈ App (SetU k)
-- Πs1 ρ₁≈ρ₂ A B = inj (, Π (proj₂ (App.red1 A)) ƛ) (, Π (proj₂ (App.red2 A)) ƛ)
--  (Π (App.rel A) (λ p → com ƛ· ƛ· (B p)))

Set' : ∀ {γ} k {Γ : ⊨ γ ctx} -> [ Γ ]⊨ Set* k type[ suc k ]
Set' k ρ1≈ρ2 = inj (, Set*) (, Set*) (Set* (s≤s ≤refl))

Set'' : ∀ {γ} k {Γ : ⊨ γ ctx} -> [ Γ ]⊨ (Set* k) ≈ (Set* k) ∶[ Set' (suc k) ]
Set'' k ρ1≈ρ2 = inj (, Set*) (, Set*) (Set* (s≤s ≤refl))

-- Alternatively, I could index [ Γ ]⊨ a type[ _ ] by the proof of accessibility...?
in-type : ∀ {γ a k} {Γ : ⊨ γ ctx} -> [ Γ ]⊨ a ≈ a ∶[ Set' k ] -> [ Γ ]⊨ a type[ k ]
in-type d ρ1≈ρ2 = com2 F.id F.id (d ρ1≈ρ2) (cumul _ _ ≤refl)

out-type : ∀ {γ a k} {Γ : ⊨ γ ctx} -> [ Γ ]⊨ a type[ k ] -> [ Γ ]⊨ a ≈ a ∶[ Set' k ]
out-type d ρ1≈ρ2 = com2 F.id F.id (d ρ1≈ρ2) (cumul _ _ ≤refl)

irr : ∀ {γ t s a k} {Γ : ⊨ γ ctx} {A1 A2 : [ Γ ]⊨ a type[ k ]}
 -> [ Γ ]⊨ t ≈ s ∶[ A1 ] 
 -> [ Γ ]⊨ t ≈ s ∶[ A2 ]
irr {A1 = A1} {A2 = A2} d ρ1≈ρ2 = com2 F.id F.id (d ρ1≈ρ2) (⟦⟧tp'-irr (A1 ρ1≈ρ2) (A2 ρ1≈ρ2))

Πs : ∀ {γ a b k} {Γ : ⊨ γ ctx} ->
     (A : [ Γ ]⊨ a type[ k ]) -> [ Γ , A ]⊨ b type[ k ] -> [ Γ ]⊨ (Π a (ƛ b)) type[ k ]
Πs A B ρ1≈ρ2 = inj (, (Π (proj₂ (App.red1 (A ρ1≈ρ2))) ƛ))
                   (, (Π (proj₂ (App.red2 (A ρ1≈ρ2))) ƛ))
     (Π (App.rel (A ρ1≈ρ2)) (λ p -> com ƛ· ƛ· (B (ρ1≈ρ2 , p))))

-- Πs' : ∀ {γ a b k} {Γ : ⊨ γ ctx} ->
--      (A : [ Γ ]⊨ a type[ k ]) -> [ Γ , A ]⊨ b type[ k ] -> [ Γ ]⊨ (Π a (ƛ b)) type[ k ]
-- Πs' A B ρ1≈ρ2 = com2 (λ p -> Π p ƛ) (λ p -> Π p ƛ) (A ρ1≈ρ2)
--   (λ x → Π x (λ p → com2 ƛ· ƛ· (B (ρ1≈ρ2 , {!!})) {!!}))
--   -- inj (, (Π (proj₂ (App.red1 (A ρ1≈ρ2))) ƛ))
--   --                  (, (Π (proj₂ (App.red2 (A ρ1≈ρ2))) ƛ))
--   --    (Π (App.rel (A ρ1≈ρ2)) (λ p -> com ƛ· ƛ· (B (ρ1≈ρ2 , p))))

fundƛ : ∀ {γ a b t s k} {Γ : ⊨ γ ctx} {A : [ Γ ]⊨ a type[ k ]} {B : [ Γ , A ]⊨ b type[ k ]}
      -> [ Γ , A ]⊨ t ≈ s ∶[ B ]
      -> [ Γ ]⊨ (ƛ t) ≈ (ƛ s) ∶[ Πs A B ]
fundƛ d ρ₁≈ρ₂ = inj (, ƛ) (, ƛ) (λ p → com ƛ· ƛ· (d (ρ₁≈ρ₂ , p)))

Nats : ∀ {γ} k {Γ : ⊨ γ ctx} -> [ Γ ]⊨ Nat type[ k ]
Nats k ρ1≈ρ2 = inj (, Nat) (, Nat) Nat

-- fund-suc : ∀ {γ t s k} {Γ : ⊨ γ ctx} 
--  -> [ Γ ]⊨ t ≈ s ∶[ Nats k ]
--  -> [ Γ ]⊨ suc t ≈ suc s ∶[ Nats k ] 
-- fund-suc d ρ1≈ρ2 =
--  inj
--   (, suc (proj₂ (App.red1 (d ρ1≈ρ2))))
--   (, suc (proj₂ (App.red2 (d ρ1≈ρ2))))
--   (suc (App.rel (d ρ1≈ρ2)))

fund-suc' : ∀ {γ t s k} {Γ : ⊨ γ ctx} 
 -> [ Γ ]⊨ t ≈ s ∶[ Nats k ]
 -> [ Γ ]⊨ suc t ≈ suc s ∶[ Nats k ] 
fund-suc' d ρ1≈ρ2 = com2 suc suc (d ρ1≈ρ2) suc
     

-- inversion lemma for proofs [ Γ ]⊨ (Π a (ƛ b)) type[ k ] ?