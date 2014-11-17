{-# OPTIONS --copatterns #-}
module Completeness where
open import Syntax
open import SyntaxTm as T
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


-- Would this be easier if I used a fancier definition that computed?
-- It's tricky because reduction still needs to be inverted
Πinv1 : ∀ {γ a b k} {Γ : ⊨ γ ctx} -> [ Γ ]⊨ (Π a (ƛ b)) type[ k ] -> [ Γ ]⊨ a type[ k ]
Πinv1 p ρ1≈ρ2 with p ρ1≈ρ2
Πinv1 p ρ1≈ρ2 | inj (._ , Π proj₂ proj₃) (._ , Π proj₄ proj₅) (Π pA pF) = inj (, proj₂) (, proj₄) pA

Πinv2 : ∀ {γ a b k} {Γ : ⊨ γ ctx} -> (d : [ Γ ]⊨ (Π a (ƛ b)) type[ k ]) -> [ Γ , Πinv1 d ]⊨ b type[ k ] 
Πinv2 p (vρ , x) with p vρ
Πinv2 p (vρ , x) | inj (._ , Π proj₂ ƛ) (._ , Π proj₄ ƛ) (Π pA pF) with pF x
Πinv2 p (vρ , x) | inj (._ , Π proj₂ ƛ) (._ , Π proj₄ ƛ) (Π pA pF) | inj (proj₁ , ƛ· proj₃) (proj₅ , ƛ· proj₆) rel = inj (, proj₃) (, proj₆) rel

fundƛ : ∀ {γ a b t s k} {Γ : ⊨ γ ctx} {A : [ Γ ]⊨ a type[ k ]} {B : [ Γ , A ]⊨ b type[ k ]}
      -> [ Γ , A ]⊨ t ≈ s ∶[ B ]
      -> [ Γ ]⊨ (ƛ t) ≈ (ƛ s) ∶[ Πs A B ]
fundƛ d ρ₁≈ρ₂ = inj (, ƛ) (, ƛ) (λ p → com ƛ· ƛ· (d (ρ₁≈ρ₂ , p)))

fundƛ' : ∀ {γ a b t s k} {Γ : ⊨ γ ctx} (pΠAB : [ Γ ]⊨ (Π a (ƛ b)) type[ k ])
      -> [ Γ , (Πinv1 pΠAB) ]⊨ t ≈ s ∶[ Πinv2 pΠAB ]
      -> [ Γ ]⊨ (ƛ t) ≈ (ƛ s) ∶[ pΠAB ]
fundƛ' pΠab d ρ1≈ρ2 = irr {A1 = Πs (Πinv1 pΠab) (Πinv2 pΠab)} {A2 = pΠab} (fundƛ {A = Πinv1 pΠab} {B = Πinv2 pΠab} d) ρ1≈ρ2

_>_•_ : ∀ {γ a b t k} {Γ : ⊨ γ ctx} (A : [ Γ ]⊨ a type[ k ]) 
 -> [ Γ , A ]⊨ b type[ k ]
 -> [ Γ ]⊨ t ∶[ A ]
 -> [ Γ ]⊨ (b [ T.id , t ]) type[ k ]
(A > B • t) ρ1≈ρ2 with B (ρ1≈ρ2 , (App.rel (t ρ1≈ρ2)))
_>_•_ A B t ρ1≈ρ2 | inj (_ , red1) (_ , red2) rel =
 inj (, red1 [ Eval.id , (proj₂ (App.red1 (t ρ1≈ρ2))) ])
     (, red2 [ Eval.id , (proj₂ (App.red2 (t ρ1≈ρ2))) ])
     rel

fund· : ∀ {γ t1 t2 s1 s2 a b k} {Γ : ⊨ γ ctx} {A : [ Γ ]⊨ a type[ k ]} {B : [ Γ , A ]⊨ b type[ k ]}
     ->       [ Γ ]⊨ t1 ≈ t2 ∶[ Πs A B ]
     -> (ds : [ Γ ]⊨ s1 ≈ s2 ∶[ A ])
     ->       [ Γ ]⊨ t1 · s1 ≈ t2 · s2 ∶[ A > B • {!!} ]
fund· dt ds ρ1≈ρ2 = {!!}

Nats : ∀ {γ} k {Γ : ⊨ γ ctx} -> [ Γ ]⊨ Nat type[ k ]
Nats k ρ1≈ρ2 = inj (, Nat) (, Nat) Nat

fund-suc' : ∀ {γ t s k} {Γ : ⊨ γ ctx} 
 -> [ Γ ]⊨ t ≈ s ∶[ Nats k ]
 -> [ Γ ]⊨ suc t ≈ suc s ∶[ Nats k ] 
fund-suc' d ρ1≈ρ2 = com2 suc suc (d ρ1≈ρ2) suc
     

-- inversion lemma for proofs [ Γ ]⊨ (Π a (ƛ b)) type[ k ] ?