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

open Clo

_⋆_ : ∀ {c d} -> (∀ {v} -> c ↘ v -> d ↘ v) -> Red c -> Red d
f ⋆ r = , f (proj₂ r)

com : ∀ {B c1 c2 d1 d2}
 -> (∀ {v} -> c1 ↘ v -> d1 ↘ v) -- Like the CBPV stack proof...
 -> (∀ {v} -> c2 ↘ v -> d2 ↘ v)
 -> c1 ≈ c2 ∈ App B -> d1 ≈ d2 ∈ App B
com F1 F2 x = inj (F1 ⋆ (red1 x)) (F2 ⋆ red2 x) (rel x)

com2 : ∀ {B c1 c2 d1 d2} {f1 f2 : Val -> Val} {C : ∀ {v1 v2} (p : B v1 v2) -> REL}
 -> (∀ {v} -> c1 ↘ v -> d1 ↘ f1 v)
 -> (∀ {v} -> c2 ↘ v -> d2 ↘ f2 v)
 -> (p : c1 ≈ c2 ∈ App B)
 -> (∀ {v1 v2} -> (p : B v1 v2) -> C p (f1 v1) (f2 v2))
 -> d1 ≈ d2 ∈ App (C (rel p))
com2 F1 F2 x F3 = inj' (F1 (rd1 x)) (F2 (rd2 x)) (F3 (rel x))


-- Do something like Applicative for 2-argument version of com?
-- Combine reductions into "product model", so dealing with 2 is as easy as one?
-- Outrageous but Meaninful Coincidences: S and K applicative instance...

Set' : ∀ {γ} k {Γ : ⊨ γ ctx} -> [ Γ ]⊨ Set* k type[ suc k ]
Set' k ρ1≈ρ2 = inj' Set* Set* (Set* (s≤s ≤refl))

Set'' : ∀ {γ} k {Γ : ⊨ γ ctx} -> [ Γ ]⊨ (Set* k) ≈ (Set* k) ∶[ Set' (suc k) ]
Set'' k ρ1≈ρ2 = inj' Set* Set* (Set* (s≤s ≤refl))

-- Alternatively, I could index [ Γ ]⊨ a type[ _ ] by the proof of accessibility...?
in-type : ∀ {γ a1 a2 k} {Γ : ⊨ γ ctx} -> [ Γ ]⊨ a1 ≈ a2 ∶[ Set' k ] -> [ Γ ]⊨ a1 ≈ a2 type[ k ]
in-type d ρ1≈ρ2 = com2 F.id F.id (d ρ1≈ρ2) (cumul _ _ ≤refl)

out-type : ∀ {γ a1 a2 k} {Γ : ⊨ γ ctx} -> [ Γ ]⊨ a1 ≈ a2 type[ k ] -> [ Γ ]⊨ a1 ≈ a2 ∶[ Set' k ]
out-type d ρ1≈ρ2 = com2 F.id F.id (d ρ1≈ρ2) (cumul _ _ ≤refl)

irr : ∀ {γ t s a k} {Γ : ⊨ γ ctx} {A1 A2 : [ Γ ]⊨ a type[ k ]}
 -> [ Γ ]⊨ t ≈ s ∶[ A1 ] 
 -> [ Γ ]⊨ t ≈ s ∶[ A2 ]
irr {A1 = A1} {A2 = A2} d ρ1≈ρ2 = com2 F.id F.id (d ρ1≈ρ2) (⟦⟧tp'-irr (A1 ρ1≈ρ2) (A2 ρ1≈ρ2))

Πs : ∀ {γ1 γ2 a1 a2 b1 b2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} ->
     (A : [ Γ ]⊨ a1 ≈ a2 type[ k ]) -> [ Γ , A ]⊨ b1 ≈ b2 type[ k ]
    -> [ Γ ]⊨ (Π a1 (ƛ b1)) ≈ (Π a2 (ƛ b2)) type[ k ]
Πs A B ρ1≈ρ2 = inj' (Π (rd1 (A ρ1≈ρ2)) ƛ)
                    (Π (rd2 (A ρ1≈ρ2)) ƛ)
     (Π (rel (A ρ1≈ρ2)) (λ p -> com ƛ· ƛ· (B (ρ1≈ρ2 , p))))


-- Would this be easier if I used a fancier definition that computed?
-- It's tricky because reduction still needs to be inverted
Πinv1 : ∀ {γ1 γ2 a1 a2 b1 b2 k} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> [ Γ ]⊨ Π a1 (ƛ b1) ≈ Π a2 (ƛ b2) type[ k ]
 -> [ Γ ]⊨ a1 ≈ a2 type[ k ]
Πinv1 p ρ1≈ρ2 with p ρ1≈ρ2
Πinv1 p ρ1≈ρ2 | inj (._ , Π proj₂ proj₃) (._ , Π proj₄ proj₅) (Π pA pF) = inj (, proj₂) (, proj₄) pA

Πinv2 : ∀ {γ1 γ2 a1 a2 b1 b2 k} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> (d : [ Γ ]⊨ Π a1 (ƛ b1) ≈ Π a2 (ƛ b2) type[ k ])
 -> [ Γ , Πinv1 d ]⊨ b1 ≈ b2 type[ k ] 
Πinv2 p (vρ , x) with p vρ
Πinv2 p (vρ , x) | inj (._ , Π proj₂ ƛ) (._ , Π proj₄ ƛ) (Π pA pF) with pF x
Πinv2 p (vρ , x) | inj (._ , Π proj₂ ƛ) (._ , Π proj₄ ƛ) (Π pA pF) | inj (proj₁ , ƛ· proj₃) (proj₅ , ƛ· proj₆) rel = inj (, proj₃) (, proj₆) rel


fundƛ : ∀ {γ1 γ2 a1 a2 b1 b2 t s k}
  {Γ : ⊨ γ1 ≈ γ2 ctx} {A : [ Γ ]⊨ a1 ≈ a2 type[ k ]} {B : [ Γ , A ]⊨ b1 ≈ b2 type[ k ]}
      -> [ Γ , A ]⊨ t ≈ s ∶h[ B ]
      -> [ Γ ]⊨ (ƛ t) ≈ (ƛ s) ∶h[ Πs A B ]
fundƛ d ρ₁≈ρ₂ = inj (, ƛ) (, ƛ) (λ p → com ƛ· ƛ· (d (ρ₁≈ρ₂ , p)))

-- fundƛ' : ∀ {γ a b t s k} {Γ : ⊨ γ ctx} (pΠAB : [ Γ ]⊨ (Π a (ƛ b)) type[ k ])
--       -> [ Γ , (Πinv1 pΠAB) ]⊨ t ≈ s ∶[ Πinv2 pΠAB ]
--       -> [ Γ ]⊨ (ƛ t) ≈ (ƛ s) ∶[ pΠAB ]
-- fundƛ' pΠab d ρ1≈ρ2 = irr {A1 = Πs (Πinv1 pΠab) (Πinv2 pΠab)} {A2 = pΠab} (fundƛ {A = Πinv1 pΠab} {B = Πinv2 pΠab} d) ρ1≈ρ2

_>_•_ : ∀ {γ1 γ2 δ1 δ2 b1 b2 σ1 σ2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} (Δ : ⊨ δ1 ≈ δ2 ctx) 
 -> [ Δ ]⊨ b1 ≈ b2 type[ k ]
 -> [ Γ ]⊨s σ1 ≈ σ2 ∶[ Δ ]
 -> [ Γ ]⊨ b1 [ σ1 ] ≈ b2 [ σ2 ] type[ k ]
(Δ > B • σ) ρ1≈ρ2 =
 let vσ = σ ρ1≈ρ2 in
 let vb = B (rel vσ) in
 inj' (rd1 vb [ rd1 vσ ])
      (rd2 vb [ rd2 vσ ])
      (rel vb)

fund-, : ∀ {γ1 γ2 δ1 δ2 σ σ' t t' a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} {Δ : ⊨ δ1 ≈ δ2 ctx}
 -> (A : [ Δ ]⊨ a1 ≈ a2 type[ k ])
 -> (dσ : [ Γ ]⊨s σ ≈ σ' ∶[ Δ ])
 -> [ Γ ]⊨ t ≈ t' ∶h[ Δ > A • dσ ]
 -> [ Γ ]⊨s σ , t ≈ σ' , t' ∶[ Δ , A ]
fund-, A dσ dt dρ =
 let vσ = dσ dρ
     vt = dt dρ in
 inj' (rd1 vσ , rd1 vt)
      (rd2 vσ , rd2 vt)
      (rel vσ , rel vt) 

fund-id : ∀ {γ1 γ2} {Γ : ⊨ γ1 ≈ γ2 ctx} -> [ Γ ]⊨s T.id ≈ T.id ∶[ Γ ]
fund-id dρ = inj (, Eval.id) (, Eval.id) dρ
 
_>h_•_ : ∀ {γ1 γ2 a1 a2 b1 b2 t1 t2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} (A : [ Γ ]⊨ a1 ≈ a2 type[ k ]) 
 -> [ Γ , A ]⊨ b1 ≈ b2 type[ k ]
 -> [ Γ ]⊨ t1 ≈ t2 ∶h[ A ]
 -> [ Γ ]⊨ b1 [ T.id , t1 ] ≈ b2 [ T.id , t2 ] type[ k ]
A >h B • t = (_ , A) > B • fund-, A fund-id t

fund-trans : ∀ {γ t1 t2 t3 a k} {Γ : ⊨ γ ctx} (A : [ Γ ]⊨ a type[ k ])
 -> [ Γ ]⊨ t1 ≈ t2 ∶[ A ]
 -> [ Γ ]⊨ t2 ≈ t3 ∶[ A ]
 -> [ Γ ]⊨ t1 ≈ t3 ∶[ A ]
fund-trans A t1≈t2 t2≈t3 ρ1≈ρ2 = {!!}

fund-sym : ∀ {γ t1 t2 a k} {Γ : ⊨ γ ctx} (A : [ Γ ]⊨ a type[ k ])
 -> [ Γ ]⊨ t1 ≈ t2 ∶[ A ]
 -> [ Γ ]⊨ t2 ≈ t1 ∶[ A ]
fund-sym A t1≈t2 ρ1≈ρ2 = {!!}

self : ∀ {γ a t1 t2 k} {Γ : ⊨ γ ctx} (A : [ Γ ]⊨ a type[ k ])
 -> [ Γ ]⊨ t1 ≈ t2 ∶[ A ]
 -> [ Γ ]⊨ t1 ≈ t1 ∶[ A ]
self A t1≈t2 = fund-trans A t1≈t2 (fund-sym A t1≈t2)


-- TODO: Could I factor out part of this? Environment plays no role here
-- What about just doing ds ρ1≈ρ2 and then using com?
-- Heterogeneous formulation makes this statement and proof simpler
fund·h : ∀ {γ1 γ2 t1 t2 s1 s2 a1 a2 b1 b2 k}
 {Γ : ⊨ γ1 ≈ γ2 ctx} {A : [ Γ ]⊨ a1 ≈ a2 type[ k ]} {B : [ Γ , A ]⊨ b1 ≈ b2 type[ k ]}
     ->       [ Γ ]⊨ t1 ≈ t2 ∶h[ Πs A B ]
     -> (ds : [ Γ ]⊨ s1 ≈ s2 ∶h[ A ])
     ->       [ Γ ]⊨ t1 · s1 ≈ t2 · s2 ∶h[ A >h B • ds ]
fund·h dt ds ρ1≈ρ2 =
 let vs = ds ρ1≈ρ2 in
 let vt = dt ρ1≈ρ2 in
 let vr = rel vt (rel vs) in
 inj' ((rd1 vt · rd1 vs) (rd1 vr))
      ((rd2 vt · rd2 vs) (rd2 vr))
      (rel vr)
-- TODO: Is it better to flatten the "App" structure?
-- What about building some more convenient operators on Red?

fundβ : ∀ {γ1 γ2 t1 t2 s1 s2 a1 a2 b1 b2 k}
 {Γ : ⊨ γ1 ≈ γ2 ctx} {A : [ Γ ]⊨ a1 ≈ a2 type[ k ]} {B : [ Γ , A ]⊨ b1 ≈ b2 type[ k ]}
 -> [ Γ , A ]⊨ t1 ≈ t2 ∶h[ B ]
 -> (ds : [ Γ ]⊨ s1 ≈ s2 ∶h[ A ])
 -> [ Γ ]⊨ (ƛ t1) · s1 ≈ (t2 [ T.id , s2 ]) ∶h[ A >h B • ds ]
fundβ dt ds ρ1≈ρ2 =
 let vs = ds ρ1≈ρ2 in
 let vt = dt (ρ1≈ρ2 , (rel vs)) in
 inj' ((ƛ · rd1 vs) (ƛ· (rd1 vt)))
      (rd2 vt [ Eval.id , rd2 vs ])
      (rel vt)

fundη : ∀ {γ1 γ2 t1 t2 a1 a2 b1 b2 k}
 {Γ : ⊨ γ1 ≈ γ2 ctx} {A : [ Γ ]⊨ a1 ≈ a2 type[ k ]} {B : [ Γ , A ]⊨ b1 ≈ b2 type[ k ]}
 -> [ Γ ]⊨ t1 ≈ t2 ∶h[ Πs A B ]
 -> [ Γ ]⊨ t1 ≈ (ƛ (t2 [ ↑ ] · idx 0)) ∶h[ Πs A B ]
fundη dt ρ1≈ρ2 =
 let vt = dt ρ1≈ρ2 in
 inj (red1 vt)
     (, ƛ)
     (λ p → let q = rel vt p in
       inj' (rd1 q)
            (ƛ· ((((rd2 vt) [ ↑ ]) · (idx top)) (rd2 q)))
            (rel q))

fund-subƛ : ∀ {γ1 γ2 t1 t2 a1 a2 b1 b2 σ1 σ2 δ1 δ2 k}
 {Γ : ⊨ γ1 ≈ γ2 ctx} {Δ : ⊨ δ1 ≈ δ2 ctx} {A : [ Δ ]⊨ a1 ≈ a2 type[ k ]} {B : [ Δ , A ]⊨ b1 ≈ b2 type[ k ]}
 -> (dσ : [ Γ ]⊨s σ1 ≈ σ2 ∶[ Δ ])
 -> [ Δ , A ]⊨ t1 ≈ t2 ∶h[ B ]
 -> [ Γ ]⊨ (ƛ t1) [ σ1 ] ≈ ƛ (t2 [ σ2 [ ↑ ] , idx 0 ]) ∶h[ Δ > Πs A B • dσ ]
fund-subƛ dσ dt dρ = 
 let vσ = dσ dρ in
 inj (, ƛ [ rd1 vσ ])
     (, ƛ)
     (λ p → let vt = dt (rel vσ , p) in
        inj' (ƛ· (rd1 vt))
             (ƛ· (rd2 vt [ ↑ [ rd2 vσ ] , idx top ]))
             (rel vt))

Nats : ∀ {γ} k {Γ : ⊨ γ ctx} -> [ Γ ]⊨ Nat type[ k ]
Nats k ρ1≈ρ2 = inj (, Nat) (, Nat) Nat

fund-suc' : ∀ {γ t s k} {Γ : ⊨ γ ctx} 
 -> [ Γ ]⊨ t ≈ s ∶[ Nats k ]
 -> [ Γ ]⊨ suc t ≈ suc s ∶[ Nats k ] 
fund-suc' d ρ1≈ρ2 = com2 suc suc (d ρ1≈ρ2) suc
     

-- inversion lemma for proofs [ Γ ]⊨ (Π a (ƛ b)) type[ k ] ?