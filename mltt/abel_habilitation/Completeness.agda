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
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_]; sym; trans)
open import Cumulativity

-- Copatterns would be useful to do all of this at once, even the record stuff...

 -- fundc' : ∀ {Γ} -> Γ ⊢ctx -> ⊨ Γ ctx
 -- fundc' ⊡ = tt
 -- fundc' (_,_ (inj x)) = fundc x , (λ x₁ → App→ ,_ (lem0 x x₁))

 -- fundt' : ∀ {Γ T} -> Γ ⊢ T type -> ⊨ Γ ctx
 -- fundt' (inj x) = fundc x

 -- -- TODO: This is messy... Some kind of inversion happening here..
 -- lem : ∀ {ρ ρ' i k A} (vT' : ⟦ Set* i ⟧ ρ ≈ ⟦ Set* i ⟧ ρ' ∈ App (SetU k))
 --  -> ⟦ A ⟧ ρ ≈ ⟦ A ⟧ ρ' ∈ App (ElU k (App.rel vT'))
 --  -> i < k × (⟦ A ⟧ ρ ≈ ⟦ A ⟧ ρ' ∈ App (SetU (pred k)))
 -- lem (inj (_ , red1) (_ , red2) rel) p with eval-deter red1 Set* | eval-deter red2 Set*
 -- lem (inj (._ , red1) (._ , red2) (Set* (s≤s x))) p | refl | refl = s≤s x , App→ (λ x₁ → cumul _ _ x x₁) p

 -- fundc : ∀ {Γ t t' T} -> Γ ⊢ t ≈ t' ∶ T -> ⊨ Γ ctx
 -- fundc (sym d) = fundc d
 -- fundc (trans d d₁) = fundc d₁
 -- fundc (Nat x) = fundc' x
 -- fundc (zero x) = fundc' x
 -- fundc (suc d) = fundc d
 -- fundc (Set* x) = fundc' x
 -- fundc (idx x₁ x₂) = fundc' x₁
 -- fundc (rec d d₁ d₂ d₃) = {!!}
 -- fundc (d · d₁) = fundc d
 -- fundc (ƛ d) = proj₁ (fundc d)
 -- fundc (Π d d₁) = fundc d
 -- fundc (d [ x ]) = {!!}
 -- fundc (conv d d₁) = fundc d
 -- fundc (sub d x) = fundc d
 -- fundc (funβ d d₁) = fundc d₁
 -- fundc (funη d) = fundc d
 -- fundc _ = {!!}
 -- -- fundc (rec-zero d d₁ d₂) = {!!}
 -- -- fundc (rec-suc d d₁ d₂ d₃) = {!!}
 -- -- fundc (sub-id d) = {!!}
 -- -- fundc (sub-comp d x x₁) = {!!}
 -- -- fundc (sub-zero x) = {!!}
 -- -- fundc (sub-suc x d) = {!!}
 -- -- fundc (sub-Nat x) = {!!}
 -- -- fundc (sub-Set x) = {!!}
 -- -- fundc (sub-ƛ x d) = {!!}
 -- -- fundc (sub-rec d d₁ d₂ d₃ x) = {!!}
 -- -- fundc (sub-idx-top x) = {!!}
 -- -- fundc (sub-idx-pop x₁ x₂) = {!!}
 -- -- fundc (sub-· x d d₁) = {!!}
 -- -- fundc (sub-Π x d d₁) = {!!}
 
 -- fundlvlv : ∀ {Γ x T} (dc : Γ ⊢ctx) (d : Γ ∋ x ∶ T) -> ℕ
 -- fundlvlv ⊡ ()
 -- fundlvlv (_,_ (inj {i} x)) top = i
 -- fundlvlv (_,_ (inj x)) (pop d) = {!!}

 -- fundlvl : ∀ {Γ t t' T} (d : Γ ⊢ t ≈ t' ∶ T) -> ℕ
 -- fundlvl (sym d) = fundlvl d
 -- fundlvl (trans d d₁) = fundlvl d₁
 -- fundlvl (Nat {i} x) = suc i
 -- fundlvl (zero x) = 0
 -- fundlvl (suc d) = 0
 -- fundlvl (Set* {i} x) = suc (suc i)
 -- fundlvl (idx x₁ x₂) = fundlvlv x₁ x₂
 -- fundlvl (rec d d₁ d₂ d₃) = {!!}
 -- fundlvl (d · d₁) = {!!}
 -- fundlvl (ƛ d) = {!!}
 -- fundlvl (Π d d₁) = {!!}
 -- fundlvl (d [ x ]) = {!!}
 -- fundlvl (conv d d₁) = {!!}
 -- fundlvl (sub d x) = {!!}
 -- fundlvl (funβ d d₁) = {!!}
 -- fundlvl (funη d) = {!!}
 -- fundlvl _ = {!!}
 -- -- fundlvl (rec-zero d d₁ d₂) = {!!}
 -- -- fundlvl (rec-suc d d₁ d₂ d₃) = {!!}
 -- -- fundlvl (sub-id d) = {!!}
 -- -- fundlvl (sub-comp d x x₁) = {!!}
 -- -- fundlvl (sub-zero x) = {!!}
 -- -- fundlvl (sub-suc x d) = {!!}
 -- -- fundlvl (sub-Nat x) = {!!}
 -- -- fundlvl (sub-Set x) = {!!}
 -- -- fundlvl (sub-ƛ x d) = {!!}
 -- -- fundlvl (sub-rec d d₁ d₂ d₃ x) = {!!}
 -- -- fundlvl (sub-idx-top x) = {!!}
 -- -- fundlvl (sub-idx-pop x₁ x₂) = {!!}
 -- -- fundlvl (sub-· x d d₁) = {!!}
 -- -- fundlvl (sub-Π x d d₁) = {!!}

 -- lem0 : ∀ {Γ A i} (d : Γ ⊢ A ≈ A ∶ Set* i) -> Γ ⊨' A type[ fundc d , pred (fundlvl d) ]
 -- lem0 d vρ = proj₂ (lem (fundt d vρ) (fund d vρ))

 -- fundtv : ∀ {Γ x T} (x1 : Γ ⊢ctx) (d : Γ ∋ x ∶ T) -> Γ ⊨' T type[ fundc' x1 , fundlvlv x1 d ]
 -- fundtv ⊡ () ρ₁
 -- fundtv (_,_ (inj x)) top {Syn.⊡} {Syn.⊡} vρ = {!!}
 -- fundtv (_,_ (inj x)) top {Syn.⊡} {_,_ ρ' a} vρ = {!!}
 -- fundtv (_,_ (inj x)) top {ρ , a} {Syn.⊡} vρ = {!!}
 -- fundtv (_,_ (inj x)) top {ρ , a} {ρ' , a₁} (vρ , va) = 
 --  let q = lem (fundt x vρ) (fund x vρ) in
 --  {!!}
 -- fundtv (_,_ x) (pop d) ρ₁ = {!!}

 -- fundt : ∀ {Γ t t' T} (d : Γ ⊢ t ≈ t' ∶ T) -> Γ ⊨' T type[ fundc d , fundlvl d ]
 -- fundt (sym d) vρ = fundt d vρ
 -- fundt (trans d d₁) vρ = fundt d₁ vρ
 -- fundt (Nat {i} x) vρ = record { red1 = , Set*; red2 = , Set*; rel = Set* ≤refl }
 -- fundt (zero x) vρ = record { red1 = , Nat; red2 = , Nat; rel = Nat }
 -- fundt (suc d) vρ = inj (, Nat) (, Nat) (Nat)
 -- fundt (Set* {i} x) vρ = inj (, Set*) (, Set*) (Set* ≤refl)
 -- fundt (idx x₁ x₂) vρ = fundtv x₁ x₂ vρ
 -- fundt (rec d d₁ d₂ d₃) vρ = {!!}
 -- fundt (d · d₁) vρ = {!!}
 -- fundt (ƛ d) vρ with proj₂ (fundc d) vρ 
 -- ... | inj (A , red1) (A' , red2) (n , rel) = {!!} --inj (, Π red1 ƛ) (, Π red2 ƛ) (Π rel (λ a≈a' → {!!})) -- TODO: This may not be n! Do I need to mutually extract the level?
 -- fundt (Π d d₁) vρ = {!!}
 -- fundt (d [ x ]) vρ = {!!}
 -- fundt (conv d d₁) vρ = {!!}
 -- fundt (sub d x) vρ = {!!}
 -- fundt (funβ d d₁) vρ = {!!}
 -- fundt (funη d) vρ = {!!}
 -- fundt _ vρ = {!!}
 -- -- fundt (rec-zero d d₁ d₂) vρ = {!!}
 -- -- fundt (rec-suc d d₁ d₂ d₃) vρ = {!!}
 -- -- fundt (sub-id d) vρ = {!!}
 -- -- fundt (sub-comp d x x₁) vρ = {!!}
 -- -- fundt (sub-zero x) vρ = {!!}
 -- -- fundt (sub-suc x d) vρ = {!!}
 -- -- fundt (sub-Nat x) vρ = {!!}
 -- -- fundt (sub-Set x) vρ = {!!}
 -- -- fundt (sub-ƛ x d) vρ = {!!}
 -- -- fundt (sub-rec d d₁ d₂ d₃ x) vρ = {!!}
 -- -- fundt (sub-idx-top x) vρ = {!!}
 -- -- fundt (sub-idx-pop x₁ x₂) vρ = {!!}
 -- -- fundt (sub-· x d d₁) vρ = {!!}
 -- -- fundt (sub-Π x d d₁) vρ = {!!}

 -- fund : ∀ {Γ t t' T} (d : Γ ⊢ t ≈ t' ∶ T) -> Γ ⊨' t ≈ t' ∶ T [ (fundc d , (fundlvl d , fundt d)) ]
 -- fund (sym d) vρ = hsymωt (fundt d (⟦,⟧ctx-sym vρ)) (fundt d vρ) (fund d (⟦,⟧ctx-sym vρ))
 -- fund (trans d d₁) vρ =
 --   let vρ' = ⟦,⟧ctx-irr (⟦,⟧ctx-self vρ) in
 --   htransω' (fundt d vρ') (fundt d₁ vρ) (fundt d₁ vρ) (fund d vρ') (fund d₁ vρ)
 -- fund (Nat x) vρ = inj (, Nat) (, Nat) Nat
 -- fund (zero x) vρ = inj (, zero) (, zero) zero
 -- fund (suc d) vρ with fund d vρ
 -- fund (suc d) vρ | inj (_ , red1) (_ , red2) rel with fundt d vρ
 -- fund (suc d) vρ | inj (_ , red1) (_ , red2) rel' | inj (._ , Nat) (._ , Nat) (Nat) = inj (, suc red1) (, suc red2) (suc rel')
 -- fund (Set* x) vρ = inj (, Set*) (, Set*) (Set* ≤refl)
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
 -- fund _ vρ = {!!}
 -- -- fund (rec-zero d d₁ d₂) vρ = {!!}
 -- -- fund (rec-suc d d₁ d₂ d₃) vρ = {!!}
 -- -- fund (sub-id d) vρ = {!!}
 -- -- fund (sub-comp d x x₁) vρ = {!!}
 -- -- fund (sub-zero x) vρ = {!!}
 -- -- fund (sub-suc x d) vρ = {!!}
 -- -- fund (sub-Nat x) vρ = {!!}
 -- -- fund (sub-Set x) vρ = {!!}
 -- -- fund (sub-ƛ x d) vρ = {!!}
 -- -- fund (sub-rec d d₁ d₂ d₃ x) vρ = {!!}
 -- -- fund (sub-idx-top x) vρ = {!!}
 -- -- fund (sub-idx-pop x₁ x₂) vρ = {!!}
 -- -- fund (sub-· x d d₁) vρ = {!!}
 -- -- fund (sub-Π x d d₁) vρ = {!!}

 -- fund-suc' : ∀ {t t' ρ ρ' k} -> ρ , ρ' ⊨'' t ≈ t' ∶ Nat [ k ] -> ρ , ρ' ⊨'' suc t ≈ suc t' ∶ Nat [ k ]
 -- proj₁ (fund-suc' (inj (._ , Nat) (._ , Nat) Nat , d2)) = inj (, Nat) (, Nat) Nat
 -- proj₂ (fund-suc' (inj (._ , Nat) (._ , Nat) Nat , d2)) = inj (, suc (proj₂ (App.red1 d2))) (, suc (proj₂ (App.red2 d2))) (suc (App.rel d2))

 -- fund-suc : ∀ {Γ t t'} -> Γ ⊨ t ≈ t' ∶ Nat -> Γ ⊨ suc t ≈ suc t' ∶ Nat
 -- proj₁ (fund-suc (p1 , p2)) = p1
 -- proj₁ (proj₂ (fund-suc (p1 , (p2 , p3)))) = p2
 -- proj₂ (proj₂ (fund-suc (p1 , (p2 , p3)))) vρ = fund-suc' (p3 vρ)

_⋆_ : ∀ {c d} -> (∀ {v} -> c ↘ v -> d ↘ v) -> Red c -> Red d
f ⋆ r = , f (proj₂ r)

-- comb : ∀ {B c1 c2} (f : Comp -> Comp) -> (∀ {c v} -> c ↘ v -> f c ↘ v)
--  -> c1 ≈ c2 ∈ App B -> f c1 ≈ f c2 ∈ App B
-- comb f F x = inj (F ⋆ (App.red1 x)) (F ⋆ App.red2 x) (App.rel x)

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

Πs : ∀ {γ a b k} {Γ : ⊨ γ ctx} ->
     (A : [ Γ ]⊨ a type[ k ]) -> [ Γ , A ]⊨ b type[ k ] -> [ Γ ]⊨ (Π a (ƛ b)) type[ k ]
Πs A B ρ1≈ρ2 = inj (, (Π (proj₂ (App.red1 (A ρ1≈ρ2))) ƛ))
                   (, (Π (proj₂ (App.red2 (A ρ1≈ρ2))) ƛ))
     (Π (App.rel (A ρ1≈ρ2)) (λ p -> com ƛ· ƛ· (B (ρ1≈ρ2 , p))))

Πs' : ∀ {γ a b k} {Γ : ⊨ γ ctx} ->
     (A : [ Γ ]⊨ a type[ k ]) -> [ Γ , A ]⊨ b type[ k ] -> [ Γ ]⊨ (Π a (ƛ b)) type[ k ]
Πs' A B ρ1≈ρ2 = com2 (λ p -> Π p ƛ) (λ p -> Π p ƛ) (A ρ1≈ρ2)
  (λ x → Π x (λ p → com2 ƛ· ƛ· (B (ρ1≈ρ2 , {!!})) {!!}))
  -- inj (, (Π (proj₂ (App.red1 (A ρ1≈ρ2))) ƛ))
  --                  (, (Π (proj₂ (App.red2 (A ρ1≈ρ2))) ƛ))
  --    (Π (App.rel (A ρ1≈ρ2)) (λ p -> com ƛ· ƛ· (B (ρ1≈ρ2 , p))))

fundƛ : ∀ {γ a b t s k} {Γ : ⊨ γ ctx} {A : [ Γ ]⊨ a type[ k ]} {B : [ Γ , A ]⊨ b type[ k ]}
      -> [ Γ , A ]⊨ t ≈ s ∶[ B ]
      -> [ Γ ]⊨ (ƛ t) ≈ (ƛ s) ∶[ Πs A B ]
fundƛ d ρ₁≈ρ₂ = inj (, ƛ) (, ƛ) (λ p → com ƛ· ƛ· (d (ρ₁≈ρ₂ , p)))

Nats : ∀ {γ} k {Γ : ⊨ γ ctx} -> [ Γ ]⊨ Nat type[ k ]
Nats k ρ1≈ρ2 = inj (, Nat) (, Nat) Nat

fund-suc : ∀ {γ t s k} {Γ : ⊨ γ ctx} 
 -> [ Γ ]⊨ t ≈ s ∶[ Nats k ]
 -> [ Γ ]⊨ suc t ≈ suc s ∶[ Nats k ] 
fund-suc d ρ1≈ρ2 =
 inj
  (, suc (proj₂ (App.red1 (d ρ1≈ρ2))))
  (, suc (proj₂ (App.red2 (d ρ1≈ρ2))))
  (suc (App.rel (d ρ1≈ρ2)))

fund-suc' : ∀ {γ t s k} {Γ : ⊨ γ ctx} 
 -> [ Γ ]⊨ t ≈ s ∶[ Nats k ]
 -> [ Γ ]⊨ suc t ≈ suc s ∶[ Nats k ] 
fund-suc' d ρ1≈ρ2 = com2 suc suc (d ρ1≈ρ2) suc
     

-- inversion lemma for proofs [ Γ ]⊨ (Π a (ƛ b)) type[ k ] ?