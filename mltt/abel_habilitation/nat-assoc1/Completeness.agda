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
open import Typing
open import Sym
open import Transitivity
open import ModelProperties
open import Function as F
open import Relation.Binary.PropositionalEquality hiding ([_]; sym; trans)
open import Cumulativity

open Clo

com : ∀ {α β : Set} {B c1 c2 d1 d2} {red1 : α -> Val -> Set} {red2 : β -> Val -> Set}
 -> (∀ {v} -> red1 c1 v -> red2 d1 v) -- Like the CBPV stack proof...
 -> (∀ {v} -> red1 c2 v -> red2 d2 v)
 -> c1 ≈ c2 ∈ Clo red1 B -> d1 ≈ d2 ∈ Clo red2 B
com F1 F2 x = inj' (F1 (rd1 x)) (F2 (rd2 x)) (rel x)

com2 : ∀ {α β : Set} {red1 : α -> Val -> Set} {red2 : β -> Val -> Set} {B c1 c2 d1 d2} {f1 f2 : Val -> Val}
 {C : ∀ {v1 v2} (p : B v1 v2) -> REL}
 -> (∀ {v} -> red1 c1 v -> red2 d1 (f1 v))
 -> (∀ {v} -> red1 c2 v -> red2 d2 (f2 v))
 -> (p : c1 ≈ c2 ∈ Clo red1 B)
 -> (∀ {v1 v2} -> (p : B v1 v2) -> C p (f1 v1) (f2 v2))
 -> d1 ≈ d2 ∈ Clo red2 (C (rel p))
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

-- irr : ∀ {γ t s a k} {Γ : ⊨ γ ctx} {A1 A2 : [ Γ ]⊨ a type[ k ]}
--  -> [ Γ ]⊨ t ≈ s ∶[ A1 ] 
--  -> [ Γ ]⊨ t ≈ s ∶[ A2 ]
-- irr {A1 = A1} {A2 = A2} d ρ1≈ρ2 = {!!} --com2 F.id F.id (d ρ1≈ρ2) (⟦⟧tp'-irr (A1 ρ1≈ρ2) (A2 ρ1≈ρ2))

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


-- This heterogeneous stuff may or may not be useful...
⟦,⟧ctx-sym : HSYM ⊨_≈_ctx ⟦_⟧hctx ⊨_≈_ctx ⟦_⟧hctx
⟦,⟧ctx-sym tt tt tt = tt
⟦,⟧ctx-sym (dγ1 , x) (dγ2 , x₁) (vρ , x₂) = (⟦,⟧ctx-sym dγ1 dγ2 vρ) , hsym* eval-deter (x vρ) (x₁ (⟦,⟧ctx-sym dγ1 dγ2 vρ)) x₂

mutual
 ctx-sym : SYM ⊨_≈_ctx
 ctx-sym tt = tt
 ctx-sym (dγ , x) = (ctx-sym dγ) , (fund-hsym-tp x)

 fund-hsym-tp : ∀ {γ1 γ2 a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} {Γ' : ⊨ γ2 ≈ γ1 ctx}
  -> [ Γ  ]⊨ a1 ≈ a2 type[ k ]
  -> [ Γ' ]⊨ a2 ≈ a1 type[ k ]
 fund-hsym-tp da dρ = App-sym symSetω (da (⟦,⟧ctx-sym _ _ dρ))

-- Is this actually necessary?
fund-hsym : ∀ {γ1 γ2 t1 t2 a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} {Γ' : ⊨ γ2 ≈ γ1 ctx}
 {A  : [ Γ ]⊨ a1 ≈ a2 type[ k ]}
 {A' : [ Γ' ]⊨ a2 ≈ a1 type[ k ]}
  -> [ Γ ]⊨ t1 ≈ t2 ∶h[ A ]
  -> [ Γ' ]⊨ t2 ≈ t1 ∶h[ A' ]
fund-hsym {A = A} {A' = A'} dt dρ = 
 let q = dt (⟦,⟧ctx-sym _ _ dρ) in
 let q1 = hsym* eval-deter (A (⟦,⟧ctx-sym _ _ dρ)) (A' dρ) (rel q) in
 inj' (rd2 q) (rd1 q) q1
-- TODO: Part of the above could be factored out...

mutual
 ctx-sym2 : ∀ {γ1 γ2} -> (Γ : ⊨ γ1 ≈ γ2 ctx) -> SYM ⟦ Γ ⟧hctx
 ctx-sym2 tt tt = tt
 ctx-sym2 (Γ , A) (ρ1≈ρ2 , v1≈v2) =
  let ρ2≈ρ1 = ctx-sym2 Γ ρ1≈ρ2
      ρ1≈ρ1 = ctx-trans2 Γ ρ1≈ρ2 ρ2≈ρ1 
      v2≈v1 = symω' _ (rel (A ρ1≈ρ2)) v1≈v2
      q  = irrLF' eval-deter A ρ1≈ρ2 ρ1≈ρ1 v2≈v1
      q1 = irrRF' eval-deter A ρ1≈ρ1 (ctx-sym2 _ ρ1≈ρ2) q
  in ρ2≈ρ1 , q1
 -- How much of this is in common with the Π case?

 ctx-trans2 : ∀ {γ1 γ2} -> (Γ : ⊨ γ1 ≈ γ2 ctx) -> TRANS ⟦ Γ ⟧hctx 
 ctx-trans2 tt tt tt = tt
 ctx-trans2 (Γ , A) (ρ1≈ρ2 , v1≈v2) (ρ2≈ρ3 , v2≈v3) =
  let ρ1≈ρ3 = ctx-trans2 Γ ρ1≈ρ2 ρ2≈ρ3
      v1≈v2' = irrLF' eval-deter A ρ1≈ρ2 ρ1≈ρ3 v1≈v2
      v2≈v3' = irrRF' eval-deter A ρ2≈ρ3 ρ1≈ρ3 v2≈v3
      v1≈v3 = transω' _ (rel (A ρ1≈ρ3)) v1≈v2' v2≈v3'
  in ρ1≈ρ3 , v1≈v3
  -- Notice that this is essentially the definition of htrans*
  -- but the type isn't right...
            -- htrans* (rel A1) (eval-deter (rd1 A1) (rd1 A3))
            --          (rel A2) (eval-deter (rd2 A1) {!!})
            --          (rel A3) (eval-deter (rd2 A2) (rd2 A3)) v1≈v2 v2≈v3

ctx-selfL :  ∀ {γ1 γ2} -> (Γ : ⊨ γ1 ≈ γ2 ctx) -> SELFL ⟦ Γ ⟧hctx
ctx-selfL Γ p = ctx-trans2 Γ p (ctx-sym2 Γ p)

fund-sym-tp : ∀ {γ1 γ2 a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx}
  -> [ Γ ]⊨ a1 ≈ a2 type[ k ]
  -> [ Γ ]⊨ a2 ≈ a1 type[ k ]
fund-sym-tp da = ΠSYM.Πsym (ctx-sym2 _) (ctx-trans2 _) (λ _ _ x → x) (λ _ _ x → x) (λ _ → symSetω' _) da
-- TODO: Is that generality necessary?

fund-sym : ∀ {γ1 γ2 t1 t2 a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} (A : [ Γ ]⊨ a1 ≈ a2 type[ k ])
 -> [ Γ ]⊨ t1 ≈ t2 ∶h[ A ]
 -> [ Γ ]⊨ t2 ≈ t1 ∶h[ A ]
fund-sym {k = k} A = ΠSYM.Πsym (ctx-sym2 _) (ctx-trans2 _) (irrLF' eval-deter A) (irrRF' eval-deter A)
       (λ p  → symω' _ (rel (A p)))

fund-trans : ∀ {γ1 γ2 t1 t2 t3 a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} (A : [ Γ ]⊨ a1 ≈ a2 type[ k ])
 -> [ Γ ]⊨ t1 ≈ t2 ∶h[ A ]
 -> [ Γ ]⊨ t2 ≈ t3 ∶h[ A ]
 -> [ Γ ]⊨ t1 ≈ t3 ∶h[ A ]
fund-trans A = ΠPER.Πtrans eval-deter (ctx-selfL _) (irrLF' eval-deter A)
 (λ p → symω' _ (rel (A p))) (λ p → transω' _ (rel (A p)))

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
 inj' (ap (rd1 vt) (rd1 vs) (rd1 vr))
      (ap (rd2 vt) (rd2 vs) (rd2 vr))
      (rel vr)

fundβ : ∀ {γ1 γ2 t1 t2 s1 s2 a1 a2 b1 b2 k}
 {Γ : ⊨ γ1 ≈ γ2 ctx} {A : [ Γ ]⊨ a1 ≈ a2 type[ k ]} {B : [ Γ , A ]⊨ b1 ≈ b2 type[ k ]}
 -> [ Γ , A ]⊨ t1 ≈ t2 ∶h[ B ]
 -> (ds : [ Γ ]⊨ s1 ≈ s2 ∶h[ A ])
 -> [ Γ ]⊨ (ƛ t1) · s1 ≈ (t2 [ T.id , s2 ]) ∶h[ A >h B • ds ]
fundβ dt ds ρ1≈ρ2 =
 let vs = ds ρ1≈ρ2 in
 let vt = dt (ρ1≈ρ2 , (rel vs)) in
 inj' (ap ƛ (rd1 vs) (ƛ· (rd1 vt)))
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
            (ƛ· (ap ((rd2 vt) [ ↑ ]) (idx top) (rd2 q)))
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

Nats : ∀ {γ1 γ2} k {Γ : ⊨ γ1 ≈ γ2 ctx} -> [ Γ ]⊨ Nat ≈ Nat type[ k ]
Nats k ρ1≈ρ2 = inj (, Nat) (, Nat) Nat

fund-suc' : ∀ {γ t s k} {Γ : ⊨ γ ctx} 
 -> [ Γ ]⊨ t ≈ s ∶[ Nats k ]
 -> [ Γ ]⊨ suc t ≈ suc s ∶[ Nats k ] 
fund-suc' d ρ1≈ρ2 = com2 suc suc (d ρ1≈ρ2) suc

mutual
 fund-plus' : ∀ {m m' n n'}
  -> m ≈ m' ∈ NatR
  -> n ≈ n' ∈ NatR
  -> (m ⊕̂ n) ≈ (m' ⊕̂ n') ∈ NatR
 fund-plus' zero n₁ = n₁
 fund-plus' (suc x) n₁ = suc (fund-plus' x n₁)
 fund-plus' (p ⊕ m) n₁ = p ⊕ fund-plus' m n₁
 fund-plus' (neu x) n₁ = x ⊕ n₁
 fund-plus' (idL x) n = x ⊕ n
 fund-plus' (idR x) n = x ⊕ n

fund-assoc' : ∀ {m m' n n' p p'}
 -> m ≈ m' ∈ NatR
 -> n ≈ n' ∈ NatR
 -> p ≈ p' ∈ NatR
 -> ((m ⊕̂ n) ⊕̂ p) ≈ (m' ⊕̂ (n' ⊕̂ p')) ∈ NatR
fund-assoc' zero n₁ p₁ = fund-plus' n₁ p₁
fund-assoc' (suc x) n₁ p₁ = suc (fund-assoc' x n₁ p₁)
fund-assoc' (p ⊕ m) n₁ p₁ = p ⊕ (fund-assoc' m n₁ p₁)
fund-assoc' (neu x) n₁ p₁ = x ⊕ (fund-plus' n₁ p₁)
fund-assoc' (idL x) n p = x ⊕ (fund-plus' n p)
fund-assoc' (idR x) n p = x ⊕ (fund-plus' n p)

fund-idR : ∀ {m m'}
 -> m ≈ m' ∈ NatR
 -> (m ⊕̂ zero) ≈ m' ∈ NatR
fund-idR zero = zero
fund-idR (suc x) = suc (fund-idR x)
fund-idR (x ⊕ x₁) = x ⊕ (fund-idR x₁)
fund-idR (neu x) = idL x
fund-idR (idL x) = idL x
fund-idR (idR x) = x ⊕ zero

fund-assoc : ∀ {γ1 γ2 m m' n n' p p' k} {Γ : ⊨ γ1 ≈ γ2 ctx} 
 -> [ Γ ]⊨ m ≈ m' ∶h[ Nats k ]
 -> [ Γ ]⊨ n ≈ n' ∶h[ Nats k ]
 -> [ Γ ]⊨ p ≈ p' ∶h[ Nats k ]
 -> [ Γ ]⊨ (m ⊕ n) ⊕ p ≈ m' ⊕ (n' ⊕ p') ∶h[ Nats k ]
fund-assoc dm dn dp ρ1≈ρ2 =
 let vm = dm ρ1≈ρ2
     vn = dn ρ1≈ρ2
     vp = dp ρ1≈ρ2
 in inj' (plus (plus (rd1 vm) (rd1 vn)) (rd1 vp))
         (plus (rd2 vm) (plus (rd2 vn) (rd2 vp)))
    (fund-assoc' (rel vm) (rel vn) (rel vp))

-- TODO: Crap! I can't prove the "rec" case unless I want to distribute it
-- it across plus, because rec can only take a Dne!
     
-- TODO: Variable rules!

-- TODO: The best way to mirror this semantic structure in syntax seems to be
-- to use an inductive-inductive definition of the syntax, indexing typing derivations by
-- well-formedness derivations. Then have an "irrelevance" rule. (because there isn't just
-- one derivation that Π A B is well-formed -- it can come from something non-canonical?)
-- Can I model this some other way, so I don't have to rely on inductive-inductive definitions?
-- e.g. packaging it up in a sigma, like induction-recursion?
-- What about a wrapper to explicitly witness well-formedness at every subnode of the typing derivation?
-- Remember that Γ ⊢ a ∶ A is kind of like Γ ⊢ Σ (A : Set k). A?

-- ..Can I just directly prove that semantic equivalence is decidable? And use that
-- in typing normal forms? It seems that if I can prove soundness and completeness,
-- then it's equivalent, so I should be able to do it directly???
-- Then I don't need to do an inductive-inductive definition....
-- I think this works! Normalize in identity context, compare values. If they're equal, done.
-- if they're not, then they're not semantically equal either, because contradiction.
-- Now how do we set up the typing rules?
-- I think I could prove decidability of [ Γ ]⊨ t ≈ s ∶[ T ] right now.
-- Do we need to prove some kind of soundness result?
-- Currently it just looks like 'Yeah here's a decidable definition of equivalence which includes
-- at least the following rules'. Wouldn't we also like to know that it's non-trivial
-- or somehow not bad..? I guess we could show that ¬ ([ Γ ]⊨ 0 ≈ 1 ∶[ Nat ])
-- What about type soundness? If [ Γ ]⊨ t ≈ s ∶[ T ] then Γ ⊢ s : T?
-- That may actually be asking too much? The typing rules may not be "complete" for semantic typing..
-- What if we start with the precondition that Γ ⊢ t ∶ T?

-- Does this give you a framework for extending your type theory? When you construct a new type,
-- can you add evaluation rules too? i.e. "strictly quotient" by reduction rules?
-- Check determinacy by verifying lack of reduction conflicts/overlapping
--   (big step, so easier than confluence?)
-- Giving the "evaluation rules" on stuck terms "reifies" a fancy property of the model --
--  its ability to model variables/neutral terms (via the presheaf/nominal style thing)
--  Is nominal logic a good way to do this? It may be that these "variables" are treated
--  like names in nominal logic!!!!

-- Extensions with other stuff? As long as your evaluation is deterministic, you're good?!

-- IMPORTANT TODO:  Show the "reify identity substitution" thing
open import Candidate
