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
 -> (∀ {v} -> red1 c1 v -> red2 d1 v) -- Reminds of equivalence of big step and stack machine proof...
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

Set' : ∀ {γ} k {Γ : ⊨ γ ctx} -> Γ ⊨ Set* k type (suc k)
Set' k ρ1≈ρ2 = inj' Set* Set* (Set* (s≤s ≤refl))

Set'' : ∀ {γ} k {Γ : ⊨ γ ctx} -> Γ ⊨ (Set* k) ≈ (Set* k) ∶ (Set' (suc k))
Set'' k ρ1≈ρ2 = inj' Set* Set* (Set* (s≤s ≤refl))

in-type : ∀ {γ a1 a2 k} {Γ : ⊨ γ ctx} -> Γ ⊨ a1 ≈ a2 ∶ Set' k -> Γ ⊨ a1 ≈ a2 type k
in-type d ρ1≈ρ2 = com2 F.id F.id (d ρ1≈ρ2) (cumul _ _ ≤refl)

out-type : ∀ {γ a1 a2 k} {Γ : ⊨ γ ctx} -> Γ ⊨ a1 ≈ a2 type k -> Γ ⊨ a1 ≈ a2 ∶ Set' k
out-type d ρ1≈ρ2 = com2 F.id F.id (d ρ1≈ρ2) (cumul _ _ ≤refl)

Πs : ∀ {γ1 γ2 a1 a2 b1 b2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} ->
     (A : Γ ⊨ a1 ≈ a2 type k ) -> (Γ , A) ⊨ b1 ≈ b2 type k
    -> Γ ⊨ (Π a1 (ƛ b1)) ≈ (Π a2 (ƛ b2)) type k
Πs A B ρ1≈ρ2 = inj' (Π (rd1 (A ρ1≈ρ2)) ƛ)
                    (Π (rd2 (A ρ1≈ρ2)) ƛ)
     (Π (rel (A ρ1≈ρ2)) (λ p -> com ƛ· ƛ· (B (ρ1≈ρ2 , p))))

Πinv1 : ∀ {γ1 γ2 a1 a2 b1 b2 k} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> Γ ⊨ Π a1 (ƛ b1) ≈ Π a2 (ƛ b2) type k
 -> Γ ⊨ a1 ≈ a2 type k
Πinv1 p ρ1≈ρ2 with p ρ1≈ρ2
Πinv1 p ρ1≈ρ2 | inj (._ , Π proj₂ proj₃) (._ , Π proj₄ proj₅) (Π pA pF) = inj (, proj₂) (, proj₄) pA

Πinv2 : ∀ {γ1 γ2 a1 a2 b1 b2 k} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> (d : Γ ⊨ Π a1 (ƛ b1) ≈ Π a2 (ƛ b2) type k)
 -> ( Γ , Πinv1 d )⊨ b1 ≈ b2 type k 
Πinv2 p (vρ , x) with p vρ
Πinv2 p (vρ , x) | inj (._ , Π proj₂ ƛ) (._ , Π proj₄ ƛ) (Π pA pF) with pF x
Πinv2 p (vρ , x) | inj (._ , Π proj₂ ƛ) (._ , Π proj₄ ƛ) (Π pA pF) | inj (proj₁ , ƛ· proj₃) (proj₅ , ƛ· proj₆) rel = inj (, proj₃) (, proj₆) rel


fundƛ : ∀ {γ1 γ2 a1 a2 b1 b2 t s k}
  {Γ : ⊨ γ1 ≈ γ2 ctx} {A : Γ ⊨ a1 ≈ a2 type k} {B : (Γ , A) ⊨ b1 ≈ b2 type k}
      -> (Γ , A) ⊨ t ≈ s ∶ B
      -> Γ ⊨ (ƛ t) ≈ (ƛ s) ∶ Πs A B
fundƛ d ρ₁≈ρ₂ = inj (, ƛ) (, ƛ) (λ p → com ƛ· ƛ· (d (ρ₁≈ρ₂ , p)))

_>_•_ : ∀ {γ1 γ2 δ1 δ2 b1 b2 σ1 σ2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} (Δ : ⊨ δ1 ≈ δ2 ctx) 
 -> Δ ⊨ b1 ≈ b2 type  k
 -> Γ ⊨s σ1 ≈ σ2 ∶ Δ
 -> Γ ⊨ b1 [ σ1 ] ≈ b2 [ σ2 ] type k
(Δ > B • σ) ρ1≈ρ2 =
 let vσ = σ ρ1≈ρ2 in
 let vb = B (rel vσ) in
 inj' (rd1 vb [ rd1 vσ ])
      (rd2 vb [ rd2 vσ ])
      (rel vb)

fund-⊡ : ∀ {γ1 γ2} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> Γ ⊨s ⊡ ≈ ⊡ ∶ ⊡
fund-⊡ ρ1≈ρ2 = inj' ⊡ ⊡ ⊡

fund-, : ∀ {γ1 γ2 δ1 δ2 σ σ' t t' a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} {Δ : ⊨ δ1 ≈ δ2 ctx}
 -> (A : Δ ⊨ a1 ≈ a2 type k)
 -> (dσ : Γ ⊨s σ ≈ σ' ∶ Δ)
 -> Γ ⊨ t ≈ t' ∶ (Δ > A • dσ)
 -> Γ ⊨s σ , t ≈ σ' , t' ∶ (Δ , A)
fund-, A dσ dt dρ =
 let vσ = dσ dρ
     vt = dt dρ in
 inj' (rd1 vσ , rd1 vt)
      (rd2 vσ , rd2 vt)
      (rel vσ , rel vt) 

fund-id : ∀ {γ1 γ2} {Γ : ⊨ γ1 ≈ γ2 ctx} -> Γ ⊨s T.id ≈ T.id ∶ Γ
fund-id dρ = inj (, Eval.id) (, Eval.id) dρ
 
_>h_•_ : ∀ {γ1 γ2 a1 a2 b1 b2 t1 t2 j k} {Γ : ⊨ γ1 ≈ γ2 ctx} (A : Γ ⊨ a1 ≈ a2 type k) 
 -> (Γ , A) ⊨ b1 ≈ b2 type j
 -> Γ ⊨ t1 ≈ t2 ∶ A
 -> Γ ⊨ b1 [ T.id , t1 ] ≈ b2 [ T.id , t2 ] type j
A >h B • t = (_ , A) > B • fund-, A fund-id t

fund-↑ : ∀ {γ1 γ2 t1 t2 k} (Γ : ⊨ γ1 ≈ γ2 ctx) (T : Γ ⊨ t1 ≈ t2 type k)
 -> (Γ , T) ⊨s ↑ ≈ ↑ ∶ Γ
fund-↑ Γ T (ρ1≈ρ2 , v1≈v2) = inj' ↑ ↑ ρ1≈ρ2


-- This heterogeneous stuff may or may not be useful...
⟦,⟧ctx-sym : HSYM ⊨_≈_ctx ⟦_⟧hctx ⊨_≈_ctx ⟦_⟧hctx
⟦,⟧ctx-sym ⊡ ⊡ ⊡ = ⊡
⟦,⟧ctx-sym (dγ1 , x) (dγ2 , x₁) (vρ , x₂) = (⟦,⟧ctx-sym dγ1 dγ2 vρ) , hsym* eval-deter (x vρ) (x₁ (⟦,⟧ctx-sym dγ1 dγ2 vρ)) x₂

mutual
 ctx-sym : SYM ⊨_≈_ctx
 ctx-sym ⊡ = ⊡
 ctx-sym (dγ , x) = (ctx-sym dγ) , (fund-hsym-tp x)

 fund-hsym-tp : ∀ {γ1 γ2 a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} {Γ' : ⊨ γ2 ≈ γ1 ctx}
  -> Γ ⊨ a1 ≈ a2 type k
  -> Γ' ⊨ a2 ≈ a1 type k
 fund-hsym-tp da dρ = App-sym symSetω (da (⟦,⟧ctx-sym _ _ dρ))

-- Is this actually necessary?
fund-hsym : ∀ {γ1 γ2 t1 t2 a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} {Γ' : ⊨ γ2 ≈ γ1 ctx}
 {A  : Γ ⊨ a1 ≈ a2 type k}
 {A' : Γ' ⊨ a2 ≈ a1 type k}
  -> Γ ⊨ t1 ≈ t2 ∶ A
  -> Γ' ⊨ t2 ≈ t1 ∶ A'
fund-hsym {A = A} {A' = A'} dt dρ = 
 let q = dt (⟦,⟧ctx-sym _ _ dρ) in
 let q1 = hsym* eval-deter (A (⟦,⟧ctx-sym _ _ dρ)) (A' dρ) (rel q) in
 inj' (rd2 q) (rd1 q) q1
-- TODO: Part of the above could be factored out...

mutual
 ctx-sym2 : ∀ {γ1 γ2} -> (Γ : ⊨ γ1 ≈ γ2 ctx) -> SYM ⟦ Γ ⟧hctx
 ctx-sym2 ⊡ ⊡ = ⊡
 ctx-sym2 (Γ , A) (ρ1≈ρ2 , v1≈v2) =
  let ρ2≈ρ1 = ctx-sym2 Γ ρ1≈ρ2
      ρ1≈ρ1 = ctx-trans2 Γ ρ1≈ρ2 ρ2≈ρ1 
      v2≈v1 = symω' _ (rel (A ρ1≈ρ2)) v1≈v2
      q  = irrLRF' eval-deter A ρ1≈ρ1 v2≈v1
  in ρ2≈ρ1 , q
 -- How much of this is in common with the Π case?

 ctx-trans2 : ∀ {γ1 γ2} -> (Γ : ⊨ γ1 ≈ γ2 ctx) -> TRANS ⟦ Γ ⟧hctx 
 ctx-trans2 ⊡ ⊡ ⊡ = ⊡
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
  -> Γ ⊨ a1 ≈ a2 type k
  -> Γ ⊨ a2 ≈ a1 type k
fund-sym-tp = ⇒Sym.⇒sym (ctx-sym2 _) (ctx-trans2 _) (symSetω' _)

fund-trans-tp : ∀ {γ1 γ2 a1 a2 a3 k} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> Γ ⊨ a1 ≈ a2 type k
 -> Γ ⊨ a2 ≈ a3 type k
 -> Γ ⊨ a1 ≈ a3 type k
fund-trans-tp = ⇒Trans.⇒trans eval-deter (ctx-selfL _) (symSetω' _) (transSetω' _)

fund-sym : ∀ {γ1 γ2 t1 t2 a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} (A : Γ ⊨ a1 ≈ a2 type k)
 -> Γ ⊨ t1 ≈ t2 ∶ A
 -> Γ ⊨ t2 ≈ t1 ∶ A
fund-sym {k = k} A = ΠSYM.Πsym (ctx-sym2 _) (ctx-trans2 _) (irrLF' eval-deter A) (irrRF' eval-deter A)
       (λ p  → symω' _ (rel (A p)))

fund-trans : ∀ {γ1 γ2 t1 t2 t3 a1 a2 k} {Γ : ⊨ γ1 ≈ γ2 ctx} (A : Γ ⊨ a1 ≈ a2 type k)
 -> Γ ⊨ t1 ≈ t2 ∶ A
 -> Γ ⊨ t2 ≈ t3 ∶ A
 -> Γ ⊨ t1 ≈ t3 ∶ A
fund-trans A = ΠPER.Πtrans eval-deter (ctx-selfL _) (irrLF' eval-deter A)
 (λ p → symω' _ (rel (A p))) (λ p → transω' _ (rel (A p)))

self : ∀ {γ a t1 t2 k} {Γ : ⊨ γ ctx} (A : Γ ⊨ a type k)
 -> Γ ⊨ t1 ≈ t2 ∶ A
 -> Γ ⊨ t1 ≈ t1 ∶ A
self A t1≈t2 = fund-trans A t1≈t2 (fund-sym A t1≈t2)


-- TODO: Could I factor out part of this? Environment plays no role here
-- What about just doing ds ρ1≈ρ2 and then using com?
-- Heterogeneous formulation makes this statement and proof simpler
fund·h : ∀ {γ1 γ2 t1 t2 s1 s2 a1 a2 b1 b2 k}
 {Γ : ⊨ γ1 ≈ γ2 ctx} {A : Γ ⊨ a1 ≈ a2 type k} {B : (Γ , A) ⊨ b1 ≈ b2 type k}
     ->       Γ ⊨ t1 ≈ t2 ∶ Πs A B
     -> (ds : Γ ⊨ s1 ≈ s2 ∶ A)
     ->       Γ ⊨ t1 · s1 ≈ t2 · s2 ∶ (A >h B • ds)
fund·h dt ds ρ1≈ρ2 =
 let vs = ds ρ1≈ρ2 in
 let vt = dt ρ1≈ρ2 in
 let vr = rel vt (rel vs) in
 inj' (ap (rd1 vt) (rd1 vs) (rd1 vr))
      (ap (rd2 vt) (rd2 vs) (rd2 vr))
      (rel vr)

fundβ : ∀ {γ1 γ2 t1 t2 s1 s2 a1 a2 b1 b2 k}
 {Γ : ⊨ γ1 ≈ γ2 ctx} {A : Γ ⊨ a1 ≈ a2 type k} {B : (Γ , A) ⊨ b1 ≈ b2 type k}
 -> (Γ , A) ⊨ t1 ≈ t2 ∶ B
 -> (ds : Γ ⊨ s1 ≈ s2 ∶ A)
 -> Γ ⊨ (ƛ t1) · s1 ≈ (t2 [ T.id , s2 ]) ∶ (A >h B • ds)
fundβ dt ds ρ1≈ρ2 =
 let vs = ds ρ1≈ρ2 in
 let vt = dt (ρ1≈ρ2 , (rel vs)) in
 inj' (ap ƛ (rd1 vs) (ƛ· (rd1 vt)))
      (rd2 vt [ Eval.id , rd2 vs ])
      (rel vt)

fundη : ∀ {γ1 γ2 t1 t2 a1 a2 b1 b2 k}
 {Γ : ⊨ γ1 ≈ γ2 ctx} {A : Γ ⊨ a1 ≈ a2 type k} {B : (Γ , A) ⊨ b1 ≈ b2 type k}
 -> Γ ⊨ t1 ≈ t2 ∶ Πs A B
 -> Γ ⊨ t1 ≈ (ƛ (t2 [ ↑ ] · idx 0)) ∶ Πs A B
fundη dt ρ1≈ρ2 =
 let vt = dt ρ1≈ρ2 in
 inj (red1 vt)
     (, ƛ)
     (λ p → let q = rel vt p in
       inj' (rd1 q)
            (ƛ· (ap ((rd2 vt) [ ↑ ]) (idx top) (rd2 q)))
            (rel q))

fund-subƛ : ∀ {γ1 γ2 t1 t2 a1 a2 b1 b2 σ1 σ2 δ1 δ2 k}
 {Γ : ⊨ γ1 ≈ γ2 ctx} {Δ : ⊨ δ1 ≈ δ2 ctx} {A : Δ ⊨ a1 ≈ a2 type k} {B : (Δ , A) ⊨ b1 ≈ b2 type k}
 -> (dσ : Γ ⊨s σ1 ≈ σ2 ∶ Δ)
 -> (Δ , A) ⊨ t1 ≈ t2 ∶ B
 -> Γ ⊨ (ƛ t1) [ σ1 ] ≈ ƛ (t2 [ σ2 [ ↑ ] , idx 0 ]) ∶ (Δ > Πs A B • dσ)
fund-subƛ dσ dt dρ = 
 let vσ = dσ dρ in
 inj (, ƛ [ rd1 vσ ])
     (, ƛ)
     (λ p → let vt = dt (rel vσ , p) in
        inj' (ƛ· (rd1 vt))
             (ƛ· (rd2 vt [ ↑ [ rd2 vσ ] , idx top ]))
             (rel vt))

Nats : ∀ {γ1 γ2} k {Γ : ⊨ γ1 ≈ γ2 ctx} -> Γ ⊨ Nat ≈ Nat type k
Nats k ρ1≈ρ2 = inj (, Nat) (, Nat) Nat

fund-zero : ∀ {γ1 γ2 k} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> Γ ⊨ zero ≈ zero ∶ Nats k
fund-zero ρ1≈ρ2 = inj' zero zero (inj' natval natval zero)

fund-suc : ∀ {γ1 γ2 t s k} {Γ : ⊨ γ1 ≈ γ2 ctx} 
 -> Γ ⊨ t ≈ s ∶ Nats k
 -> Γ ⊨ suc t ≈ suc s ∶ Nats k
fund-suc d ρ1≈ρ2 =
 let vt = d ρ1≈ρ2 in
 inj' (suc (rd1 vt) (rd1 (rel vt))) (suc (rd2 vt) (rd2 (rel vt))) (inj' natval natval (suc (rel (rel vt))))

mutual
 fund-plus' : ∀ {m m' n n'}
  -> m ≈ m' ∈ NatV
  -> n ≈ n' ∈ NatV
  -> (m ⊕̂ n) ≈ (m' ⊕̂ n') ∈ NatV
 fund-plus' zero n₁ = n₁
 fund-plus' (suc x) n₁ = suc (fund-plus' x n₁)
 fund-plus' (natneu p) n = natneu (fund-plus'' p n)

 fund-plus'' : ∀ {e1 e2 n n'}
  -> e1 ≈ e2 ∈ NatNe
  -> n ≈ n' ∈ NatV
  -> (e1 ++ n) ≈ (e2 ++ n') ∈ NatNe
 fund-plus'' (x ⊕ x₁) n₁ = x ⊕ fund-plus' x₁ n₁

fund-plus : ∀ {γ1 γ2 m m' n n' k} {Γ : ⊨ γ1 ≈ γ2 ctx} 
 -> Γ ⊨ m ≈ m' ∶ Nats k
 -> Γ ⊨ n ≈ n' ∶ Nats k
 -> Γ ⊨ m ⊕ n ≈ m' ⊕ n' ∶ Nats k
fund-plus dm dn ρ1≈ρ2 =
 let vm = dm ρ1≈ρ2
     vn = dn ρ1≈ρ2
 in inj' (plus (rd1 vm) (rd1 vn) (rd1 (rel vm)) (rd1 (rel vn)))
         (plus (rd2 vm) (rd2 vn) (rd2 (rel vm)) (rd2 (rel vn)))
         (inj' natval natval (fund-plus' (rel (rel vm)) (rel (rel vn))))

mutual
 fund-assoc' : ∀ {m m' n n' p p'}
  -> m ≈ m' ∈ NatV
  -> n ≈ n' ∈ NatV
  -> p ≈ p' ∈ NatV
  -> ((m ⊕̂ n) ⊕̂ p) ≈ (m' ⊕̂ (n' ⊕̂ p')) ∈ NatV
 fund-assoc' zero n₁ p₁ = fund-plus' n₁ p₁
 fund-assoc' (suc x) n₁ p₁ = suc (fund-assoc' x n₁ p₁)
 fund-assoc' (natneu x) n p = natneu (fund-assoc'' x n p)

 fund-assoc'' : ∀ {e1 e2 p p' n n'}
  -> e1 ≈ e2 ∈ NatNe
  -> n ≈ n' ∈ NatV
  -> p ≈ p' ∈ NatV
  -> ((e1 ++ n) ++ p) ≈ e2 ++ (n' ⊕̂ p') ∈ NatNe
 fund-assoc'' (x ⊕ x₁) p₁ n₁ = x ⊕ (fund-assoc' x₁ p₁ n₁)

fund-assoc : ∀ {γ1 γ2 m m' n n' p p' k} {Γ : ⊨ γ1 ≈ γ2 ctx} 
 -> Γ ⊨ m ≈ m' ∶ Nats k
 -> Γ ⊨ n ≈ n' ∶ Nats k
 -> Γ ⊨ p ≈ p' ∶ Nats k
 -> Γ ⊨ (m ⊕ n) ⊕ p ≈ m' ⊕ (n' ⊕ p') ∶ Nats k
fund-assoc dm dn dp ρ1≈ρ2 =
 let vm = dm ρ1≈ρ2
     vn = dn ρ1≈ρ2
     vp = dp ρ1≈ρ2
 in inj' (plus (plus (rd1 vm) (rd1 vn) (rd1 (rel vm)) (rd1 (rel vn))) (rd1 vp) natval (rd1 (rel vp)))
         (plus (rd2 vm) (plus (rd2 vn) (rd2 vp) (rd2 (rel vn)) (rd2 (rel vp))) (rd2 (rel vm)) natval)
         (inj' natval natval (fund-assoc' (rel (rel vm)) (rel (rel vn)) (rel (rel vp))))

mutual
 fund-idR' : ∀ {m m'}
  -> m ≈ m' ∈ NatV
  -> (m ⊕̂ zero) ≈ m' ∈ NatV
 fund-idR' zero = zero
 fund-idR' (suc x) = suc (fund-idR' x)
 fund-idR' (natneu x) = natneu (fund-idR'' x)

 fund-idR'' : ∀ {m m'}
  -> m ≈ m' ∈ NatNe
  -> (m ++ zero) ≈ m' ∈ NatNe
 fund-idR'' (x ⊕ x₁) = x ⊕ (fund-idR' x₁)

fund-idR : ∀ {γ1 γ2 m m' k} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> Γ ⊨ m ≈ m' ∶ Nats k
 -> Γ ⊨ (m ⊕ zero) ≈ m' ∶ Nats k
fund-idR dm ρ1≈ρ2 =
 let vm = dm ρ1≈ρ2 in
 inj' (plus (rd1 vm) zero (rd1 (rel vm)) natval)
      (rd2 vm)
      (inj' natval (rd2 (rel vm)) (fund-idR' (rel (rel vm))))

fund-lookuptp : ∀ {γ1 γ2 t1 t2 x}
 -> (Γ : ⊨ γ1 ≈ γ2 ctx)
 -> γ1 ∋ x ∶ t1
 -> γ2 ∋ x ∶ t2
 -> ∃ (λ k -> Γ ⊨ t1 ≈ t2 type k)
fund-lookuptp ⊡ () x2
fund-lookuptp (Γ , x) top top = _ , (_>_•_ {Γ = Γ , x} Γ x (fund-↑ Γ x))
fund-lookuptp (Γ₂ , x₁) (pop x1) (pop x2) =
 let q = fund-lookuptp Γ₂ x1 x2
 in _ , _>_•_ {Γ = Γ₂ , x₁} Γ₂ (proj₂ q) (fund-↑ Γ₂ x₁)


fund-lookup : ∀ {γ1 γ2 t1 t2 x}
 -> (Γ : ⊨ γ1 ≈ γ2 ctx)
 -> (x1 : γ1 ∋ x ∶ t1)
 -> (x2 : γ2 ∋ x ∶ t2)
 -> Γ ∋m x ∶ (proj₂ (fund-lookuptp Γ x1 x2))
fund-lookup (Γ , x) top top (vρ , x₁) = inj' top top x₁
fund-lookup (Γ , x₁) (pop x1) (pop x2) (ρ1≈ρ2 , v1≈v2) =
 let q = fund-lookup Γ x1 x2 ρ1≈ρ2
 in inj' (pop (rd1 q)) (pop (rd2 q)) (rel q)

fund-idx : ∀ {γ1 γ2 t1 t2 k x}
 -> {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> {T : Γ ⊨ t1 ≈ t2 type k}
 -> Γ ∋m x ∶ T
 -> Γ ⊨ idx x ≈ idx x ∶ T
fund-idx dx ρ1≈ρ2 = inj' (idx (rd1 (dx ρ1≈ρ2))) (idx (rd2 (dx ρ1≈ρ2))) (rel (dx ρ1≈ρ2))

fund-idx' : ∀ {γ1 γ2 t1 t2 x}
 -> {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> (x1 : γ1 ∋ x ∶ t1)
 -> (x2 : γ2 ∋ x ∶ t2)
 -> Γ ⊨ idx x ≈ idx x ∶ (proj₂ (fund-lookuptp Γ x1 x2))
fund-idx' {Γ = Γ} x1 x2 ρ1≈ρ2 = fund-idx  {Γ = Γ} {T = proj₂ (fund-lookuptp Γ x1 x2)} (fund-lookup Γ x1 x2) ρ1≈ρ2


fund-⊡η : ∀ {γ1 γ2 σ1 σ2} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> Γ ⊨s σ1 ≈ σ1 ∶ ⊡
 -> Γ ⊨s σ2 ≈ σ2 ∶ ⊡
 -> Γ ⊨s σ1 ≈ σ2 ∶ ⊡
fund-⊡η σ1 σ2 ρ with σ1 ρ | σ2 ρ
... | inj (._ , r1) (._ , r2) ⊡ | inj (._ , r3) (._ , r4) ⊡ = inj' r1 r4 ⊡
-- This is not exactly the form it takes in the syntax right now, but that can be recovered
-- with transitivity and symmetry

⊨s-sym : ∀ {γ1 γ2 σ1 σ2 δ1 δ2} {Γ : ⊨ γ1 ≈ γ2 ctx} {Δ : ⊨ δ1 ≈ δ2 ctx}
 -> Γ ⊨s σ1 ≈ σ2 ∶ Δ
 -> Γ ⊨s σ2 ≈ σ1 ∶ Δ
⊨s-sym = ⇒Sym.⇒sym (ctx-sym2 _) (ctx-trans2 _) (ctx-sym2 _)

⊨s-trans : ∀ {γ1 γ2 σ1 σ2 σ3 δ1 δ2} {Γ : ⊨ γ1 ≈ γ2 ctx} {Δ : ⊨ δ1 ≈ δ2 ctx}
 -> Γ ⊨s σ1 ≈ σ2 ∶ Δ
 -> Γ ⊨s σ2 ≈ σ3 ∶ Δ
 -> Γ ⊨s σ1 ≈ σ3 ∶ Δ
⊨s-trans = ⇒Trans.⇒trans evals-deter (ctx-selfL _) (ctx-sym2 _) (ctx-trans2 _)

fund-cumul : ∀ {γ1 γ2 a1 a2 j k} {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> j ≤ k
 -> Γ ⊨ a1 ≈ a2 type j
 -> Γ ⊨ a1 ≈ a2 type k
fund-cumul j≤k a ρ =
 let va = a ρ
 in inj' (rd1 va) (rd2 va) (cumul _ _ j≤k (rel va))

fund-conversion' : ∀ {γ a1 a2 a3 a4 i j k t1 t2} {Γ : ⊨ γ ctx}
 -> {A1 : Γ ⊨ a1 ≈ a2 type i}
 -> (A2 : Γ ⊨ a4 ≈ a3 type j)
 -> (A : Γ ⊨ a1 ≈ a3 type k)
 -> Γ ⊨ t1 ≈ t2 ∶ A1
 -> Γ ⊨ t1 ≈ t2 ∶ A2
fund-conversion' {A1 = A1} A2 A t ρ =
 let q0 = irrL _ _ (rel (A1 ρ)) (eval-deter (rd1 (A1 ρ)) (rd1 (A ρ))) (rel (A ρ)) (rel (t ρ))
     q1 = irrR _ _ (rel (A ρ)) (eval-deter (rd2 (A ρ)) (rd2 (A2 ρ))) (rel (A2 ρ)) q0
 in inj' (rd1 (t ρ)) (rd2 (t ρ)) q1

fund-conversion'' : ∀ {γ a1 a2 a3 a4 i j k t1 t2} {Γ : ⊨ γ ctx}
 -> {A1 : Γ ⊨ a2 ≈ a1 type i}
 -> (A2 : Γ ⊨ a3 ≈ a4 type j)
 -> (A : Γ ⊨ a3 ≈ a1 type k)
 -> Γ ⊨ t1 ≈ t2 ∶ A1
 -> Γ ⊨ t1 ≈ t2 ∶ A2
fund-conversion'' {A1 = A1} A2 A t ρ =
 let q0 = irrR _ _ (rel (A1 ρ)) (eval-deter (rd2 (A1 ρ)) (rd2 (A ρ))) (rel (A ρ)) (rel (t ρ))
     q1 = irrL _ _ (rel (A ρ)) (eval-deter (rd1 (A ρ)) (rd1 (A2 ρ))) (rel (A2 ρ)) q0
 in inj' (rd1 (t ρ)) (rd2 (t ρ)) q1

fund-conversion : ∀ {γ a1 a2 a3 a4 i j k t1 t2} {Γ : ⊨ γ ctx}
 -> {A1 : Γ ⊨ a1 ≈ a2 type i}
 -> {A2 : Γ ⊨ a3 ≈ a4 type j}
 -> (A : Γ ⊨ a1 ≈ a3 type k)
 -> Γ ⊨ t1 ≈ t2 ∶ A1
 -> Γ ⊨ t1 ≈ t2 ∶ A2
fund-conversion {A1 = A1} {A2 = A2} A t ρ =
 let a3a4 = fund-sym-tp A2
     a3a3 = fund-trans-tp A2 a3a4
     q0 = fund-conversion' {A1 = A1} a3a4 A t
     q1 = fund-conversion'' {A1 = a3a4} A2 a3a3 q0 ρ
 in q1
-- Hmm there are too many combinations of this and it seems somewhat arbitrary which one we use?

unbox-lem : ∀ {n1 n2}
 -> (vn : n1 ≈ n2 ∈ NatR)
 -> natval (proj₁ (red1 vn)) ≈ n2 ∈ NatR
unbox-lem (inj (_ , natval) (_ , r2) rel) = inj' natval r2 rel
unbox-lem (inj (._ , neu) (_ , r2) rel) = inj' natval r2 rel

fund-plus-sub : ∀ {γ1 γ2 δ1 δ2 t1 t1' t2 t2' σ σ' j} {Γ : ⊨ γ1 ≈ γ2 ctx} {Δ : ⊨ δ1 ≈ δ2 ctx}
 -> Γ ⊨ t1 ≈ t1' ∶ (Nats j)
 -> Γ ⊨ t2 ≈ t2' ∶ (Nats j)
 -> Δ ⊨s σ ≈ σ' ∶ Γ
 -> Δ ⊨ (t1 ⊕ t2) [ σ ] ≈ (t1' [ σ' ] ⊕ t2' [ σ' ]) ∶ (Nats j)
fund-plus-sub t1 t2 σ ρ =
 let vσ = σ ρ
     v1 = t1 (rel vσ)
     v2 = t2 (rel vσ)
 in inj' (plus (rd1 v1) (rd1 v2) (rd1 (rel v1)) (rd1 (rel v2)) [ rd1 vσ ])
         (plus ((rd2 v1) [ (rd2 vσ) ]) ((rd2 v2) [ (rd2 vσ) ]) (rd2 (rel v1)) (rd2 (rel v2)))
         (inj' natval natval (fund-plus' (rel (rel v1)) (rel (rel v2))))

open import Candidate

-- TODO: Refactor this mess
fund-rec' : ∀ {t tz ts n1 n2 j k}
 -> (T : (⊡ , Nats j) ⊨ t type k)
 -> ⊡ ⊨ tz ∶ (Nats j >h T • (fund-zero {k = j}))
 -> ((⊡ , Nats j) , T) ⊨ ts ∶ (_>_•_ {Γ = (⊡ , Nats j) , T} (⊡ , (Nats j)) T (fund-, {Γ = (⊡ , Nats j) , T} (Nats j) (fund-⊡ {Γ = (⊡ , Nats j) , T}) (fund-suc {k = j} {Γ = (⊡ , Nats j) , T} (fund-idx' {Γ = (⊡ , Nats j) , T} (pop top) (pop top)))))
 -> (vn : n1 ≈ n2 ∈ NatV)
 -> (rec t , tz , ts , n1) ≈ (rec t , tz , ts , n2) ∈ Clo _↘r_ ⟦ T (⊡ , inj' natval natval vn) ⟧tp
fund-rec' dT dtz dts zero = inj' (zero (rd1 (dtz ⊡))) (zero (rd2 (dtz ⊡))) (rel (dtz ⊡))
fund-rec' dT dtz dts (suc x) =
 let vx = fund-rec' dT dtz dts x
     vtx = dts ((⊡ , (inj' natval natval x)) , (rel vx))
 in inj' (suc (rd1 vx) (rd1 vtx)) (suc (rd2 vx) (rd2 vtx)) (rel vtx)
fund-rec' dT dtz dts (natneu x) =
 let vT = dT (⊡ , (inj' natval natval (natneu x)))
 in inj' (ne (rd1 vT)) (ne (rd2 vT)) (reflectω (rel vT) (λ n →
   let q = reifyNatNe x n in
   inj' (rec (rd1 q)) (rec (rd2 q)) (cong (rec _ _ _) (rel q))))

-- TODO: If I make _⊨_∶_ a record, will elaboration assume its injective enough to make this work without
-- having to specify implicits?
fund-rec : ∀ {γ1 γ2 t tz ts tn tn' j k} -> {Γ : ⊨ γ1 ≈ γ2 ctx}
 -> (T : (⊡ , Nats j) ⊨ t type k)
 -> ⊡ ⊨ tz ∶ (Nats j >h T • (fund-zero {k = j}))
 -> ((⊡ , Nats j) , T) ⊨ ts ∶( _>_•_ {Γ = (⊡ , Nats j) , T} (⊡ , (Nats j)) T (fund-, {Γ = (⊡ , Nats j) , T} {Δ = ⊡} (Nats j) (fund-⊡ {Γ = (⊡ , Nats j) , T}) (fund-suc {k = j} {Γ = (⊡ , Nats j) , T} (fund-idx' {Γ = (⊡ , Nats j) , T} (pop top) (pop top)))))
 -> (dn : Γ ⊨ tn ≈ tn' ∶ Nats j)
 -> Γ ⊨ (rec t tz ts tn) ≈ (rec t tz ts tn') ∶ ((⊡ , (Nats j)) > T • fund-, (Nats j) fund-⊡ dn)
fund-rec dT dtz dts dn ρ1≈ρ2 =
 let vn = dn ρ1≈ρ2
     q = fund-rec' dT dtz dts (rel (rel vn))
     q0 = irrLRF' eval-deter dT (⊡ , unbox-lem (rel vn)) (rel q)
      -- Is there a better way to arrange this so that I don't need to use irrLF here?
 in inj' (rec (rd1 vn) (rd1 (rel vn)) (rd1 q))
         (rec (rd2 vn) (rd2 (rel vn)) (rd2 q))
         q0

fund-rec'' : ∀ {t tz ts n1 n2 j k}
 -> (T : (⊡ , Nats j) ⊨ t type k)
 -> ⊡ ⊨ tz ∶ (Nats j >h T • (fund-zero {k = j}))
 -> let Δ = (⊡ , Nats j) , T
        u1 = fund-↑ ⊡ (Nats j)
        N0 = Nats j
        N1 = _>_•_ {Γ = ⊡ , Nats j} ⊡ N0 u1
        u2 = fund-↑ (⊡ , Nats j) T
        N2 = _>_•_ {Γ = Δ} (⊡ , Nats j) N1 u2
        z' : Δ ⊨ idx 1 ≈ idx 1 ∶ N2
        z' = fund-idx' {Γ = Δ} (pop top) (pop top)
        σ' : Δ ⊨s (⊡ , idx 1) ≈ (⊡ , idx 1) ∶ (⊡ , Nats j)
        σ' = fund-, {Γ = Δ} (Nats j) (fund-⊡ {Γ = Δ}) z'
        T' : Δ ⊨ t [ ⊡ , idx 1 ] type k
        T' = _>_•_ {Γ = Δ} (⊡ , Nats j) T σ' in
    Δ ⊨ ts ≈ ts ∶ T'
 -> (vn : n1 ≈ n2 ∈ NatV)
 -> (rec t , tz , ts , n1) ≈ (rec t , tz , ts , n2) ∈ Clo _↘r_ ⟦ T (⊡ , inj' natval natval vn) ⟧tp
fund-rec'' dT dtz dts = {!!}

-- TODO: Still need rec 0 and rec suc rules...

-- IMPORTANT TODO:  Show the "reify identity substitution" thing
