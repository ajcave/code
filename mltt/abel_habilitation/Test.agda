{-# OPTIONS --copatterns #-}
module Test where
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

record Comb2 {A B C : Set} (R : PREL A) (red : B × A -> C -> Set) (F : ∀ {a a'} -> a ≈ a' ∈ R -> PREL C) (T1 T2 : B) : Set where
 constructor inj
 field
  out : T1 ≈ T2 ∈ (Π* red R F)
open Comb2

mutual
 data ⊨₂_≈_ctx : Ctx -> Ctx -> Set where
  ⊡ : ⊨₂ ⊡ ≈ ⊡ ctx
  _,_ : ∀ {γ1 γ2 t1 t2 k} -> (Γ : ⊨₂ γ1 ≈ γ2 ctx) -> Γ ⊨₂ t1 ≈ t2 type' k
       -> ⊨₂ (γ1 , t1) ≈ (γ2 , t2) ctx
  
 _⊨₂_≈_type'_ : ∀ {γ1 γ2 : Ctx} (Γ : ⊨₂ γ1 ≈ γ2 ctx) (T1 T2 : Exp) (k : ℕ) -> Set 
 Γ ⊨₂ t1 ≈ t2 type' k = t1 ≈ t2 ∈ Comb2 ⟦ Γ ⟧hctx₂ _↘_ (λ _ -> SetU k)

 ⟦_⟧hctx₂ : {Γ1 Γ2 : Ctx} -> ⊨₂ Γ1 ≈ Γ2 ctx -> EnvREL
 ⟦ ⊡ ⟧hctx₂ = EmpRel
 ⟦ Γ , T ⟧hctx₂ = Comb ⟦ Γ ⟧hctx₂ (λ vρ -> ⟦ out T vρ ⟧tp)

_⊨₂_≈_type_ : ∀ {γ1 γ2 : Ctx} (Γ : ⊨₂ γ1 ≈ γ2 ctx) (T1 T2 : Exp) (k : ℕ) -> Set 
Γ ⊨₂ t1 ≈ t2 type k = t1 ≈ t2 ∈ Comb2 ⟦ Γ ⟧hctx₂ _↘_ (λ _ -> SetU k)

_∋m₂_∶_ : ∀ {γ1 γ2} (Γ : ⊨₂ γ1 ≈ γ2 ctx) {k} -> ℕ -> {T1 T2 : Exp} -> Γ ⊨₂ T1 ≈ T2 type k -> Set
Γ ∋m₂ x ∶ T  = x ≈ x ∈ Π* lookup_↘_ ⟦ Γ ⟧hctx₂ (λ vρ -> ⟦ out T vρ ⟧tp)

record _⊨₂_≈_∶_ {γ1 γ2} (Γ : ⊨₂ γ1 ≈ γ2 ctx) {k} (t t' : Exp) {T1 T2 : Exp} (A : Γ ⊨₂ T1 ≈ T2 type k) : Set where
 constructor inj
 field
  out₂ : t ≈ t' ∈ Π* _↘_ ⟦ Γ ⟧hctx₂ (λ vρ -> ⟦ out A vρ ⟧tp)
open _⊨₂_≈_∶_

_⊨₂_type_ : {Γ : Ctx} -> ⊨₂ Γ ≈ Γ ctx -> Exp -> ℕ -> Set
Γ ⊨₂ T type k  = Γ ⊨₂ T ≈ T type k 

record _⊨s₂_≈_∶_ {γ1 γ2 δ1 δ2} (Γ : ⊨₂ γ1 ≈ γ2 ctx) (σ1 σ2 : Subst) (Δ : ⊨₂ δ1 ≈ δ2 ctx) : Set where
 constructor inj
 field
  out₃ : ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ ⟧hctx₂) → ⟦ σ1 ⟧ ρ ≈ ⟦ σ2 ⟧ ρ' ∈ (Clo _↘s_ ⟦ Δ ⟧hctx₂)
open _⊨s₂_≈_∶_

_>_•_ : ∀ {γ1 γ2 δ1 δ2 b1 b2 σ1 σ2 k} {Γ : ⊨₂ γ1 ≈ γ2 ctx} (Δ : ⊨₂ δ1 ≈ δ2 ctx) 
 -> Δ ⊨₂ b1 ≈ b2 type  k
 -> Γ ⊨s₂ σ1 ≈ σ2 ∶ Δ
 -> Γ ⊨₂ b1 [ σ1 ] ≈ b2 [ σ2 ] type k
Δ > B • σ = inj (λ ρ1≈ρ2 -> 
 let vσ = out₃ σ ρ1≈ρ2 in
 let vb = out B (rel vσ) in
 inj' (rd1 vb [ rd1 vσ ])
      (rd2 vb [ rd2 vσ ])
      (rel vb))

fund-⊡ : ∀ {γ1 γ2} {Γ : ⊨₂ γ1 ≈ γ2 ctx}
 -> Γ ⊨s₂ ⊡ ≈ ⊡ ∶ ⊡
out₃ fund-⊡ ρ1≈ρ2 = inj' ⊡ ⊡ ⊡

fund-, : ∀ {γ1 γ2 δ1 δ2 σ σ' t t' a1 a2 k} {Γ : ⊨₂ γ1 ≈ γ2 ctx} {Δ : ⊨₂ δ1 ≈ δ2 ctx}
 -> (A : Δ ⊨₂ a1 ≈ a2 type k)
 -> (dσ : Γ ⊨s₂ σ ≈ σ' ∶ Δ)
 -> Γ ⊨₂ t ≈ t' ∶ (Δ > A • dσ)
 -> Γ ⊨s₂ σ , t ≈ σ' , t' ∶ (Δ , A)
out₃ (fund-, A dσ dt) dρ =
 let vσ = out₃ dσ dρ
     vt = out₂ dt dρ in
 inj' (rd1 vσ , rd1 vt)
      (rd2 vσ , rd2 vt)
      (rel vσ , rel vt) 

fund-id : ∀ {γ1 γ2} {Γ : ⊨₂ γ1 ≈ γ2 ctx} -> Γ ⊨s₂ T.id ≈ T.id ∶ Γ
fund-id = inj (inj (, Eval.id) (, Eval.id))

_>h_•_ : ∀ {γ1 γ2 a1 a2 b1 b2 t1 t2 j k} {Γ : ⊨₂ γ1 ≈ γ2 ctx} (A : Γ ⊨₂ a1 ≈ a2 type k) 
 -> (Γ , A) ⊨₂ b1 ≈ b2 type j
 -> Γ ⊨₂ t1 ≈ t2 ∶ A
 -> Γ ⊨₂ b1 [ T.id , t1 ] ≈ b2 [ T.id , t2 ] type j
A >h B • t = (_ , A) > B • fund-, A fund-id (inj (out₂ t)) --(_ , A) > B • fund-, A fund-id t

Nats : ∀ {γ1 γ2} k {Γ : ⊨₂ γ1 ≈ γ2 ctx} -> Γ ⊨₂ Nat ≈ Nat type k
out (Nats k) ρ1≈ρ2 = inj (, Nat) (, Nat) Nat


fund-zero : ∀ {γ1 γ2 k} {Γ : ⊨₂ γ1 ≈ γ2 ctx}
 -> Γ ⊨₂ zero ≈ zero ∶ Nats k
out₂ fund-zero ρ1≈ρ2 = inj' zero zero (inj' natval natval zero)

fund-suc : ∀ {γ1 γ2 t s k} {Γ : ⊨₂ γ1 ≈ γ2 ctx} 
 -> Γ ⊨₂ t ≈ s ∶ Nats k
 -> Γ ⊨₂ suc t ≈ suc s ∶ Nats k
out₂ (fund-suc d) ρ1≈ρ2 =
 let vt = out₂ d ρ1≈ρ2 in
 inj' (suc (rd1 vt) (rd1 (rel vt))) (suc (rd2 vt) (rd2 (rel vt))) (inj' natval natval (suc (rel (rel vt))))

fund-↑ : ∀ {γ1 γ2 t1 t2 k} (Γ : ⊨₂ γ1 ≈ γ2 ctx) (T : Γ ⊨₂ t1 ≈ t2 type k)
 -> (Γ , T) ⊨s₂ ↑ ≈ ↑ ∶ Γ
out₃ (fund-↑ Γ T) (ρ1≈ρ2 , v1≈v2) = inj' ↑ ↑ ρ1≈ρ2

fund-lookuptp : ∀ {γ1 γ2 t1 t2 x}
 -> (Γ : ⊨₂ γ1 ≈ γ2 ctx)
 -> γ1 ∋ x ∶ t1
 -> γ2 ∋ x ∶ t2
 -> ∃ (λ k -> Γ ⊨₂ t1 ≈ t2 type k)
fund-lookuptp ⊡ () x2
fund-lookuptp (Γ , x) top top = _ , (_>_•_ {Γ = Γ , x} Γ x (fund-↑ Γ x))
fund-lookuptp (Γ₂ , x₁) (pop x1) (pop x2) =
 let q = fund-lookuptp Γ₂ x1 x2
 in _ , _>_•_ {Γ = Γ₂ , x₁} Γ₂ (proj₂ q) (fund-↑ Γ₂ x₁)


fund-lookup : ∀ {γ1 γ2 t1 t2 x}
 -> (Γ : ⊨₂ γ1 ≈ γ2 ctx)
 -> (x1 : γ1 ∋ x ∶ t1)
 -> (x2 : γ2 ∋ x ∶ t2)
 -> Γ ∋m₂ x ∶ (proj₂ (fund-lookuptp Γ x1 x2))
fund-lookup (Γ , x) top top (vρ , x₁) = inj' top top x₁
fund-lookup (Γ , x₁) (pop x1) (pop x2) (ρ1≈ρ2 , v1≈v2) =
 let q = fund-lookup Γ x1 x2 ρ1≈ρ2
 in inj' (pop (rd1 q)) (pop (rd2 q)) (rel q)

fund-idx : ∀ {γ1 γ2 t1 t2 k x}
 -> {Γ : ⊨₂ γ1 ≈ γ2 ctx}
 -> {T : Γ ⊨₂ t1 ≈ t2 type k}
 -> Γ ∋m₂ x ∶ T
 -> Γ ⊨₂ idx x ≈ idx x ∶ T
out₂ (fund-idx dx) ρ1≈ρ2 = inj' (idx (rd1 (dx ρ1≈ρ2))) (idx (rd2 (dx ρ1≈ρ2))) (rel (dx ρ1≈ρ2))

fund-idx' : ∀ {γ1 γ2 t1 t2 x}
 -> {Γ : ⊨₂ γ1 ≈ γ2 ctx}
 -> (x1 : γ1 ∋ x ∶ t1)
 -> (x2 : γ2 ∋ x ∶ t2)
 -> Γ ⊨₂ idx x ≈ idx x ∶ (proj₂ (fund-lookuptp Γ x1 x2))
fund-idx' {Γ = Γ} x1 x2 = fund-idx  {Γ = Γ} {T = proj₂ (fund-lookuptp Γ x1 x2)} (fund-lookup Γ x1 x2)

fund-rec' : ∀ {t tz ts n1 n2 j k}
 -> (T : (⊡ , Nats j) ⊨₂ t type k)
 -> ⊡ ⊨₂ tz ≈ tz ∶ (_ >h T • (fund-zero {k = j}))
 -> let Δ = (⊡ , Nats j) , T
        z' : Δ ⊨₂ idx 1 ≈ idx 1 ∶ _
        z' = fund-idx' (pop top) (pop top)
        σ' : Δ ⊨s₂ (⊡ , idx 1) ≈ (⊡ , idx 1) ∶ (⊡ , Nats j)
        σ' = fund-, _ fund-⊡ (inj (out₂ z'))
    in Δ ⊨₂ ts ≈ ts ∶ (_ > T • σ')
 -> (vn : n1 ≈ n2 ∈ NatV)
 -> (rec t , tz , ts , n1) ≈ (rec t , tz , ts , n2) ∈ Clo _↘r_ ⟦ out T (⊡ , inj' natval natval vn) ⟧tp
fund-rec' dT dtz dts = {!!}