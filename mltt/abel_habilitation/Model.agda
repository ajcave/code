module Model where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Nat
open import WfNat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Util

REL = PREL Val

_≈_∈_ : ∀ {α} -> α -> α -> PREL α -> Set
a ≈ b ∈ A = A a b

⊤' : PREL Dnf
⊤' (↓[ A ] a) (↓[ A₁ ] a₁) = ∀ n → ∃ (λ v → Rnf n , a ∶ A ↘ v × Rnf n , a₁ ∶ A₁ ↘ v)

⊥' : PREL Dne
⊥' e e' = ∀ n → ∃ (λ u → Rne n , e ↘ u × Rne n , e' ↘ u)

data NatR : REL where
 zero : zero ≈ zero ∈ NatR
 suc : ∀ {a a'} -> a ≈ a' ∈ NatR -> suc a ≈ suc a' ∈ NatR
 neu : ∀ {e e'} -> e ≈ e' ∈ ⊥' -> ↑[ Nat ] e ≈ ↑[ Nat ] e' ∈ NatR

EnvREL : Set₁
EnvREL = Env -> Env -> Set

--record 

record App (B : REL) (c1 c2 : Comp) : Set where
 constructor inj
 field
  b1 : Val
  b2 : Val
  red1 : c1 ↘ b1
  red2 : c2 ↘ b2
  rel : B b1 b2

App→ : ∀ {B B'} -> B →₂ B' -> App B →₂ App B'
App→ f (inj b1 b2 red1 red2 rel) = inj _ _ red1 red2 (f rel)

AppDeter1 :  ∀ {c1 c2 c3 B B'} 
    (p : c1 ≈ c2 ∈ App B)
    (q : c2 ≈ c3 ∈ App B')
   -> App.b2 p ≡ App.b1 q
AppDeter1 (inj b1 b2 red1 red2 rel)
          (inj b3 b4 red3 red4 rel') = eval-deter red2 red3

AppDeter2 :  ∀ {c1 c2 c3 B B'} 
    (p : c1 ≈ c2 ∈ App B)
    (q : c2 ≈ c3 ∈ App B')
   -> App.b1 q ≡ App.b2 p 
AppDeter2 p q = sym (AppDeter1 p q)

AppDeter3 :  ∀ {c1 c2 c3 B B'} 
    (p : c1 ≈ c2 ∈ App B)
    (q : c1 ≈ c3 ∈ App B')
   -> App.b1 p ≡ App.b1 q
AppDeter3 (inj b1 b2 red1 red2 rel)
          (inj b3 b4 red3 red4 rel') = eval-deter red1 red3 

AppDeter4 :  ∀ {c1 c2 c3 B B'} 
    (p : c2 ≈ c1 ∈ App B)
    (q : c3 ≈ c1 ∈ App B')
   -> App.b2 p ≡ App.b2 q
AppDeter4 (inj b1 b2 red1 red2 rel)
          (inj b3 b4 red3 red4 rel') = eval-deter red2 red4

record ⟦_⟧s_≈⟦_⟧s_∈_ σ ρ σ' ρ' (B : EnvREL) : Set where
 field
  ρ1 : Env
  ρ2 : Env
  red1 : ⟦ σ  ⟧s ρ  ↘ ρ1
  red2 : ⟦ σ' ⟧s ρ' ↘ ρ2
  rel : B ρ1 ρ2

ΠR : (A : REL) -> (∀ {a a'} -> A a a' -> REL) -> REL
ΠR A F f f' = ∀ {a a'} -> (p : A a a') -> (f · a) ≈ (f' · a') ∈ (App (F p))

data NeuRel : REL where
 inj : ∀ {e1 E1 e2 E2} -- -> E1 ≈ E ∈⊥ -> E2 ≈ E ∈⊥  -- TODO! ?
     -> e1 ≈ e2 ∈ ⊥' -> NeuRel (↑[ E1 ] e1) (↑[ E2 ] e2)

module SetF (k : ℕ) (SetP : ∀ {j} -> j < k -> REL) where
 mutual
  data SetR : Val -> Val -> Set where
   Neu : ∀ {j E E'} -> E ≈ E' ∈ ⊥' -> j ≤ k -> ↑[ Set* j ] E ≈ ↑[ Set* j ] E' ∈ SetR
   Nat : Nat ≈ Nat ∈ SetR
   Π : ∀ {A A' F F'} (pA : A ≈ A' ∈ SetR)
    -> (pF : F ≈ F' ∈ ΠR (El pA) (λ _ -> SetR))
    -> (Π A F) ≈ (Π A' F') ∈ SetR
   Set* : ∀ {j} -> j < k -> Set* j ≈ Set* j ∈ SetR

  El : ∀ {A A'} -> A ≈ A' ∈ SetR -> REL
  El (Neu {E} _ x) = NeuRel
  El Nat = NatR
  El (Π pA pF) = ΠR (El pA) (λ p → El (App.rel (pF p)))
  El (Set* j<k) = SetP j<k

SetU' : {n : ℕ} -> Acc n -> REL
SetU' {n} (inj f) = SetF.SetR n (λ p → SetU' (f p))

SetU : ℕ -> REL
SetU n = SetU' (nat-acc {n})

Type : REL
Type A B = ∃ (λ n → SetU n A B)

ElU' : {n : ℕ} (p : Acc n) -> ∀ {A A'} -> A ≈ A' ∈ (SetU' p) -> REL
ElU' {n} (inj p) = SetF.El n (λ q → SetU' (p q))

ElU : (n : ℕ) -> ∀ {A A'} -> A ≈ A' ∈ (SetU n) -> REL
ElU n = ElU' (nat-acc {n})

[_] : ∀ {A A'} -> A ≈ A' ∈ Type -> REL
[ n , pA ] = ElU n pA

⟦_⟧tp : ∀ {c1 c2} -> c1 ≈ c2 ∈ App Type -> REL
⟦ vT ⟧tp = [ App.rel vT ]

mutual
 ⊨_ctx : Ctx -> Set
 ⊨ ⊡ ctx = ⊤
 ⊨ (Γ , T) ctx = Σ (⊨ Γ ctx) (λ vΓ → ∀ {ρ ρ'} → ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx → ⟦ T ⟧ ρ ≈ ⟦ T ⟧ ρ' ∈ App Type)

 ⟦_,_⟧ctx : (Γ : Ctx) -> ⊨ Γ ctx -> EnvREL
 ⟦_,_⟧ctx ⊡ tt ⊡ ⊡ = ⊤
 ⟦_,_⟧ctx (Γ , T) (vΓ , vT) (ρ , a) (ρ' , a') = Σ (ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx) (λ vρ → a ≈ a' ∈ ⟦ vT vρ ⟧tp)
 ⟦_,_⟧ctx _ _ _ _ = ⊥

_⊨'_type[_] : (Γ : Ctx) -> Exp -> ⊨ Γ ctx -> Set
Γ ⊨' T type[ vΓ ] = ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx) → ⟦ T ⟧ ρ ≈ ⟦ T ⟧ ρ' ∈ App Type

_⊨_type : Ctx -> Exp -> Set
Γ ⊨ T type = Σ (⊨ Γ ctx) (λ vΓ → Γ ⊨' T type[ vΓ ])

_⊨'_≈_∶_[_] : (Γ : Ctx) -> Exp -> Exp -> (T : Exp) -> Γ ⊨ T type -> Set
Γ ⊨' t ≈ t' ∶ T [ vΓ , vT ] =
  ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx) → ⟦ t ⟧ ρ ≈ ⟦ t' ⟧ ρ' ∈ App ⟦ vT vρ ⟧tp

_⊨_≈_∶_ : Ctx -> Exp -> Exp -> Exp -> Set
Γ ⊨ t ≈ t' ∶ T = Σ (Γ ⊨ T type)
  (λ p -> Γ ⊨' t ≈ t' ∶ T [ p ] )

_⊨_∶_ : Ctx -> Exp -> Exp -> Set
Γ ⊨ t ∶ T    =    Γ ⊨ t ≈ t ∶ T

_⊨s_≈_∶_ : Ctx -> Subst -> Subst -> Ctx -> Set
Γ ⊨s σ ≈ σ' ∶ Δ = Σ (⊨ Γ ctx) (λ vΓ → Σ (⊨ Δ ctx) (λ vΔ →
  ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx) → ⟦ σ ⟧s ρ ≈⟦ σ' ⟧s ρ' ∈ ⟦ Δ , vΔ ⟧ctx))

_⊨s_∶_ : Ctx -> Subst -> Ctx -> Set
Γ ⊨s σ ∶ Δ    =    Γ ⊨s σ ≈ σ ∶ Δ
