module Model where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit
open import Data.Empty

PREL : Set -> Set₁
PREL α = α -> α -> Set

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

record _·_≈_·_∈App_ (f a f' a' : Val) (B : REL) : Set where
 field
  b1 : Val
  b2 : Val
  red1 : f  · a  ↘ b1
  red2 : f' · a' ↘ b2
  rel : B b1 b2

record ⟦_⟧_≈⟦_⟧_∈_ t ρ t' ρ' (B : REL) : Set where
 field
  b1 : Val
  b2 : Val
  red1 : ⟦ t  ⟧ ρ  ↘ b1
  red2 : ⟦ t' ⟧ ρ' ↘ b2
  rel : B b1 b2

record ⟦_⟧s_≈⟦_⟧s_∈_ σ ρ σ' ρ' (B : EnvREL) : Set where
 field
  ρ1 : Env
  ρ2 : Env
  red1 : ⟦ σ  ⟧s ρ  ↘ ρ1
  red2 : ⟦ σ' ⟧s ρ' ↘ ρ2
  rel : B ρ1 ρ2

ΠR : (A : REL) -> (∀ {a a'} -> A a a' -> REL) -> REL
ΠR A F f f' = ∀ {a a'} -> (p : A a a') -> f · a ≈ f' · a' ∈App (F p)

syntax ΠR A F f f' = f ≈ f' ∈Π A , F

data NeuRel : REL where
 inj : ∀ {e1 E1 e2 E2} -- -> E1 ≈ E ∈⊥ -> E2 ≈ E ∈⊥  -- TODO! ?
     -> e1 ≈ e2 ∈ ⊥' -> NeuRel (↑[ E1 ] e1) (↑[ E2 ] e2)

mutual
 data SetR : Val -> Val -> Set where
  Neu : ∀ {E E'} -> E ≈ E' ∈ ⊥' -> ↑[ Set* ] E ≈ ↑[ Set* ] E' ∈ SetR
  Nat : Nat ≈ Nat ∈ SetR
  Π : ∀ {A A' F F'} (pA : A ≈ A' ∈ SetR)
   -> F ≈ F' ∈ ΠR (El pA) (λ _ -> SetR)
   -> (Π A F) ≈ (Π A' F') ∈ SetR

 El : ∀ {A A'} -> A ≈ A' ∈ SetR -> REL
 El (Neu x) = NeuRel
 El Nat = NatR
 El (Π pA pF) = ΠR (El pA) (λ p → El (_·_≈_·_∈App_.rel (pF p)))

⟦_⟧tp : ∀ {T ρ ρ'} -> ⟦ T ⟧ ρ ≈⟦ T ⟧ ρ' ∈ SetR -> REL
⟦ vT ⟧tp = El (⟦_⟧_≈⟦_⟧_∈_.rel vT)

mutual
 ⊨_ctx : Ctx -> Set
 ⊨ ⊡ ctx = ⊤
 ⊨ (Γ , T) ctx = Σ (⊨ Γ ctx) (λ vΓ → ∀ {ρ ρ'} → ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx → ⟦ T ⟧ ρ ≈⟦ T ⟧ ρ' ∈ SetR)

 ⟦_,_⟧ctx : (Γ : Ctx) -> ⊨ Γ ctx -> EnvREL
 ⟦_,_⟧ctx ⊡ tt ⊡ ⊡ = ⊤
 ⟦_,_⟧ctx (Γ , T) (vΓ , vT) (ρ , a) (ρ' , a') = Σ (ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx) (λ vρ → a ≈ a' ∈ ⟦ vT vρ ⟧tp)
 ⟦_,_⟧ctx _ _ _ _ = ⊥

_⊨_type : Ctx -> Exp -> Set
Γ ⊨ T type = Σ (⊨ Γ ctx) (λ vΓ → ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx) → ⟦ T ⟧ ρ ≈⟦ T ⟧ ρ' ∈ SetR)

_⊨_≈_∶_ : Ctx -> Exp -> Exp -> Exp -> Set
Γ ⊨ t ≈ t' ∶ T = Σ (Γ ⊨ T type)
  (λ {(vΓ , vT) -> ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx) → ⟦ t ⟧ ρ ≈⟦ t' ⟧ ρ' ∈ ⟦ vT vρ ⟧tp })

_⊨_∶_ : Ctx -> Exp -> Exp -> Set
Γ ⊨ t ∶ T    =    Γ ⊨ t ≈ t ∶ T

_⊨s_≈_∶_ : Ctx -> Subst -> Subst -> Ctx -> Set
Γ ⊨s σ ≈ σ' ∶ Δ = Σ (⊨ Γ ctx) (λ vΓ → Σ (⊨ Δ ctx) (λ vΔ →
  ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ , vΓ ⟧ctx) → ⟦ σ ⟧s ρ ≈⟦ σ' ⟧s ρ' ∈ ⟦ Δ , vΔ ⟧ctx))

_⊨s_∶_ : Ctx -> Subst -> Ctx -> Set
Γ ⊨s σ ∶ Δ    =    Γ ⊨s σ ≈ σ ∶ Δ