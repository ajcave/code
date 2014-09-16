module Model where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit
open import Data.Empty

_≈_∈⊤ : Dnf -> Dnf -> Set
↓[ A ] a ≈ ↓[ A₁ ] a₁ ∈⊤ = ∀ n → ∃ (λ v → Rnf n , a ∶ A ↘ v × Rnf n , a₁ ∶ A₁ ↘ v)

_≈_∈⊥ : Dne -> Dne -> Set
e ≈ e' ∈⊥ = ∀ n → ∃ (λ u → Rne n , e ↘ u × Rne n , e' ↘ u)

data _≈_∈Nat : Val -> Val -> Set where
 zero : zero ≈ zero ∈Nat
 suc : ∀ {a a'} -> a ≈ a' ∈Nat -> suc a ≈ suc a' ∈Nat
 neu : ∀ {e e'} -> e ≈ e' ∈⊥ -> ↑[ Nat ] e ≈ ↑[ Nat ] e' ∈Nat

REL : Set₁
REL = Val -> Val -> Set

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

ΠREL : (A : REL) -> (∀ {a a'} -> A a a' -> REL) -> REL
ΠREL A F f f' = ∀ {a a'} -> (p : A a a') -> f · a ≈ f' · a' ∈App (F p)

syntax ΠREL A F f f' = f ≈ f' ∈Π A , F

data NeuRel : REL where
 inj : ∀ {e1 E1 e2 E2} -- -> E1 ≈ E ∈⊥ -> E2 ≈ E ∈⊥  -- TODO! ?
     -> e1 ≈ e2 ∈⊥ -> NeuRel (↑[ E1 ] e1) (↑[ E2 ] e2)

mutual
 data _≈_∈Set : Val -> Val -> Set where
  Neu : ∀ {E E'} -> E ≈ E' ∈⊥ -> ↑[ Set* ] E ≈ ↑[ Set* ] E' ∈Set
  Nat : Nat ≈ Nat ∈Set
  Π : ∀ {A A' F F'} (pA : A ≈ A' ∈Set)
   -> F ≈ F' ∈Π (El pA) , (λ _ -> _≈_∈Set)
   -> (Π A F) ≈ (Π A' F') ∈Set

 El : ∀ {A A'} -> A ≈ A' ∈Set -> REL
 El (Neu x) = NeuRel
 El Nat = _≈_∈Nat
 El (Π pA pF) = ΠREL (El pA) (λ p → El (_·_≈_·_∈App_.rel (pF p)))

--syntax El _≈_∈⟦_⟧_ : Val -> Val -> 

⟦_⟧tp : ∀ {T ρ ρ'} -> ⟦ T ⟧ ρ ≈⟦ T ⟧ ρ' ∈ _≈_∈Set -> REL
⟦ vT ⟧tp = El (⟦_⟧_≈⟦_⟧_∈_.rel vT)

_≈_∈⟦_⟧tp : Val -> Val -> ∀ {T ρ ρ'} -> ⟦ T ⟧ ρ ≈⟦ T ⟧ ρ' ∈ _≈_∈Set -> Set
a ≈ a' ∈⟦ pT ⟧tp = ⟦ pT ⟧tp a a'

mutual
 ⊨_ctx : Ctx -> Set
 ⊨ ⊡ ctx = ⊤
 ⊨ (Γ , T) ctx = Σ (⊨ Γ ctx) (λ vΓ → ∀ {ρ ρ'} → ρ ≈ ρ' ∈⟦ Γ , vΓ ⟧ → ⟦ T ⟧ ρ ≈⟦ T ⟧ ρ' ∈ _≈_∈Set)

 ⟦_,_⟧ctx : (Γ : Ctx) -> ⊨ Γ ctx -> EnvREL
 ⟦_,_⟧ctx ⊡ tt ⊡ ⊡ = ⊤
 ⟦_,_⟧ctx (Γ , T) (vΓ , vT) (ρ , a) (ρ' , a') = Σ (ρ ≈ ρ' ∈⟦ Γ , vΓ ⟧) (λ vρ → a ≈ a' ∈⟦ vT vρ ⟧tp)
 ⟦_,_⟧ctx _ _ _ _ = ⊥

 _≈_∈⟦_,_⟧ : Env -> Env -> (Γ : Ctx) -> ⊨ Γ ctx -> Set
 ρ ≈ ρ' ∈⟦ Γ , vΓ ⟧ = ⟦ Γ , vΓ ⟧ctx ρ ρ'

_⊨_type : Ctx -> Exp -> Set
Γ ⊨ T type = Σ (⊨ Γ ctx) (λ vΓ → ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈⟦ Γ , vΓ ⟧) → ⟦ T ⟧ ρ ≈⟦ T ⟧ ρ' ∈ _≈_∈Set)

_⊨_≈_∶_ : Ctx -> Exp -> Exp -> Exp -> Set
Γ ⊨ t ≈ t' ∶ T = Σ (Γ ⊨ T type)
  (λ {(vΓ , vT) -> ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈⟦ Γ , vΓ ⟧) → ⟦ t ⟧ ρ ≈⟦ t' ⟧ ρ' ∈ ⟦ vT vρ ⟧tp })

_⊨_∶_ : Ctx -> Exp -> Exp -> Set
Γ ⊨ t ∶ T    =    Γ ⊨ t ≈ t ∶ T

_⊨s_≈_∶_ : Ctx -> Subst -> Subst -> Ctx -> Set
Γ ⊨s σ ≈ σ' ∶ Δ = Σ (⊨ Γ ctx) (λ vΓ → Σ (⊨ Δ ctx) (λ vΔ →
  ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈⟦ Γ , vΓ ⟧) → ⟦ σ ⟧s ρ ≈⟦ σ' ⟧s ρ' ∈ ⟦ Δ , vΔ ⟧ctx))

