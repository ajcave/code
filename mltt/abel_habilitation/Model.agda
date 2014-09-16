module Model where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product

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

record _·_≈_·_∈App_ (f a f' a' : Val) (B : REL) : Set where
 field
  b1 : Val
  b2 : Val
  red1 : f  · a  ↘ b1
  red2 : f' · a' ↘ b2
  rel : B b1 b2

ΠREL : (A : REL) -> (∀ {a a'} -> A a a' -> REL) -> REL
ΠREL A F f f' = ∀ {a a'} -> (p : A a a') -> f · a ≈ f' · a' ∈App (F p)

syntax ΠREL A F f f' = f ≈ f' ∈Π A , F

mutual
 data _≈_∈Set : Val -> Val -> Set where
  Neu : ∀ {E E'} -> E ≈ E' ∈⊥ -> ↑[ Set* ] E ≈ ↑[ Set* ] E' ∈Set
  Nat : Nat ≈ Nat ∈Set
  Π : ∀ {A A' F F'} (pA : A ≈ A' ∈Set)
   -> F ≈ F' ∈Π (El pA) , (λ _ -> _≈_∈Set)
   -> (Π A F) ≈ (Π A' F') ∈Set

 El : ∀ {A A'} -> A ≈ A' ∈Set -> REL
 El (Neu x) = {!!}
 El Nat = _≈_∈Nat
 El (Π pA pF) = ΠREL (El pA) (λ p → El (_·_≈_·_∈App_.rel (pF p)))