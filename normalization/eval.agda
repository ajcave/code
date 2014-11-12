module eval where
open import Data.Nat
open import Data.Unit
open import Data.Product

data tp : Set where
 nat : tp
 _⇒_ : tp -> tp -> tp

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : ctx A -> A -> ctx A

data var : ctx tp -> tp -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ S -> var (Γ , T) S

data tm (Γ : ctx tp) : tp -> Set where
 _·_ : ∀ {T S} -> tm Γ (T ⇒ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇒ S)
 v : ∀ {T} -> var Γ T -> tm Γ T
 zero : tm Γ nat
 suc : tm Γ nat -> tm Γ nat

ex : tm ⊡ (nat ⇒ nat)
ex = ƛ (v top)

ex2 : tm ⊡ nat
ex2 = ex · zero

⟦_⟧t : tp -> Set
⟦ nat ⟧t = ℕ
⟦ y ⇒ y' ⟧t = ⟦ y ⟧t → ⟦ y' ⟧t

⟦_⟧c : ctx tp -> Set
⟦ ⊡ ⟧c = Unit
⟦ Γ , T ⟧c = ⟦ Γ ⟧c × ⟦ T ⟧t

data ⟦_⟧c' : ctx tp -> Set where
 ⊡ : ⟦ ⊡ ⟧c'
 _,_ : ∀ {Γ T} -> ⟦ Γ ⟧c' -> ⟦ T ⟧t -> ⟦ Γ , T ⟧c'

lookup : ∀ {Γ T} -> var Γ T -> ⟦ Γ ⟧c -> ⟦ T ⟧t
lookup top (ρ , x) = x
lookup (pop y) (ρ , x) = lookup y ρ

eval : ∀ {Γ T} -> tm Γ T -> ⟦ Γ ⟧c -> ⟦ T ⟧t
eval (y · y') ρ = eval y ρ (eval y' ρ)
eval (ƛ y) ρ = λ x → eval y (ρ , x)
eval (v y) ρ = lookup y ρ
eval zero ρ = 0
eval (suc y) ρ = 1 + eval y ρ

ex3 : ℕ
ex3 = eval ex2 unit