{-# OPTIONS --no-positivity-check #-}
module semantics where
open import mu-ltl
open import Data.Sum
open import Data.Nat
open import FinMap
open import Coinduction
open import Product
open import Unit
open import Data.Empty

ωnat : Set
ωnat = ℕ ⊎ Unit

data _≤ω_ : ωnat -> ωnat -> Set where
 inj₁ : ∀ {n m} -> (n≤m : n ≤ m) -> (inj₁ n) ≤ω (inj₁ m)
 inj₂ : ∀ {α} -> α ≤ω (inj₂ tt)

≤ω-refl : ∀ {α} -> α ≤ω α
≤ω-refl {inj₁ x} = {!!}
≤ω-refl {inj₂ y} = inj₂

obj : Set₁
obj = ωnat -> Set

○⁺ : obj -> obj
○⁺ A (inj₁ zero) = Unit
○⁺ A (inj₁ (suc n)) = A (inj₁ n)
○⁺ A (inj₂ tt) = A (inj₂ tt)

_⊃⁺_ : obj -> obj -> obj
(A ⊃⁺ B) α = ∀ β → β ≤ω α → A β → B β

_∧⁺_ : obj -> obj -> obj
(A ∧⁺ B) α = A α × B α

_∨⁺_ : obj -> obj -> obj
(A ∨⁺ B) α = A α ⊎ B α

⊤⁺ : obj
⊤⁺ α = Unit

mutual
 data ν⁺ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) (α : ωnat) : Set where
  ⟨_⟩ : ∞ (⟦ F ⟧f (ρ , (ν⁺ F ρ)) α) -> ν⁺ F ρ α

 data μ⁺ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) (α : ωnat) : Set where
  ⟨_⟩ : ⟦ F ⟧f (ρ , (μ⁺ F ρ)) α -> μ⁺ F ρ α

 ⟦_⟧f : ∀ {Δ} -> functor Δ -> (ρ : gksubst Δ obj) -> obj
 ⟦_⟧f (▹ A) ρ = lookup ρ A
 ⟦_⟧f (μ F) ρ = μ⁺ F ρ
 ⟦_⟧f (ν F) ρ = ν⁺ F ρ
 ⟦_⟧f (○ A) ρ = ○⁺ (⟦ A ⟧f ρ)
 ⟦_⟧f (A ⊃ B) ρ = ⟦ A ⟧f tt ⊃⁺ ⟦ B ⟧f ρ
 ⟦_⟧f (A ∧ B) ρ = ⟦ A ⟧f ρ ∧⁺ ⟦ B ⟧f ρ
 ⟦_⟧f (A ∨ B) ρ = ⟦ A ⟧f ρ ∨⁺ ⟦ B ⟧f ρ
 ⟦_⟧f ⊤ ρ = ⊤⁺

⟦_⟧t : prop -> obj
⟦ A ⟧t = ⟦ A ⟧f tt

⟦_⟧c : ctx prop -> obj
⟦ ⊡ ⟧c = ⊤⁺
⟦ Γ , T ⟧c = ⟦ Γ ⟧c ∧⁺ ⟦ T ⟧t

Functorial : obj -> Set
Functorial A = ∀ {α β} -> β ≤ω α -> A α -> A β

○⁺f : ∀ {A} -> Functorial A -> Functorial (○⁺ A)
○⁺f F {inj₁ n} {inj₁ .0} (inj₁ z≤n) = λ x → tt
○⁺f F {inj₁ .(suc n)} {inj₁ .(suc m)} (inj₁ {suc m} {suc n} (s≤s m≤n)) = F (inj₁ m≤n)
○⁺f F {inj₂ .tt} {inj₁ zero} inj₂ = λ x → tt
○⁺f F {inj₂ .tt} {inj₁ (suc n)} inj₂ = F inj₂
○⁺f F {inj₁ x} {inj₂ y} ()
○⁺f F {inj₂ y} {inj₂ y'} x = λ x' → x'

mutual
 ⟦_⟧mf : ∀ {Δ} (F : functor Δ) {ρ : gksubst Δ obj} (P : gsubst-pred Functorial ρ) -> Functorial (⟦ F ⟧f ρ)
 ⟦_⟧mf (▹ A) ρ = lookup-pred ρ A
 ⟦_⟧mf (μ F) ρ = {!!}
 ⟦_⟧mf (ν F) ρ = {!!}
 ⟦_⟧mf (○ A) ρ = ○⁺f (⟦ A ⟧mf ρ)
 ⟦_⟧mf (A ⊃ B) ρ = {!!}
 ⟦_⟧mf (A ∧ B) ρ = {!!}
 ⟦_⟧mf (A ∨ B) ρ = {!!}
 ⟦_⟧mf ⊤ ρ = {!!}

_⇒_ : obj -> obj -> Set
A ⇒ B = ∀ α → A α → B α

_∘⁺_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C
f ∘⁺ g = λ α x → f α (g α x)

id⁺ : ∀ A -> A ⇒ A
id⁺ A α x = x

π₁⁺ : ∀ {A B} -> (A ∧⁺ B) ⇒ A
π₁⁺ α t = proj₁ t

π₂⁺ : ∀ {A B} -> (A ∧⁺ B) ⇒ B
π₂⁺ α t = proj₂ t

<_,_>⁺ : ∀ {A B C} -> A ⇒ B -> A ⇒ C -> A ⇒ (B ∧⁺ C)
< t , u >⁺ α x = (t α x) , (u α x)

-- TODO: Build up proofs of naturality at the same time by only using nice combinators
∧⁺-assoc' : ∀ A B C -> ((A ∧⁺ B) ∧⁺ C) ⇒ (A ∧⁺ (B ∧⁺ C))
∧⁺-assoc' A B C = < π₁⁺ ∘⁺ π₁⁺ , < (π₂⁺ ∘⁺ π₁⁺) , π₂⁺ >⁺ >⁺

∧⁺-assoc : ∀ {A B C} -> ((A ∧⁺ B) ∧⁺ C) ⇒ (A ∧⁺ (B ∧⁺ C))
∧⁺-assoc {A} {B} {C} = ∧⁺-assoc' A B C

λ⁺ : ∀ {Γ B C} -> (Γ ∧⁺ B) ⇒ C -> Γ ⇒ (B ⊃⁺ C)
λ⁺ t α γ β β≤α b = t β ({!!} , b)

_·⁺_ : ∀ {Γ B C} -> Γ ⇒ (B ⊃⁺ C) -> Γ ⇒ B -> Γ ⇒ C
(M ·⁺ N) α γ = M α γ α (≤ω-refl {α}) (N α γ)

⟦_⟧e : ∀ {θ Γ T} -> θ , Γ ⊢ T - true -> ((○⁺ (⟦ θ ⟧c)) ∧⁺ ⟦ Γ ⟧c) ⇒ ⟦ T ⟧t
⟦ ▹ x ⟧e = {!!}
⟦ ƛ M ⟧e = λ⁺ (⟦ M ⟧e ∘⁺ ∧⁺-assoc)
⟦ M · N ⟧e = ⟦ M ⟧e ·⁺ ⟦ N ⟧e
⟦ let-◦ M N ⟧e = {!!}
⟦ ◦ M ⟧e = {!!}
⟦ inj M ⟧e = {!!}
⟦ rec F M N ⟧e = {!!}
⟦ out M ⟧e = {!!}
⟦ mu-ltl.unfold F M N ⟧e = {!!}
⟦ < M , N > ⟧e = {!!}
⟦ fst M ⟧e = {!!}
⟦ snd M ⟧e = {!!}
⟦ inl M ⟧e = {!!}
⟦ inr M ⟧e = {!!}
⟦ case M N1 N2 ⟧e = {!!}
⟦ unit ⟧e = λ α _ → tt