module editor-multi where
open import Data.Nat
open import Data.Product
open import Data.Fin

data Func (Δ : ℕ) : Set₁ where
 `Σ `Π : (A : Set) -> (f : (l : A) -> Func Δ) -> Func Δ
 `μ : Func (suc Δ) -> Func Δ
 κ : Set -> Func Δ
 ▹ : Fin Δ -> Func Δ

Env : ∀ Δ -> Set₁
Env Δ = Fin Δ -> Set

Ext : ∀ {Δ} -> Env Δ -> Set -> Env (suc Δ)
Ext ρ A zero = A
Ext ρ A (suc x) = ρ x

mutual
 ⟦_⟧ : ∀ {Δ} -> Func Δ -> Env Δ -> Set
 ⟦_⟧ (`Σ A f) ρ = Σ A (λ l → ⟦ f l ⟧ ρ)
 ⟦_⟧ (`Π A f) ρ = (l : A) → ⟦ f l ⟧ ρ
 ⟦_⟧ (`μ F) ρ = μ F ρ
 ⟦_⟧ (κ A) ρ = A
 ⟦_⟧ (▹ X) ρ = ρ X

 data μ {Δ} (F : Func (suc Δ)) (ρ : Env Δ) : Set where
  inj : ⟦ F ⟧ (Ext ρ (μ F ρ)) -> μ F ρ

data ProdLab : Set where `fst `snd : ProdLab

_⊗_ : ∀ {Δ} -> Func Δ -> Func Δ -> Func Δ
F ⊗ G = `Π ProdLab (λ {`fst → F; `snd → G})

⨁ : ∀ {Δ} {A : Set} -> (f : (l : A) -> Func Δ) -> Func Δ
⨁ f = `Σ _ f

data ExpLab : Set where `lam `app `var : ExpLab

ExpF : Func 1
ExpF = ⨁ (λ { `lam -> ▹ zero;
              `app -> ▹ zero ⊗ ▹ zero;
              `var -> κ ℕ })

Exp = μ ExpF

{-
data exp : Set where
 lam : exp -> exp
 app : exp -> exp -> exp
 var : ℕ -> exp

conv : Exp -> exp
conv (inj (`lam , e)) = lam (conv e)
conv (inj (`app , es)) = app (conv (es `fst)) (conv (es `snd))
conv (inj (`var , x)) = var x -}
