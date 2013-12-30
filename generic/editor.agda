module editor where
open import Data.Nat
open import Data.Product

data Func : Set₁ where
 `Σ `Π : (A : Set) -> (f : (l : A) -> Func) -> Func
 ▹ : Set -> Func
 `X : Func

⟦_⟧ : Func -> Set -> Set
⟦_⟧ (`Σ A f) X = Σ A (λ l → ⟦ f l ⟧ X)
⟦_⟧ (`Π A f) X = (l : A) → ⟦ f l ⟧ X
⟦_⟧ (▹ A) X = A
⟦_⟧ `X X = X

data μ (F : Func) : Set where
 inj : ⟦ F ⟧ (μ F) -> μ F

data ProdLab : Set where `fst `snd : ProdLab

_⊗_ : Func -> Func -> Func
F ⊗ G = `Π ProdLab (λ {`fst → F; `snd → G})

⨁ : {A : Set} -> (f : (l : A) -> Func) -> Func
⨁ f = `Σ _ f


data ExpLab : Set where `lam `app `var : ExpLab

ExpF = ⨁ (λ { `lam -> `X;
              `app -> `X ⊗ `X;
              `var -> ▹ ℕ })

Exp = μ ExpF

data exp : Set where
 lam : exp -> exp
 app : exp -> exp -> exp
 var : ℕ -> exp

conv : Exp -> exp
conv (inj (`lam , e)) = lam (conv e)
conv (inj (`app , es)) = app (conv (es `fst)) (conv (es `snd))
conv (inj (`var , x)) = var x
