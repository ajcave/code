module editor where
open import Data.Product

data Func : Set₁ where
 `Σ `Π : (A : Set) -> (f : (l : A) -> Func) -> Func
 `X : Func

⟦_⟧ : Func -> Set -> Set
⟦_⟧ (`Σ A f) X = Σ A (λ l → ⟦ f l ⟧ X)
⟦_⟧ (`Π A f) X = (l : A) → ⟦ f l ⟧ X
⟦_⟧ `X X = X

data μ (F : Func) : Set where
 inj : ⟦ F ⟧ (μ F) -> μ F

