module editor-mutual where
open import Data.Nat
open import Data.Product
open import Data.Fin
open import Data.Empty
open import Data.Unit

data Func (Δ : Set) : Set₁ where
 `Σ `Π : (A : Set) -> (f : (l : A) -> Func Δ) -> Func Δ
 _⊗_ : (F G : Func Δ) -> Func Δ
 κ : Set -> Func Δ
 ▹ : Δ -> Func Δ
 `1 : Func Δ

-- data ProdLab : Set where `fst `snd : ProdLab
-- _⊗_ : ∀ {Δ} -> Func Δ -> Func Δ -> Func Δ
-- F ⊗ G = `Π ProdLab (λ {`fst → F; `snd → G})

⨁ : ∀ {Δ} {A : Set} -> (f : (l : A) -> Func Δ) -> Func Δ
⨁ f = `Σ _ f

Defs : Set -> Set₁
Defs Δ = Δ -> Func Δ



Env : Set -> Set₁
Env Δ = Δ -> Set

⟦_⟧ : ∀ {Δ} -> Func Δ -> Env Δ -> Set
⟦_⟧ (`Σ A f) ρ = Σ A (λ l → ⟦ f l ⟧ ρ)
⟦_⟧ (`Π A f) ρ = (l : A) → ⟦ f l ⟧ ρ
⟦_⟧ (F ⊗ G) ρ = (⟦ F ⟧ ρ) × (⟦ G ⟧ ρ)
⟦_⟧ (κ A) ρ = A
⟦_⟧ (▹ X) ρ = ρ X
⟦_⟧ `1 ρ = Unit

-- Constructs them simultaneously using indexing
data μ {Δ} (Ds : Defs Δ) : Δ -> Set where
 inj : ∀ {l} -> ⟦ Ds l ⟧ (μ Ds) -> μ Ds l

data TypeLabs : Set where `tree `nodelist : TypeLabs
data ListLab : Set where `nil `cons : ListLab
data TreeLab : Set where `children : TreeLab

data ExpLab : Set where `exp : ExpLab

EFam : Defs ExpLab
EFam `exp = κ ℕ

⟦_⟧e : ExpLab -> Set
⟦ l ⟧e = μ EFam l

FamF : Defs TypeLabs
FamF `tree     = ⨁ (λ {`children → κ ⟦ `exp ⟧e ⊗ ▹ `nodelist})
FamF `nodelist = ⨁ (λ {`nil  → `1;
                      `cons → ▹ `tree ⊗ ▹ `nodelist})

-- mutual
--  data Tree : Set where
--   children : ℕ -> NodeList -> Tree
--  data NodeList : Set where
--   nil : NodeList
--   cons : Tree -> NodeList -> NodeList

⟦_⟧f : TypeLabs -> Set
⟦ l ⟧f = μ FamF l



mutual
 conv1 : ⟦ `tree ⟧f -> ⟦ `tree ⟧f
 conv1 (inj (`children , (n , ts))) = inj (`children , (n , conv2 ts))

 conv2 : ⟦ `nodelist ⟧f -> ⟦ `nodelist ⟧f
 conv2 (inj (`nil , _)) = inj (`nil , unit)
 conv2 (inj (`cons , (h , t))) = inj (`cons , (conv1 h ,  conv2 t))


{-

_⊗_ : ∀ {Δ} -> Func Δ -> Func Δ -> Func Δ
F ⊗ G = `Π ProdLab (λ {`fst → F; `snd → G})


data ExpLab : Set where `lam `app `var : ExpLab

ExpF : Func 1
ExpF = ⨁ (λ { `lam -> ▹ zero;
              `app -> ▹ zero ⊗ ▹ zero;
              `var -> κ ℕ })

Exp = μ ExpF -}

{-
data exp : Set where
 lam : exp -> exp
 app : exp -> exp -> exp
 var : ℕ -> exp

conv : Exp -> exp
conv (inj (`lam , e)) = lam (conv e)
conv (inj (`app , es)) = app (conv (es `fst)) (conv (es `snd))
conv (inj (`var , x)) = var x -}
