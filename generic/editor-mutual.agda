module editor-mutual where
open import Data.Nat
open import Data.Product
open import Data.Fin
open import Data.Empty

data Func (Δ : Set) : Set₁ where
 `Σ `Π : (A : Set) -> (f : (l : A) -> Func Δ) -> Func Δ
 κ : Set -> Func Δ
 ▹ : Δ -> Func Δ

`1 : ∀ {Δ} -> Func Δ
`1 = `Π ⊥ (λ ())

data ProdLab : Set where `fst `snd : ProdLab
_⊗_ : ∀ {Δ} -> Func Δ -> Func Δ -> Func Δ
F ⊗ G = `Π ProdLab (λ {`fst → F; `snd → G})

⨁ : ∀ {Δ} {A : Set} -> (f : (l : A) -> Func Δ) -> Func Δ
⨁ f = `Σ _ f

Defs : Set -> Set₁
Defs Δ = Δ -> Func Δ

data Labs : Set where `tree `nodelist : Labs
data ListLab : Set where `nil `cons : ListLab
data TreeLab : Set where `children : TreeLab

FamF : Defs Labs
FamF `tree     = ⨁ (λ {`children → ▹ `nodelist})
FamF `nodelist = ⨁ (λ {`nil  → `1;
                      `cons → ▹ `tree ⊗ ▹ `nodelist})

mutual
 data Tree : Set where
  children : NodeList -> Tree
 data NodeList : Set where
  nil : NodeList
  cons : Tree -> NodeList -> NodeList

Env : Set -> Set₁
Env Δ = Δ -> Set

mutual
 ⟦_⟧ : ∀ {Δ} -> Func Δ -> Env Δ -> Set
 ⟦_⟧ (`Σ A f) ρ = Σ A (λ l → ⟦ f l ⟧ ρ)
 ⟦_⟧ (`Π A f) ρ = (l : A) → ⟦ f l ⟧ ρ
 ⟦_⟧ (κ A) ρ = A
 ⟦_⟧ (▹ X) ρ = ρ X

-- Constructs them simultaneously using indexing
data μ {Δ} (Ds : Defs Δ) : Δ -> Set where
 inj : ∀ {l} -> ⟦ Ds l ⟧ (μ Ds) -> μ Ds l

⟦_⟧f : Labs -> Set
⟦ l ⟧f = μ FamF l

mutual
 conv1 : ⟦ `tree ⟧f -> Tree
 conv1 (inj (`children , ts)) = children (conv2 ts)

 conv2 : ⟦ `nodelist ⟧f -> NodeList
 conv2 (inj (`nil , _)) = nil
 conv2 (inj (`cons , ht)) = cons (conv1 (ht `fst)) (conv2 (ht `snd))


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
