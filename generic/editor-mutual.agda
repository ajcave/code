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

-- data ProdLbl : Set where `fst `snd : ProdLbl
-- _⊗_ : ∀ {Δ} -> Func Δ -> Func Δ -> Func Δ
-- F ⊗ G = `Π ProdLbl (λ {`fst → F; `snd → G})

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

data TypeLbls : Set where `tree `nodelist : TypeLbls
data ListLbl : Set where `nil `cons : ListLbl
data TreeLbl : Set where `children : TreeLbl
data STpLbl : Set where `tp : STpLbl
data TpLbl : Set where `base `arr : TpLbl
data SExpLbl : Set where `exp : SExpLbl
data ExpLbl : Set where `lam `app `var : ExpLbl

TpFam : Defs STpLbl
TpFam `tp = ⨁ (λ {`base → `1; `arr → ▹ `tp ⊗ ▹ `tp})

EFam : Defs SExpLbl
EFam `exp = ⨁ (λ {`lam → κ (μ TpFam `tp) ⊗ ▹ `exp;
                  `app → ▹ `exp ⊗ ▹ `exp;
                  `var → κ ℕ})

⟦_⟧e : SExpLbl -> Set
⟦ l ⟧e = μ EFam l

FamF : Defs TypeLbls
FamF `tree     = ⨁ (λ {`children → κ ⟦ `exp ⟧e ⊗ ▹ `nodelist})
FamF `nodelist = ⨁ (λ {`nil  → `1;
                      `cons → ▹ `tree ⊗ ▹ `nodelist})

-- mutual
--  data Tree : Set where
--   children : ℕ -> NodeList -> Tree
--  data NodeList : Set where
--   nil : NodeList
--   cons : Tree -> NodeList -> NodeList

⟦_⟧f : TypeLbls -> Set
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
