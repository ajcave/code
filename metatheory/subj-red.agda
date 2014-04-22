module subj-red where
open import Data.Nat
open import Data.Fin

data tp : Set where
 i : tp
 _⇝_ : (T S : tp) -> tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

-- data var : (Γ : ctx) -> tp -> Set where
--  top : ∀ {Γ T} -> var (Γ , T) T
--  pop : ∀ {Γ S T} -> var Γ T -> var (Γ , S) T


data exp (Γ : ℕ) :  Set where
 ▹ : Fin Γ -> exp Γ
 _·_ : ∀ (M : exp Γ) (N : exp Γ) -> exp Γ
 ƛ : (M : exp (suc Γ)) -> exp Γ

-- data exp (Γ : ctx) : tp -> Set where
--  ▹ : ∀ {T} -> var Γ T -> exp Γ T
--  _·_ : ∀ {T S} (M : exp Γ (T ⇝ S)) (N : exp Γ T) -> exp Γ S
--  ƛ : ∀ {T S} (M : exp (Γ , T) S) -> exp Γ (T ⇝ S)

-- data sub : (Γ : ctx) -> ctx -> Set where
--  ⊡ : ∀ {Γ} -> sub Γ ⊡
--  _,_ : ∀ {Γ Δ T} (σ : sub Γ Δ) (M : exp Γ T) -> sub Γ (Δ , T)

-- data vsub : (Γ : ctx) -> ctx -> Set where
--  ⊡ : ∀ {Γ} -> vsub Γ ⊡
--  _,_ : ∀ {Γ Δ T} (σ : vsub Γ Δ) (x : var Γ T) -> vsub Γ (Δ , T)

-- [_]v : ∀ {Γ Δ T} (σ : vsub Γ Δ) (x : var Δ T) -> var Γ T
-- [ ⊡ ]v ()
-- [ σ , x ]v top = x
-- [ σ , x ]v (pop y) = [ σ ]v y

-- map : ∀ {Γ Δ θ} (f : ∀ {T} -> var Γ T -> var θ T) (σ : vsub Γ Δ) -> vsub θ Δ
-- map f ⊡ = ⊡
-- map f (σ , x) = (map f σ) , (f x)

-- vext : ∀ {Γ Δ T} (σ : vsub Γ Δ) -> vsub (Γ , T) (Δ , T)
-- vext σ = map pop σ , top

-- id : ∀ {Γ} -> vsub Γ Γ
-- id {⊡} = ⊡
-- id {Γ , T} = (map pop id) , top

-- wkn : ∀ {Γ T} -> vsub (Γ , T) Γ
-- wkn = map pop id

-- [_] : ∀ {Γ Δ T} (σ : vsub Γ Δ) (M : exp Δ T) -> exp Γ T
-- [_] σ (▹ y) = ▹ ([ σ ]v y)
-- [_] σ (M · N) = ([ σ ] M) · ([ σ ] N)
-- [_] σ (ƛ M) = ƛ ([ vext σ ] M)

-- [_]tv : ∀ {Γ Δ T} (σ : sub Γ Δ) (x : var Δ T) -> exp Γ T
-- [ ⊡ ]tv ()
-- [ σ , x ]tv top = x
-- [ σ , x ]tv (pop y) = [ σ ]tv y

-- tmap : ∀ {Γ Δ θ} (f : ∀ {T} -> exp Γ T -> exp θ T) (σ : sub Γ Δ) -> sub θ Δ
-- tmap f ⊡ = ⊡
-- tmap f (σ , x) = (tmap f σ) , (f x)

-- [_]t : ∀ {Γ Δ T} (σ : sub Γ Δ) (M : exp Δ T) -> exp Γ T
-- [_]t σ (▹ y) = [ σ ]tv y
-- [_]t σ (M · N) = [ σ ]t M · [ σ ]t N
-- [_]t σ (ƛ M) = ƛ ([ tmap [ wkn ] σ , (▹ top) ]t M)

-- tid : ∀ {Γ} -> sub Γ Γ
-- tid {⊡} = ⊡
-- tid {Γ , T} = (tmap [ wkn ] tid) , (▹ top)

-- [_/x] : ∀ {Γ T S} (N : exp Γ T) (M : exp (Γ , T) S) -> exp Γ S
-- [ N /x] M = [ tid , N ]t M



