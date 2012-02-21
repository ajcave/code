module uniqueness where

data tp : Set where
 i : tp
 _⇒_ : tp -> tp -> tp

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

record unit : Set where
 constructor tt

data var {A : Set} : ctx A -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T 

data exp (Γ : ctx unit) : Set where
 ▹ : var Γ tt -> exp Γ
 _·_ : exp Γ -> exp Γ -> exp Γ
 ƛ : tp -> exp (Γ , tt) -> exp Γ

<_> : ctx tp -> ctx unit
< ⊡ > = ⊡
< Γ , T > = < Γ > , tt

lookup : (Γ : ctx tp) -> var < Γ > tt -> tp
lookup ⊡ ()
lookup (Γ , T) top = T
lookup (Γ , T) (pop y) = lookup Γ y 

data of (Γ : ctx tp) : exp < Γ > -> tp -> Set where
 ▹ : (x : var < Γ > tt) -> of Γ (▹ x) (lookup Γ x) 
 _·_ : ∀ {m n T S} (M : of Γ m (T ⇒ S)) (N : of Γ n T) -> of Γ (m · n) S
 ƛ : ∀ {m T S} (M : of (Γ , T) m S) -> of Γ (ƛ T m) (T ⇒ S)

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

uniqueness : ∀ {Γ m T S} -> of Γ m T -> of Γ m S -> T ≡ S
uniqueness (▹ x) (▹ .x) = refl
uniqueness (M · N) (M' · N') with uniqueness M M'
... | refl = refl
uniqueness (ƛ M) (ƛ M') with uniqueness M M'
... | refl = refl