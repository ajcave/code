module generic where
open import Data.Sum
open import Data.Product
open import Function

data code : Set₁ where
 Vz : code
 _⊕_ : (C D : code) -> code 
 _⊗_ : (C D : code) -> code
 ⇒ : (C : code) -> code
 _⊃_ : (A : Set) -> (C : code) -> code
 ⊤ : code

record unit : Set where
 constructor *

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (ψ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

_⟨_⟩ : code -> ctx unit -> (ctx unit -> Set) -> Set
_⟨_⟩ Vz ψ X = X ψ
_⟨_⟩ (C ⊕ D) ψ X = (C ⟨ ψ ⟩) X ⊎ (D ⟨ ψ ⟩) X
_⟨_⟩ (C ⊗ D) ψ X = ((C ⟨ ψ ⟩) X) × ((D ⟨ ψ ⟩) X)
_⟨_⟩ (⇒ C) ψ X = (C ⟨ (ψ , *) ⟩) X
_⟨_⟩ (A ⊃ C) ψ X = A → (C ⟨ ψ ⟩) X
_⟨_⟩ ⊤ ψ X = unit

data _[_] (C : code) (ψ : ctx unit) : Set where
 ▹ : (x : var ψ *) -> C [ ψ ]
 sup : (M : (C ⟨ ψ ⟩) (_[_] C)) -> C [ ψ ]

exp : code
exp = (Vz ⊗ Vz) ⊕ (⇒ Vz)

vsubst : ∀ {A} (ψ φ : ctx A) -> Set
vsubst ψ φ = ∀ {T} -> var ψ T -> var φ T

ext : ∀ {A ψ φ} {T : A} -> vsubst ψ φ -> var φ T -> vsubst (ψ , T) φ
ext σ x top = x
ext σ x (pop y) = σ y

--map : ∀ C {X Y} (f : ∀ {ψ} -> X ψ -> Y ψ) φ -> (C ⟨ φ ⟩) X -> (C ⟨ ψ ⟩) Y

mutual
 rn : ∀ {C ψ φ} -> vsubst ψ φ -> C [ ψ ] -> C [ φ ]
 rn σ (▹ x) = ▹ (σ x)
 rn {C} σ (sup M) = sup (rn2 C C σ M)

 rn2 : ∀ C D {ψ φ} -> vsubst ψ φ
   -> (C ⟨ ψ ⟩) (_[_] D)  -> (C ⟨ φ ⟩) (_[_] D)
 rn2 Vz E σ M = rn σ M
 rn2 (C ⊕ D) E σ (inj₁ x) = inj₁ (rn2 C E σ x)
 rn2 (C ⊕ D) E σ (inj₂ y) = inj₂ (rn2 D E σ y)
 rn2 (C ⊗ D) E σ (proj₁ , proj₂) = (rn2 C E σ proj₁) , rn2 D E σ proj₂
 rn2 (⇒ C) E σ M = rn2 C E (ext (pop ∘ σ) top) M
 rn2 (A ⊃ C) E σ M = λ x → rn2 C E σ (M x)
 rn2 ⊤ E σ M = *