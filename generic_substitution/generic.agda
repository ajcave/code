module generic where
open import Data.Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

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


-- TODO: Ugh do the gsubst generality. Make that a library...
vsubst : ∀ {A} (ψ φ : ctx A) -> Set
vsubst ψ φ = ∀ {T} -> var ψ T -> var φ T

ext : ∀ {A ψ φ} {T : A} -> vsubst ψ φ -> var φ T -> vsubst (ψ , T) φ
ext σ x top = x
ext σ x (pop y) = σ y

tsubst : ∀ (C : code) (ψ φ : ctx unit) -> Set
tsubst C ψ φ = {T : _} → var ψ T → C [ φ ]

ext2 : ∀ {C ψ φ} -> tsubst C ψ φ -> C [ φ ] -> tsubst C (ψ , *) φ
ext2 σ x top = x
ext2 σ x (pop y) = σ y

-- TODO: I thought with care it was possible to make it so the C's don't have to be passed
-- around explicitly... Some paper of McBride demonstrates this...
mutual
 rn : ∀ C {ψ φ} -> vsubst ψ φ -> C [ ψ ] -> C [ φ ]
 rn C σ (▹ x) = ▹ (σ x)
 rn C σ (sup M) = sup (rn2 C C σ M)

 rn2 : ∀ C D {ψ φ} -> vsubst ψ φ
   -> (C ⟨ ψ ⟩) (_[_] D)  -> (C ⟨ φ ⟩) (_[_] D)
 rn2 Vz E σ M = rn E σ M
 rn2 (C ⊕ D) E σ (inj₁ x) = inj₁ (rn2 C E σ x)
 rn2 (C ⊕ D) E σ (inj₂ y) = inj₂ (rn2 D E σ y)
 rn2 (C ⊗ D) E σ (proj₁ , proj₂) = (rn2 C E σ proj₁) , rn2 D E σ proj₂
 rn2 (⇒ C) E σ M = rn2 C E (ext (pop ∘ σ) top) M
 rn2 (A ⊃ C) E σ M = λ x → rn2 C E σ (M x)
 rn2 ⊤ E σ M = *


-- TODO: Can we the second of these operations to some kind of "map"?
-- Probably violates the termination checker?
mutual
 sub : ∀ C {ψ φ} -> tsubst C ψ φ -> C [ ψ ] -> C [ φ ]
 sub C σ (▹ x) = σ x
 sub C σ (sup M) = sup (sub2 C C σ M)

 sub2 : ∀ C D {ψ φ} -> tsubst D ψ φ
   -> (C ⟨ ψ ⟩) (_[_] D)  -> (C ⟨ φ ⟩) (_[_] D)
 sub2 Vz D σ M = sub D σ M
 sub2 (C ⊕ D) D' σ (inj₁ x) = inj₁ (sub2 C D' σ x)
 sub2 (C ⊕ D) D' σ (inj₂ y) = inj₂ (sub2 D D' σ y)
 sub2 (C ⊗ D) D' σ (proj₁ , proj₂) = (sub2 C D' σ proj₁) , sub2 D D' σ proj₂
 sub2 (⇒ C) D σ M = sub2 C D (ext2 (rn D pop ∘ σ) (▹ top)) M
 sub2 (A ⊃ C) D σ M = λ x → sub2 C D σ (M x)
 sub2 ⊤ D σ M = *

mutual
 lem1 : ∀ C {ψ φ ρ} (σ1 : vsubst φ ρ) (σ2 : vsubst ψ φ) (M : C [ ψ ])
  -> rn C σ1 (rn C σ2 M) ≡ rn C (σ1 ∘ σ2) M
 lem1 C σ1 σ2 (▹ x) = refl
 lem1 C σ1 σ2 (sup M) = {!!}

 lem2 : ∀ C D {ψ φ ρ} (σ1 : vsubst φ ρ) (σ2 : vsubst ψ φ) (M : (C ⟨ ψ ⟩) (_[_] D))
  -> rn2 C D σ1 (rn2 C D σ2 M) ≡ rn2 C D (σ1 ∘ σ2) M
 lem2 C D σ1 σ2 M = ?

exp : code
exp = (Vz ⊗ Vz) ⊕ (⇒ Vz)

exp-subst : ∀ {ψ φ} -> tsubst exp ψ φ -> exp [ ψ ] -> exp [ φ ]
exp-subst σ M = sub exp σ M