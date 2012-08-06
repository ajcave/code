module generic where
open import Data.Sum
open import Product
open import Data.Unit hiding (⊤)
open import FinMapF
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

data code : Set₁ where
 Vz : code
 _⊕_ : (C D : code) -> code 
 _⊗_ : (C D : code) -> code
 ⇒ : (C : code) -> code
-- _⊃_ : (A : Set) -> (C : code) -> code
         -- requries funext or sophisticated equivalence relations later
 ⊤ : code

* : Unit
* = unit

-- This might help reconstructing codes?
{-data wrap (A : Set) : Set where
 con : A -> wrap A -}

_⟨_⟩ : code -> ctx Unit -> (ctx Unit -> Set) -> Set
_⟨_⟩ Vz ψ X = X ψ
_⟨_⟩ (C ⊕ D) ψ X = (C ⟨ ψ ⟩) X ⊎ (D ⟨ ψ ⟩) X
_⟨_⟩ (C ⊗ D) ψ X = ((C ⟨ ψ ⟩) X) × ((D ⟨ ψ ⟩) X)
_⟨_⟩ (⇒ C) ψ X = (C ⟨ (ψ , *) ⟩) X
--_⟨_⟩ (A ⊃ C) ψ X = A → (C ⟨ ψ ⟩) X
_⟨_⟩ ⊤ ψ X = Unit

data _[_] (C : code) (ψ : ctx Unit) : Set where
 ▹ : (x : var ψ *) -> C [ ψ ]
 sup : (M : (C ⟨ ψ ⟩) (_[_] C)) -> C [ ψ ]

tsubst : ∀ (C : code) (ψ φ : ctx Unit) -> Set
tsubst C ψ φ = gsubst ψ (λ _ -> C [ φ ])

-- TODO: I thought with care it was possible to make it so the C's don't have to be passed
-- around explicitly... Some paper of McBride demonstrates this...
mutual
 rn : ∀ {C} {ψ φ} -> vsubst ψ φ -> C [ ψ ] -> C [ φ ]
 rn σ (▹ x) = ▹ (σ x)
 rn {C} σ (sup M) = sup (rn2 C σ M)

 rn2 : ∀ C {D} {ψ φ} -> vsubst ψ φ
   -> (C ⟨ ψ ⟩) (_[_] D)  -> (C ⟨ φ ⟩) (_[_] D)
 rn2 Vz σ M = rn σ M
 rn2 (C ⊕ D) σ (inj₁ x) = inj₁ (rn2 C σ x)
 rn2 (C ⊕ D) σ (inj₂ y) = inj₂ (rn2 D σ y)
 rn2 (C ⊗ D) σ (proj₁ , proj₂) = (rn2 C σ proj₁) , rn2 D σ proj₂
 rn2 (⇒ C) σ M = rn2 C (extend (pop ∘ σ) top) M
-- rn2 (A ⊃ C) E σ M = λ x → rn2 C E σ (M x)
 rn2 ⊤ σ M = *

-- TODO: Can we the second of these operations to some kind of "map"?
-- Probably violates the termination checker?
mutual
 sub : ∀ {C} {ψ φ} -> tsubst C ψ φ -> C [ ψ ] -> C [ φ ]
 sub σ (▹ x) = σ x
 sub {C} σ (sup M) = sup (sub2 C σ M)

 sub2 : ∀ C {D} {ψ φ} -> tsubst D ψ φ
   -> (C ⟨ ψ ⟩) (_[_] D)  -> (C ⟨ φ ⟩) (_[_] D)
 sub2 Vz σ M = sub σ M
 sub2 (C ⊕ D) σ (inj₁ x) = inj₁ (sub2 C σ x)
 sub2 (C ⊕ D) σ (inj₂ y) = inj₂ (sub2 D σ y)
 sub2 (C ⊗ D) σ (proj₁ , proj₂) = (sub2 C σ proj₁) , sub2 D σ proj₂
 sub2 (⇒ C) σ M = sub2 C (extend (rn pop ∘ σ) (▹ top)) M
-- sub2 (A ⊃ C) D σ M = λ x → sub2 C D σ (M x)
 sub2 ⊤ σ M = *

mutual
 rn-cong : ∀ {C} {ψ φ} {σ1 σ2 : vsubst ψ φ} (σ1≡σ2 : gsubst' ψ (λ x -> σ1 x ≡ σ2 x)) (M : C [ ψ ])
  -> rn σ1 M ≡ rn σ2 M
 rn-cong σ1≡σ2 (▹ x) = cong ▹ (σ1≡σ2 x)
 rn-cong {C} σ1≡σ2 (sup M) = cong sup (rn2-cong C σ1≡σ2 M)

 rn2-cong : ∀ C {D} {ψ φ} {σ1 σ2 : vsubst ψ φ} (σ1≡σ2 : ∀ {T} (x : var ψ T) -> σ1 x ≡ σ2 x)
   (M : (C ⟨ ψ ⟩) (_[_] D))
  -> rn2 C σ1 M ≡ rn2 C σ2 M
 rn2-cong Vz σ1≡σ2 M = rn-cong σ1≡σ2 M
 rn2-cong (C ⊕ D) σ1≡σ2 (inj₁ x) = cong inj₁ (rn2-cong C σ1≡σ2 x)
 rn2-cong (C ⊕ D) σ1≡σ2 (inj₂ y) = cong inj₂ (rn2-cong D σ1≡σ2 y)
 rn2-cong (C ⊗ D) σ1≡σ2 (proj₁ , proj₂) = cong₂ _,_ (rn2-cong C σ1≡σ2 proj₁) (rn2-cong D σ1≡σ2 proj₂)
 rn2-cong (⇒ C) {σ1 = σ1} {σ2 = σ2} σ1≡σ2 M = rn2-cong C (extend' (λ x ->
     extend (pop ∘ σ1) top x ≡ extend (pop ∘ σ2) top x)
     (cong pop ∘ σ1≡σ2) refl) M
-- rn2-cong (A ⊃ C) D σ1 σ2 σ1≡σ2 M = {!!}
 rn2-cong ⊤ σ1≡σ2 M = refl

mutual
 lem1 : ∀ {C} {ψ φ ρ} {σ1 : vsubst φ ρ} {σ2 : vsubst ψ φ} (M : C [ ψ ])
  -> rn σ1 (rn σ2 M) ≡ rn (σ1 ∘ σ2) M
 lem1 (▹ x) = refl
 lem1 {C} (sup M) = cong sup (lem2 C M)

 lem2 : ∀ C {D} {ψ φ ρ} {σ1 : vsubst φ ρ} {σ2 : vsubst ψ φ} (M : (C ⟨ ψ ⟩) (_[_] D))
  -> rn2 C σ1 (rn2 C σ2 M) ≡ rn2 C (σ1 ∘ σ2) M
 lem2 Vz M = lem1 M
 lem2 (C ⊕ D) (inj₁ x) = cong inj₁ (lem2 C x)
 lem2 (C ⊕ D) (inj₂ y) = cong inj₂ (lem2 D y)
 lem2 (C ⊗ D) M = cong₂ _,_ (lem2 C (proj₁ M)) (lem2 D (proj₂ M))
 lem2 (⇒ C) {σ1 = σ1} {σ2 = σ2} M = trans (lem2 C M)
                              (rn2-cong C (extend' (λ x →
        (extend (pop ∘ σ1) top ∘ extend (pop ∘ σ2) top) x ≡ extend (pop ∘ σ1 ∘ σ2) top x)
        (λ x → refl) refl) M)
-- lem2 (A ⊃ C) D σ1 σ2 M = {!!}
 lem2 ⊤ M = refl

-- TODO: Try simulating and using label types?
exp : code
exp = {- "μ" Vz. -} (Vz ⊗ Vz) ⊕ (⇒ Vz)

exp-vsubst : ∀ {ψ φ} -> vsubst ψ φ -> exp [ ψ ] -> exp [ φ ]
exp-vsubst σ M = rn σ M

exp-subst : ∀ {ψ φ} -> tsubst exp ψ φ -> exp [ ψ ] -> exp [ φ ]
exp-subst σ M = sub σ M

-- Goal: Intrinsically typed terms
-- Goal: Judgements ("dependent types") e.g. Typing? Big step reduction? Small step?
-- Goal: Try for a nice proof of Church Rosser
-- Goal: Join with "associativity for free" technique
-- Goal: Intrinsically typed system F? How about representing LF?
