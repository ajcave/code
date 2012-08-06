module generic-firstorder where
open import Data.Sum
open import Product
open import FinMap
open import Function
open import Data.Unit hiding (⊤)
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


-- TODO: Ugh do the gsubst generality. Make that a library...
-- Probably want to use the first order representation so we have less problems reconstructing
-- And also we can get an eta law for free by computing it to _×_
vsubst : ∀ {A} (ψ φ : ctx A) -> Set
vsubst ψ φ = gsubst ψ (var φ)

tsubst : ∀ (C : code) (ψ φ : ctx Unit) -> Set
tsubst C ψ φ = gsubst ψ (λ _ -> C [ φ ])

-- TODO: I thought with care it was possible to make it so the C's don't have to be passed
-- around explicitly... Some paper of McBride demonstrates this...
mutual
 rn : ∀ C {ψ φ} -> vsubst ψ φ -> C [ ψ ] -> C [ φ ]
 rn C σ (▹ x) = ▹ (lookup σ x)
 rn C σ (sup M) = sup (rn2 C C σ M)

 rn2 : ∀ C D {ψ φ} -> vsubst ψ φ
   -> (C ⟨ ψ ⟩) (_[_] D)  -> (C ⟨ φ ⟩) (_[_] D)
 rn2 Vz E σ M = rn E σ M
 rn2 (C ⊕ D) E σ (inj₁ x) = inj₁ (rn2 C E σ x)
 rn2 (C ⊕ D) E σ (inj₂ y) = inj₂ (rn2 D E σ y)
 rn2 (C ⊗ D) E σ (proj₁ , proj₂) = (rn2 C E σ proj₁) , rn2 D E σ proj₂
 rn2 (⇒ C) E σ M = rn2 C E ((gmap pop σ) , top) M
-- rn2 (A ⊃ C) E σ M = λ x → rn2 C E σ (M x)
 rn2 ⊤ E σ M = *

-- TODO: Can we the second of these operations to some kind of "map"?
-- Probably violates the termination checker?
mutual
 sub : ∀ C {ψ φ} -> tsubst C ψ φ -> C [ ψ ] -> C [ φ ]
 sub C σ (▹ x) = lookup σ x
 sub C σ (sup M) = sup (sub2 C C σ M)

 sub2 : ∀ C D {ψ φ} -> tsubst D ψ φ
   -> (C ⟨ ψ ⟩) (_[_] D)  -> (C ⟨ φ ⟩) (_[_] D)
 sub2 Vz D σ M = sub D σ M
 sub2 (C ⊕ D) D' σ (inj₁ x) = inj₁ (sub2 C D' σ x)
 sub2 (C ⊕ D) D' σ (inj₂ y) = inj₂ (sub2 D D' σ y)
 sub2 (C ⊗ D) D' σ (proj₁ , proj₂) = (sub2 C D' σ proj₁) , sub2 D D' σ proj₂
 sub2 (⇒ C) D σ M = sub2 C D ((gmap (rn D {!!}) σ) , (▹ top)) M
-- sub2 (A ⊃ C) D σ M = λ x → sub2 C D σ (M x)
 sub2 ⊤ D σ M = *

{-mutual
 rn-cong : ∀ C {ψ φ} (σ1 σ2 : vsubst ψ φ) (σ1≡σ2 : ∀ {T} (x : var ψ T) -> σ1 x ≡ σ2 x) (M : C [ ψ ])
  -> rn C σ1 M ≡ rn C σ2 M
 rn-cong C σ1 σ2 σ1≡σ2 (▹ x) = cong ▹ (σ1≡σ2 x)
 rn-cong C σ1 σ2 σ1≡σ2 (sup M) = cong sup (rn2-cong C C σ1 σ2 σ1≡σ2 M)

 rn2-cong : ∀ C D {ψ φ} (σ1 σ2 : vsubst ψ φ) (σ1≡σ2 : ∀ {T} (x : var ψ T) -> σ1 x ≡ σ2 x)
   (M : (C ⟨ ψ ⟩) (_[_] D))
  -> rn2 C D σ1 M ≡ rn2 C D σ2 M
 rn2-cong Vz D σ1 σ2 σ1≡σ2 M = rn-cong D σ1 σ2 σ1≡σ2 M
 rn2-cong (C ⊕ D) D' σ1 σ2 σ1≡σ2 (inj₁ x) = cong inj₁ (rn2-cong C D' σ1 σ2 σ1≡σ2 x)
 rn2-cong (C ⊕ D) D' σ1 σ2 σ1≡σ2 (inj₂ y) = cong inj₂ (rn2-cong D D' σ1 σ2 σ1≡σ2 y)
 rn2-cong (C ⊗ D) D' σ1 σ2 σ1≡σ2 (proj₁ , proj₂) = cong₂ _,_ (rn2-cong C D' σ1 σ2 σ1≡σ2 proj₁) (rn2-cong D D' σ1 σ2 σ1≡σ2 proj₂)
 rn2-cong (⇒ C) D σ1 σ2 σ1≡σ2 M = rn2-cong C D ((pop ∘ σ1) , top) ((pop ∘ σ2) , top) {!!} M
-- rn2-cong (A ⊃ C) D σ1 σ2 σ1≡σ2 M = {!!}
 rn2-cong ⊤ D σ1 σ2 σ1≡σ2 M = refl -}

mutual
 lem1 : ∀ C {ψ φ ρ} (σ1 : vsubst φ ρ) (σ2 : vsubst ψ φ) (M : C [ ψ ])
  -> rn C σ1 (rn C σ2 M) ≡ rn C (gmap (lookup σ1) σ2) M
 lem1 C σ1 σ2 (▹ x) = {!!}
 lem1 C σ1 σ2 (sup M) = cong sup (lem2 C C σ1 σ2 M)

 lem2 : ∀ C D {ψ φ ρ} (σ1 : vsubst φ ρ) (σ2 : vsubst ψ φ) (M : (C ⟨ ψ ⟩) (_[_] D))
  -> rn2 C D σ1 (rn2 C D σ2 M) ≡ rn2 C D (gmap (lookup σ1) σ2) M
 lem2 Vz D σ1 σ2 M = lem1 D σ1 σ2 M
 lem2 (C ⊕ D) D' σ1 σ2 (inj₁ x) = cong inj₁ (lem2 C D' σ1 σ2 x)
 lem2 (C ⊕ D) D' σ1 σ2 (inj₂ y) = cong inj₂ (lem2 D D' σ1 σ2 y)
 lem2 (C ⊗ D) D' σ1 σ2 M = cong₂ _,_ (lem2 C D' σ1 σ2 (proj₁ M)) (lem2 D D' σ1 σ2 (proj₂ M))
 lem2 (⇒ C) D σ1 σ2 M = trans (lem2 C D ((gmap pop σ1) , top) ((gmap pop σ2) , top) M)
                              (cong₂ (rn2 C D) (cong₂ _,_ (trans (gmap-funct σ2) (trans (gmap-cong (λ x → lookup-gmap pop σ1 x)) (sym (gmap-funct σ2)))) refl) refl)
-- lem2 (A ⊃ C) D σ1 σ2 M = {!!}
 lem2 ⊤ D σ1 σ2 M = refl

-- TODO: Try simulating and using label types?
exp : code
exp = {- "μ" Vz. -} (Vz ⊗ Vz) ⊕ (⇒ Vz)

exp-vsubst : ∀ {ψ φ} -> vsubst ψ φ -> exp [ ψ ] -> exp [ φ ]
exp-vsubst σ M = rn exp σ M

exp-subst : ∀ {ψ φ} -> tsubst exp ψ φ -> exp [ ψ ] -> exp [ φ ]
exp-subst σ M = sub exp σ M

-- Goal: Intrinsically typed terms
-- Goal: Judgements ("dependent types") e.g. Typing? Big step reduction? Small step?
-- Goal: Try for a nice proof of Church Rosser
-- Goal: Join with "associativity for free" technique
-- Goal: Intrinsically typed system F? How about representing LF?
