module FinMap where
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Product
open import Function

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (ψ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

gsubst : ∀ {A} -> ctx A -> (F : A -> Set) -> Set
gsubst ⊡ F = Unit
gsubst (ψ , T) F = (gsubst ψ F) × (F T)

lookup : ∀ {A} {ψ : ctx A} {F T} -> gsubst ψ F -> var ψ T -> F T
lookup {A} {⊡} σ ()
lookup {A} {ψ , T} σ top = proj₂ σ
lookup {A} {ψ , T} σ (pop y) = lookup (proj₁ σ) y

-- This is an example where using a direct definition of × gives better reconstruction
gmap : ∀ {A} {ψ : ctx A} {F G} -> (∀ {T} -> F T -> G T) -> gsubst ψ F -> gsubst ψ G
gmap {A} {⊡} f σ = unit
gmap {A} {ψ , T} f σ = (gmap f (proj₁ σ)) , (f (proj₂ σ))

gmap-funct : ∀ {A} {ψ : ctx A} {F G H : A -> Set} {f : ∀ {T} -> F T -> G T} {g : ∀ {T} -> G T -> H T} (σ : gsubst ψ F)
 -> gmap g (gmap f σ) ≡ gmap (g ∘ f) σ
gmap-funct {A} {⊡} σ = refl
gmap-funct {A} {ψ , T} σ = cong₂ _,_ (gmap-funct (proj₁ σ)) refl

gmap-cong : ∀ {A} {ψ : ctx A} {F G : A -> Set} {f g : ∀ {T} -> F T -> G T} {σ : gsubst ψ F} (p : ∀ {T} (x : F T) -> f x ≡ g x)
 -> gmap f σ ≡ gmap g σ
gmap-cong {A} {⊡} p = refl
gmap-cong {A} {ψ , T} p = cong₂ _,_ (gmap-cong p) (p _)

lookup-gmap : ∀ {A} {ψ : ctx A} {F G : A -> Set} (f : ∀ {T} -> F T -> G T) (σ : gsubst ψ F) {T} (x : var ψ T)
 -> lookup (gmap f σ) x ≡ f (lookup σ x)
lookup-gmap {A} {⊡} f σ ()
lookup-gmap {A} {ψ , T} f σ top = refl
lookup-gmap {A} {ψ , T} f σ (pop y) = lookup-gmap f (proj₁ σ) y