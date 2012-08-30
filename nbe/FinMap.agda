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

gksubst : ∀ {A} -> ctx A -> (F : Set) -> Set
gksubst ψ F = gsubst ψ (λ _ -> F)

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

vsubst : ∀ {A} -> ctx A -> ctx A -> Set
vsubst Γ Δ = gsubst Γ (var Δ)

[_]v : ∀ {A} {F : A -> Set} {Δ T} (σ : gsubst Δ F) -> var Δ T -> F T
[_]v {A} {F} {⊡} σ ()
[_]v {A} {F} {ψ , T} (σ , M) top = M
[_]v {A} {F} {ψ , T} (σ , M) (pop y) = [ σ ]v y

wkn : ∀ {A} {Γ1 Γ2} {T : A} -> vsubst Γ1 Γ2 -> vsubst Γ1 (Γ2 , T)
wkn σ = gmap pop σ

id-vsub : ∀ {A} {Γ : ctx A} -> vsubst Γ Γ
id-vsub {A} {⊡} = unit
id-vsub {A} {Γ , T} = (wkn id-vsub) , top

wkn-vsub : ∀ {A} {Γ : ctx A} {T} -> vsubst Γ (Γ , T)
wkn-vsub {A} {Γ} {T} = wkn id-vsub

vsub-ext : ∀ {A T} {Γ1 Γ2 : ctx A} -> vsubst Γ1 Γ2 -> vsubst (Γ1 , T) (Γ2 , T)
vsub-ext σ = (gmap pop σ) , top