module FinMap where
open import Level
open import Unit
open import Relation.Binary.PropositionalEquality
open import Product
open import Function

data ctx {a} (A : Set a) : Set a where
 ⊡ : ctx A
 _,_ : (ψ : ctx A) -> (T : A) -> ctx A

data var {a} {A : Set a} : (Γ : ctx A) -> A -> Set a where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

gsubst : ∀ {a b} {A : Set a} -> ctx A -> (F : A -> Set b) -> Set b
gsubst ⊡ F = Unit
gsubst (ψ , T) F = (gsubst ψ F) × (F T)

gksubst : ∀ {a b} {A : Set a} -> ctx A -> (F : Set b) -> Set b
gksubst ψ F = gsubst ψ (λ _ -> F)

gsubst' : ∀ {a b} {A : Set a} (ψ : ctx A) (F : gksubst ψ (Set b)) -> Set b
gsubst' ⊡ F = Unit
gsubst' (ψ , T) F = gsubst' ψ (proj₁ F) × proj₂ F

interp : ∀ {a b} {A : Set a} {ψ : ctx A} {F : A -> Set b} -> (∀ {U} -> var ψ U -> F U) -> gsubst ψ F
interp {A = A} {⊡} σ = tt
interp {A = A} {ψ , T} σ = (interp (σ ∘ pop)) , (σ top)

lookup : ∀ {a b} {A : Set a} {ψ : ctx A} {F : A -> Set b} {T} -> gsubst ψ F -> var ψ T -> F T
lookup {A = A} {⊡} σ ()
lookup {A = A} {ψ , T} σ top = proj₂ σ
lookup {A = A} {ψ , T} σ (pop y) = lookup (proj₁ σ) y

gsubst-pred : ∀ {a b c} {A : Set a} {ψ : ctx A} {F : A -> Set b}  (P : ∀ {U} -> F U -> Set c) (σ : gsubst ψ F) -> Set c
gsubst-pred {A = A} {⊡} P σ = Unit
gsubst-pred {A = A} {ψ , T} P σ = (gsubst-pred P (proj₁ σ)) × (P (proj₂ σ))

--gsubst' ψ (interp (P ∘ (lookup σ)))

lookup' : ∀ {a b} {A : Set a} {ψ : ctx A} {F : gksubst ψ (Set b)} {T} -> gsubst' ψ F -> (x : var ψ T) -> lookup F x
lookup' {A = A} {⊡} σ ()
lookup' {A = A} {ψ , T} σ top = proj₂ σ
lookup' {A = A} {ψ , T} σ (pop y) = lookup' (proj₁ σ) y

lookup-pred : ∀ {a b c} {A : Set a} {ψ : ctx A} {F : A -> Set b} {P : ∀ {U} -> F U -> Set c} {σ : gsubst ψ F}
  (θ : gsubst-pred P σ) {T} -> (x : var ψ T) -> P (lookup σ x)
lookup-pred {A = A} {⊡} θ ()
lookup-pred {A = A} {ψ , T} θ top = proj₂ θ
lookup-pred {A = A} {ψ , T} θ (pop y) = lookup-pred (proj₁ θ) y

-- This is an example where using a direct definition of × gives better reconstruction
gmap : ∀ {a b c} {A : Set a} {ψ : ctx A} {F : A -> Set b} {G : A -> Set c} -> (∀ {T} -> F T -> G T) -> gsubst ψ F -> gsubst ψ G
gmap {a} {b} {c} {A} {⊡} f σ = tt
gmap {a} {b} {c} {A} {ψ , T} f σ = (gmap f (proj₁ σ)) , (f (proj₂ σ))

gmap-id : ∀ {a b} {A : Set a} {F : A -> Set b} {ψ : ctx A} (σ : gsubst ψ F) -> gmap id σ ≡ σ
gmap-id {a} {b} {A} {F} {⊡} σ = refl
gmap-id {a} {b} {A} {F} {ψ , T} σ = cong₂ _,_ (gmap-id (proj₁ σ)) refl

gmap-funct : ∀ {a} {b} {c} {d} {A : Set a} {ψ : ctx A} {F : A -> Set b} {G : A -> Set c} {H : A -> Set d} {f : ∀ {T} -> F T -> G T} {g : ∀ {T} -> G T -> H T} (σ : gsubst ψ F)
 -> gmap g (gmap f σ) ≡ gmap (g ∘ f) σ
gmap-funct {a} {b} {c} {d} {A} {⊡} σ = refl
gmap-funct {a} {b} {c} {d} {A} {ψ , T} σ = cong₂ _,_ (gmap-funct (proj₁ σ)) refl

gmap-cong : ∀ {a} {b} {c} {A : Set a} {ψ : ctx A} {F : A -> Set b} {G : A -> Set c} {f g : ∀ {T} -> F T -> G T} {σ : gsubst ψ F} (p : ∀ {T} (x : F T) -> f x ≡ g x)
 -> gmap f σ ≡ gmap g σ
gmap-cong {A = A} {⊡} p = refl
gmap-cong {A = A} {ψ , T} p = cong₂ _,_ (gmap-cong p) (p _)

lookup-gmap : ∀ {a b c} {A : Set a} {ψ : ctx A} {F : A -> Set b} {G : A -> Set c} (f : ∀ {T} -> F T -> G T) (σ : gsubst ψ F) {T} (x : var ψ T)
 -> lookup (gmap f σ) x ≡ f (lookup σ x)
lookup-gmap {A = A} {⊡} f σ ()
lookup-gmap {A = A} {ψ , T} f σ top = refl
lookup-gmap {A = A} {ψ , T} f σ (pop y) = lookup-gmap f (proj₁ σ) y

vsubst : ∀ {a} {A : Set a} -> ctx A -> ctx A -> Set a
vsubst Γ Δ = gsubst Γ (var Δ)

[_]v : ∀ {a b} {A : Set a} {F : A -> Set b} {Δ T} (σ : gsubst Δ F) -> var Δ T -> F T
[ σ ]v x = lookup σ x

wkn : ∀ {a} {A : Set a} {Γ1 Γ2} {T : A} -> vsubst Γ1 Γ2 -> vsubst Γ1 (Γ2 , T)
wkn σ = gmap pop σ

id-vsub : ∀ {a} {A : Set a} {Γ : ctx A} -> vsubst Γ Γ
id-vsub {a} {A} {⊡} = tt
id-vsub {a} {A} {Γ , T} = (wkn id-vsub) , top

wkn-vsub : ∀ {a} {A : Set a} {Γ : ctx A} {T} -> vsubst Γ (Γ , T)
wkn-vsub {a} {A} {Γ} {T} = wkn id-vsub

vsub-ext : ∀ {a} {A : Set a} {T} {Γ1 Γ2 : ctx A} -> vsubst Γ1 Γ2 -> vsubst (Γ1 , T) (Γ2 , T)
vsub-ext σ = (gmap pop σ) , top

_∘v_ : ∀ {a} {A : Set a} {Δ Γ ψ : ctx A} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘v σ2) = gmap [ σ1 ]v σ2

cmap : ∀ {a b} {A : Set a} {B : Set b} (f : A -> B) (Ψ : ctx A) -> ctx B
cmap f ⊡ = ⊡
cmap f (ψ , T) = (cmap f ψ) , (f T)

cmap-var : ∀ {a b} {A : Set a} {B : Set b} (f : A -> B) {Ψ : ctx A} {T} (x : var Ψ T) -> var (cmap f Ψ) (f T)
cmap-var f top = top
cmap-var f (pop y) = pop (cmap-var f y)

ren-assoc : ∀ {a} {A : Set a} {n m k k' : ctx A} (w : vsubst n m) {w' : vsubst m k} {v : vsubst k k'}
 -> (v ∘v (w' ∘v w)) ≡ ((v ∘v w') ∘v w)
ren-assoc w {w'} {v} = trans (gmap-funct w) (gmap-cong (λ x → sym (lookup-gmap (lookup v) w' x)))

id-v-right : ∀ {a} {A : Set a} {n m : ctx A} {w : vsubst n m} -> w ≡ (w ∘v id-vsub)
id-v-right {a} {A} {⊡} = refl
id-v-right {a} {A} {ψ , T} = cong₂ _,_ (trans id-v-right (sym (gmap-funct id-vsub))) refl

lookup-id : ∀ {a} {A : Set a} {n : ctx A} {T} {x : var n T} -> x ≡ lookup id-vsub x
lookup-id {a} {A} {⊡} {x = ()}
lookup-id {a} {A} {ψ , .T} {T} {top} = refl
lookup-id {a} {A} {ψ , T} {T'} {pop y} = trans (cong pop lookup-id) (sym (lookup-gmap pop id-vsub y))

id-v-left : ∀ {a} {A : Set a} {n m : ctx A} {w : vsubst n m} -> w ≡ (id-vsub ∘v w)
id-v-left {a} {A} {⊡} = refl
id-v-left {a} {A} {ψ , T} = cong₂ _,_ id-v-left lookup-id

vsub-ext-funct : ∀ {a} {A : Set a} {n m k : ctx A} {T : A} (w : vsubst n m) (w' : vsubst m k)
 -> vsub-ext {T = T} (w' ∘v w) ≡ (vsub-ext w') ∘v (vsub-ext w)
vsub-ext-funct w w' = cong (λ α → α , top) (trans (gmap-funct w) (trans (gmap-cong (λ x → sym (lookup-gmap pop w' x))) (sym (gmap-funct w))))