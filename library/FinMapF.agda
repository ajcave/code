module FinMapF where
open import Function
open import Level

data ctx {p} (A : Set p) : Set p where
 ⊡ : ctx A
 _,_ : (ψ : ctx A) -> (T : A) -> ctx A

data var {p} {A : Set p} : (Γ : ctx A) -> A -> Set p where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

gsubst' : ∀ {a b} {A : Set a} (ψ : ctx A) (F : ∀ {T} -> var ψ T -> Set b) -> Set (a ⊔ b)
gsubst' ψ F = ∀ {T} (x : var ψ T) -> F x

init : ∀ {a b} {A : Set a} {U} (F : ∀ {T} -> var ⊡ T -> Set b) -> gsubst' ⊡ F
init F x = {!!}

extend' : ∀ {a b} {A : Set a} {U} {ψ : ctx A} (F : ∀ {T} -> var (ψ , U) T -> Set b) -> gsubst' ψ (F ∘ pop) -> F top -> gsubst' (ψ , U) F
extend' F σ M top = M
extend' F σ M (pop y) = σ y

-- Specialized to non-dependent to get better reconstruction behaviour
gsubst : ∀ {a b} {A : Set a} (ψ : ctx A) (F : A -> Set b) -> Set (a ⊔ b)
gsubst ψ F = gsubst' ψ (λ {T} x -> F T)

extend : ∀ {a b} {A : Set a} {F : A -> Set b} {U} {ψ : ctx A} -> gsubst ψ F -> F U -> gsubst (ψ , U) F
extend {a} {b} {A} {F} σ M = extend' (λ {T} x -> F T) σ M

vsubst : ∀ {a} {A : Set a} (ψ φ : ctx A) -> Set a
vsubst ψ φ = gsubst ψ (λ T -> var φ T)

-- Specialize to a constant family
gksubst : ∀ {a b} {A : Set a} (ψ : ctx A) (F : Set b) -> Set (a ⊔ b)
gksubst ψ F = gsubst ψ (λ _ -> F)

kextend : ∀ {a b} {A : Set a} {F : Set b} {U} {ψ : ctx A} -> gksubst ψ F -> F -> gksubst (ψ , U) F
kextend {a} {b} {A} {F} σ M = extend' (λ _ -> F) σ M




