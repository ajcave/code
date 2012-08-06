module FinMapF where
open import Function

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (ψ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

gsubst' : ∀ {A} (ψ : ctx A) (F : ∀ {T} -> var ψ T -> Set) -> Set
gsubst' ψ F = ∀ {T} (x : var ψ T) -> F x

extend' : ∀ {A} {U} {ψ : ctx A} (F : ∀ {T} -> var (ψ , U) T -> Set) -> gsubst' ψ (F ∘ pop) -> F top -> gsubst' (ψ , U) F
extend' F σ M top = M
extend' F σ M (pop y) = σ y

-- Specialized to non-dependent to get better reconstruction behaviour
gsubst : ∀ {A} (ψ : ctx A) (F : A -> Set) -> Set
gsubst ψ F = gsubst' ψ (λ {T} x -> F T)

extend : ∀ {A} {F : A -> Set} {U} {ψ : ctx A} -> gsubst ψ F -> F U -> gsubst (ψ , U) F
extend {A} {F} σ M = extend' (λ {T} x -> F T) σ M

vsubst : ∀ {A} (ψ φ : ctx A) -> Set
vsubst ψ φ = gsubst ψ (λ T -> var φ T)


