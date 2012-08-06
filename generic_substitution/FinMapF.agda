module FinMapF where

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (ψ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

gsubst : ∀ {A} (ψ : ctx A) (F : A -> Set) -> Set
gsubst ψ F = ∀ {T} (x : var ψ T) -> F T

extend : ∀ {A} {F : A -> Set} {ψ : ctx A}  -> gsubst ψ F -> ∀ {T} -> F T -> gsubst (ψ , T) F
extend σ M top = M
extend σ M (pop y) = σ y

vsubst : ∀ {A} (ψ φ : ctx A) -> Set
vsubst ψ φ = gsubst ψ (λ T -> var φ T)
