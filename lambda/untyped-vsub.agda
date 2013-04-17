module untyped-vsub where
open import lambda
open import FinMap

[_]r : ∀ {Γ Δ} (σ : vsubst Γ Δ) -> (M : tm Γ) -> tm Δ
[_]r σ (▹ x) = ▹ (lookup σ x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (M · N) = ([ σ ]r M) · ([ σ ]r N)
