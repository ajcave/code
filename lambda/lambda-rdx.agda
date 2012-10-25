module lambda-rdx where
open import FinMap
open import Unit

♯tm : Unitz
♯tm = tt

* : Unitz
* = tt

data tm (Γ : ctx Unitz) : Set where
 ▹ : (x : var Γ ♯tm) -> tm Γ
 ƛ : (M : tm (Γ , ♯tm)) -> tm Γ
 _·_ : (M : tm Γ) -> (N : tm Γ) -> tm Γ
 _[_] : (M : tm (Γ , ♯tm)) -> (N : tm Γ) -> tm Γ

[_]r : ∀ {Γ Δ} (σ : vsubst Γ Δ) -> (M : tm Γ) -> tm Δ
[_]r σ (▹ x) = ▹ (lookup σ x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (M · N) = ([ σ ]r M) · ([ σ ]r N)
[_]r σ (M [ N ]) = [ vsub-ext σ ]r M [ [ σ ]r N ]