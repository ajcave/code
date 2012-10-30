module stlc where
open import Product
open import FinMap
open import Unit

data tp : Set where
 i : tp
 _⇝_ : (T S : tp) -> tp

data tm (Γ : ctx tp) : (T : tp) -> Set where
 ▹ : ∀ {T} -> (x : var Γ T) -> tm Γ T
 _·_ : ∀ {T S} -> (M : tm Γ (T ⇝ S)) -> (N : tm Γ T) -> tm Γ S
 ƛ : ∀ {T S} -> (M : tm (Γ , T) S) -> tm Γ (T ⇝ S)

[_]r : ∀ {Γ Δ T} (σ : vsubst Γ Δ) -> (M : tm Γ T) -> tm Δ T
[_]r σ (▹ x) = ▹ (lookup σ x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (M · N) = ([ σ ]r M) · ([ σ ]r N)

tsubst : ctx tp -> ctx tp -> Set
tsubst Γ Δ = gsubst Γ (tm Δ)

[_]t : ∀ {Γ Δ T} (σ : tsubst Γ Δ) -> (M : tm Γ T) -> tm Δ T
[_]t σ (▹ x) = lookup σ x
[_]t σ (M · N) = [ σ ]t M · [ σ ]t N
[_]t σ (ƛ M) = ƛ ([ (gmap [ wkn-vsub ]r σ) , (▹ top) ]t M)

id-tsubst : ∀ {Γ} -> tsubst Γ Γ
id-tsubst = interp ▹

