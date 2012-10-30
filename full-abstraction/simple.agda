module simple where
open import Relation.Binary.PropositionalEquality hiding (subst ; [_] )
open import FinMap
open import stlc
open import Product
open import Data.Empty

data _≈_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 ▹ : ∀ {T} (x : var Γ T) -> (▹ x) ≈ (▹ x)
 _·_ : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 N2 : tm Γ T} -> M1 ≈ M2 -> N1 ≈ N2 -> (M1 · N1) ≈ (M2 · N2)
 ƛ : ∀ {T S} {M1 M2 : tm (Γ , T) S} -> M1 ≈ M2 -> (ƛ M1) ≈ (ƛ M2)
 β : ∀ {T S} (M : tm (Γ , T) S) (N : tm Γ T) -> ((ƛ M) · N) ≈ [ id-tsubst , N ]t M
 η : ∀ {T S} (M : tm Γ (T ⇝ S)) -> M ≈ (ƛ ([ wkn-vsub ]r M · (▹ top)))
 ≈-trans : ∀ {T} {M N P : tm Γ T} -> M ≈ N -> N ≈ P -> M ≈ P
 ≈-sym : ∀ {T} {M N : tm Γ T} -> M ≈ N -> N ≈ M

≈-refl : ∀ {Γ T} {M : tm Γ T} -> M ≈ M
≈-refl {M = ▹ y} = ▹ y
≈-refl {M = M · N} = ≈-refl · ≈-refl
≈-refl {M = ƛ M} = ƛ ≈-refl

sem : (T : tp) -> Set
sem i = ⊥
sem (T ⇝ S) = sem T → sem S

⟦_⟧ : ∀ {Γ T} -> tm Γ T -> gsubst Γ sem -> sem T
⟦_⟧ (▹ x) σ = lookup σ x
⟦_⟧ (M · N) σ = ⟦ M ⟧ σ (⟦ N ⟧ σ)
⟦_⟧ (ƛ M) σ = λ x → ⟦ M ⟧ (σ , x)

postulate
 funext : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g

comp : ∀ {Γ Δ T} (M : tm Γ T) (σ : tsubst Γ Δ) (ρ : gsubst Δ sem) -> ⟦ [ σ ]t M ⟧ ρ ≡ ⟦ M ⟧ (gmap (λ x → ⟦ x ⟧ ρ) σ)
comp (▹ x) σ ρ = sym (lookup-gmap (λ x' → ⟦ x' ⟧ ρ) σ x)
comp (M · N) σ ρ = cong₂ (λ α β' → α β') (comp M σ ρ) (comp N σ ρ)
comp (ƛ M) σ ρ = {!!}

soundness : ∀ {Γ T} -> {M1 M2 : tm Γ T} -> M1 ≈ M2 -> (σ : gsubst Γ sem)  -> ⟦ M1 ⟧ σ ≡ ⟦ M2 ⟧ σ
soundness (▹ x) σ = refl
soundness (M · N) σ = cong₂ (λ α β' → α β') (soundness M σ) (soundness N σ)
soundness (ƛ M) σ = {!funext!}
soundness (β M N) σ = trans {!!} (sym (comp M (id-tsubst , N) σ))
soundness (η M1) σ = {!+!}
soundness (≈-trans p1 p2) σ = trans (soundness p1 σ) (soundness p2 σ)
soundness (≈-sym p) σ = sym (soundness p σ)