module untyped-vsub where
open import Unit
open import lambda
open import FinMap
open import Product

[_]r : ∀ {Γ Δ} (σ : vsubst Γ Δ) -> (M : tm Γ) -> tm Δ
[_]r σ (▹ x) = ▹ (lookup σ x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (M · N) = ([ σ ]r M) · ([ σ ]r N)

tsubst : ctx Unitz -> ctx Unitz -> Set
tsubst Γ Δ = gsubst Γ (λ _ -> tm Δ)

tsub-ext : ∀ {Γ Δ} -> tsubst Γ Δ -> tsubst (Γ , *) (Δ , *)
tsub-ext σ = gmap [ wkn-vsub ]r σ , ▹ top

[_]t : ∀ {Γ Δ} (σ : tsubst Γ Δ) -> (M : tm Γ) -> tm Δ
[_]t σ (▹ x) = lookup σ x
[_]t σ (M · N) = [ σ ]t M · [ σ ]t N
[_]t σ (ƛ M) = ƛ ([ tsub-ext σ ]t M)

id-tsubst : ∀ {Γ} -> tsubst Γ Γ
id-tsubst = interp ▹

[_/x] : ∀ {Γ} (N : tm Γ) (M : tm (Γ , *)) -> tm Γ
[ N /x] M = [ id-tsubst , N ]t M

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
sub-identity : ∀ {Γ Δ} (σ : tsubst Γ Δ) (N : tm Γ) M -> [ σ ]t ([ N /x] M) ≡ [ σ , ([ σ ]t N) ]t M
sub-identity σ N M = trustMe

sub-identity2 : ∀ {Γ Δ} (σ : tsubst Γ Δ) (N : tm Γ) M -> [ [ σ ]t N /x] ([ tsub-ext σ ]t M) ≡ [ σ ]t ([ N /x] M)
sub-identity2 σ N M = trustMe