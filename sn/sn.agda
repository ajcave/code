module sn where
open import lambda
open import untyped-vsub
open import full-red
open import Product
open import FinMap
open import Unit

data sn {Γ} (M : tm Γ) : Set where
 intro : (∀ {N} -> M ⟶ N -> sn N) -> sn M

sn⟶* : ∀ {Γ} {M N : tm Γ} -> sn M -> M ⟶* N -> sn N
sn⟶* sm refl = sm
sn⟶* (intro x) (step1 x₁ r) = sn⟶* (x x₁) r 

sn-sub1 : ∀ {Γ Δ} (σ : tsubst Γ Δ) {M N} -> sn ([ σ ]t M) -> M ⟶ N -> sn ([ σ ]t N)
sn-sub1 σ (intro x) r = x (red-sub σ r)

sn-sub2 : ∀ {Γ} {u u' : tm Γ} M -> sn ([ u /x] M) -> u ⟶ u' -> sn ([ u' /x] M)
sn-sub2 M sm r = sn⟶* sm (red-sub2 M ((⟶*s-refl _) , (step1 r refl)))

sn-sub3 : ∀ {Γ Δ} (σ : tsubst Γ Δ) {M} -> sn ([ σ ]t M) -> sn M
sn-sub3 σ (intro x) = intro (λ r → sn-sub3 σ (x (red-sub σ r)))
 
mutual
 lem5 : ∀ {Γ} {u : tm Γ} {t} -> sn u -> sn t -> sn ([ u /x] t) -> ∀ {N} -> (ƛ t · u) ⟶ N -> sn N
 lem5 su st sr β = sr
 lem5 {Γ} {u} su (intro x) sr (ƛ t₁ ·₁ .u) = lem6 su (x t₁) (sn-sub1 (id-tsubst , u) sr t₁)
 lem5 {Γ} {u} {t} (intro x) st sr (.(ƛ t) ·₂ t₁) = lem6 (x t₁) st (sn-sub2 t sr t₁)
 
 lem6 : ∀ {Γ} {u : tm Γ} {t} -> sn u -> sn t -> sn ([ u /x] t) -> sn (ƛ t · u)
 lem6 su st sr = intro (lem5 su st sr)