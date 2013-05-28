module full-red where
open import lambda
open import untyped-vsub
open import FinMap
open import Product
open import Relation.Binary.PropositionalEquality
open import Unit

data _⟶_ {Γ} : tm Γ -> tm Γ -> Set where
 β : ∀ {M} {N} -> ((ƛ M) · N) ⟶ [ N /x] M
 _·₁_ : ∀ {M1 M2} -> M1 ⟶ M2 -> ∀ N -> (M1 · N) ⟶ (M2 · N)
 _·₂_ : ∀ M {N1 N2} -> N1 ⟶ N2 -> (M · N1) ⟶ (M · N2)
 ƛ : ∀ {M1 M2} -> M1 ⟶ M2 -> (ƛ M1) ⟶ (ƛ M2)

red-sub : ∀ {Γ Δ} {t1 t2 : tm Γ} (σ : tsubst Γ Δ) -> t1 ⟶ t2 -> ([ σ ]t t1) ⟶ ([ σ ]t t2)
red-sub σ (β {M} {N}) = subst (λ α → [ σ ]t (ƛ M · N) ⟶ α) (sub-identity2 σ N M) β
red-sub σ (r ·₁ N) = (red-sub σ r) ·₁ ([ σ ]t N)
red-sub σ (M ·₂ r) = ([ σ ]t M) ·₂ (red-sub σ r)
red-sub σ (ƛ r) = ƛ (red-sub (tsub-ext σ) r)

data _⟶*_ {Γ} : tm Γ -> tm Γ -> Set where
 refl : ∀ {M} -> M ⟶* M
 step1 : ∀ {M N P} -> M ⟶ N -> N ⟶* P -> M ⟶* P

⟶*-trans : ∀ {Γ} {M N P : tm Γ} -> M ⟶* N -> N ⟶* P -> M ⟶* P
⟶*-trans refl r2 = r2
⟶*-trans (step1 x r1) r2 = step1 x (⟶*-trans r1 r2)

data _⟶*s_ {Γ} : ∀ {Δ} -> tsubst Δ Γ -> tsubst Δ Γ -> Set where
 ⊡ : _⟶*s_ {Γ} {⊡} tt tt
 _,_ : ∀ {Δ} {σ1 σ2} {M1 M2 : tm Γ} -> _⟶*s_ {Γ} {Δ} σ1 σ2 -> M1 ⟶* M2 -> _⟶*s_ {Γ} {Δ , *} (σ1 , M1) (σ2 , M2)

_·₃_ : ∀ {Γ} {M1 M2 N1 N2 : tm Γ} -> M1 ⟶* M2 -> N1 ⟶* N2 -> (M1 · N1) ⟶* (M2 · N2)
refl ·₃ refl = refl
refl ·₃ step1 x r2 = step1 (_ ·₂ x) (refl ·₃ r2)
step1 x r1 ·₃ r2 = step1 (x ·₁ _) (r1 ·₃ r2)

ƛ' : ∀ {Γ} {M1 M2 : tm (Γ , *)} -> M1 ⟶* M2 -> (ƛ M1) ⟶* (ƛ M2)
ƛ' refl = refl
ƛ' (step1 x r) = step1 (ƛ x) (ƛ' r)

red-sub-var : ∀ {Γ Δ} (x : var Γ *) {σ1 σ2 : tsubst Γ Δ} -> σ1 ⟶*s σ2 -> lookup σ1 x ⟶* lookup σ2 x
red-sub-var {⊡} () {tt} {tt} r
red-sub-var {Γ , .tt} top {proj₁ , proj₂} {proj₃ , proj₄} (r , x) = x
red-sub-var {Γ , .tt} (pop x) {proj₁ , proj₂} {proj₃ , proj₄} (r , x₁) = red-sub-var x r

red-sub2 : ∀ {Γ Δ} (M : tm Γ) {σ1 σ2 : tsubst Γ Δ} -> σ1 ⟶*s σ2 -> ([ σ1 ]t M) ⟶* ([ σ2 ]t M)
red-sub2 (▹ x) r = red-sub-var x r
red-sub2 (ƛ M) r = ƛ' (red-sub2 M ({!!} , refl))
red-sub2 (M · M₁) r = (red-sub2 M r) ·₃ (red-sub2 M₁ r)
