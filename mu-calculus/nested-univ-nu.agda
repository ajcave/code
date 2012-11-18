module nested-univ-nu where
open import FinMap
open import Product
open import Unit
open import Function
open import Coinduction hiding (fold; unfold)

record type : Set where
 constructor #prop

mutual
 data functor (ζ : ctx type) : Set where
  ▹ : (A : var ζ #prop) -> functor ζ
  μ : (F : functor (ζ , #prop)) -> functor ζ
  ν : (F : functor (ζ , #prop)) -> functor ζ
--  _⊃_ : (A : prop) (B : functor ζ) -> functor ζ
  _∧_ : (A B : functor ζ) -> functor ζ
--  _∨_ : (A B : functor ζ) -> functor ζ
--  ⊤ : functor ζ

 prop : Set
 prop = functor ⊡

mutual
 data μ⁺ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ Set)  : Set where
  ⟨_⟩ : (⟦ F ⟧f (ρ , (μ⁺ F ρ))) -> μ⁺ F ρ

 data ν⁺ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ Set)  : Set where
  ⟨_⟩ : ∞ (⟦ F ⟧f (ρ , (ν⁺ F ρ))) -> ν⁺ F ρ

 ⟦_⟧f : ∀ {Δ} -> functor Δ -> (ρ : gksubst Δ Set) -> Set
 ⟦_⟧f (▹ A) ρ = [ ρ ]v A
 ⟦_⟧f (μ F) ρ = μ⁺ F ρ
 ⟦ ν F ⟧f ρ = ν⁺ F ρ
 ⟦_⟧f (A ∧ B) ρ = (⟦ A ⟧f ρ) × (⟦ B ⟧f ρ)

out : ∀ {Δ} {F : functor (Δ , #prop)} {ρ : gksubst Δ Set} -> ν⁺ F ρ -> ⟦ F ⟧f (ρ , (ν⁺ F ρ))
out ⟨ y ⟩ = ♭ y

data arrow : ∀ {Δ} -> (ρ1 : gksubst Δ Set) -> (ρ2 : gksubst Δ Set) -> Set₁ where
 ⊡ : arrow tt tt
 _,_ : ∀ {Δ} {ρ1 ρ2 : gksubst Δ Set} (σ : arrow ρ1 ρ2) {A B} (N : A -> B) -> arrow {Δ , #prop} (ρ1 , A) (ρ2 , B)

arrow-lookup : ∀ {ζ} {σ1 σ2 : gksubst ζ Set} (θ : arrow σ1 σ2) (A : var ζ #prop) -> [ σ1 ]v A -> [ σ2 ]v A
arrow-lookup ⊡ ()
arrow-lookup (θ , N) top = N
arrow-lookup (θ , N) (pop y) = arrow-lookup θ y

mutual
 μmap : ∀ {Δ} (F : functor (Δ , #prop)) ρ1 ρ2 -> (σ : arrow ρ1 ρ2) -> μ⁺ F ρ1 -> μ⁺ F ρ2
 μmap F ρ1 ρ2 σ ⟨ y ⟩ = ⟨ (fmap F (ρ1 , μ⁺ F ρ1) (ρ2 , μ⁺ F ρ2) (σ , μmap F ρ1 ρ2 σ) y) ⟩ 

 fmap : ∀ {Δ} (F : functor Δ) ρ1 ρ2 -> (σ : arrow ρ1 ρ2) -> (⟦ F ⟧f ρ1) -> (⟦ F ⟧f ρ2)
 fmap (▹ A) ρ1 ρ2 σ x = arrow-lookup σ A x
 fmap (μ F) ρ1 ρ2 σ x = μmap F ρ1 ρ2 σ x
 fmap (ν F) ρ1 ρ2 σ x = {!!}
 fmap (A ∧ B) ρ1 ρ2 σ (x₁ , x₂) = (fmap A ρ1 ρ2 σ x₁) , (fmap B ρ1 ρ2 σ x₂)

-- Need to try a one-variable-at-a-time version

mutual
 data arr1 : Set -> Set -> Set₁ where
  ▸ : ∀ {A B} -> (A -> B) -> arr1 A B
  fold⁻ : ∀ {Δ} {ρ1 ρ2 : gksubst Δ Set} (F : functor (Δ , #prop)) (σ : arrow' ρ1 ρ2) {C} (m : ⟦ F ⟧f (ρ2 , C) -> C)
       -> arr1 (⟦ μ F ⟧f ρ1) C
  unfold⁻ : ∀ {Δ} {ρ1 ρ2 : gksubst Δ Set} (F : functor (Δ , #prop)) (σ : arrow' ρ1 ρ2) {C} (m : C -> ⟦ F ⟧f (ρ1 , C))
       -> arr1 C (⟦ ν F ⟧f ρ2)

 data arrow' : ∀ {Δ} -> (ρ1 : gksubst Δ Set) -> (ρ2 : gksubst Δ Set) -> Set₁ where
  ⊡ : arrow' tt tt
  _,_ : ∀ {Δ} {ρ1 ρ2 : gksubst Δ Set} (σ : arrow' ρ1 ρ2) {A B} (N : arr1 A B) -> arrow' {Δ , #prop} (ρ1 , A) (ρ2 , B)

mutual
 arrow-lookup' : ∀ {ζ} {σ1 σ2 : gksubst ζ Set} (θ : arrow' σ1 σ2) (A : var ζ #prop) -> [ σ1 ]v A -> [ σ2 ]v A
 arrow-lookup' ⊡ () x
 arrow-lookup' (σ , ▸ N) top x = N x
 arrow-lookup' (σ , fold⁻ F σ' m) top x = fold F σ' m x
 arrow-lookup' (σ , unfold⁻ F σ' m) top x = unfold F σ' m x
 arrow-lookup' (σ , N) (pop y) x = arrow-lookup' σ y x
 
 fmap' : ∀ {Δ} (F : functor Δ) ρ1 ρ2 -> (σ : arrow' ρ1 ρ2) -> (⟦ F ⟧f ρ1) -> (⟦ F ⟧f ρ2)
 fmap' (▹ A) ρ1 ρ2 σ x = arrow-lookup' σ A x
 fmap' (μ F) ρ1 ρ2 σ y = fold F σ ⟨_⟩ y
 fmap' (ν F) ρ1 ρ2 σ y = unfold F σ out y
 fmap' (A ∧ B) ρ1 ρ2 σ (x₁ , x₂) = fmap' A ρ1 ρ2 σ x₁ , fmap' B ρ1 ρ2 σ x₂

 fold : ∀ {Δ} (F : functor (Δ , #prop)) {C} {ρ1 ρ2} (σ : arrow' ρ1 ρ2) -> (⟦ F ⟧f (ρ2 , C) -> C) -> ⟦ μ F ⟧f ρ1 -> C
 fold F σ m ⟨ y ⟩ = m (fmap' F _ _ (σ , fold⁻ F σ m) y)

 unfold : ∀ {Δ} (F : functor (Δ , #prop)) {C} {ρ1 ρ2} (σ : arrow' ρ1 ρ2) -> (C -> ⟦ F ⟧f (ρ1 , C)) -> C -> ⟦ ν F ⟧f ρ2
 unfold F σ m y = ⟨ (♯ fmap' F _ _ (σ , unfold⁻ F σ m) (m y)) ⟩
-- TODO: I think we could get rid of the θ part by doing another fmap?

--conv :  ∀ {ζ} {σ1 σ2 : gksubst ζ Set} (θ : arrow' σ1 σ2)