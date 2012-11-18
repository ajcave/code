module nested-univ where
open import FinMap
open import Product
open import Unit
open import Function

record type : Set where
 constructor #prop

mutual
 data functor (ζ : ctx type) : Set where
  ▹ : (A : var ζ #prop) -> functor ζ
  μ : (F : functor (ζ , #prop)) -> functor ζ
-- ν : (F : functor (ζ , #prop)) -> functor ζ
--  _⊃_ : (A : prop) (B : functor ζ) -> functor ζ
  _∧_ : (A B : functor ζ) -> functor ζ
--  _∨_ : (A B : functor ζ) -> functor ζ
--  ⊤ : functor ζ

 prop : Set
 prop = functor ⊡

mutual
 data μ⁺ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ Set)  : Set where
  ⟨_⟩ : (⟦ F ⟧f (ρ , (μ⁺ F ρ))) -> μ⁺ F ρ

 ⟦_⟧f : ∀ {Δ} -> functor Δ -> (ρ : gksubst Δ Set) -> Set
 ⟦_⟧f (▹ A) ρ = [ ρ ]v A
 ⟦_⟧f (μ F) ρ = μ⁺ F ρ
 ⟦_⟧f (A ∧ B) ρ = (⟦ A ⟧f ρ) × (⟦ B ⟧f ρ)

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
 fmap (A ∧ B) ρ1 ρ2 σ (x₁ , x₂) = (fmap A ρ1 ρ2 σ x₁) , (fmap B ρ1 ρ2 σ x₂)

-- Need to try a one-variable-at-a-time version

data arrow' : ∀ {Δ} -> (ρ1 : gksubst Δ Set) -> (ρ2 : gksubst Δ Set) -> Set₁ where
 ⊡ : arrow' tt tt
 _,_ : ∀ {Δ} {ρ1 ρ2 : gksubst Δ Set} (σ : arrow' ρ1 ρ2) {A B} (N : A -> B) -> arrow' {Δ , #prop} (ρ1 , A) (ρ2 , B)
 _!_ : ∀ {Δ} {ρ1 ρ2 : gksubst Δ Set} (σ : arrow' ρ1 ρ2) (F : functor (Δ , #prop))
       -> arrow' {Δ , #prop} (ρ1 , ⟦ μ F ⟧f ρ1) (ρ2 , ⟦ μ F ⟧f ρ2)
 alg : ∀ {Δ} {ρ1 ρ2 : gksubst Δ Set} (σ : arrow' ρ1 ρ2) (F : functor (Δ , #prop)) {C} (m : ⟦ F ⟧f (ρ2 , C) -> C)
       -> arrow' {Δ , #prop} (ρ1 , ⟦ μ F ⟧f ρ1) (ρ2 , C)

mutual
 arrow-lookup' : ∀ {ζ} {σ1 σ2 : gksubst ζ Set} (θ : arrow' σ1 σ2) (A : var ζ #prop) -> [ σ1 ]v A -> [ σ2 ]v A
 arrow-lookup' ⊡ () x
 arrow-lookup' (σ , N) top x = N x
 arrow-lookup' (σ , N) (pop y) x = arrow-lookup' σ y x
 arrow-lookup' (σ ! F) top ⟨ y ⟩ = ⟨ (fmap' F _ _ (σ ! F) y) ⟩ -- fmap' (μ F) _ _ (σ ! F) x if we don't pattern match x to ⟨ y ⟩
 arrow-lookup' (σ ! F) (pop y) x = arrow-lookup' σ y x
 arrow-lookup' (alg σ F m) top ⟨ x ⟩ = m (fmap' F _ _ (alg σ F m) x)
 arrow-lookup' (alg σ F m) (pop y) x = arrow-lookup' σ y x
 
 fmap' : ∀ {Δ} (F : functor Δ) ρ1 ρ2 -> (σ : arrow' ρ1 ρ2) -> (⟦ F ⟧f ρ1) -> (⟦ F ⟧f ρ2)
 fmap' (▹ A) ρ1 ρ2 σ x = arrow-lookup' σ A x
 fmap' (μ F) ρ1 ρ2 σ ⟨ y ⟩ = ⟨ (fmap' F (ρ1 , μ⁺ F ρ1) (ρ2 , μ⁺ F ρ2) (σ ! F) y) ⟩
 fmap' (A ∧ B) ρ1 ρ2 σ (x₁ , x₂) = fmap' A ρ1 ρ2 σ x₁ , fmap' B ρ1 ρ2 σ x₂


--conv :  ∀ {ζ} {σ1 σ2 : gksubst ζ Set} (θ : arrow' σ1 σ2)