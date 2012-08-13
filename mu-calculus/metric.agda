{-# OPTIONS --no-positivity-check #-}
module metric where
open import Data.Unit hiding (⊤ ; _≤_)
open import Data.Nat
open import Data.Bool hiding (_∧_ ; _∨_)
open import Induction.Nat
open import Induction.WellFounded
open import Data.Product
open import Data.Sum
open import FinMapF

data prop (Δ : ctx Unit) : Set where
 ▹ : (X : var Δ unit) -> prop Δ
 μ : (F : prop (Δ , unit)) -> prop Δ
 _⇒_ : (T : prop ⊡) (S : prop Δ) -> prop Δ
 _∧_ _∨_ : (T S : prop Δ) -> prop Δ
 ⊤ : prop Δ
 ○ : (T : prop Δ) -> prop Δ

mutual
 data μ⁺ {Δ} (F : prop (Δ , unit)) (f : gksubst Δ Set) : Set where
  ⟨_⟩ : ⟦ F ⟧ (kextend f (μ⁺ F f)) -> μ⁺ F f

 ⟦_⟧ : ∀ {Δ} -> prop Δ -> (f : gksubst Δ Set) -> Set
 ⟦_⟧ (▹ X) f = f X
 ⟦_⟧ (μ F) f = μ⁺ F f
 ⟦_⟧ (T ⇒ S) f = ⟦ T ⟧ init → ⟦ S ⟧ f -- Almost passes positivity check, except for this
 ⟦_⟧ (T ∧ S) f = ⟦ T ⟧ f × ⟦ S ⟧ f
 ⟦_⟧ (T ∨ S) f = (⟦ T ⟧ f) ⊎ (⟦ S ⟧ f)
 ⟦_⟧ ⊤ f = Unit
 ⟦_⟧ (○ T) f = ⟦ T ⟧ f

data bool⁺ : Set₁ where
 true false : bool⁺
 sup : ∀ (A : Set) (f : A -> bool⁺) -> bool⁺

and : bool⁺ -> bool⁺ -> bool⁺
and true b = b
and b true = b
and false _ = false
and _ false = false
and (sup A f) (sup A' f') = sup (A ⊎ A') (λ { (inj₁ x) → f x; (inj₂ y) → f' y})

agree : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (n : ℕ) (F : gsubst' Δ (λ x -> ∀ m -> m <′ n -> f x -> f x -> bool⁺)) (t u : ⟦ T ⟧ f) → Acc _<′_ n -> bool⁺
agree (▹ X) f zero F t u q = true
agree (▹ X) f (suc n) F t u q = F X n ≤′-refl t u
agree (μ F) f n F' ⟨ t ⟩ ⟨ u ⟩ (acc rs) = agree F (extend f (μ⁺ F f)) n (extend'
   (λ x → (m : _) → m <′ n → extend f (μ⁺ F f) x → extend f (μ⁺ F f) x → bool⁺)
    F' (λ m x x' x0 → agree (μ F) f m (λ x1 m' x2 → F' x1 m' {!!}) x' x0 (rs m x))) t u (acc rs)
agree (T ⇒ S) f n F t u q = sup (⟦ T ⟧ init) (λ x → agree S f n F (t x) (u x) q)
agree (T ∧ S) f n F t u q = and (agree T f n F (proj₁ t) (proj₁ u) q) (agree S f n F (proj₂ t) (proj₂ u) q)
agree (T ∨ S) f n F t u q = {!!}
agree ⊤ f n F t u rs = {!!}
agree (○ T) f zero F t u q = true
agree (○ T) f (suc n) F t u (acc rs) = agree T f n (λ x m x' → F x m (≤′-step x')) t u (rs n ≤′-refl)