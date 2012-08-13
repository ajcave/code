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
open import Coinduction

data prop (Δ : ctx Unit) : Set where
 ▹ : (X : var Δ unit) -> prop Δ
 μ ν : (F : prop (Δ , unit)) -> prop Δ
 _⇒_ : (T : prop ⊡) (S : prop Δ) -> prop Δ
 _∧_ _∨_ : (T S : prop Δ) -> prop Δ
 ⊤ : prop Δ
 ○ : (T : prop Δ) -> prop Δ

mutual
 data ν⁺ {Δ} (F : prop (Δ , unit)) (f : gksubst Δ Set) : Set where
  ⟨_⟩ : ∞ (⟦ F ⟧ (kextend f (ν⁺ F f))) -> ν⁺ F f

 data μ⁺ {Δ} (F : prop (Δ , unit)) (f : gksubst Δ Set) : Set where
  ⟨_⟩ : ⟦ F ⟧ (kextend f (μ⁺ F f)) -> μ⁺ F f

 ⟦_⟧ : ∀ {Δ} -> prop Δ -> (f : gksubst Δ Set) -> Set
 ⟦_⟧ (▹ X) f = f X
 ⟦_⟧ (μ F) f = μ⁺ F f
 ⟦_⟧ (ν F) f = ν⁺ F f
 ⟦_⟧ (T ⇒ S) f = ⟦ T ⟧ init → ⟦ S ⟧ f -- Almost passes positivity check, except for this
 ⟦_⟧ (T ∧ S) f = ⟦ T ⟧ f × ⟦ S ⟧ f
 ⟦_⟧ (T ∨ S) f = (⟦ T ⟧ f) ⊎ (⟦ S ⟧ f)
 ⟦_⟧ ⊤ f = Unit
 ⟦_⟧ (○ T) f = ⟦ T ⟧ f

-- We could lower this to Set by restricting the A to be in the prop universe
data bool⁺ : Set₁ where
 true false : bool⁺
 sup : ∀ (A : Set) (f : A -> bool⁺) -> bool⁺
-- TODO: Probably we don't need arbitrary nesting, just need one sup at the topmost level

and : bool⁺ -> bool⁺ -> bool⁺
and true b = b
and b true = b
and false _ = false
and _ false = false
and (sup A f) (sup A' f') = sup (A ⊎ A') (λ { (inj₁ x) → f x; (inj₂ y) → f' y})

≤′-trans : ∀ {n m p} -> n ≤′ m -> m ≤′ p -> n ≤′ p
≤′-trans r ≤′-refl = r
≤′-trans r (≤′-step m≤′n) = ≤′-step (≤′-trans r m≤′n)

agree : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (n : ℕ) (F : gsubst' Δ (λ x -> ∀ m -> m <′ n -> f x -> f x -> bool⁺)) (t u : ⟦ T ⟧ f) → Acc _<′_ n -> bool⁺
agree (▹ X) f zero F t u q = true -- variables are implicitly circled
agree (▹ X) f (suc n) F t u q = F X n ≤′-refl t u
agree (μ F) f n F' ⟨ t ⟩ ⟨ u ⟩ (acc rs) = agree F (extend f (μ⁺ F f)) n (extend'
   (λ x → (m : _) → m <′ n → extend f (μ⁺ F f) x → extend f (μ⁺ F f) x → bool⁺)
    F' (λ m x x' x0 → agree (μ F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) x)) x' x0 (rs m x))) t u (acc rs)
agree (ν F) f n F' ⟨ t ⟩ ⟨ u ⟩ (acc rs) = agree F (extend f (ν⁺ F f)) n (extend'
   (λ x → (m : _) → m <′ n → extend f (ν⁺ F f) x → extend f (ν⁺ F f) x → bool⁺)
    F' (λ m x x' x0 → agree (ν F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) x)) x' x0 (rs m x))) (♭ t) (♭ u) (acc rs)
agree (T ⇒ S) f n F t u q = sup (⟦ T ⟧ init) (λ x → agree S f n F (t x) (u x) q)
agree (T ∧ S) f n F t u q = and (agree T f n F (proj₁ t) (proj₁ u) q) (agree S f n F (proj₂ t) (proj₂ u) q)
agree (T ∨ S) f n F (inj₁ x) (inj₁ x') q = agree T f n F x x' q
agree (T ∨ S) f n F (inj₁ x) (inj₂ y) q = false
agree (T ∨ S) f n F (inj₂ y) (inj₁ x) q = false
agree (T ∨ S) f n F (inj₂ y) (inj₂ y') q = agree S f n F y y' q
agree ⊤ f n F t u rs = true
agree (○ T) f zero F t u q = true
agree (○ T) f (suc n) F t u (acc rs) = agree T f n (λ x m x' → F x m (≤′-step x')) t u (rs n ≤′-refl)

data CoNat : Set where
 zero : CoNat
 suc : ∞ CoNat -> CoNat
-- inf : ∀ (A : Set) (f : A -> ∞ CoNat) -> CoNat

ω : CoNat
ω = suc (♯ ω)

data CoNat⁺ : Set₁ where
 inf : ∀ (A : Set) (f : A -> CoNat) -> CoNat⁺ 

inj : CoNat -> CoNat⁺
inj n = inf Unit (λ unit -> n)

suc⁺ : CoNat⁺ -> CoNat⁺
suc⁺ (inf A f) = inf A (λ x → suc (♯ f x))

zero⁺ : CoNat⁺
zero⁺ = inf Unit (λ unit -> zero)

cmin : CoNat⁺ -> CoNat⁺ -> CoNat⁺
cmin (inf A f) (inf A' f') = inf (A ⊎ A') λ {(inj₁ x) → f x; (inj₂ x) → f' x}

agree' : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (F : gsubst' Δ (λ x -> f x -> f x -> CoNat)) (t u : ⟦ T ⟧ f) → CoNat⁺
agree' (▹ X) f F t u = {!!}
agree' (μ F) f F' t u = {!!}
agree' (ν F) f F' t u = {!!}
agree' (T ⇒ S) f F t u = {!!}
agree' (T ∧ S) f F t u = cmin (agree' T f F (proj₁ t) (proj₁ u)) (agree' S f F (proj₂ t) (proj₂ u))
agree' (T ∨ S) f F (inj₁ x) (inj₁ x') = agree' T f F x x'
agree' (T ∨ S) f F (inj₁ x) (inj₂ y) = zero⁺
agree' (T ∨ S) f F (inj₂ y) (inj₁ x) = zero⁺
agree' (T ∨ S) f F (inj₂ y) (inj₂ y') = agree' S f F y y'
agree' ⊤ f F t u = inj ω
agree' (○ T) f F t u = suc⁺ (agree' T f F t u)