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
open import Function
open import Coinduction
open import Relation.Binary.PropositionalEquality

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
 inf : ∀ (A : Set) (f : A -> bool⁺) -> bool⁺
-- TODO: Probably we don't need arbitrary nesting, just need one sup at the topmost level (like below)

data Complete (C : Set) : Set₁ where
 emb : C -> Complete C
 inf : ∀ (A : Set) (f : A -> C) -> Complete C

Complete-idx : ∀ {C : Set} -> Complete C -> Set
Complete-idx (emb y) = Unit
Complete-idx (inf A f) = A

extract : ∀ {C : Set} (x : Complete C) -> Complete-idx x -> C
extract (emb y) t = y
extract (inf A f) t = f t

inf' : ∀ {C : Set} (A : Set) (f : A -> Complete C) -> Complete C
inf' A f = inf (Σ A (λ x → Complete-idx (f x))) (λ x → extract (f (proj₁ x)) (proj₂ x))

and : Complete Bool -> Complete Bool -> Complete Bool
and (emb true) b = b
and (emb false) _ = emb false
and b (emb true) = b
and _ (emb false) = emb false
and (inf A f) (inf A' f') = inf (A ⊎ A') λ {(inj₁ x) → f x; (inj₂ x) → f' x}

≤′-trans : ∀ {n m p} -> n ≤′ m -> m ≤′ p -> n ≤′ p
≤′-trans r ≤′-refl = r
≤′-trans r (≤′-step m≤′n) = ≤′-step (≤′-trans r m≤′n)

agree : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (n : ℕ) (F : gsubst' Δ (λ x -> ∀ m -> m <′ n -> f x -> f x -> Complete Bool)) (t u : ⟦ T ⟧ f) → Acc _<′_ n -> Complete Bool
agree (▹ X) f zero F t u q = emb true -- variables are implicitly circled
agree (▹ X) f (suc n) F t u q = F X n ≤′-refl t u
agree (μ F) f n F' ⟨ t ⟩ ⟨ u ⟩ (acc rs) = agree F (extend f (μ⁺ F f)) n (extend'
   (λ x → (m : _) → m <′ n → (t u : extend f (μ⁺ F f) x) → Complete Bool)
    F' (λ m x x' x0 → agree (μ F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) x)) x' x0 (rs m x))) t u (acc rs)
agree (ν F) f n F' ⟨ t ⟩ ⟨ u ⟩ (acc rs) = agree F (extend f (ν⁺ F f)) n (extend'
   (λ x → (m : _) → m <′ n → (t u : extend f (ν⁺ F f) x) → Complete Bool)
    F' (λ m x x' x0 → agree (ν F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) x)) x' x0 (rs m x))) (♭ t) (♭ u) (acc rs)
agree (T ⇒ S) f n F t u q = inf' (⟦ T ⟧ init) (λ x → agree S f n F (t x) (u x) q)
agree (T ∧ S) f n F (t1 , t2) (u1 , u2) q = and (agree T f n F t1 u1 q) (agree S f n F t2 u2 q)
agree (T ∨ S) f n F (inj₁ x) (inj₁ x') q = agree T f n F x x' q
agree (T ∨ S) f n F (inj₁ x) (inj₂ y) q = emb false
agree (T ∨ S) f n F (inj₂ y) (inj₁ x) q = emb false
agree (T ∨ S) f n F (inj₂ y) (inj₂ y') q = agree S f n F y y' q
agree ⊤ f n F t u rs = emb true
agree (○ T) f zero F t u q = emb true
agree (○ T) f (suc n) F t u (acc rs) = agree T f n (λ x m x' → F x m (≤′-step x')) t u (rs n ≤′-refl)

agree'' : (T : prop ⊡) (t u : ⟦ T ⟧ init) (n : ℕ) -> Complete Bool
agree'' T t u n = agree T init n (init {F = (λ x -> ∀ m -> m <′ n -> init x -> init x -> Complete Bool)}) t u (<-well-founded n)

test1 : emb true ≡
  (agree'' (μ ((⊤ ∨ ⊤) ∨ ○ (▹ top)))
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₁ unit)) ⟩) ⟩) ⟩)
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₂ unit)) ⟩) ⟩) ⟩)
  (suc (suc (suc zero))))
test1 = refl

test2 : emb false ≡
  (agree'' (μ ((⊤ ∨ ⊤) ∨ ○ (▹ top)))
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₁ unit)) ⟩) ⟩) ⟩)
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₂ unit)) ⟩) ⟩) ⟩)
  (suc (suc (suc (suc zero)))))
test2 = refl

data CoNat : Set₁ where
 zero : CoNat
 suc : ∞ CoNat -> CoNat
 inf : ∀ (A : Set) (f : A -> CoNat) -> CoNat

ω : CoNat
ω = suc (♯ ω)

-- Huh this seems like some kind of monad?
record _⁺ (F : Set) : Set₁ where
 constructor inf
 field
  idx : Set
  f : (idx -> F)

inf⁺ : ∀ {F : Set} (A : Set) -> (f : A -> F ⁺) -> F ⁺
inf⁺ {F} A f = inf (Σ A (λ x → _⁺.idx (f x))) (λ x → _⁺.f (f (proj₁ x)) (proj₂ x))

collapse : bool⁺ -> Bool ⁺
collapse true = inf Unit (λ x → true)
collapse false = inf Unit (λ x → false)
collapse (inf A f) = inf⁺ A (λ x → collapse (f x))

{-
cmin : CoNat -> CoNat -> CoNat
cmin m n = {!!}
-}

agrees-to : (f : ℕ -> Bool ⁺) -> CoNat
agrees-to f with f zero
... | (inf idx f') = inf idx (λ x → foo (f' x))
 where foo : Bool -> CoNat
       foo true = suc (♯ agrees-to (f ∘ suc))
       foo false = zero

--agrees-to' : ∀ (T : prop ⊡) (t u : ⟦ T ⟧ init) -> CoNat
--agrees-to' T t u = agrees-to (λ x → collapse (agree'' T t u x))


-- I think this abides by some kind of "lexicographic" termination/productivity condition?
{-agree' : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (F : gsubst' Δ (λ x -> ∀ (t u : f x) -> CoNat)) (t u : ⟦ T ⟧ f) → CoNat
agree' (▹ X) f F t u = suc (♯ F X t u)
agree' (μ F) f F' ⟨ t ⟩ ⟨ u ⟩ = agree' F (extend f (μ⁺ F f)) (extend' (λ x → (t' u' : extend f (μ⁺ F f) x) → CoNat) F' (λ t' u' → suc (♯ agree' (μ F) f F' u' t'))) t u
agree' (ν F) f F' ⟨ t ⟩ ⟨ u ⟩ = {!!}
agree' (T ⇒ S) f F t u = inf (⟦ T ⟧ init) (λ x → ♯ agree' S f F (t x) (u x))
agree' (T ∧ S) f F t u = cmin (agree' T f F (proj₁ t) (proj₁ u)) (agree' S f F (proj₂ t) (proj₂ u))
agree' (T ∨ S) f F (inj₁ x) (inj₁ x') = agree' T f F x x'
agree' (T ∨ S) f F (inj₁ x) (inj₂ y) = zero
agree' (T ∨ S) f F (inj₂ y) (inj₁ x) = zero
agree' (T ∨ S) f F (inj₂ y) (inj₂ y') = agree' S f F y y'
agree' ⊤ f F t u = ω
agree' (○ T) f F t u = suc (♯ agree' T f F t u) -}