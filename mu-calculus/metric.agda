{-# OPTIONS --no-positivity-check #-}
module metric where
open import Data.Unit hiding (⊤ ; _≤_)
open import Data.Nat
open import Data.Empty
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
 ▹○ : (X : var Δ unit) -> prop Δ
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
 ⟦_⟧ (▹○ X) f = f X
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

-- TODO: This seems like a monad or a functor or something of some kind...
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

-- Ah, we could just as well be defining a Prop stating that they agree up to n, i.e. that they are equal in ≈ⁿ
agree : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (n : ℕ) (F : gsubst' Δ (λ x -> ∀ m -> m <′ n -> f x -> f x -> Complete Bool)) (t u : ⟦ T ⟧ f) → Acc _<′_ n -> Complete Bool
agree (▹○ X) f zero F t u q = emb true -- variables are implicitly circled
agree (▹○ X) f (suc n) F t u q = F X n ≤′-refl t u
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
  (agree'' (μ ((⊤ ∨ ⊤) ∨ (▹○ top)))
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₁ unit)) ⟩) ⟩) ⟩)
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₂ unit)) ⟩) ⟩) ⟩)
  (suc zero))
test1 = refl

test2 : emb false ≡
  (agree'' (μ ((⊤ ∨ ⊤) ∨ (▹○ top)))
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₁ unit)) ⟩) ⟩) ⟩)
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₂ unit)) ⟩) ⟩) ⟩)
  (suc (suc (suc (suc zero)))))
test2 = refl

-- Hmm I wonder if we can make it so we only need one inf?
-- i.e. switch to regular CoNat after inf
data CoNat : Set₁ where
 zero : CoNat
 suc : ∞ CoNat -> CoNat
 inf : ∀ (A : Set) (f : A -> CoNat) -> CoNat

agrees-to : (f : ℕ -> Complete Bool) -> CoNat
agrees-to f with f zero
agrees-to f | emb true = suc (♯ agrees-to (f ∘ suc))
agrees-to f | emb false = zero
... | (inf idx f') = inf idx (λ x → foo (f' x))
 where foo : Bool -> CoNat
       foo true = suc (♯ agrees-to (f ∘ suc))
       foo false = zero

agrees-to' : ∀ (T : prop ⊡) (t u : ⟦ T ⟧ init) -> CoNat
agrees-to' T t u = agrees-to (λ x → agree'' T t u x)

cast : CoNat -> ℕ
cast zero = zero
cast (suc y) = suc (cast (♭ y))
cast (inf A f) = {!!}

test3 : ℕ
test3 =  cast (agrees-to' (μ ((⊤ ∨ ⊤) ∨ (▹○ top)))
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₁ unit)) ⟩) ⟩) ⟩)
  (⟨ (inj₂ ⟨ (inj₂ ⟨ (inj₁ (inj₂ unit)) ⟩) ⟩) ⟩)
  )

-- TODO: Now, can we show that this is in fact an ultrametric, and that each type satisfies its universal property
-- (for contraction mappings)? (Especially the fixed points)

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


-- We're actually defining the equivalence relation ≈ⁿ here!
agree2 : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (n : ℕ) (F : gsubst' Δ (λ x -> ∀ m -> m <′ n -> f x -> f x -> Set)) (t u : ⟦ T ⟧ f) → Acc _<′_ n -> Set
agree2 (▹○ X) f zero F t u q = Unit -- Variables are implicitly circled
agree2 (▹○ X) f (suc n) F t u q = F X n ≤′-refl t u
agree2 (μ F) f n F' ⟨ t ⟩ ⟨ u ⟩ (acc rs) = agree2 F (extend f (μ⁺ F f)) n (extend'
   (λ x → (m : _) → m <′ n → (t u : extend f (μ⁺ F f) x) → Set)
    F' (λ m x x' x0 → agree2 (μ F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) x)) x' x0 (rs m x))) t u (acc rs)
agree2 (ν F) f n F' ⟨ t ⟩ ⟨ u ⟩ (acc rs) = agree2 F (extend f (ν⁺ F f)) n (extend'
   (λ x → (m : _) → m <′ n → (t u : extend f (ν⁺ F f) x) → Set)
    F' (λ m x x' x0 → agree2 (ν F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) x)) x' x0 (rs m x))) (♭ t) (♭ u) (acc rs)
agree2 (T ⇒ S) f n F t u q = (x : ⟦ T ⟧ init) → agree2 S f n F (t x) (u x) q
agree2 (T ∧ S) f n F (t₁ , t₂) (u₁ , u₂) q = (agree2 T f n F t₁ u₁ q) × (agree2 S f n F t₂ u₂ q)
agree2 (T ∨ S) f n F (inj₁ x) (inj₁ x') q = agree2 T f n F x x' q
agree2 (T ∨ S) f n F (inj₁ x) (inj₂ y) q = ⊥
agree2 (T ∨ S) f n F (inj₂ y) (inj₁ x) q = ⊥
agree2 (T ∨ S) f n F (inj₂ y) (inj₂ y') q = agree2 S f n F y y' q
agree2 ⊤ f n F t u q = Unit
agree2 (○ T) f zero F t u q = Unit
agree2 (○ T) f (suc n) F t u (acc rs) = agree2 T f n (λ x m x' → F x m (≤′-step x')) t u (rs n ≤′-refl)

agree2' : ∀ (T : prop ⊡) (t u : ⟦ T ⟧ init) -> ℕ -> Set
agree2' T t u n = agree2 T init n (init {F = λ x → (m : _) → m <′ n → init x → init x → Set}) t u (<-well-founded n)

agree2-refl : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (n : ℕ) (F : gsubst' Δ (λ x -> ∀ m -> m <′ n -> f x -> f x -> Set)) (F-refl : gsubst' Δ (λ x -> ∀ m (p : m <′ n) (t : f x) -> F x m p t t)) (t : ⟦ T ⟧ f) → (p : Acc _<′_ n) -> agree2 T f n F t t p
agree2-refl (▹○ X) f zero F Fr t p = unit
agree2-refl (▹○ X) f (suc n) F Fr t p = Fr X n ≤′-refl t
agree2-refl (μ F) f n F' Fr ⟨ t ⟩ (acc rs) = agree2-refl F _ n (extend'
   (λ x → (m : _) → m <′ n → (t u : extend f (μ⁺ F f) x) → Set)
    F' (λ m x x' x0 → agree2 (μ F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) x)) x' x0 (rs m x)))
   (extend'
      (λ x → (m : _) (p : m <′ n) (t' : extend f (μ⁺ F f) x) →
        extend' (λ x' → (m' : _) → m' <′ n → (t0 u : extend f (μ⁺ F f) x') → Set)
                F'
                 (λ m' x' x0 x1 → agree2 (μ F) f m' (λ x2 m0 x3 → F' x2 m0 (≤′-trans (≤′-step x3) x')) x0 x1 (rs m' x'))
         x m p t' t')
   Fr (λ m p t' → agree2-refl (μ F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) p)) (λ x m' p' t0 → Fr _ _ _ _) t' (rs m p))) t (acc rs)
agree2-refl (ν F) f n F' Fr ⟨ t ⟩ (acc rs) = agree2-refl F _ n (extend'
   (λ x → (m : _) → m <′ n → (t u : extend f (ν⁺ F f) x) → Set)
    F' (λ m x x' x0 → agree2 (ν F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) x)) x' x0 (rs m x)))
   (extend'
      (λ x → (m : _) (p : m <′ n) (t' : extend f (ν⁺ F f) x) →
        extend' (λ x' → (m' : _) → m' <′ n → (t0 u : extend f (ν⁺ F f) x') → Set)
                F'
                 (λ m' x' x0 x1 → agree2 (ν F) f m' (λ x2 m0 x3 → F' x2 m0 (≤′-trans (≤′-step x3) x')) x0 x1 (rs m' x'))
         x m p t' t')
   Fr (λ m p t' → agree2-refl (ν F) f m (λ x1 m' x2 → F' x1 m' (≤′-trans (≤′-step x2) p)) (λ x m' p' t0 → Fr _ _ _ _) t' (rs m p))) (♭ t) (acc rs)
agree2-refl (T ⇒ S) f n F Fr t p = λ x → agree2-refl S f n F Fr (t x) p
agree2-refl (T ∧ S) f n F Fr (t₁ , t₂) p = (agree2-refl T f n F Fr t₁ p) , (agree2-refl S f n F Fr t₂ p)
agree2-refl (T ∨ S) f n F Fr (inj₁ x) p = agree2-refl T f n F Fr x p
agree2-refl (T ∨ S) f n F Fr (inj₂ y) p = agree2-refl S f n F Fr y p
agree2-refl ⊤ f n F Fr t p = unit
agree2-refl (○ T) f zero F Fr t p = unit
agree2-refl (○ T) f (suc n) F Fr t (acc rs) = agree2-refl T f n (λ x m x' → F x m (≤′-step x')) (λ x m p → Fr _ _ _) t (rs n ≤′-refl)

syntax agree2 T t u n = t ≈[ T , n ] u

≈-refl : ∀ {T : prop ⊡} {n : ℕ} {t} -> agree2' T t t n
≈-refl {T} {n} {t} = agree2-refl T init n (init {F = λ x → (m : _) → m <′ n → init x → init x → Set}) (init {F = λ x → ∀ m (p : m <′ n) (t' : init x) → init {F = λ x → (m : _) → m <′ n → init x → init x → Set} x m p t' t'}) t (<-well-founded n)

agree2-sym : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (n : ℕ)
 (F : gsubst' Δ (λ x -> ∀ m -> m <′ n -> f x -> f x -> Set))
 (F-sym : gsubst' Δ (λ x -> ∀ m (p : m <′ n) (t u : f x) -> F x m p t u -> F x m p u t))
 (t u : ⟦ T ⟧ f) → (p : Acc _<′_ n) -> agree2 T f n F t u p -> agree2 T f n F u t p
agree2-sym (▹○ X) f zero F Fs t u p x = unit
agree2-sym (▹○ X) f (suc n) F Fs t u p x = Fs X n ≤′-refl t u x
agree2-sym (μ F) f n F' Fs ⟨ t ⟩ ⟨ u ⟩ (acc rs) x = agree2-sym F (extend f (μ⁺ F f)) n (extend'
   (λ x' → (m : _) → m <′ n → (t' u' : extend f (μ⁺ F f) x') → Set) F'
    (λ m x' t' u' → agree2 (μ F) f m (λ x0 m' z → F' x0 m' (≤′-trans (≤′-step z) x')) t' u' (rs m x')))
   (extend' (λ x' → (m : ℕ) (p : suc m ≤′ n) (t' u' : extend f (μ⁺ F f) x') →
         extend' (λ x0 → (m' : ℕ) → suc m' ≤′ n → extend f (μ⁺ F f) x0 → extend f (μ⁺ F f) x0 → Set)
         F'
         (λ m' x0 t0 u0 → agree2 (μ F) f m' (λ x1 m0 z → F' x1 m0 (≤′-trans (≤′-step z) x0)) t0 u0 (rs m' x0))
         x' m p t' u' →
         extend' (λ x0 → (m' : ℕ) → suc m' ≤′ n → extend f (μ⁺ F f) x0 → extend f (μ⁺ F f) x0 → Set)
         F'
         (λ m' x0 t0 u0 → agree2 (μ F) f m' (λ x1 m0 z → F' x1 m0 (≤′-trans (≤′-step z) x0)) t0 u0 (rs m' x0))
         x' m p u' t')
      Fs (λ m p t' u' x' → agree2-sym (μ F) f m (λ x0 m' x1 → F' x0 m' (≤′-trans (≤′-step x1) p)) (λ x0 m' p' t0 u0 x1 → Fs x0 m' (≤′-trans (≤′-step p') p) t0 u0 x1) t' u' (rs m p) x'))
   t u (acc rs) x
agree2-sym (ν F) f n F' Fs ⟨ t ⟩ ⟨ u ⟩ (acc rs) x = agree2-sym F (extend f (ν⁺ F f)) n (extend'
   (λ x' → (m : _) → m <′ n → (t' u' : extend f (ν⁺ F f) x') → Set) F'
    (λ m x' t' u' → agree2 (ν F) f m (λ x0 m' z → F' x0 m' (≤′-trans (≤′-step z) x')) t' u' (rs m x')))
   (extend' (λ x' → (m : ℕ) (p : suc m ≤′ n) (t' u' : extend f (ν⁺ F f) x') →
         extend' (λ x0 → (m' : ℕ) → suc m' ≤′ n → extend f (ν⁺ F f) x0 → extend f (ν⁺ F f) x0 → Set)
         F'
         (λ m' x0 t0 u0 → agree2 (ν F) f m' (λ x1 m0 z → F' x1 m0 (≤′-trans (≤′-step z) x0)) t0 u0 (rs m' x0))
         x' m p t' u' →
         extend' (λ x0 → (m' : ℕ) → suc m' ≤′ n → extend f (ν⁺ F f) x0 → extend f (ν⁺ F f) x0 → Set)
         F'
         (λ m' x0 t0 u0 → agree2 (ν F) f m' (λ x1 m0 z → F' x1 m0 (≤′-trans (≤′-step z) x0)) t0 u0 (rs m' x0))
         x' m p u' t')
      Fs (λ m p t' u' x' → agree2-sym (ν F) f m (λ x0 m' x1 → F' x0 m' (≤′-trans (≤′-step x1) p)) (λ x0 m' p' t0 u0 x1 → Fs x0 m' (≤′-trans (≤′-step p') p) t0 u0 x1) t' u' (rs m p) x'))
   (♭ t) (♭ u) (acc rs) x
agree2-sym (T ⇒ S) f n F Fs t u p x = λ x' → agree2-sym S f n F Fs (t x') (u x') p (x x')
agree2-sym (T ∧ S) f n F Fs (t₁ , t₂) (u₁ , u₂) p (x₁ , x₂) = agree2-sym T f n F Fs t₁ u₁ p x₁ , agree2-sym S f n F Fs t₂ u₂ p x₂
agree2-sym (T ∨ S) f n F Fs (inj₁ x) (inj₁ x') p x0 = agree2-sym T f n F Fs x x' p x0
agree2-sym (T ∨ S) f n F Fs (inj₁ x) (inj₂ y) p ()
agree2-sym (T ∨ S) f n F Fs (inj₂ y) (inj₁ x) p ()
agree2-sym (T ∨ S) f n F Fs (inj₂ y) (inj₂ y') p x = agree2-sym S f n F Fs y y' p x
agree2-sym ⊤ f n F Fs t u p x = unit
agree2-sym (○ T) f zero F Fs t u p x = unit
agree2-sym (○ T) f (suc n) F Fs t u (acc rs) x = agree2-sym T f n (λ x' m x0 → F x' m (≤′-step x0)) (λ x' m p → Fs x' m (≤′-step p)) t u (rs n ≤′-refl) x 

≈-sym : ∀ {T : prop ⊡} {n : ℕ} {t u} -> agree2' T t u n -> agree2' T u t n
≈-sym {T} {n} {t} {u} x = agree2-sym T init n (init {F = λ x → (m : _) → m <′ n → init x → init x → Set})
  (init {F = λ x' → (m : ℕ) (p : suc m ≤′ n) (t' u' : init x') →
        init {F = λ x → (m : _) → m <′ n → init x → init x → Set} x' m p t' u'
      → init {F = λ x → (m : _) → m <′ n → init x → init x → Set} x' m p u' t'})
  t u (<-well-founded n) x

agree2-trans : ∀ {Δ} (T : prop Δ) (f : gksubst Δ Set) (n : ℕ)
 (F : gsubst' Δ (λ x -> ∀ m -> m <′ n -> f x -> f x -> Set))
 (F-trans : gsubst' Δ (λ x -> ∀ m (p : m <′ n) (t u v : f x) -> F x m p t u -> F x m p u v -> F x m p t v))
 (t u v : ⟦ T ⟧ f) → (p : Acc _<′_ n) -> agree2 T f n F t u p -> agree2 T f n F u v p -> agree2 T f n F t v p
agree2-trans (▹○ X) f zero F Ft t u v p r1 r2 = unit
agree2-trans (▹○ X) f (suc n) F Ft t u v p r1 r2 = Ft X n ≤′-refl t u v r1 r2
agree2-trans (μ F) f n F' Ft ⟨ t ⟩ ⟨ u ⟩ ⟨ v ⟩ (acc rs) r1 r2 = agree2-trans F (extend f (μ⁺ F f)) n
  (extend' (λ x → (m : ℕ) → m <′ n → extend f (μ⁺ F f) x → extend f (μ⁺ F f) x → Set)
     F' (λ m x x' x0 → agree2 (μ F) f m (λ x1 m' z → F' x1 m' (≤′-trans (≤′-step z) x)) x' x0 (rs m x)))
  (extend' (λ x → (m : ℕ) (p : suc m ≤′ n) (t' u' v' : extend f (μ⁺ F f) x) →
        extend' (λ x' → (m' : ℕ) → suc m' ≤′ n → extend f (μ⁺ F f) x' → extend f (μ⁺ F f) x' → Set)
        F' (λ m' x' x0 x1 → agree2 (μ F) f m' (λ x2 m0 z → F' x2 m0 (≤′-trans (≤′-step z) x')) x0 x1 (rs m' x'))
        x m p t' u' →
        extend' (λ x' → (m' : ℕ) → suc m' ≤′ n → extend f (μ⁺ F f) x' → extend f (μ⁺ F f) x' → Set)
        F' (λ m' x' x0 x1 → agree2 (μ F) f m' (λ x2 m0 z → F' x2 m0 (≤′-trans (≤′-step z) x')) x0 x1 (rs m' x'))
        x m p u' v' →
        extend' (λ x' → (m' : ℕ) → suc m' ≤′ n → extend f (μ⁺ F f) x' → extend f (μ⁺ F f) x' → Set)
        F' (λ m' x' x0 x1 → agree2 (μ F) f m' (λ x2 m0 z → F' x2 m0 (≤′-trans (≤′-step z) x')) x0 x1 (rs m' x'))
        x m p t' v')
     Ft (λ m p t' u' v' x x' → {!agree2-trans!}))
  t u v (acc rs) r1 r2
agree2-trans (ν F) f n F' Ft ⟨ t ⟩ ⟨ u ⟩ ⟨ v ⟩ (acc rs) r1 r2 = {!!}
agree2-trans (T ⇒ S) f n F Ft t u v p r1 r2 = λ x → agree2-trans S f n F Ft (t x) (u x) (v x) p (r1 x) (r2 x)
agree2-trans (T ∧ S) f n F Ft (t₁ , t₂) (u₁ , u₂) (v₁ , v₂) p (r1₁ , r1₂) (r2₁ , r2₂) = (agree2-trans T f n F Ft t₁ u₁ v₁ p r1₁ r2₁) , (agree2-trans S f n F Ft t₂ u₂ v₂ p r1₂ r2₂)
agree2-trans (T ∨ S) f n F Ft (inj₁ x) (inj₁ x') (inj₁ x0) p r1 r2 = agree2-trans T f n F Ft x x' x0 p r1 r2
agree2-trans (T ∨ S) f n F Ft (inj₁ x) (inj₁ x') (inj₂ y) p r1 ()
agree2-trans (T ∨ S) f n F Ft (inj₁ x) (inj₂ y) v p () r2
agree2-trans (T ∨ S) f n F Ft (inj₂ y) (inj₁ x) v p () r2
agree2-trans (T ∨ S) f n F Ft (inj₂ y) (inj₂ y') (inj₁ x) p r1 ()
agree2-trans (T ∨ S) f n F Ft (inj₂ y) (inj₂ y') (inj₂ y0) p r1 r2 = agree2-trans S f n F Ft y y' y0 p r1 r2
agree2-trans ⊤ f n F Ft t u v p r1 r2 = unit
agree2-trans (○ T) f zero F Ft t u v p r1 r2 = unit
agree2-trans (○ T) f (suc n) F Ft t u v (acc rs) r1 r2 = agree2-trans T f n (λ x m x' x0 x1 → F x m (≤′-step x') x0 x1) (λ x m p t' u' v' x' x0 → Ft x m (≤′-step p) t' u' v' x' x0) t u v (rs n ≤′-refl) r1 r2
