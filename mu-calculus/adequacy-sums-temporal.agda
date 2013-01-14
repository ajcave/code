module adequacy-sums-temporal where
open import Relation.Binary.PropositionalEquality
open import stlc-products-sums-circ
open import Product
open import FinMap
open import Unit
open import Data.Bool
open import Data.Sum
open import Data.Empty
open import Data.Nat hiding (_*_; _+_)

≤-refl : ∀ {n} -> n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {n m q} -> m ≤ q -> n ≤ m -> n ≤ q
≤-trans z≤n z≤n = z≤n
≤-trans (s≤s m≤n) z≤n = z≤n
≤-trans (s≤s m≤n) (s≤s m≤n') = s≤s (≤-trans m≤n m≤n')

obj : Set₁
obj = ℕ -> Set

-- Step indexed logical relations style:
-- http://www.mpi-sws.org/~dreyer/papers/lslr/main.pdf
⟦_⟧t : tp -> obj
⟦ T ⇝ S ⟧t n = ∀ m -> m ≤ n -> ⟦ T ⟧t m  → ⟦ S ⟧t m
⟦ T * S ⟧t n = ⟦ T ⟧t n × ⟦ S ⟧t n
⟦ unit ⟧t n = Unit
⟦ T + S ⟧t n = ⟦ T ⟧t n ⊎ ⟦ S ⟧t n
⟦ empty ⟧t n = ⊥
⟦_⟧t (○ T) zero = Unit
⟦_⟧t (○ T) (suc n) = ⟦ T ⟧t n


record E' (T : tp) (R : value T -> Set) n (x : ⟦ T ⟧t n) (t : tm ⊡ ⊡ T)   : Set where
 constructor ev
 field
  val : value T
  t⟶v : t ⟶β* (inj val)
  vv : R val

mutual
 V : (T : tp) (n : ℕ) -> ⟦ T ⟧t n -> value T -> Set
 V (T ⇝ S) n f v = ∀ m (p : m ≤ n) w y → V T m y w → E S m (f m p y) (inj v · inj w)
 V (T * S) n (x₁ , x₂)  < M1 , M2 > = (V T n x₁ M1) × (V S n x₂ M2)
 V unit n x v = Unit
 V (T + S) n (inj₁ x) (inl M) = V T n x M
 V (T + S) n (inj₁ x) (inr M) = ⊥
 V (T + S) n (inj₂ y) (inl M) = ⊥
 V (T + S) n (inj₂ y) (inr M) = V S n y M
 V empty n () v
 V (○ T) zero v (• M) = Unit
 V (○ T) (suc n) v (• M) = V T n v M

 E : ∀ (T : tp) (n : ℕ) (x : ⟦ T ⟧t n) (t : tm ⊡ ⊡ T) -> Set
 E T n x t = E' T (V T n x) n x t

forg : ∀ T {n m} (p : m ≤ n) -> ⟦ T ⟧t n -> ⟦ T ⟧t m
forg (T ⇝ S) p t = {!!}
forg (T * S) p (proj₁ , proj₂) = (forg T p proj₁) , forg S p proj₂
forg (T + S) p (inj₁ x) = inj₁ (forg T p x)
forg (T + S) p (inj₂ y) = inj₂ (forg S p y)
forg unit p t = tt
forg empty p ()
forg (○ T) z≤n t = tt
forg (○ T) (s≤s m≤n) t = forg T m≤n t

⟦_⟧m : ∀ {θ Γ T} (t : tm θ Γ T) -> ∀ n -> (σn : gsubst θ (λ T -> ⟦ ○ T ⟧t n)) (σ : gsubst Γ (λ T -> ⟦ T ⟧t n)) -> ⟦ T ⟧t n
⟦_⟧m (▹ x) n σn σ = lookup σ x
⟦_⟧m (M · N) n σn σ = ⟦ M ⟧m n σn σ n ≤-refl (⟦ N ⟧m n σn σ)
⟦_⟧m (ƛ M) n σn σ = λ m m≤n x → ⟦ M ⟧m m (gmap (λ {T'} → forg (○ T') m≤n) σn) ((gmap (λ {T'} → forg T' m≤n) σ) , x)
⟦_⟧m < M1 , M2 > n σn σ = (⟦ M1 ⟧m n σn σ) , (⟦ M2 ⟧m n σn σ)
⟦_⟧m (fst M) n σn σ = proj₁ (⟦ M ⟧m n σn σ)
⟦_⟧m (snd M) n σn σ = proj₂ (⟦ M ⟧m n σn σ)
⟦_⟧m tt n σn σ = tt
⟦_⟧m (inl M) n σn σ = inj₁ (⟦ M ⟧m n σn σ)
⟦_⟧m (inr M) n σn σ = inj₂ (⟦ M ⟧m n σn σ)
⟦_⟧m (case M N1 N2) n σn σ with ⟦ M ⟧m n σn σ
⟦_⟧m (case M N1 N2) n σn σ | inj₁ x = ⟦ N1 ⟧m n σn (σ , x)
⟦_⟧m (case M N1 N2) n σn σ | inj₂ y = ⟦ N2 ⟧m n σn (σ , y)
⟦_⟧m (abort M) n σn σ = ⊥-elim (⟦ M ⟧m n σn σ)
⟦_⟧m (let-• M N) n σn σ = ⟦ N ⟧m n (σn , ⟦ M ⟧m n σn σ) σ
⟦_⟧m (• M) zero σn σ = tt
⟦_⟧m (• M) (suc n) σn σ = ⟦ M ⟧m n tt σn


--⟦_⟧c : ∀ {Γ} (σ : gsubst Γ value) -> gsubst Γ ⟦_⟧t
--⟦ σ ⟧c = gmap (λ v → ⟦ inj v ⟧m tt) σ

Vc : ∀ {Γ} n (ρ : gsubst Γ (λ T -> ⟦ T ⟧t n)) (σ : gsubst Γ value)  -> Set
Vc {⊡} n tt tt = Unit
Vc {Γ , T} n (ρ₁ , x) (σ₁ , t) = Vc n ρ₁ σ₁ × (V T n x t)

Vcn : ∀ {Γ} n (ρ : gsubst Γ (λ T -> ⟦ ○ T ⟧t n)) (σ : gsubst Γ value)  -> Set
Vcn {⊡} n tt tt = Unit
Vcn {Γ , T} n (ρ₁ , x) (σ₁ , t) = Vcn n ρ₁ σ₁ × (V (○ T) n x (• t))

lemma : ∀ {θ Γ T} (t : tm θ Γ T) (σn : gsubst θ value) (σ : gsubst Γ value) n (ρn : gsubst θ (λ T -> ⟦ ○ T ⟧t n)) (ρ : gsubst Γ (λ T -> ⟦ T ⟧t n))
 -> Vcn n ρn σn -> Vc n ρ σ -> E T n (⟦ t ⟧m n ρn ρ) ([ gmap inj σ ]t ([ gmap inj σn ]va t))
lemma (▹ x) σn σ n ρn ρ r1 r2 = {!!}
lemma (M · N) σn σ n ρn ρ r1 r2 with lemma M σn σ n ρn ρ r1 r2 | lemma N σn σ n ρn ρ r1 r2
lemma (M · N) σn σ n ρn ρ r1 r2 | ev (ƛ M') t⟶v vv | ev val' t⟶v' vv' with vv n ≤-refl val' (⟦ N ⟧m n ρn ρ) vv'
lemma (M · N) σn σ n ρn ρ r1 r2 | ev (ƛ M') t⟶v' vv | ev val' t⟶v0 vv' | ev val t⟶v vv0 = ev val (⟶β*-trans (t⟶v' · t⟶v0) t⟶v) vv0
lemma {T = T ⇝ S} (ƛ M) σn σ n ρn ρ r1 r2 = ev _ (refl _) f
 where f : (m : ℕ) (p : m ≤ n) (w : value T) (y : ⟦ T ⟧t m) → V T m y w → E S m (⟦ ƛ M ⟧m n ρn ρ m p y) (inj (ƛ ([ tsub-ext (gmap inj σ) ]t ([ gmap inj σn ]va M))) · inj w)
       f m p w y r with lemma M σn (σ , w) m (gmap (λ {T'} -> forg (○ T') p) ρn) (gmap (λ {T'} -> forg T' p) ρ , y) {!!} ({!!} , r)
       ... | ev v' s vv = ev v' (⟶β*-trans (β _ _) (⟶β*≡-trans {!!} s)) vv
lemma < M1 , M2 > σn σ n ρn ρ r1 r2 = {!!}
lemma (fst M) σn σ n ρn ρ r1 r2 = {!!}
lemma (snd M) σn σ n ρn ρ r1 r2 = {!!}
lemma tt σn σ n ρn ρ r1 r2 = {!!}
lemma (inl M) σn σ n ρn ρ r1 r2 = {!!}
lemma (inr M) σn σ n ρn ρ r1 r2 = {!!}
lemma (case M N1 N2) σn σ n ρn ρ r1 r2 = {!!}
lemma (abort M) σn σ n ρn ρ r1 r2 with lemma M σn σ n ρn ρ r1 r2
lemma (abort M) σn σ n ρn ρ r1 r2 | ev () t⟶v vv
lemma (let-• M N) σn σ n ρn ρ r1 r2 with lemma M σn σ n ρn ρ r1 r2
lemma (let-• M N) σn σ n ρn ρ r1 r2 | ev (• val) t⟶v vv with lemma N (σn , val) σ n (ρn , (⟦ M ⟧m n ρn ρ)) ρ (r1 , vv) r2
lemma (let-• M N) σn σ n ρn ρ r1 r2 | ev (• val) t⟶v vv | ev val' t⟶v' vv' = ev val' (⟶β*-trans (⟶β*-trans (let-• t⟶v _) (⟶β*≡-trans₂ (let-•β _ _) {!!})) t⟶v') vv'
lemma (• M) σn σ zero ρn ρ r1 r2 = ev (• {!!}) (• {!!}) tt -- Crap! Do I want to quantify over all n in the semantics? Is this an indication that we want a "tick semantics"?
lemma (• M) σn σ (suc n) ρn ρ r1 r2 with lemma M tt σn n tt ρn tt {!!}
lemma (• M) σn σ (suc n) ρn ρ r1 r2 | ev val t⟶v vv = ev (• val) (• (⟶β*≡-trans (cong [ gmap inj σ ]t {!!}) t⟶v)) vv
