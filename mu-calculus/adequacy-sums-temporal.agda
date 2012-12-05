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

{-
⟦_⟧m : ∀ {θ Γ T} (t : tm Γ T) -> (σ : gsubst Γ ⟦_⟧t) -> ⟦ T ⟧t
⟦_⟧m (▹ x) σ = lookup σ x
⟦_⟧m (M · N) σ = ⟦ M ⟧m σ (⟦ N ⟧m σ)
⟦_⟧m (ƛ M) σ = λ x → ⟦ M ⟧m (σ , x)
⟦_⟧m < M1 , M2 > σ = (⟦ M1 ⟧m σ) , (⟦ M2 ⟧m σ)
⟦_⟧m (fst M) σ = proj₁ (⟦ M ⟧m σ)
⟦_⟧m (snd M) σ = proj₂ (⟦ M ⟧m σ)
⟦_⟧m tt σ = tt
⟦_⟧m (inl M) σ = inj₁ (⟦ M ⟧m σ)
⟦ inr M ⟧m σ = inj₂ (⟦ M ⟧m σ)
⟦ case M N1 N2 ⟧m σ with ⟦ M ⟧m σ
⟦_⟧m (case M N1 N2) σ | inj₁ x = ⟦ N1 ⟧m (σ , x)
⟦_⟧m (case M N1 N2) σ | inj₂ y = ⟦ N2 ⟧m (σ , y)
⟦ abort M ⟧m σ = ⊥-elim (⟦ M ⟧m σ)


--⟦_⟧c : ∀ {Γ} (σ : gsubst Γ value) -> gsubst Γ ⟦_⟧t
--⟦ σ ⟧c = gmap (λ v → ⟦ inj v ⟧m tt) σ

Vc : ∀ {Γ} (ρ : gsubst Γ ⟦_⟧t) (σ : gsubst Γ value)  -> Set
Vc {⊡} tt tt = Unit
Vc {Γ , T} (ρ₁ , x) (σ₁ , t) = Vc ρ₁ σ₁ × (V T x t)

Vc-lookup : ∀ {Γ T} {ρ : gsubst Γ ⟦_⟧t} {σ : gsubst Γ value} -> Vc ρ σ -> (x : var Γ T) -> V T (lookup ρ x) (lookup σ x)
Vc-lookup {⊡} p ()
Vc-lookup {ψ , T} (proj₁ , proj₂) top = proj₂
Vc-lookup {ψ , T} (proj₁ , proj₂) (pop y) = Vc-lookup proj₁ y

-- TODO: What happens in a deterministic call-by-value setting?
-- TODO: Can we use this technique to do weak normalization with sums (where we don't care about unique normal forms)?
-- TODO: Try disjunction
lemma : ∀ {Γ T} (t : tm Γ T) (σ : gsubst Γ value) (ρ : gsubst Γ ⟦_⟧t) -> Vc ρ σ -> E T (⟦ t ⟧m ρ) ([ gmap inj σ ]t t)
lemma (▹ x) σ ρ x' = ev (lookup σ x) (⟶β*≡-trans (lookup-gmap inj σ x) (refl _)) (Vc-lookup x' x)
lemma (M · N) σ ρ x with lemma M σ ρ x | lemma N σ ρ x
lemma (M · N) σ ρ x | ev (ƛ v) v⟶m vv | ev v' t⟶v vv' with vv v' (⟦ N ⟧m ρ) vv'
lemma (M · N) σ ρ x | ev (ƛ v) v⟶m vv | ev v' t⟶v' vv' | ev v0 t⟶v vv0 = ev v0 (⟶β*-trans (v⟶m · t⟶v') t⟶v) vv0
lemma (ƛ {T} M) σ ρ x = ev (ƛ ([ tsub-ext (gmap inj σ) ]t M)) (refl _)
 (λ w y x' → let q = lemma M (σ , w) (ρ , y) (x , x')
             in ev (E'.val q) (⟶β*-trans (β _ _) (⟶β*≡-trans (lem2 M) (E'.t⟶v q))) (E'.vv q))
lemma < M1 , M2 > σ ρ x with lemma M1 σ ρ x | lemma M2 σ ρ x
lemma < M1 , M2 > σ ρ x | ev v t⟶v vv | ev v' t⟶v' vv' = ev < v , v' > < t⟶v , t⟶v' > (vv , vv')
lemma (fst M) σ ρ x with lemma M σ ρ x
lemma (fst M) σ ρ x | ev < M1 , M2 > t⟶v (proj₁ , proj₂) = ev M1 (⟶β*-trans (fst t⟶v) (β*1 (inj M1) (inj M2))) proj₁
lemma (snd M) σ ρ x with lemma M σ ρ x
lemma (snd M) σ ρ x | ev < M1 , M2 > t⟶v (proj₁ , proj₂) = ev M2 (⟶β*-trans (snd t⟶v) (β*2 (inj M1) (inj M2))) proj₂
lemma tt σ ρ x = ev tt (refl tt) tt
lemma (inl M) σ ρ x with lemma M σ ρ x
lemma (inl M) σ ρ x | ev val t⟶v vv = ev (inl val) (inl t⟶v) vv
lemma (inr M) σ ρ x with lemma M σ ρ x
lemma (inr M) σ ρ x | ev val t⟶v vv = ev (inr val) (inr t⟶v) vv
lemma (case M N1 N2) σ ρ x with lemma M σ ρ x 
lemma (case M N1 N2) σ ρ x | ev val t⟶v vv with ⟦ M ⟧m ρ
lemma (case M N1 N2) σ ρ x' | ev (inl M') t⟶v vv | inj₁ x with lemma N1 (σ , M') (ρ , x) (x' , vv)
lemma (case M N1 N2) σ ρ x' | ev (inl M') t⟶v vv | inj₁ x | ev val t⟶v' vv' =
   ev val (⟶β*-trans (case t⟶v _ _) (⟶β*-trans (β+₁ _ _ _) (⟶β*≡-trans (lem2 N1) t⟶v'))) vv'
lemma (case M N1 N2) σ ρ x' | ev (inr M') t⟶v () | inj₁ x
lemma (case M N1 N2) σ ρ x | ev (inl M') t⟶v () | inj₂ y
lemma (case M N1 N2) σ ρ x | ev (inr M') t⟶v vv | inj₂ y with lemma N2 (σ , M') (ρ , y) (x , vv)
lemma (case M N1 N2) σ ρ x | ev (inr M') t⟶v' vv | inj₂ y | ev val t⟶v vv' =
   ev val (⟶β*-trans (case t⟶v' _ _) (⟶β*-trans (β+₂ _ _ _) (⟶β*≡-trans (lem2 N2) t⟶v))) vv'
lemma (abort M) σ ρ x = ⊥-elim (⟦ M ⟧m ρ)

adequacy : ∀ (t : tm ⊡ (unit + unit)) b -> ⟦ t ⟧m tt ≡ (⟦ inj b ⟧m tt) -> t ⟶β* (inj b)
adequacy t b x with subst (λ α -> E _ α ([ tt ]t t)) x (lemma t tt tt tt)
adequacy t (inl tt) x | ev (inl tt) t⟶v vv = ⟶β*≡-trans (sym (lem1½ _)) t⟶v
adequacy t (inl tt) x | ev (inr M) t⟶v ()
adequacy t (inr tt) x | ev (inl M) t⟶v ()
adequacy t (inr tt) x | ev (inr tt) t⟶v vv = ⟶β*≡-trans (sym (lem1½ _)) t⟶v
-- TODO: Seems this entails normalization! Is strengthening it to full abstraction going to get us under binders?

-}