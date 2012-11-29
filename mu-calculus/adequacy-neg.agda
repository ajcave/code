module adequacy-neg where
open import Relation.Binary.PropositionalEquality
open import stlc-products
open import Product
open import FinMap
open import Unit
open import Data.Bool


-- Step indexed logical relations style:
-- http://www.mpi-sws.org/~dreyer/papers/lslr/main.pdf
⟦_⟧t : tp -> Set
⟦ T ⇝ S ⟧t = ⟦ T ⟧t → ⟦ S ⟧t
⟦ T * S ⟧t = ⟦ T ⟧t × ⟦ S ⟧t
⟦ unit ⟧t = Unit
⟦ bool ⟧t = Bool


record E' (T : tp) (R : value T -> Set) (x : ⟦ T ⟧t) (t : tm ⊡ T)   : Set where
 constructor ev
 field
  val : value T
  t⟶v : t ⟶β* (inj val)
  vv : R val

mutual
 V : (T : tp) -> ⟦ T ⟧t -> value T -> Set
 V (T ⇝ S) f v = ∀ w y → V T y w → E S (f y) (inj v · inj w)
 V (T * S) (x₁ , x₂)  < M1 , M2 > = (V T x₁ M1) × (V S x₂ M2)
 V unit x v = Unit
 V bool x v = v ≡ bconst x

 E : ∀ (T : tp) (x : ⟦ T ⟧t) (t : tm ⊡ T) -> Set
 E T x t = E' T (V T x) x t

⟦_⟧m : ∀ {Γ T} (t : tm Γ T) -> (σ : gsubst Γ ⟦_⟧t) -> ⟦ T ⟧t
⟦_⟧m (▹ x) σ = lookup σ x
⟦_⟧m (M · N) σ = ⟦ M ⟧m σ (⟦ N ⟧m σ)
⟦_⟧m (ƛ M) σ = λ x → ⟦ M ⟧m (σ , x)
⟦_⟧m < M1 , M2 > σ = (⟦ M1 ⟧m σ) , (⟦ M2 ⟧m σ)
⟦_⟧m (fst M) σ = proj₁ (⟦ M ⟧m σ)
⟦_⟧m (snd M) σ = proj₂ (⟦ M ⟧m σ)
⟦_⟧m tt σ = tt
⟦_⟧m (bconst b) σ = b

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
lemma (M · N) σ ρ x | ev (ƛ v) v⟶m vv | ev v' t⟶v' vv' | ev v0 t⟶v vv0 = ev v0 (⟶β*-trans (v⟶m ·* t⟶v') t⟶v) vv0
lemma (ƛ {T} M) σ ρ x = ev (ƛ ([ tsub-ext (gmap inj σ) ]t M)) (refl _)
 (λ w y x' → let q = lemma M (σ , w) (ρ , y) (x , x')
             in ev (E'.val q) (step (β _ _) (⟶β*≡-trans (lem2 M) (E'.t⟶v q))) (E'.vv q))
lemma < M1 , M2 > σ ρ x with lemma M1 σ ρ x | lemma M2 σ ρ x
lemma < M1 , M2 > σ ρ x | ev v t⟶v vv | ev v' t⟶v' vv' = ev < v , v' > < t⟶v , t⟶v' >* (vv , vv')
lemma (fst M) σ ρ x with lemma M σ ρ x
lemma (fst M) σ ρ x | ev < M1 , M2 > t⟶v (proj₁ , proj₂) = ev M1 (⟶β*-trans (fst* t⟶v) (step1 (β*1 (inj M1) (inj M2)))) proj₁
lemma (snd M) σ ρ x with lemma M σ ρ x
lemma (snd M) σ ρ x | ev < M1 , M2 > t⟶v (proj₁ , proj₂) = ev M2 (⟶β*-trans (snd* t⟶v) (step1 (β*2 (inj M1) (inj M2)))) proj₂
lemma tt σ ρ x = ev tt (refl tt) tt
lemma (bconst y) σ ρ x = ev (bconst y) (refl (bconst y)) refl

adequacy : ∀ (t : tm ⊡ bool) b -> ⟦ t ⟧m tt ≡ b -> t ⟶β* (bconst b)
adequacy t b x with lemma t tt tt tt
adequacy t .(⟦ t ⟧m tt) refl | ev .(bconst (⟦ t ⟧m tt)) t⟶v refl = ⟶β*≡-trans (sym (lem1½ _)) t⟶v
-- TODO: Seems this entails normalization! Is strengthening it to full abstraction going to get us under binders?

