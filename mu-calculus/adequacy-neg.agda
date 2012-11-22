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


data E' (T : tp) (R : value T -> Set) (x : ⟦ T ⟧t) (t : tm ⊡ T)   : Set where
 ev : ∀ v -> (t⟶v : t ⟶β* (inj v)) -> (vv : R v) -> E' T R x t

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

lemma : ∀ {Γ T} (t : tm Γ T) (σ : gsubst Γ value) (ρ : gsubst Γ ⟦_⟧t) -> Vc ρ σ -> E T (⟦ t ⟧m ρ) ([ gmap inj σ ]t t)
lemma (▹ x) σ ρ x' = {!!}
lemma (M · N) σ ρ x with lemma M σ ρ x | lemma N σ ρ x
lemma (M · N) σ ρ x | ev (ƛ v) v⟶m vv | ev v' t⟶v vv' with vv v' (⟦ N ⟧m ρ) vv'
lemma (M · N) σ ρ x | ev (ƛ v) v⟶m vv | ev v' t⟶v' vv' | ev v0 t⟶v vv0 = ev {!!} {!!} {!!}
lemma (ƛ M) σ ρ x = {!!}
lemma < M1 , M2 > σ ρ x = {!!}
lemma (fst M) σ ρ x = {!!}
lemma (snd M) σ ρ x = {!!}
lemma tt σ ρ x = {!!}
lemma (bconst y) σ ρ x = {!!}


