module stlc-products where
open import Product
open import FinMap
open import Unit
open import Data.Bool

data tp : Set where
 _⇝_ : (T S : tp) -> tp
 _*_ : (T S : tp) -> tp
 unit : tp
 bool : tp

data tm (Γ : ctx tp) : (T : tp) -> Set where
 ▹ : ∀ {T} -> (x : var Γ T) -> tm Γ T
 _·_ : ∀ {T S} -> (M : tm Γ (T ⇝ S)) -> (N : tm Γ T) -> tm Γ S
 ƛ : ∀ {T S} -> (M : tm (Γ , T) S) -> tm Γ (T ⇝ S)
 <_,_> : ∀ {T S} (M1 : tm Γ T) (M2 : tm Γ S) -> tm Γ (T * S)
 fst : ∀ {T S} (M : tm Γ (T * S)) -> tm Γ T
 snd : ∀ {T S} (M : tm Γ (T * S)) -> tm Γ S
 tt : tm Γ unit
 bconst : Bool -> tm Γ bool

[_]r : ∀ {Γ Δ T} (σ : vsubst Γ Δ) -> (M : tm Γ T) -> tm Δ T
[_]r σ (▹ x) = ▹ (lookup σ x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (M · N) = ([ σ ]r M) · ([ σ ]r N)
[ σ ]r < M , N > = < ([ σ ]r M) , ([ σ ]r N) >
[ σ ]r (fst M) = fst ([ σ ]r M)
[ σ ]r (snd M) = snd ([ σ ]r M)
[ σ ]r tt = tt
[ σ ]r (bconst b) = bconst b


tsubst : ctx tp -> ctx tp -> Set
tsubst Γ Δ = gsubst Γ (tm Δ)

tsub-ext : ∀ {Γ Δ T} -> tsubst Γ Δ -> tsubst (Γ , T) (Δ , T)
tsub-ext σ = (gmap [ wkn-vsub ]r σ) , (▹ top)

[_]t : ∀ {Γ Δ T} (σ : tsubst Γ Δ) -> (M : tm Γ T) -> tm Δ T
[_]t σ (▹ x) = lookup σ x
[_]t σ (M · N) = [ σ ]t M · [ σ ]t N
[_]t σ (ƛ M) = ƛ ([ tsub-ext σ ]t M)
[ σ ]t < M , N > = < ([ σ ]t M) , ([ σ ]t N) >
[ σ ]t (fst M) = fst ([ σ ]t M)
[ σ ]t (snd M) = snd ([ σ ]t M)
[ σ ]t tt = tt
[ σ ]t (bconst b) = bconst b

id-tsubst : ∀ {Γ} -> tsubst Γ Γ
id-tsubst = interp ▹

data value : tp -> Set where
 ƛ : ∀ {T S} -> (M : tm (⊡ , T) S) -> value (T ⇝ S)
 <_,_> : ∀ {T S} (M1 : value T) (M2 : value S) -> value (T * S)
 tt : value unit
 bconst : Bool -> value bool

inj : ∀ {T} -> value T -> tm ⊡ T
inj (ƛ M) = ƛ M
inj < M1 , M2 > = < (inj M1) , (inj M2) >
inj tt = tt
inj (bconst b) = bconst b

data _⟶β_ : ∀ {T} -> tm ⊡ T -> tm ⊡ T -> Set where
 β : ∀ {T S} (M : tm (⊡ , T) S) (N : tm ⊡ T) -> ((ƛ M) · N) ⟶β [ tt , N ]t M
 β*1 : ∀ {T S} (M : tm ⊡ T) (N : tm ⊡ S) -> (fst < M , N >) ⟶β M
 β*2 : ∀ {T S} (M : tm ⊡ T) (N : tm ⊡ S) -> (snd < M , N >) ⟶β N
 _·₁_ : ∀ {T S} {M M' : tm ⊡ (T ⇝ S)} (s : M ⟶β M') (N : tm ⊡ T)  -> (M · N) ⟶β (M' · N)
 _·₂_ : ∀ {T S} (M : tm ⊡ (T ⇝ S)) {N N' : tm ⊡ T} (s : N ⟶β N') -> (M · N) ⟶β (M · N')
 <_,_>₁ : ∀ {T S} {M M' : tm ⊡ T} (s : M ⟶β M') (N : tm ⊡ S)  -> < M , N > ⟶β < M' , N >
 <_,_>₂ : ∀ {T S} (M : tm ⊡ T) {N N' : tm ⊡ S} (s : N ⟶β N') -> < M , N > ⟶β < M , N' >
 fst : ∀ {T S} {M M' : tm ⊡ (T * S)} (s : M ⟶β M')   -> (fst M) ⟶β (fst M')
 snd : ∀ {T S} {M M' : tm ⊡ (T * S)} (s : M ⟶β M')   -> (snd M) ⟶β (snd M')

data _⟶β*_ : ∀ {T} -> tm ⊡ T -> tm ⊡ T -> Set where
 refl : ∀ {T} (M : tm ⊡ T) -> M ⟶β* M
 step : ∀ {T} {M1 M2 M3 : tm ⊡ T} -> M1 ⟶β M2 -> M2 ⟶β* M3 -> M1 ⟶β* M3

step1 : ∀ {T} {M1 M2 : tm ⊡ T} -> M1 ⟶β M2 -> M1 ⟶β* M2
step1 s = step s (refl _)

⟶β*-trans : ∀ {T} {M1 M2 M3 : tm ⊡ T} -> M1 ⟶β* M2 -> M2 ⟶β* M3 -> M1 ⟶β* M3 
⟶β*-trans (refl M2) s2 = s2
⟶β*-trans (step y y') s2 = step y (⟶β*-trans y' s2)

_·₁*_ : ∀ {T S} {M M' : tm ⊡ (T ⇝ S)} (s : M ⟶β* M') (N : tm ⊡ T)  -> (M · N) ⟶β* (M' · N)
_·₁*_ (refl M') N = refl (M' · N)
step y y' ·₁* N = step (y ·₁ N) (y' ·₁* N)

_·₂*_ : ∀ {T S} (M : tm ⊡ (T ⇝ S)) {N N' : tm ⊡ T} (s : N ⟶β* N') -> (M · N) ⟶β* (M · N')
_·₂*_ M (refl N') = refl (M · N')
M ·₂* step y y' = step (M ·₂ y) (M ·₂* y')

_·*_ : ∀ {T S} {M M' : tm ⊡ (T ⇝ S)} (sm : M ⟶β* M') {N N' : tm ⊡ T} (sn : N ⟶β* N') -> (M · N) ⟶β* (M' · N')
sm ·* sn = ⟶β*-trans (sm ·₁* _) (_ ·₂* sn)

fst* : ∀ {T S} {M M' : tm ⊡ (T * S)} (s : M ⟶β* M')   -> (fst M) ⟶β* (fst M')
fst* (refl M') = refl (fst M')
fst* (step y y') = step (fst y) (fst* y')

snd* : ∀ {T S} {M M' : tm ⊡ (T * S)} (s : M ⟶β* M')   -> (snd M) ⟶β* (snd M')
snd* (refl M') = refl (snd M')
snd* (step y y') = step (snd y) (snd* y')





 

