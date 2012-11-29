module stlc-products-sums where
open import Relation.Binary.PropositionalEquality
open import Product
open import FinMap
open import Unit
open import Data.Bool

data tp : Set where
 _⇝_ : (T S : tp) -> tp
 _*_ : (T S : tp) -> tp
 _+_ : (T S : tp) -> tp
 unit : tp
 empty : tp

-- TODO: Try adding empty type?
data tm (Γ : ctx tp) : (T : tp) -> Set where
 ▹ : ∀ {T} -> (x : var Γ T) -> tm Γ T
 _·_ : ∀ {T S} -> (M : tm Γ (T ⇝ S)) -> (N : tm Γ T) -> tm Γ S
 ƛ : ∀ {T S} -> (M : tm (Γ , T) S) -> tm Γ (T ⇝ S)
 <_,_> : ∀ {T S} (M1 : tm Γ T) (M2 : tm Γ S) -> tm Γ (T * S)
 fst : ∀ {T S} (M : tm Γ (T * S)) -> tm Γ T
 snd : ∀ {T S} (M : tm Γ (T * S)) -> tm Γ S
 tt : tm Γ unit
 inl : ∀ {S T} (M : tm Γ T) -> tm Γ (T + S)
 inr : ∀ {T S} (M : tm Γ S) -> tm Γ (T + S)
 case : ∀ {T S C} (M : tm Γ (T + S)) (N1 : tm (Γ , T) C) (N2 : tm (Γ , S) C) -> tm Γ C
 abort : ∀ {C} (M : tm Γ empty) -> tm Γ C

[_]r : ∀ {Γ Δ T} (σ : vsubst Γ Δ) -> (M : tm Γ T) -> tm Δ T
[_]r σ (▹ x) = ▹ (lookup σ x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (M · N) = ([ σ ]r M) · ([ σ ]r N)
[ σ ]r < M , N > = < ([ σ ]r M) , ([ σ ]r N) >
[ σ ]r (fst M) = fst ([ σ ]r M)
[ σ ]r (snd M) = snd ([ σ ]r M)
[ σ ]r tt = tt
[ σ ]r (inl M) = inl ([ σ ]r M)
[ σ ]r (inr M) = inr ([ σ ]r M)
[ σ ]r (case M N1 N2) = case ([ σ ]r M) ([ vsub-ext σ ]r N1) ([ vsub-ext σ ]r N2)
[ σ ]r (abort M) = abort ([ σ ]r M)


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
[ σ ]t (inl M) = inl ([ σ ]t M)
[ σ ]t (inr M) = inr ([ σ ]t M)
[ σ ]t (case M N1 N2) = case ([ σ ]t M) ([ tsub-ext σ ]t N1) ([ tsub-ext σ ]t N2)
[ σ ]t (abort M) = abort ([ σ ]t M)

id-tsubst : ∀ {Γ} -> tsubst Γ Γ
id-tsubst {⊡} = tt
id-tsubst {ψ , T} = tsub-ext id-tsubst

-- TODO
postulate
 lem1 : ∀ {Γ Γ' Γ'' T S} {σ : tsubst Γ Γ'} {σ' : tsubst Γ' Γ''} {M : tm Γ'' T} (N : tm (Γ , T) S)
        -> [ σ' , M ]t ([ tsub-ext σ ]t N) ≡ [ gmap [ σ' ]t σ , M ]t N
 lem1½ : ∀ {Γ T} (M : tm Γ T) -> [ id-tsubst ]t M ≡ M

lem2 : ∀ {Γ Γ' T S} {σ : tsubst Γ Γ'} {M : tm Γ' T} (N : tm (Γ , T) S) -> [ id-tsubst , M ]t ([ tsub-ext σ ]t N) ≡ [ σ , M ]t N
lem2 {σ = σ} N = trans (lem1 N) (cong (λ α → [ α , _ ]t N) (trans (gmap-cong lem1½) (gmap-id σ)))

data value : tp -> Set where
 ƛ : ∀ {T S} -> (M : tm (⊡ , T) S) -> value (T ⇝ S)
 <_,_> : ∀ {T S} (M1 : value T) (M2 : value S) -> value (T * S)
 tt : value unit
 inl : ∀ {S T} -> (M : value T) -> value (T + S)
 inr : ∀ {T S} -> (M : value S) -> value (T + S)

inj : ∀ {T} -> value T -> tm ⊡ T
inj (ƛ M) = ƛ M
inj < M1 , M2 > = < (inj M1) , (inj M2) >
inj tt = tt
inj (inl M) = inl (inj M)
inj (inr M) = inr (inj M)

data _⟶β*_ : ∀ {T} -> tm ⊡ T -> tm ⊡ T -> Set where
 β : ∀ {T S} (M : tm (⊡ , T) S) (N : tm ⊡ T) -> ((ƛ M) · N) ⟶β* [ tt , N ]t M
 β*1 : ∀ {T S} (M : tm ⊡ T) (N : tm ⊡ S) -> (fst < M , N >) ⟶β* M
 β*2 : ∀ {T S} (M : tm ⊡ T) (N : tm ⊡ S) -> (snd < M , N >) ⟶β* N
 _·_ : ∀ {T S} {M M' : tm ⊡ (T ⇝ S)} (sm : M ⟶β* M') {N N' : tm ⊡ T} (sn : N ⟶β* N')  -> (M · N) ⟶β* (M' · N')
 <_,_> : ∀ {T S} {M M' : tm ⊡ T} (sm : M ⟶β* M') {N N' : tm ⊡ S} (sn : N ⟶β* N')  -> < M , N > ⟶β* < M' , N' >
 fst : ∀ {T S} {M M' : tm ⊡ (T * S)} (s : M ⟶β* M')   -> (fst M) ⟶β* (fst M')
 snd : ∀ {T S} {M M' : tm ⊡ (T * S)} (s : M ⟶β* M')   -> (snd M) ⟶β* (snd M')
 inl : ∀ {S T} {M M' : tm ⊡ T} (s : M ⟶β* M')         -> (inl {⊡} {S} M) ⟶β* (inl M')
 inr : ∀ {T S} {M M' : tm ⊡ S} (s : M ⟶β* M')         -> (inr {⊡} {T} M) ⟶β* (inr M')
 case : ∀ {T S C} {M M' : tm ⊡ (T + S)} (S : M ⟶β* M') (N1 : tm (⊡ , T) C) N2 -> (case M N1 N2) ⟶β* (case M' N1 N2)
 β+₁ : ∀ {T S C} (M : tm ⊡ T) (N1 : tm (⊡ , T) C) (N2 : tm (⊡ , S) C) -> (case (inl M) N1 N2) ⟶β* [ tt , M ]t N1
 β+₂ : ∀ {T S C} (M : tm ⊡ S) (N1 : tm (⊡ , T) C) (N2 : tm (⊡ , S) C) -> (case (inr M) N1 N2) ⟶β* [ tt , M ]t N2
 refl : ∀ {T} (M : tm ⊡ T) -> M ⟶β* M
 ⟶β*-trans : ∀ {T} {M1 M2 M3 : tm ⊡ T} -> M1 ⟶β* M2 -> M2 ⟶β* M3 -> M1 ⟶β* M3

⟶β*≡-trans : ∀ {T} {M1 M2 M3 : tm ⊡ T} -> M1 ≡ M2 -> M2 ⟶β* M3 -> M1 ⟶β* M3 
⟶β*≡-trans refl s2 = s2





 

