module stlc-products-sums-circ where
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
 ○ : (T : tp) -> tp

-- TODO: Try adding empty type?
data tm (θ : ctx tp) (Γ : ctx tp) : (T : tp) -> Set where
 ▹ : ∀ {T} -> (x : var Γ T) -> tm θ Γ T
 _·_ : ∀ {T S} -> (M : tm θ Γ (T ⇝ S)) -> (N : tm θ Γ T) -> tm θ Γ S
 ƛ : ∀ {T S} -> (M : tm θ (Γ , T) S) -> tm θ Γ (T ⇝ S)
 <_,_> : ∀ {T S} (M1 : tm θ Γ T) (M2 : tm θ Γ S) -> tm θ Γ (T * S)
 fst : ∀ {T S} (M : tm θ Γ (T * S)) -> tm θ Γ T
 snd : ∀ {T S} (M : tm θ Γ (T * S)) -> tm θ Γ S
 tt : tm θ Γ unit
 inl : ∀ {S T} (M : tm θ Γ T) -> tm θ Γ (T + S)
 inr : ∀ {T S} (M : tm θ Γ S) -> tm θ Γ (T + S)
 case : ∀ {T S C} (M : tm θ Γ (T + S)) (N1 : tm θ (Γ , T) C) (N2 : tm θ (Γ , S) C) -> tm θ Γ C
 abort : ∀ {C} (M : tm θ Γ empty) -> tm θ Γ C
 let-• : ∀ {T C} (M : tm θ Γ T) (N : tm (θ , T) Γ C) -> tm θ Γ C
 • : ∀ {T} (M : tm ⊡ θ T) -> tm θ Γ T

[_]r : ∀ {θ Γ Δ T} (σ : vsubst Γ Δ) -> (M : tm θ Γ T) -> tm θ Δ T
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
[ σ ]r (let-• M N) = let-• ([ σ ]r M) ([ σ ]r N)
[ σ ]r (• M) = • M

[_]nv : ∀ {θ θ' Γ T} (σ : vsubst θ θ') -> (M : tm θ Γ T) -> tm θ' Γ T
[_]nv σ (▹ x) = ▹ x
[_]nv σ (ƛ M) = ƛ ([ σ ]nv M)
[_]nv σ (M · N) = ([ σ ]nv M) · ([ σ ]nv N)
[ σ ]nv < M , N > = < ([ σ ]nv M) , ([ σ ]nv N) >
[ σ ]nv (fst M) = fst ([ σ ]nv M)
[ σ ]nv (snd M) = snd ([ σ ]nv M)
[ σ ]nv tt = tt
[ σ ]nv (inl M) = inl ([ σ ]nv M)
[ σ ]nv (inr M) = inr ([ σ ]nv M)
[ σ ]nv (case M N1 N2) = case ([ σ ]nv M) ([ σ ]nv N1) ([ σ ]nv N2)
[ σ ]nv (abort M) = abort ([ σ ]nv M)
[ σ ]nv (let-• M N) = let-• ([ σ ]nv M) ([ vsub-ext σ ]nv N)
[ σ ]nv (• M) = • ([ σ ]r M)

tsubst : ctx tp -> ctx tp -> ctx tp -> Set
tsubst θ Γ Δ = gsubst Γ (tm θ Δ)

tsub-ext : ∀ {θ Γ Δ T} -> tsubst θ Γ Δ -> tsubst θ (Γ , T) (Δ , T)
tsub-ext σ = (gmap [ wkn-vsub ]r σ) , (▹ top)

[_]t : ∀ {θ Γ Δ T} (σ : tsubst θ Γ Δ) -> (M : tm θ Γ T) -> tm θ Δ T
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
[ σ ]t (let-• M N) = let-• ([ σ ]t M) ([ gmap [ wkn-vsub ]nv σ ]t N)
[ σ ]t (• M) = • M

id-tsubst : ∀ {Γ θ} -> tsubst θ Γ Γ
id-tsubst {⊡} = tt
id-tsubst {ψ , T} = tsub-ext id-tsubst

validsub : ∀ (θ1 θ2 : ctx tp) -> Set
validsub θ1 θ2 = tsubst ⊡ θ1 θ2

validsub-ext : ∀ {θ1 θ2 T} -> validsub θ1 θ2 -> validsub (θ1 , T) (θ2 , T)
validsub-ext σ = tsub-ext σ

validsub-id : ∀ {θ} -> validsub θ θ
validsub-id = id-tsubst

[_]va_ : ∀ {θ1 θ2 Γ C} (θ : validsub θ1 θ2) (M : tm θ1 Γ C) ->  tm θ2 Γ C
[ θ ]va ▹ x = ▹ x
[ θ ]va ƛ M = ƛ ([ θ ]va M)
[ θ ]va (M · N) = ([ θ ]va M) · ([ θ ]va N)
[ θ ]va let-• M N = let-• ([ θ ]va M) ([ validsub-ext θ ]va N)
[ θ ]va • M = • ([ θ ]t M)
[ σ ]va < M , N > = < [ σ ]va M , [ σ ]va N >
[ σ ]va (fst M) = fst ([ σ ]va M)
[ σ ]va (snd M) = snd ([ σ ]va M)
[ σ ]va (inl M) = inl ([ σ ]va M)
[ σ ]va (inr M) = inr ([ σ ]va M)
[ σ ]va (case M N1 N2) = case ([ σ ]va M) ([ σ ]va N1) ([ σ ]va N2)
[ σ ]va tt = tt
[ σ ]va (abort M) = abort ([ σ ]va M)

-- TODO
postulate
 lem1 : ∀ {θ Γ Γ' Γ'' T S} {σ : tsubst θ Γ Γ'} {σ' : tsubst θ Γ' Γ''} {M : tm θ Γ'' T} (N : tm θ (Γ , T) S)
        -> [ σ' , M ]t ([ tsub-ext σ ]t N) ≡ [ gmap [ σ' ]t σ , M ]t N
 lem1½ : ∀ {θ Γ T} (M : tm θ Γ T) -> [ id-tsubst ]t M ≡ M

lem2 : ∀ {θ Γ Γ' T S} {σ : tsubst θ Γ Γ'} {M : tm θ Γ' T} (N : tm θ (Γ , T) S) -> [ id-tsubst , M ]t ([ tsub-ext σ ]t N) ≡ [ σ , M ]t N
lem2 {σ = σ} N = trans (lem1 N) (cong (λ α → [ α , _ ]t N) (trans (gmap-cong lem1½) (gmap-id σ)))

data value : tp -> Set where
 ƛ : ∀ {T S} -> (M : tm ⊡ (⊡ , T) S) -> value (T ⇝ S)
 <_,_> : ∀ {T S} (M1 : value T) (M2 : value S) -> value (T * S)
 tt : value unit
 inl : ∀ {S T} -> (M : value T) -> value (T + S)
 inr : ∀ {T S} -> (M : value S) -> value (T + S)

inj : ∀ {T} -> value T -> tm ⊡ ⊡ T
inj (ƛ M) = ƛ M
inj < M1 , M2 > = < (inj M1) , (inj M2) >
inj tt = tt
inj (inl M) = inl (inj M)
inj (inr M) = inr (inj M)

data _⟶β*_ : ∀ {T} -> tm ⊡ ⊡ T -> tm ⊡ ⊡ T -> Set where
 β : ∀ {T S} (M : tm ⊡ (⊡ , T) S) (N : tm ⊡ ⊡ T) -> ((ƛ M) · N) ⟶β* [ tt , N ]t M
 β*1 : ∀ {T S} (M : tm ⊡ ⊡ T) (N : tm ⊡ ⊡ S) -> (fst < M , N >) ⟶β* M
 β*2 : ∀ {T S} (M : tm ⊡ ⊡ T) (N : tm ⊡ ⊡ S) -> (snd < M , N >) ⟶β* N
 _·_ : ∀ {T S} {M M' : tm _ ⊡ (T ⇝ S)} (sm : M ⟶β* M') {N N' : tm _ ⊡ T} (sn : N ⟶β* N')  -> (M · N) ⟶β* (M' · N')
 <_,_> : ∀ {T S} {M M' : tm _ ⊡ T} (sm : M ⟶β* M') {N N' : tm _ ⊡ S} (sn : N ⟶β* N')  -> < M , N > ⟶β* < M' , N' >
 fst : ∀ {T S} {M M' : tm _ ⊡ (T * S)} (s : M ⟶β* M')   -> (fst M) ⟶β* (fst M')
 snd : ∀ {T S} {M M' : tm _ ⊡ (T * S)} (s : M ⟶β* M')   -> (snd M) ⟶β* (snd M')
 inl : ∀ {S T} {M M' : tm _ ⊡ T} (s : M ⟶β* M')         -> (inl {⊡} {⊡} {S} M) ⟶β* (inl M')
 inr : ∀ {T S} {M M' : tm _ ⊡ S} (s : M ⟶β* M')         -> (inr {⊡} {⊡} {T} M) ⟶β* (inr M')
 case : ∀ {T S C} {M M' : tm _ ⊡ (T + S)} (S : M ⟶β* M') (N1 : tm _ (⊡ , T) C) N2 -> (case M N1 N2) ⟶β* (case M' N1 N2)
 β+₁ : ∀ {T S C} (M : tm _ ⊡ T) (N1 : tm _ (⊡ , T) C) (N2 : tm _ (⊡ , S) C) -> (case (inl M) N1 N2) ⟶β* [ tt , M ]t N1
 β+₂ : ∀ {T S C} (M : tm _ ⊡ S) (N1 : tm _ (⊡ , T) C) (N2 : tm _ (⊡ , S) C) -> (case (inr M) N1 N2) ⟶β* [ tt , M ]t N2
 refl : ∀ {T} (M : tm _ ⊡ T) -> M ⟶β* M
 ⟶β*-trans : ∀ {T} {M1 M2 M3 : tm _ ⊡ T} -> M1 ⟶β* M2 -> M2 ⟶β* M3 -> M1 ⟶β* M3

⟶β*≡-trans : ∀ {T} {M1 M2 M3 : tm ⊡ ⊡ T} -> M1 ≡ M2 -> M2 ⟶β* M3 -> M1 ⟶β* M3 
⟶β*≡-trans refl s2 = s2





 

