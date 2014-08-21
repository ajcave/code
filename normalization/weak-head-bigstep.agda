module weak-head-bigstep where
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product


record Unit : Set where
 constructor tt

postulate
 atomic_tp : Set

data tp : Set where
 atom : tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

vsubst : ctx -> ctx -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

_∘₁_ : ∀ {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘₁ g) x = f (g x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> ext id x ≡ x
ext-id z = refl
ext-id (s y) = refl

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = s

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)

[_]v : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_]v σ (v y) = v (σ y)
[_]v σ (M · N) = [ σ ]v M · [ σ ]v N
[_]v σ (ƛ M) = ƛ ([ ext σ ]v M)

mutual
 data val : tp -> Set where
  ƛ_[_] : ∀ {Γ T S} -> tm (Γ , T) S -> sub Γ -> val (T ⇝ S)
  c : val atom

 sub : (Γ : ctx) -> Set
 sub Γ = ∀ {T} -> var Γ T -> val T

_,,_ : ∀ {Γ1 T} -> sub Γ1 -> val T -> sub (Γ1 , T)
(σ ,, M) z = M
(σ ,, M) (s y) = σ y


data _[_]⇓_ : ∀ {Γ T} -> tm Γ T -> sub Γ -> val T -> Set where
 app : ∀ {Γ T S} {M : tm Γ (T ⇝ S)} {N : tm Γ T} {σ : sub Γ} {Γ'} {M' : tm (Γ' , T) S} {N' : val T}
         {σ' : sub Γ'} {V}
       -> M [ σ ]⇓ (ƛ M' [ σ' ])
       -> N [ σ ]⇓ N'
       -> M' [ σ' ,, N' ]⇓ V
       -> (M · N) [ σ ]⇓ V
 v : ∀ {Γ T} {x : var Γ T} {σ : sub Γ} -> (v x) [ σ ]⇓ (σ x)
 ƛ : ∀ {Γ T S} {M : tm (Γ , T) S} {σ : sub Γ} ->
         (ƛ M) [ σ ]⇓ (ƛ M [ σ ])

reduce : ∀ T -> val T -> Set
reduce atom t = Unit
reduce (T ⇝ S) (ƛ t [ σ ]) = ∀ (x : val T) -> reduce T x -> Σ (val S) (λ w -> (t [ σ ,, x ]⇓ w) × reduce S w)

reduce-ext : ∀ {Γ} {σ : ∀ {U} (x : var Γ U) -> val U} (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) {T} {t : val T} (w : reduce T t) ->
 ∀ {U} (x : var (Γ , T) U) -> reduce U ((σ ,, t) x)
reduce-ext θ w z = w
reduce-ext θ w (s y) = θ y

thm : ∀ {Γ T} (σ : sub Γ) (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) (t : tm Γ T)
  -> Σ (val T) (λ w -> (t [ σ ]⇓ w) × reduce T w)
thm σ θ (v x) = (σ x) , (v , θ x)
thm σ θ (t · t₁) with thm σ θ t | thm σ θ t₁
thm σ θ (t · t₁) | (ƛ v1 [ σ' ]) , pf1 , r1 | v2 , pf2 , r2 with r1 v2 r2
thm σ θ (t · t₁) | ƛ v1 [ σ' ] , pf1 , r1 | v2 , pf2 , r2 | v3 , pf3 , r3 = v3 , ((app pf1 pf2 pf3) , r3)
thm σ θ (ƛ {T} {S} t) = ƛ t [ σ ] , (ƛ , (λ v1 r -> thm (σ ,, v1) (reduce-ext θ r) t))
