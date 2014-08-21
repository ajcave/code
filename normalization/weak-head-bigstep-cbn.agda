module weak-head-bigstep-cbn where
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
 data clo : tp -> Set where
  _[_]' : ∀ {Γ T} -> tm Γ T -> sub Γ -> clo T

 sub : (Γ : ctx) -> Set
 sub Γ = ∀ {T} -> var Γ T -> clo T

data val : tp -> Set where
 ƛ_[_] : ∀ {Γ T S} -> tm (Γ , T) S -> sub Γ -> val (T ⇝ S)

_,,_ : ∀ {Γ1 T} -> sub Γ1 -> clo T -> sub (Γ1 , T)
(σ ,, M) z = M
(σ ,, M) (s y) = σ y


data _⇓_ : ∀ {T} -> clo T -> val T -> Set where
 app : ∀ {Γ T S} {M : tm Γ (T ⇝ S)} {N : tm Γ T} {σ : sub Γ} {Γ'} {M' : tm (Γ' , T) S}
         {σ' : sub Γ'} {V}
       -> M [ σ ]' ⇓ (ƛ M' [ σ' ])
       -> M' [ σ' ,, (N [ σ ]' ) ]' ⇓ V
       -> (M · N) [ σ ]' ⇓ V
 v : ∀ {Γ T} {x : var Γ T} {σ : sub Γ} {v1} -> (σ x) ⇓ v1 -> (v x) [ σ ]' ⇓ v1
 ƛ : ∀ {Γ T S} {M : tm (Γ , T) S} {σ : sub Γ} ->
         (ƛ M) [ σ ]' ⇓ (ƛ M [ σ ])

halts : ∀ {T} -> clo T -> Set
halts (t [ σ ]') = ∃ (λ w -> t [ σ ]' ⇓ w)

mutual
 redval : ∀ T -> val T -> Set
 redval atom ()
 redval (T ⇝ T₁) (ƛ t [ σ ]) = ∀ x -> redclo T x -> redclo T₁ (t [ σ ,, x ]')
 
 redclo : ∀ T -> clo T -> Set
 redclo T t = ∃ (λ w -> (t ⇓ w) × redval T w)

-- reduce : ∀ T -> clo T -> Set
-- reduce atom t = halts t
-- reduce (T ⇝ S) t = ∃ (λ Γ -> Σ (tm (Γ , T) S) (λ t' -> Σ (sub Γ) (λ σ -> t ⇓ (ƛ t' [ σ ]) × (∀ (x : clo T) -> reduce T x -> reduce S (t' [ σ ,, x ]' )))))

reduce-ext : ∀ {Γ} {σ : ∀ {U} (x : var Γ U) -> clo U} (θ : ∀ {U} (x : var Γ U) -> redclo U (σ x)) {T} {t : clo T} (w : redclo T t) ->
 ∀ {U} (x : var (Γ , T) U) -> redclo U ((σ ,, t) x)
reduce-ext θ w z = w
reduce-ext θ w (s y) = θ y

thm : ∀ {Γ T} (σ : sub Γ) (θ : ∀ {U} (x : var Γ U) -> redclo U (σ x)) (t : tm Γ T)
  -> redclo T (t [ σ ]')
thm σ θ (v x) with θ x
... | q1 , q2 , q3 = q1 , v q2 , q3
thm σ θ (t · t₁) with thm σ θ t 
... | (ƛ v1 [ σ1 ]) , p1 , r1 with r1 (t₁ [ σ ]') (thm σ θ t₁)
... | v3 , p3 , r3 = v3 , ((app p1 p3) , r3)
thm σ θ (ƛ t) = ƛ t [ σ ] , (ƛ , (λ x x₁ → thm (σ ,, x) (reduce-ext θ x₁) t))

⊡' : sub ⊡
⊡' ()

norm : ∀ {T} (t : tm ⊡ T) -> halts (t [ ⊡' ]')
norm t with thm ⊡' (λ ()) t
... | v1 , p1 , r1 = v1 , p1

-- What about proving soundness and completeness w.r.t equational theory?
-- What about a cbn evaluation strategy?
