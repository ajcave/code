module weak-head-env-machine where
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product


record Unit : Set where
 constructor tt

data tp : Set where
 atom : tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)


mutual
 data val : tp -> Set where
  ƛ_[_] : ∀ {Γ T S} -> tm (Γ , T) S -> sub Γ -> val (T ⇝ S)

 sub : (Γ : ctx) -> Set
 sub Γ = ∀ {T} -> var Γ T -> val T

_,,_ : ∀ {Γ1 T} -> sub Γ1 -> val T -> sub (Γ1 , T)
(σ ,, M) z = M
(σ ,, M) (s y) = σ y

data act : tp -> tp -> Set where
 ap1 : ∀ {Γ T C} -> tm Γ T -> sub Γ -> act (T ⇝ C) C
 ap2 : ∀ {Γ T C} -> tm (Γ , T) C -> sub Γ -> act T C

data cont : tp -> tp -> Set where
 ⊡ : ∀ {T} -> cont T T
 _,_ : ∀ {T S C} -> cont S C -> act T S -> cont T C

data config : tp -> Set where
 _▹_[_] : ∀ {Γ T S} -> cont T S -> tm Γ T -> sub Γ -> config S
 _◅_ : ∀ {T S} -> cont T S -> val T -> config S

data _⟶_ : ∀ {C} -> config C -> config C -> Set where
 ap1 : ∀ {Γ T S C} {M : tm Γ (T ⇝ S)} {N} {σ : sub Γ} {K : cont S C} ->
       (K ▹ (M · N) [ σ ]) ⟶ ((K , ap1 N σ) ▹ M [ σ ])
 lam : ∀ {Γ T S C} {M : tm (Γ , T) S} {σ : sub Γ} {K : cont (T ⇝ S) C} ->
       (K ▹ (ƛ M) [ σ ]) ⟶ (K ◅ (ƛ M [ σ ]))
 ap2 : ∀ {Γ Γ' T S C} {M : tm (Γ , T) S} {N : tm Γ' T} {σ : sub Γ} {σ' : sub Γ'} {K : cont S C} ->
       ((K , ap1 N σ') ◅ (ƛ M [ σ ])) ⟶ ((K , ap2 M σ) ▹ N [ σ' ])
 β : ∀ {Γ T S C} {M : tm (Γ , T) S} {V : val T} {σ : sub Γ} {K : cont S C} ->
       ((K , ap2 M σ) ◅ V) ⟶ (K ▹ M [ σ ,, V ])
 v : ∀ {Γ T C} {x : var Γ T} {σ : sub Γ} {K : cont T C} ->
       (K ▹ (v x) [ σ ]) ⟶ (K ◅ (σ x))

data _⟶*_ {C} : config C -> config C -> Set where
 refl : ∀ {c} -> c ⟶* c
 _,_ : ∀ {c1 c2 c3} -> c1 ⟶ c2 -> c2 ⟶* c3 -> c1 ⟶* c3

⟶*-trans : ∀ {C} {c1 c2 c3 : config C} -> c1 ⟶* c2 -> c2 ⟶* c3 -> c1 ⟶* c3
⟶*-trans refl t = t
⟶*-trans (t1 , t2) t3 = t1 , (⟶*-trans t2 t3)

reduce : ∀ T -> val T -> Set
reduce atom t = Unit
reduce (T ⇝ S) (ƛ t [ σ ]) = ∀ (x : val T) {C} (K : cont S C) -> reduce T x -> Σ (val S) (λ w -> ((K ▹ t [ σ ,, x ]) ⟶* (K ◅ w)) × reduce S w)

reduce-ext : ∀ {Γ} {σ : ∀ {U} (x : var Γ U) -> val U} (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) {T} {t : val T} (w : reduce T t) ->
 ∀ {U} (x : var (Γ , T) U) -> reduce U ((σ ,, t) x)
reduce-ext θ w z = w
reduce-ext θ w (s y) = θ y


-- Could move the quantification over K inside... (I do this in the next file...)
-- I think we could do this whole thing in the empty continuation, and have a lemma that lets us reduce in contexts?
thm : ∀ {Γ T} (σ : sub Γ) (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) (t : tm Γ T) {C} (K : cont T C)
  -> Σ (val T) (λ w -> ((K ▹ t [ σ ]) ⟶* (K ◅ w)) × reduce T w)
thm σ θ (v x) K = (σ x) , ((v , refl) , (θ x))
thm σ θ (t · t₁) K with thm σ θ t (K , ap1 t₁ σ)
... | (ƛ v1 [ σ' ]) , p1 , r1 with thm σ θ t₁ (K , ap2 v1 σ')
... | v2 , p2 , r2 with r1 v2 K r2
... | v3 , p3 , r3 = v3 , (⟶*-trans (ap1 , p1) (⟶*-trans (ap2 , p2) (β , p3)) , r3)
thm σ θ (ƛ t) K = ƛ t [ σ ] , ((lam , refl) , (λ x K' x' → thm (σ ,, x) (reduce-ext θ x') t K'))

⊡' : sub ⊡
⊡' ()

norm : ∀ {T} (t : tm ⊡ T) {C} (K : cont T C) -> ∃ (λ v -> (K ▹ t [ ⊡' ]) ⟶* (K ◅ v))
norm t K with thm ⊡' (λ ()) t K
norm t K | v1 , p1 , _ = v1 , p1

-- What about proving soundness and completeness w.r.t equational theory?
-- What about a cbn evaluation strategy?
