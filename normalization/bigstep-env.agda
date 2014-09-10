module bigstep-env where
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
 data neut (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> neut Γ T
  _·_ : ∀ {T S} -> neut Γ (T ⇝ S) -> norm Γ T -> neut Γ S
 data norm (Γ : ctx) : (T : tp) -> Set where
  ▹ : ∀ {T} -> neut Γ T -> norm Γ T
  ƛ : ∀ {T S} -> norm (Γ , T) S -> norm Γ (T ⇝ S)

sub : (Γ Δ : ctx) -> Set
sub Γ Δ = ∀ {T} -> var Γ T -> norm Δ T

_,,_ : ∀ {Γ1 Δ T} -> sub Γ1 Δ -> norm Δ T -> sub (Γ1 , T) Δ
(σ ,, M) z = M
(σ ,, M) (s y) = σ y

id : ∀ {Γ} -> sub Γ Γ
id = λ x -> ▹ (v x)

ext : ∀ {Γ Δ T} -> sub Γ Δ -> sub (Γ , T) (Δ , T)
ext σ x = ?

data _[_]⇓_ : ∀ {Γ Δ T} -> tm Γ T -> sub Γ Δ -> norm Δ T -> Set where
 app : ∀ {Γ Δ T S} {M : tm Γ (T ⇝ S)} {N : tm Γ T} {σ : sub Γ Δ} {M' : norm (Δ , T) S} {N' : norm Δ T} {V}
       -> M [ σ ]⇓ (ƛ M')
       -> N [ σ ]⇓ N'
       -> M' [ id ,, N' ]⇓ V
       -> (M · N) [ σ ]⇓ V
 v : ∀ {Γ Δ T} {x : var Γ T} {σ : sub Γ Δ} -> (v x) [ σ ]⇓ (σ x)
 ƛ : ∀ {Γ Δ T S} {M : tm (Γ , T) S} {σ : sub Γ} {M' : norm (Δ , T) S} -> 
          M [ ext σ ]⇓ M'
       -> (ƛ M) [ σ ]⇓ (ƛ M')

-- reduce : ∀ T -> val T -> Set
-- reduce atom t = Unit
-- reduce (T ⇝ S) (ƛ t [ σ ]) = ∀ (x : val T) -> reduce T x -> Σ (val S) (λ w -> (t [ σ ,, x ]⇓ w) × reduce S w)

-- reduce-ext : ∀ {Γ} {σ : sub Γ} (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) {T} {t : val T} (w : reduce T t) ->
--  ∀ {U} (x : var (Γ , T) U) -> reduce U ((σ ,, t) x)
-- reduce-ext θ w z = w
-- reduce-ext θ w (s y) = θ y

-- thm : ∀ {Γ T} (σ : sub Γ) (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) (t : tm Γ T)
--   -> Σ (val T) (λ w -> (t [ σ ]⇓ w) × reduce T w)
-- thm σ θ (v x) = (σ x) , (v , θ x)
-- thm σ θ (t · t₁) with thm σ θ t | thm σ θ t₁
-- thm σ θ (t · t₁) | (ƛ v1 [ σ' ]) , pf1 , r1 | v2 , pf2 , r2 with r1 v2 r2
-- thm σ θ (t · t₁) | ƛ v1 [ σ' ] , pf1 , r1 | v2 , pf2 , r2 | v3 , pf3 , r3 = v3 , ((app pf1 pf2 pf3) , r3)
-- thm σ θ (ƛ {T} {S} t) = ƛ t [ σ ] , (ƛ , (λ v1 r -> thm (σ ,, v1) (reduce-ext θ r) t))

-- ⊡' : sub ⊡
-- ⊡' ()

-- norm : ∀ {T} -> (t : tm ⊡ T) -> ∃ (λ v -> t [ ⊡' ]⇓ v)
-- norm t with thm ⊡' (λ ()) t
-- norm t | proj₁ , proj₂ , proj₃ = proj₁ , proj₂

-- What about proving soundness and completeness w.r.t equational theory?
-- What about a cbn evaluation strategy?
