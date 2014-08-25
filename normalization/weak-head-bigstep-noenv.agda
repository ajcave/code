module weak-head-bigstep-noenv where
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

tsub : (Γ1 Γ2 : ctx) -> Set
tsub Γ1 Γ2 = ∀ {T} -> var Γ1 T -> tm Γ2 T

tsub-ext : ∀ {Γ1 Γ2 T} -> tsub Γ1 Γ2 -> tsub (Γ1 , T) (Γ2 , T)
tsub-ext σ z = v z
tsub-ext σ (s y) = [ s ]v (σ y)

[_]t : ∀ {Γ1 Γ2 T} (σ : tsub Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_]t σ (v y) = σ y
[_]t σ (M · N) = [ σ ]t M · [ σ ]t N
[_]t σ (ƛ M) = ƛ ([ tsub-ext σ ]t M)

_,,t_ : ∀ {Γ1 Γ2 T} -> tsub Γ1 Γ2 -> tm Γ2 T -> tsub (Γ1 , T) Γ2
(σ ,,t M) z = M
(σ ,,t M) (s y) = σ y

mutual
 val : tp -> Set
 val T = tm ⊡ T
 -- data val : tp -> Set where
 --  ƛ : ∀ {T S} -> tm (⊡ , T) S ->  val (T ⇝ S)

 sub : (Γ : ctx) -> Set
 sub Γ = ∀ {T} -> var Γ T -> val T

_,,_ : ∀ {Γ1 T} -> sub Γ1 -> val T -> sub (Γ1 , T)
(σ ,, M) z = M
(σ ,, M) (s y) = σ y


data _⇓_ : ∀ {T} -> tm ⊡ T -> val T -> Set where
 app : ∀ {T S} {M : tm ⊡ (T ⇝ S)} {N : tm ⊡ T} {M' : tm (⊡ , T) S} {N' : val T}
         {V}
       -> M ⇓ (ƛ M')
       -> N ⇓ N'
       -> ([ v ,,t N' ]t M') ⇓ V
       -> (M · N) ⇓ V
 ƛ : ∀ {T S} {M : tm (⊡ , T) S}->
         (ƛ M) ⇓ (ƛ M)

open import Data.Empty

reduce : ∀ T -> val T -> Set
reduce atom t = Unit
reduce (T ⇝ S) t = ∀ (x : val T) -> reduce T x -> Σ (val S) (λ w -> ((t · x) ⇓ w) × reduce S w)

reduce-ext : ∀ {Γ} {σ : ∀ {U} (x : var Γ U) -> val U} (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) {T} {t : val T} (w : reduce T t) ->
 ∀ {U} (x : var (Γ , T) U) -> reduce U ((σ ,, t) x)
reduce-ext θ w z = w
reduce-ext θ w (s y) = θ y

thm : ∀ {Γ T} (σ : sub Γ) (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) (t : tm Γ T)
  -> reduce T ([ σ ]t t)
thm σ θ (v x) = {!!}
thm σ θ (t · t₁) = {!!}
thm σ θ (ƛ {T} {S} t) = λ x x₁ → {!!} , ((app ƛ {!!} {!!}) , {!!}) --ƛ t [ σ ] , (ƛ , (λ v1 r -> thm (σ ,, v1) (reduce-ext θ r) t))

⊡' : sub ⊡
⊡' ()

norm : ∀ {T} -> (t : tm ⊡ T) -> ∃ (λ v -> t ⇓ v)
norm t = {!!} 

-- What about proving soundness and completeness w.r.t equational theory?
-- What about a cbn evaluation strategy?
