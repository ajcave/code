module nbe-explicit-subst-metavars where
open import FinMap
open import Product
open import Unit

postulate
 atomic_tp : Set

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp
 _⊗_ : (T S : tp) -> tp
 unit : tp

mutual 
 data rtm (Γ : ctx tp) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
  π₁ : ∀ {T S} -> rtm Γ (T ⊗ S) -> rtm Γ T
  π₂ : ∀ {T S} -> rtm Γ (T ⊗ S) -> rtm Γ S
 data ntm (Γ : ctx tp) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T ⊗ S)
  tt : ntm Γ unit


sem : (Γ : ctx tp) -> (T : tp) -> Set
sem Γ (atom A) = rtm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S 
sem Γ (T ⊗ S) = sem Γ T × sem Γ S
sem Γ unit = Unit

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (lookup σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (vsub-ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = rappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘v σ) s
appSubst (T ⊗ S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
appSubst unit σ tt = tt

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)
 reflect {T ⊗ S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = neut M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn-vsub (reflect (v top))))
 reify {T ⊗ S} M = < reify (_×_.proj₁ M) , reify (_×_.proj₂ M) >
 reify {unit} tt = tt

subst : ctx tp -> ctx tp -> Set
subst Γ Δ = gsubst Γ (sem Δ)

data tm  (Γ : ctx tp) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 π₁ : ∀ {T S} -> tm Γ (T ⊗ S) -> tm Γ T
 π₂ : ∀ {T S} -> tm Γ (T ⊗ S) -> tm Γ S
 <_,_> : ∀ {T S} -> tm Γ T -> tm Γ S -> tm Γ (T ⊗ S)
 tt : tm Γ unit

-- Traditional nbe
eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = lookup θ y
eval θ (M · N) = eval θ M _ id-vsub (eval θ N)
eval θ (ƛ M) = λ _ σ s -> eval (gmap (appSubst _ σ) θ , s) M
eval θ (π₁ M) = _×_.proj₁ (eval θ M)
eval θ (π₂ N) = _×_.proj₂ (eval θ N)
eval θ < M , N > = eval θ M , eval θ N
eval θ tt = tt

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval {! (λ x → reflect (v x) ) !} M) 
