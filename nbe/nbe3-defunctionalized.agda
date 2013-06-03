module nbe3-defunctionalized where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Unit : Set where
 constructor tt

postulate
 atomic_tp : Set

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp
 _×_ : (T S : tp) -> tp
 unit : tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

vsubst : ctx -> ctx -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U

mutual 
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
  π₁ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ T
  π₂ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T × S)
  tt : ntm Γ unit

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 π₁ : ∀ {T S} -> tm Γ (T × S) -> tm Γ T
 π₂ : ∀ {T S} -> tm Γ (T × S) -> tm Γ S
 <_,_> : ∀ {T S} -> tm Γ T -> tm Γ S -> tm Γ (T × S)
 tt : tm Γ unit


_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 data lam (T S : tp) : (Γ : ctx) -> Set where
  appSubstClo : ∀ {Δ Γ} (w : vsubst Γ Δ) -> lam T S Γ -> lam T S Δ
  reflectClo : ∀ {Γ} -> rtm Γ (T ⇝ S) -> lam T S Γ
  evalClo : ∀ {Γ Δ} (θ : subst Γ Δ) (M : tm (Γ , T) S) -> lam T S Δ

 sem : (Γ : ctx) -> (T : tp) -> Set
 sem Γ (atom A) = rtm Γ (atom A)
 sem Γ (T ⇝ S) = lam T S Γ 
 sem Γ (T × S) = sem Γ T * sem Γ S
 sem Γ unit = Unit

 subst : ctx -> ctx -> Set
 subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T


 appLam : ∀ {T S Γ Δ} -> lam T S Γ -> vsubst Γ Δ -> sem Δ T -> sem Δ S
 appLam (appSubstClo w x) σ x₁ = appLam x (σ ∘ w) x₁
 appLam (reflectClo x) σ s' = reflect (rappSubst σ x · reify s')
 appLam (evalClo θ M) σ x = eval (extend (λ x₁ → appSubst _ σ (θ x₁)) x) M
  


 appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
 appSubst (atom A) σ M = rappSubst σ M
 appSubst (T ⇝ S) σ M = appSubstClo σ M
 appSubst (T × S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
 appSubst unit σ tt = tt

 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = N
 reflect {T ⇝ S} N = reflectClo N
 reflect {T × S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = neut M
 reify {T ⇝ S} M = ƛ (reify (appLam M wkn (reflect (v z)))) 
 reify {T × S} M = < reify (_*_.fst M) , reify (_*_.snd M) >
 reify {unit} tt = tt


 extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
 extend θ M z = M
 extend θ M (s y) = θ y


 eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
 eval θ (v y) = θ y
 eval θ (M · N) = appLam (eval θ M) id (eval θ N) 
 eval θ (ƛ M) = evalClo θ M 
 eval θ (π₁ M) = _*_.fst (eval θ M)
 eval θ (π₂ N) = _*_.snd (eval θ N)
 eval θ < M , N > = eval θ M , eval θ N
 eval θ tt = tt

 nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
 nbe M = reify (eval (λ x → reflect (v x)) M) 
