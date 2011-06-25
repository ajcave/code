{-# OPTIONS --no-positivity-check #-}
module nbe where

postulate
 atomic_tp : Set

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

vsubst : ctx -> ctx -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U

mutual
 data sem (Γ : ctx) : (T : tp) -> Set where 
  neut : ∀ {A} -> neu Γ (atom A) -> sem Γ (atom A)
  ƛ : ∀ {T S} -> (∀ {Δ} -> (∀ {U} -> var Γ U -> var Δ U)
                        -> sem Δ T -> sem Δ S) -> sem Γ (T ⇝ S)
 data neu (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> neu Γ T
  _·_ : ∀ {T S} -> neu Γ (T ⇝ S) -> sem Γ T -> neu Γ S

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

mutual
 appSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> sem Δ S -> sem Γ S
 appSubst σ (neut R) = neut (nappSubst σ R)
 appSubst σ (ƛ f) = ƛ (λ σ' → λ s → f (σ' ∘ σ) s ) 

 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> neu Δ S -> neu Γ S
 nappSubst σ (v y) = v (σ y)
 nappSubst σ (R · N) = (nappSubst σ R) · appSubst σ N

reflect : ∀ {Γ T} -> neu Γ T -> sem Γ T
reflect {T = atom P} R = neut R
reflect {T = U ⇝ S} R = ƛ (λ σ → λ s → reflect (nappSubst σ R · s))

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)



id : ∀ {Γ} -> vsubst Γ Γ
id x = x

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reify : ∀ {Γ T} -> sem Γ T -> tm Γ T
 reify (neut R) = nreify R
 reify (ƛ f) = ƛ (reify (f wkn (reflect (v z))))
 
 nreify : ∀ {Γ T} -> neu Γ T -> tm Γ T
 nreify (v y) = v y
 nreify (R · N) = (nreify R) · (reify N)

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = appSubst id (θ y)

eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
eval θ (M · N) with eval θ M
eval θ (M · N) | ƛ f = f id (eval θ N)
eval θ (ƛ M) = ƛ (λ σ → λ s → eval (extend (λ x → appSubst σ (θ x)) s) M)

init : subst ⊡ ⊡
init ()

nbe : ∀ {T} -> tm ⊡ T -> tm ⊡ T
nbe M = reify (eval init M)

--- Alternative: Do it properly:

mutual 
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)

mutual
 reify' : ∀ {Γ T} -> sem Γ T -> ntm Γ T
 reify' (neut R) = neut (nreify' R)
 reify' (ƛ f) = ƛ (reify' (f wkn (reflect (v z))))
 
 nreify' : ∀ {Γ T} -> neu Γ T -> rtm Γ T
 nreify' (v y) = v y
 nreify' (R · N) = (nreify' R) · (reify' N)

nbe' : ∀ {T} -> tm ⊡ T -> ntm ⊡ T
nbe' M = reify' (eval init M)