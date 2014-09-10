module nbe3-freeweakening where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

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

mutual 
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : rtm Γ (atom) -> ntm Γ (atom)


Rtm : (Γ : ctx) (T : tp) -> Set
Rtm Γ T = ∀ {Δ} -> vsubst Γ Δ -> rtm Δ T

Ntm : (Γ : ctx) (T : tp) -> Set
Ntm Γ T = ∀ {Δ} -> vsubst Γ Δ -> ntm Δ T

sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom) = Rtm Γ atom
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S 

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

-- mutual
--  rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
--  rappSubst σ (v y) = v (σ y)
--  rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
--  rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
--  rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
--  nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
--  nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
--  nappSubst σ (neut R) = neut (rappSubst σ R)
--  nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
--  nappSubst σ tt = tt

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom) σ M = λ x → M (x ∘ σ)
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {T Γ} -> Rtm Γ T -> sem Γ T
 reflect {atom} N = N
 reflect {T ⇝ S} N = λ _ σ s → reflect (λ π -> (N (π ∘ σ)) · (reify s π))

 reify : ∀ {T Γ} -> sem Γ T -> Ntm Γ T
 reify {atom} M π = neut (M π)
 reify {T ⇝ S} {Γ} M {Δ} π = ƛ (reify (M _ wkn (reflect {Γ = Γ , T} (λ π' → v (π' z)))) (ext π))
                           --ƛ (reify (M _ (wkn ∘ π) (reflect {Γ = Δ , T} (λ π' → v (π' z)))) id)

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y


data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)

-- Traditional nbe
eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
eval θ (M · N) = eval θ M _ id (eval θ N)
eval θ (ƛ M) = λ Δ' σ s -> eval (extend (λ {T} x → appSubst T σ (θ x)) s) M

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval (λ x → reflect (λ π → v (π x))) M) id --reify (eval (λ x → reflect (v x)) M) 
