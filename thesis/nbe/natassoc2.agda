module natassoc2 where
open import Data.List hiding (sum)

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Unit : Set where
 constructor tt

data tp : Set where
 nat : tp
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
  iter : ∀ {C} -> List (rtm Γ nat) -> ntm (Γ , C) C -> ntm Γ C -> rtm Γ C
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  suc : ntm Γ nat -> ntm Γ nat
  sum : List (rtm Γ nat) -> ntm Γ nat
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T × S)
  tt : ntm Γ unit


sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ nat = ntm Γ nat
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S 
sem Γ (T × S) = sem Γ T * sem Γ S
sem Γ unit = Unit

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
 rappSubst σ (iter xs f b) = iter (rlSubst σ xs) (nappSubst (ext σ) f) (nappSubst σ b)

 rlSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> List (rtm Δ S) -> List (rtm Γ S)
 rlSubst σ [] = []
 rlSubst σ (x ∷ Rs) = (rappSubst σ x) ∷ (rlSubst σ Rs)

 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (sum Rs) = sum (rlSubst σ Rs) --neut (rappSubst σ R)
 nappSubst σ (suc N) = suc (nappSubst σ N)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst nat σ M = nappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s
appSubst (T × S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
appSubst unit σ tt = tt

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {nat} N = sum (N ∷ [])
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)
 reflect {T × S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {nat} M = M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z))))
 reify {T × S} M = < reify (_*_.fst M) , reify (_*_.snd M) >
 reify {unit} tt = tt

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

ext' : ∀ {Γ Δ T} -> subst Γ Δ -> subst (Γ , T) (Δ , T)
ext' σ = extend (λ x → appSubst _ s (σ x)) (reflect (v z))

-- -- Here we have admissibility of cut for ntm. Not necessary for nbe,
-- -- but nice to state.
-- mutual
--  srSubst : ∀ {Γ Δ T} -> subst Γ Δ -> rtm Γ T -> sem Δ T
--  srSubst θ (v y) = θ y
--  srSubst θ (R · N) = srSubst θ R _ id (sSubst θ N)
--  srSubst θ (π₁ R) = _*_.fst (srSubst θ R)
--  srSubst θ (π₂ R) = _*_.snd (srSubst θ R)

--  sSubst : ∀ {Γ Δ T} -> subst Γ Δ -> ntm Γ T -> sem Δ T
--  sSubst θ (ƛ M) = λ Δ σ s → sSubst (extend (λ x → appSubst _ σ (θ x)) s) M
--  sSubst θ (neut y) = srSubst θ y
--  sSubst θ < M , N > = sSubst θ M , sSubst θ N
--  sSubst θ tt = tt

-- nSubst : ctx -> ctx -> Set
-- nSubst Γ Δ = ∀ {S} -> var Γ S -> ntm Δ S
-- cut : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Γ T -> ntm Δ T
-- cut θ t = reify (sSubst (λ x → sSubst (λ x' → reflect (v x')) (θ x)) t)

-- nv : ∀ {Γ T} -> var Γ T -> ntm Γ T
-- nv x = reify (reflect (v x))

-- nExtend : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Δ T -> nSubst (Γ , T) Δ
-- nExtend θ N z = N
-- nExtend θ N (s y) = θ y

-- nId : ∀ {Γ} -> nSubst Γ Γ
-- nId x = nv x

-- napp : ∀ {Γ T S} -> ntm Γ (T ⇝ S) -> ntm Γ T -> ntm Γ S
-- napp (ƛ N) M = cut (nExtend nId M) N

-- nfst : ∀ {Γ T S} -> ntm Γ (T × S) -> ntm Γ T
-- nfst < M , N > = M

-- nsnd : ∀ {Γ T S} -> ntm Γ (T × S) -> ntm Γ S
-- nsnd < M , N > = N

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 π₁ : ∀ {T S} -> tm Γ (T × S) -> tm Γ T
 π₂ : ∀ {T S} -> tm Γ (T × S) -> tm Γ S
 <_,_> : ∀ {T S} -> tm Γ T -> tm Γ S -> tm Γ (T × S)
 tt : tm Γ unit
 suc : tm Γ nat -> tm Γ nat
 zero : tm Γ nat
 _+'_ : tm Γ nat -> tm Γ nat -> tm Γ nat
 iter : ∀ {C} -> tm Γ nat -> tm (Γ , C) C -> tm Γ C -> tm Γ C

-- complete : ∀ {Γ T} -> tm Γ T -> ntm Γ T
-- complete (v y) = nv y
-- complete (M · N) = napp (complete M) (complete N)
-- complete (ƛ M) = ƛ (complete M)
-- complete (π₁ M) = nfst (complete M)
-- complete (π₂ N) = nsnd (complete N)
-- complete < M , N > = < complete M , complete N >
-- complete tt = tt

_⊕_ : ∀ {Γ} -> ntm Γ nat -> ntm Γ nat -> ntm Γ nat
suc n ⊕ m = suc (n ⊕ m)
n ⊕ suc m = suc (n ⊕ m)
sum x ⊕ sum x₁ = sum (x ++ x₁)

arr : ∀ Γ T -> Set
arr Γ T = ∀ {Δ} -> subst Γ Δ -> sem Δ T

iter' : ∀ {Γ T} -> arr (Γ , T) T -> arr Γ T -> ∀ {Δ} -> subst Γ Δ -> sem Δ nat -> sem Δ T
iter' f b σ (suc n) = f (extend σ (iter' f b σ n))
iter' f b σ (sum []) = b σ
iter' f b σ (sum (x ∷ x₁)) = reflect (iter (x ∷ x₁) (reify (f (ext' σ))) (reify (b σ)))

eval : ∀ {Γ T} -> tm Γ T -> arr Γ T
eval (v y) θ = θ y
eval (M · N) θ = eval M θ _ id (eval N θ)
eval (ƛ M) θ = λ _ σ s -> eval M (extend (λ x → appSubst _ σ (θ x)) s)
eval (π₁ M) θ = _*_.fst (eval M θ)
eval (π₂ N) θ = _*_.snd (eval N θ)
eval < M , N > θ = eval M θ , eval N θ
eval tt θ = tt
eval (suc n) θ = suc (eval n θ)
eval zero θ = sum []
eval (m +' n) θ = (eval m θ) ⊕ (eval n θ)
eval (iter xs f b) θ = iter' (eval f) (eval b) θ (eval xs θ)

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval M (λ x → reflect (v x))) 

