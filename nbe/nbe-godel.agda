module nbe-godel where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Unit : Set where
 constructor tt

data atomic_tp : Set where
 nat : atomic_tp
 list : atomic_tp

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
  rec : ∀ {C} -> rtm Γ (atom nat) -> ntm Γ C -> ntm Γ (C ⇝ C) -> rtm Γ C
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T × S)
  tt : ntm Γ unit
  z : ntm Γ (atom nat)
  s : (N : ntm Γ (atom nat)) -> ntm Γ (atom nat)
  nil : ntm Γ (atom list)
  cons : (N : ntm Γ (atom nat)) -> (L : ntm Γ (atom list)) -> ntm Γ (atom list)


sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = ntm Γ (atom A)
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
 rappSubst σ (rec R E0 ES) = rec (rappSubst σ R) (nappSubst σ E0) (nappSubst σ ES)
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt
 nappSubst σ z = z
 nappSubst σ (s N) = s (nappSubst σ N)
 nappSubst σ nil = nil
 nappSubst σ (cons N L) = cons (nappSubst σ N) (nappSubst σ L)

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = nappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s
appSubst (T × S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
appSubst unit σ tt = tt

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = neut N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)
 reflect {T × S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z))))
 reify {T × S} M = < reify (_*_.fst M) , reify (_*_.snd M) >
 reify {unit} N = tt

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

iter1 : ∀ {A : Set} {Γ} (N : ntm Γ (atom nat)) -> (f : rtm Γ (atom nat) -> A) -> A -> (A -> A) -> A
iter1 z f e0 es = e0
iter1 (s N) f e0 es = es (iter1 N f e0 es)
iter1 (neut R) f e0 es = f R

-- Here we have admissibility of cut for ntm. Not necessary for nbe,
-- but nice to state.
mutual
 srSubst : ∀ {Γ Δ T} -> subst Γ Δ -> rtm Γ T -> sem Δ T
 srSubst θ (v y) = θ y
 srSubst θ (R · N) = srSubst θ R _ id (sSubst θ N)
 srSubst θ (π₁ R) = _*_.fst (srSubst θ R)
 srSubst θ (π₂ R) = _*_.snd (srSubst θ R)
 srSubst θ (rec R E0 ES) with srSubst θ R
 ... | w = iter1 w (λ x → reflect (rec x (reify (sSubst θ E0)) (reify (sSubst θ ES)))) (sSubst θ E0) (λ x → sSubst θ ES _ id x)

 sSubst : ∀ {Γ Δ T} -> subst Γ Δ -> ntm Γ T -> sem Δ T
 sSubst θ (ƛ M) = λ Δ σ s → sSubst (extend (λ x → appSubst _ σ (θ x)) s) M
 sSubst θ (neut y) = srSubst θ y
 sSubst θ < M , N > = sSubst θ M , sSubst θ N
 sSubst θ tt = tt
 sSubst θ z = z
 sSubst θ (s N) = s (sSubst θ N)
 sSubst θ nil = nil
 sSubst θ (cons N L) = cons (sSubst θ N) (sSubst θ L) 

sId : ∀ {Γ} -> subst Γ Γ
sId x = reflect (v x)

nSubst : ctx -> ctx -> Set
nSubst Γ Δ = ∀ {S} -> var Γ S -> ntm Δ S

embed : ∀ {Γ T} -> ntm Γ T -> sem Γ T
embed N = sSubst sId N

embed* : ∀ {Γ Δ} -> nSubst Γ Δ -> subst Γ Δ
embed* θ x = embed (θ x)

cut : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Γ T -> ntm Δ T
cut θ t = reify (sSubst (embed* θ) t)

nv : ∀ {Γ T} -> var Γ T -> ntm Γ T
nv x = reify (reflect (v x))

nExtend : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Δ T -> nSubst (Γ , T) Δ
nExtend θ N z = N
nExtend θ N (s y) = θ y

nId : ∀ {Γ} -> nSubst Γ Γ
nId x = nv x

napp : ∀ {Γ T S} -> ntm Γ (T ⇝ S) -> ntm Γ T -> ntm Γ S
napp (ƛ N) M = cut (nExtend nId M) N

nfst : ∀ {Γ T S} -> ntm Γ (T × S) -> ntm Γ T
nfst < M , N > = M

nsnd : ∀ {Γ T S} -> ntm Γ (T × S) -> ntm Γ S
nsnd < M , N > = N

η-expand : ∀ {C Γ} -> rtm Γ C -> ntm Γ C
η-expand R = reify (reflect R)

nrec : ∀ {Γ C} -> ntm Γ (atom nat) -> ntm Γ C -> ntm Γ (C ⇝ C) -> ntm Γ C
nrec (neut y) E0 ES = η-expand (rec y E0 ES)
nrec z E0 ES = E0
nrec (s N) E0 (ƛ y) = cut (nExtend nId (nrec N E0 (ƛ y))) y

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 π₁ : ∀ {T S} -> tm Γ (T × S) -> tm Γ T
 π₂ : ∀ {T S} -> tm Γ (T × S) -> tm Γ S
 <_,_> : ∀ {T S} -> tm Γ T -> tm Γ S -> tm Γ (T × S)
 tt : tm Γ unit
 z : tm Γ (atom nat)
 s : (M : tm Γ (atom nat)) -> tm Γ (atom nat)
 nil : tm Γ (atom list)
 cons : (N : tm Γ (atom nat)) -> (L : tm Γ (atom list)) -> tm Γ (atom list) 
 rec : ∀ {C} -> tm Γ (atom nat) -> tm Γ C -> tm Γ (C ⇝ C) -> tm Γ C

complete : ∀ {Γ T} -> tm Γ T -> ntm Γ T
complete (v y) = nv y
complete (M · N) = napp (complete M) (complete N)
complete (ƛ M) = ƛ (complete M)
complete (π₁ M) = nfst (complete M)
complete (π₂ N) = nsnd (complete N)
complete < M , N > = < complete M , complete N >
complete tt = tt
complete z = z
complete (s N) = s (complete N)
complete nil = nil
complete (cons N L) = cons (complete N) (complete L)
complete (rec R E0 ES) = nrec (complete R) (complete E0) (complete ES)
