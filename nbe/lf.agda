{-# OPTIONS --no-positivity-check #-}
module lf where

record unit : Set where
 constructor tt

data _+_ (A B : Set) : Set where
 inl : A -> A + B
 inr : B -> A + B

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

data var : Set where
 z : var
 s : var -> var

mutual
 data atomic_tp : Set where
  vec : (n : ntm) -> atomic_tp
  nat : atomic_tp
 data tp : Set where
  ▹ : (A : atomic_tp) -> tp
  Π : (T : tp) -> (S : tp) -> tp
 data rtm : Set where
  ▹ : (x : var) -> rtm
  _·_ : (R : rtm) -> (N : ntm) -> rtm
  z : rtm
 data ntm : Set where
  ▹ : (R : rtm) -> ntm
  ƛ : (N : ntm) -> ntm

mutual
 data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) -> {T : tp} -> type Γ T -> ctx
 data Var : (Γ : ctx) (x : var) (T : tp) -> Set where
  z : ∀ {Γ t T} -> Var (_,_ Γ {t} T) z t
  s : ∀ {Γ t u U n} -> Var Γ n t -> Var (_,_ Γ {u} U) (s n) t
 data atomic_type : (Γ : ctx) (T : atomic_tp) -> Set where
  vec : ∀ {Γ} {N : ntm} -> nterm Γ N (▹ nat) -> atomic_type Γ (vec N)
  nat : ∀ {Γ} -> atomic_type Γ nat 
 data type : (Γ : ctx) (T : tp) -> Set where
  ▹ : ∀ {Γ} {A : atomic_tp} -> atomic_type Γ A -> type Γ (▹ A)
  Π : ∀ {Γ t s} -> (T : type Γ t) -> type (Γ , T) s -> type Γ (Π t s)
 data rterm : (Γ : ctx) (R : rtm) (T : tp) -> Set where
  ▹ : ∀ {Γ T} {x : var} (X : Var Γ x T) -> rterm Γ (▹ x) T
  _·_ : ∀ {Γ r n s t} (R : rterm Γ r (Π s t)) (N : nterm Γ n s) -> rterm Γ (r · n) (sub t N)
  z : ∀ {Γ} -> rterm Γ z (▹ nat)
 data nterm : (Γ : ctx) (M : ntm) (T : tp) -> Set where
  ▹ : ∀ {Γ a r} {A : atomic_type Γ a} -> rterm Γ r (▹ a) -> nterm Γ (▹ r) (▹ a)
  ƛ : ∀ {Γ t} (T : type Γ t) {n u U} (N : nterm (Γ , T) n U) -> nterm Γ n (Π t u)
 
 sub : ∀ {Γ n s} (t : tp) -> nterm Γ n s -> tp
 sub t n = {!!}
{-
mutual
 data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) -> (T : tp Γ) -> ctx
 data tp : (Γ : ctx) -> Set where
  atom : ∀ {Γ} (A : atomic_tp) -> tp Γ
  _⇝_ : ∀ {Γ} (T : tp Γ) -> (S : tp (Γ , T)) -> tp Γ
  wkn : ∀ {Γ S} -> (T : tp Γ) -> tp (Γ , S) 
 data var : (Γ : ctx) -> (T : tp Γ) -> Set where
  z : ∀ {Γ T} -> var (Γ , T) (wkn T)
  s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) (wkn T) -}
 
{- data rtm (Γ : ctx) : (T : tp Γ) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp Γ) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A) -}

{-
vsubst : ctx -> ctx -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U

mutual 

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)

sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = rtm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S 

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (σ y)
 rappSubst σ (M · N) = rappSubst σ M · nappSubst σ N
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = rappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = neut M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z))))

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
eval θ (M · N) with eval θ M
eval θ (M · N) | f = f _ id (eval θ N)
eval θ (ƛ M) = λ _ σ s -> eval (extend (λ x → appSubst _ σ (θ x)) s) M

nbe : ∀ {T} -> tm ⊡ T -> ntm ⊡ T
nbe M = reify (eval (λ ()) M) -}