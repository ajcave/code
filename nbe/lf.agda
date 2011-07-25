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

data nat : Set where
 z : nat
 s : nat -> nat

data var : nat -> Set where
 z : ∀ {n} -> var (s n)
 s : ∀ {n} -> var n -> var (s n)

mutual
 data atomic_tp (n : nat) : Set where
  vec : (N : ntm n) -> atomic_tp n
  Nat : atomic_tp n
 data tp (n : nat) : Set where
  ▹ : (A : atomic_tp n) -> tp n
  Π : (T : tp n) -> (S : tp (s n)) -> tp n
 data rtm (n : nat) : Set where
  ▹ : (x : var n) -> rtm n
  _·_ : (R : rtm n) -> (N : ntm n) -> rtm n
  z : rtm n
 data ntm (n : nat) : Set where
  ▹ : (R : rtm n) -> ntm n
  ƛ : (N : ntm (s n)) -> ntm n

vsub : ∀ (n m : nat) -> Set
vsub n m = var n → var m 

vext : ∀ {n m} -> vsub n m -> vsub (s n) (s m)
vext σ z = z
vext σ (s y) = s (σ y)

mutual 
 tvsub : ∀ {n m} -> vsub n m -> tp n -> tp m
 tvsub σ (▹ A) = ▹ (atvsub σ A)
 tvsub σ (Π T S) = Π (tvsub σ T) (tvsub (vext σ) S)

 atvsub : ∀ {n m} -> vsub n m -> atomic_tp n -> atomic_tp m
 atvsub σ (vec N) = vec (nvsub σ N)
 atvsub σ Nat = Nat

 nvsub : ∀ {n m} -> vsub n m -> ntm n -> ntm m
 nvsub σ (▹ R) = ▹ (rvsub σ R)
 nvsub σ (ƛ N) = ƛ (nvsub (vext σ) N)

 rvsub : ∀ {n m} -> vsub n m -> rtm n -> rtm m
 rvsub σ (▹ x) = ▹ (σ x)
 rvsub σ (R · N) = (rvsub σ R) · (nvsub σ N)
 rvsub σ z = z

twkn : ∀ {n} -> tp n -> tp (s n)
twkn t = tvsub s t

mutual
 data ctx : nat -> Set where
  ⊡ : ctx z
  _,_ : ∀ {n} (Γ : ctx n) -> {T : tp n} -> type Γ T -> ctx (s n)
 data Var : ∀ {n} (Γ : ctx n) (x : var n) (T : tp n) -> Set where
  z : ∀ {n Γ t T} -> Var (_,_ {n} Γ {t} T) z (twkn t) 
  s : ∀ {n Γ t u U n'} -> Var Γ n' t -> Var (_,_ {n} Γ {u} U) (s n') (twkn t)
 data atomic_type {n : nat } (Γ : ctx n) : (T : atomic_tp n) -> Set where
  vec : ∀ {N : ntm n} -> nterm Γ N (▹ Nat) -> atomic_type Γ (vec N)
  Nat : atomic_type Γ Nat 
 data type {n} (Γ : ctx n) : (T : tp n) -> Set where
  ▹ : ∀ {A : atomic_tp n} -> atomic_type Γ A -> type Γ (▹ A)
  Π : ∀ {t s} -> (T : type Γ t) -> type (Γ , T) s -> type Γ (Π t s)
 data rterm {n} (Γ : ctx n) : (R : rtm n) (T : tp n) -> Set where
  ▹ : ∀ {T} {x : var n} (X : Var Γ x T) -> rterm Γ (▹ x) T
  _·_ : ∀ {r n s t} (R : rterm Γ r (Π s t)) (N : nterm Γ n s) -> rterm Γ (r · n) {!!} -- (tsub t N)
  z : rterm Γ z (▹ Nat)
 data nterm {n} (Γ : ctx n) : (M : ntm n) (T : tp n) -> Set where
  ▹ : ∀ {a r} {A : atomic_type Γ a} -> rterm Γ r (▹ a) -> nterm Γ (▹ r) (▹ a)
  ƛ : ∀ {t} (T : type Γ t) {n' u U} (N : nterm (Γ , T) n' U) -> nterm Γ (ƛ n') (Π t u)


 tsub : ∀ {n Γ N s} (t : tp n) -> nterm Γ N s -> tp n
 tsub (▹ (vec n')) n0 = ▹ (vec {!!})
 tsub (▹ nat) n' = ▹ nat
 tsub (Π T S) n' = Π (tsub T n') {!sub!}

{-
mutual
 data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) -> (T : tp Γ) -> ctx
 data tp : (Γ : ctx) -> Set where
  _⇝_ : ∀ {Γ} (T : tp Γ) -> (S : tp (Γ , T)) -> tp Γ
 data var2 : (Γ : ctx) -> (T : tp Γ) -> Set where
  z : ∀ {Γ T} -> var2 (Γ , T) (wkn T)
  s : ∀ {Γ T S} -> var2 Γ T -> var2 (Γ , S) (wkn T) 

 wkn : ∀ {Γ S} -> (T : tp Γ) -> tp (Γ , S) -- this _,_ use is apparently not allowed
 wkn t = ? -}
 
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