module nbe-lf where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Unit : Set where
 constructor tt

postulate
 atomic_tp : Set
 nat : atomic_tp
 list : atomic_tp

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp
 _×_ : (T S : tp) -> tp
 unit : tp

data ctx' (A : Set) : Set where
 ⊡ : ctx' A
 _,_ : (Γ : ctx' A) -> (T : A) -> ctx' A

ctx = ctx' tp

data var {A : Set} : (Γ : ctx' A) -> (T : A) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

data vsubst : ∀ (Γ : ctx) (Δ : ctx) -> Set where 
 ⊡ : ∀ {Δ} -> vsubst ⊡ Δ
 _,_ : ∀ {Γ Δ U} -> (σ : vsubst Γ Δ) -> (x : var Δ U) -> vsubst (Γ , U) Δ

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
  z : ntm Γ (atom nat)
  s : (N : ntm Γ (atom nat)) -> ntm Γ (atom nat)
  nil : ntm Γ (atom list)
  cons : (N : ntm Γ (atom nat)) -> (L : ntm Γ (atom list)) -> ntm Γ (atom list)

sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = ntm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S 
sem Γ (T × S) = sem Γ T * sem Γ S
sem Γ unit = Unit

vsubst-app : ∀ {Γ Δ U} -> vsubst Γ Δ -> var Γ U -> var Δ U
vsubst-app ⊡ ()
vsubst-app (σ , x) z = x
vsubst-app (σ , x) (s y) = vsubst-app σ y

vsubst-map : ∀ {Δ Γ ψ} -> (∀ {U} -> var Δ U -> var Γ U) -> vsubst ψ Δ -> vsubst ψ Γ
vsubst-map σ1 ⊡ = ⊡
vsubst-map σ1 (σ , x) = (vsubst-map σ1 σ) , (σ1 x)

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
σ1 ∘ σ2 = vsubst-map (vsubst-app σ1) σ2

id : ∀ {Γ} -> vsubst Γ Γ
id {⊡} = ⊡
id {Γ , T} = vsubst-map s id , z

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = vsubst-map s id

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ = (wkn ∘ σ) , z

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (vsubst-app σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt
 nappSubst σ z = z
 nappSubst σ (s N) = s (nappSubst σ N)
 nappSubst σ nil = nil
 nappSubst σ (cons N L) = cons (nappSubst σ N) (nappSubst σ L)

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = nappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s
appSubst (T × S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
appSubst unit σ tt = tt

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

mutual
 srSubst : ∀ {Γ Δ T} -> subst Γ Δ -> rtm Γ T -> sem Δ T
 srSubst θ (v y) = θ y
 srSubst θ (R · N) = srSubst θ R _ id (sSubst θ N)
 srSubst θ (π₁ R) = _*_.fst (srSubst θ R)
 srSubst θ (π₂ R) = _*_.snd (srSubst θ R)

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

n-ext : ∀ {Γ Δ T} -> nSubst Γ Δ -> nSubst (Γ , T) (Δ , T)
n-ext θ z = nv z
n-ext θ (s y) = nappSubst wkn (θ y)

nId : ∀ {Γ} -> nSubst Γ Γ
nId x = nv x

n-single : ∀ {Γ T} -> ntm Γ T -> nSubst (Γ , T) Γ
n-single N = nExtend nId N

n-single-subst : ∀ {Γ T S} -> ntm (Γ , S) T -> ntm Γ S -> ntm Γ T
n-single-subst M N = cut (n-single N) M

napp : ∀ {Γ T S} -> ntm Γ (T ⇝ S) -> ntm Γ T -> ntm Γ S
napp (ƛ M) N = n-single-subst M N

nfst : ∀ {Γ T S} -> ntm Γ (T × S) -> ntm Γ T
nfst < M , N > = M

nsnd : ∀ {Γ T S} -> ntm Γ (T × S) -> ntm Γ S
nsnd < M , N > = N

data lf-atomic-tp (Γ : ctx) : atomic_tp -> Set where
 lf-nat' : lf-atomic-tp Γ nat
 lf-vec' : (N : ntm Γ (atom nat)) -> lf-atomic-tp Γ list

data lf-tp (Γ : ctx) : (t : tp) -> Set where
 atom : ∀ {a} (A : lf-atomic-tp Γ a) -> lf-tp Γ (atom a)
 _⇝_ : ∀ {s t} (S : lf-tp Γ s) -> (T : lf-tp (Γ , s) t) -> lf-tp Γ (s ⇝ t)
 _×_ : ∀ {s t} (S : lf-tp Γ s) -> (T : lf-tp Γ t) -> lf-tp Γ (s × t)
 unit : lf-tp Γ unit

lf-nat : ∀ {Γ} -> lf-tp Γ (atom nat)
lf-nat = atom lf-nat'
lf-vec : ∀ {Γ} (N : ntm Γ (atom nat)) -> lf-tp Γ (atom list)
lf-vec N = atom (lf-vec' N)

lf-tp-vsubst-atomic : ∀ {γ δ : ctx} (σ : vsubst γ δ) {a} (A : lf-atomic-tp γ a) -> lf-atomic-tp δ a
lf-tp-vsubst-atomic σ lf-nat' = lf-nat'
lf-tp-vsubst-atomic σ (lf-vec' N) = lf-vec' (nappSubst σ N)

lf-tp-vsubst : ∀ {γ δ : ctx} (σ : vsubst γ δ) {s} (S : lf-tp γ s) -> lf-tp δ s
lf-tp-vsubst σ (atom A) = atom (lf-tp-vsubst-atomic σ A)
lf-tp-vsubst σ (S ⇝ T) = (lf-tp-vsubst σ S) ⇝ (lf-tp-vsubst (ext σ) T)
lf-tp-vsubst σ (S × T) = (lf-tp-vsubst σ S) × (lf-tp-vsubst σ T)
lf-tp-vsubst σ unit = unit

lf-tp-subst-atomic : ∀ {γ δ : ctx} (θ : nSubst γ δ) {a} (A : lf-atomic-tp γ a) -> lf-atomic-tp δ a
lf-tp-subst-atomic θ lf-nat' = lf-nat'
lf-tp-subst-atomic θ (lf-vec' N) = lf-vec' (cut θ N)

lf-tp-subst : ∀ {γ δ : ctx} (θ : nSubst γ δ) {s} (S : lf-tp γ s) -> lf-tp δ s
lf-tp-subst θ (atom A) = atom (lf-tp-subst-atomic θ A)
lf-tp-subst θ (S ⇝ T) = (lf-tp-subst θ S) ⇝ (lf-tp-subst (n-ext θ) T)
lf-tp-subst θ (S × T) = (lf-tp-subst θ S) × (lf-tp-subst θ T)
lf-tp-subst θ unit = unit

lf-tp-wkn : ∀ {Γ : ctx} (t : tp) {s} (S : lf-tp Γ s) -> lf-tp (Γ , t) s
lf-tp-wkn t S = lf-tp-vsubst wkn S

{- Compare this style with not indexing by everything. Involves induction-recursion everywhere?
   I suspect there may be more preservation lemmas? -}
data lf-ctx : ctx -> Set where
 ⊡ : lf-ctx ⊡
 _,_ : ∀ {γ} (Γ : lf-ctx γ) -> {t : tp} -> (T : lf-tp γ t) -> lf-ctx (γ , t)

data lf-var : ∀ {γ} (Γ : lf-ctx γ) {t} (T : lf-tp γ t) (x : var γ t) -> Set where
 z : ∀ {γ Γ t T} -> lf-var {γ , t} (Γ , T) (lf-tp-wkn t T) z
 s : ∀ {γ Γ t T u U x} -> lf-var {γ} Γ {t} T x -> lf-var (Γ , U) (lf-tp-wkn u T) (s x)

mutual
 data _⊢_⇒_ {γ} (Γ : lf-ctx γ) : ∀ {t}  (r : rtm γ t) (T : lf-tp γ t) -> Set where
  v : ∀ {t T x} ->
         lf-var Γ {t} T x
      -> Γ ⊢ (v x) ⇒ T
  _·_ : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp (γ , t) s} {r n} ->
         (R : Γ ⊢ r ⇒ (T ⇝ S))
      -> (N : Γ ⊢ n ⇐ T)
      ->      Γ ⊢ (r · n) ⇒ (lf-tp-subst (n-single n) S)
  π₁ : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp γ s} {r} ->
         (R : Γ ⊢ r ⇒ (T × S))
       ->     Γ ⊢ (π₁ r) ⇒ T
  π₂ : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp γ s} {r} ->
         (R : Γ ⊢ r ⇒ (T × S))
       ->     Γ ⊢ (π₂ r) ⇒ S
 data _⊢_⇐_ {γ} (Γ : lf-ctx γ) : ∀ {t} (n : ntm γ t) (T : lf-tp γ t) -> Set where
  ƛ : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp (γ , t) s} {n} ->
         (N : (Γ , T) ⊢    n  ⇐ S)
      ->       Γ      ⊢ (ƛ n) ⇐ (T ⇝ S)
  neut : ∀ {a} {A : lf-atomic-tp γ a} {r} ->
         (R : Γ ⊢ r ⇒ (atom A))
       ->     Γ ⊢ (neut r) ⇐ (atom A)
  <_,_> : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp γ s} {m n} ->
         (M : Γ ⊢ m ⇐ T)
      -> (N : Γ ⊢ n ⇐ S)
      ->      Γ ⊢ < m , n > ⇐ (T × S)
  tt : Γ ⊢ tt ⇐ unit
  z : Γ ⊢ z ⇐ lf-nat
  s : ∀ {n}
         (N : Γ ⊢ n ⇐ lf-nat)
      ->      Γ ⊢ (s n) ⇐ lf-nat
  nil : Γ ⊢ nil ⇐ (lf-vec z)
  cons : ∀ {m n l}
         (N : Γ ⊢ n ⇐ lf-nat)
      -> (L : Γ ⊢ l ⇐ (lf-vec m))
      ->      Γ ⊢ (cons n l) ⇐ (lf-vec (s m))

subst-lemma-var : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : vsubst γ δ}
   (θ : ∀ {u} {U : lf-tp γ u} {x : var γ u} (X : lf-var Γ U x) -> lf-var Δ (lf-tp-vsubst σ U) (vsubst-app σ x))
   {t x} {T : lf-tp γ t} (X : lf-var Γ T x) -> lf-var Δ (lf-tp-vsubst σ T) (vsubst-app σ x)
subst-lemma-var θ z = θ z
subst-lemma-var {σ = σ , x} θ (s y) = subst-lemma-var {!!} {!!} -- θ should reflect the structure of σ

mutual
 rsubst-lemma : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : vsubst γ δ}
   (θ : ∀ {u} {U : lf-tp γ u} {x : var γ u} (X : lf-var Γ U x) -> lf-var Δ (lf-tp-vsubst σ U) (vsubst-app σ x))
   {t r} {T : lf-tp γ t} (R : Γ ⊢ r ⇒ T) -> Δ ⊢ (rappSubst σ r) ⇒ (lf-tp-vsubst σ T)
 rsubst-lemma θ (v y) = v (subst-lemma-var θ y)
 rsubst-lemma θ (R · N) = {!!} · nsubst-lemma θ N
 rsubst-lemma θ (π₁ R) = π₁ (rsubst-lemma θ R)
 rsubst-lemma θ (π₂ R) = π₂ (rsubst-lemma θ R)

 nsubst-lemma : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : vsubst γ δ}
   (θ : ∀ {u} {U : lf-tp γ u} {x : var γ u} (X : lf-var Γ U x) -> lf-var Δ (lf-tp-vsubst σ U) (vsubst-app σ x))
   {t n} {T : lf-tp γ t} (N : Γ ⊢ n ⇐ T) -> Δ ⊢ (nappSubst σ n) ⇐ (lf-tp-vsubst σ T)
 nsubst-lemma θ (ƛ N) = ƛ {!!}
 nsubst-lemma θ (neut R) = neut (rsubst-lemma θ R)
 nsubst-lemma θ < M , N > = < (nsubst-lemma θ M) , (nsubst-lemma θ N) >
 nsubst-lemma θ tt = tt
 nsubst-lemma θ z = z
 nsubst-lemma θ (s N) = s (nsubst-lemma θ N)
 nsubst-lemma θ nil = nil
 nsubst-lemma θ (cons N L) = cons (nsubst-lemma θ N) (nsubst-lemma θ L)
