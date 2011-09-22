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

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

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
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)

sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = ntm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S

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
ext σ = (vsubst-map s σ) , z

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (vsubst-app σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = nappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = neut N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z))))

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

mutual
 srSubst : ∀ {Γ Δ T} -> subst Γ Δ -> rtm Γ T -> sem Δ T
 srSubst θ (v y) = θ y
 srSubst θ (R · N) = srSubst θ R _ id (sSubst θ N)

 sSubst : ∀ {Γ Δ T} -> subst Γ Δ -> ntm Γ T -> sem Δ T
 sSubst θ (ƛ M) = λ Δ σ s → sSubst (extend (λ x → appSubst _ σ (θ x)) s) M
 sSubst θ (neut y) = srSubst θ y

η-exp : ∀ {Γ S} -> rtm Γ S -> ntm Γ S
η-exp r = reify (reflect r)

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

postulate
 lf-atomic-tp : (Γ : ctx) -> atomic_tp -> Set
 lf-tp-vsubst-atomic : ∀ {γ δ : ctx} (σ : vsubst γ δ) {a} (A : lf-atomic-tp γ a) -> lf-atomic-tp δ a
 lf-tp-subst-atomic : ∀ {γ δ : ctx} (θ : nSubst γ δ) {a} (A : lf-atomic-tp γ a) -> lf-atomic-tp δ a

data lf-tp (Γ : ctx) : (t : tp) -> Set where
 atom : ∀ {a} (A : lf-atomic-tp Γ a) -> lf-tp Γ (atom a)
 _⇝_ : ∀ {s t} (S : lf-tp Γ s) -> (T : lf-tp (Γ , s) t) -> lf-tp Γ (s ⇝ t)

lf-tp-vsubst : ∀ {γ δ : ctx} (σ : vsubst γ δ) {s} (S : lf-tp γ s) -> lf-tp δ s
lf-tp-vsubst σ (atom A) = atom (lf-tp-vsubst-atomic σ A)
lf-tp-vsubst σ (S ⇝ T) = (lf-tp-vsubst σ S) ⇝ (lf-tp-vsubst (ext σ) T)

lf-tp-subst : ∀ {γ δ : ctx} (θ : nSubst γ δ) {s} (S : lf-tp γ s) -> lf-tp δ s
lf-tp-subst θ (atom A) = atom (lf-tp-subst-atomic θ A)
lf-tp-subst θ (S ⇝ T) = (lf-tp-subst θ S) ⇝ (lf-tp-subst (n-ext θ) T)

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
 data _⊢_⇐_ {γ} (Γ : lf-ctx γ) : ∀ {t} (n : ntm γ t) (T : lf-tp γ t) -> Set where
  ƛ : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp (γ , t) s} {n} ->
         (N : (Γ , T) ⊢    n  ⇐ S)
      ->       Γ      ⊢ (ƛ n) ⇐ (T ⇝ S)
  neut : ∀ {a} {A : lf-atomic-tp γ a} {r} ->
         (R : Γ ⊢ r ⇒ (atom A))
       ->     Γ ⊢ (neut r) ⇐ (atom A)

lf-vsubst : ∀ {γ δ} (Γ : lf-ctx γ) (σ : vsubst γ δ) (Δ : lf-ctx δ) -> Set
lf-vsubst {γ} {δ} Γ σ Δ = ∀ {u} {U : lf-tp γ u} {x : var γ u} (X : lf-var Γ U x) -> lf-var Δ (lf-tp-vsubst σ U) (vsubst-app σ x)

data _≡_ {A : Set} (x : A) : (y : A) -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

vsubst' : ctx -> ctx -> Set
vsubst' γ δ = ∀ {U} -> var γ U -> var δ U

_∘₁_ : ∀ {A B C} (f : vsubst' B C) (g : vsubst' A B) -> (vsubst' A C)
(f ∘₁ g) x = f (g x)

vsubst-map-functorality : ∀ {γ δ ψ φ} (σ1 : vsubst' γ δ) (σ2 : vsubst' ψ γ) (σ3 : vsubst φ ψ)
  -> vsubst-map σ1 (vsubst-map σ2 σ3) ≡ vsubst-map (λ x -> σ1 (σ2 x)) σ3
vsubst-map-functorality σ1 σ2 ⊡ = refl
vsubst-map-functorality σ1 σ2 (σ , x) rewrite vsubst-map-functorality σ1 σ2 σ = refl

vsubst-app-map : ∀ {γ δ ψ} (σ1 : vsubst' γ δ) (σ2 : vsubst ψ γ) {t} (x : var ψ t)
  -> vsubst-app (vsubst-map σ1 σ2) x ≡ σ1 (vsubst-app σ2 x)
vsubst-app-map σ1 ⊡ ()
vsubst-app-map σ1 (σ , x) z = refl
vsubst-app-map σ1 (σ , x) (s y) rewrite vsubst-app-map σ1 σ y = refl

vsubst-map-extensional : ∀ {γ δ ψ} {σ1 σ2 : vsubst' γ δ} (eq : ∀ {u} (x : var γ u) -> σ1 x ≡ σ2 x) (σ3 : vsubst ψ γ)
  -> vsubst-map σ1 σ3 ≡ vsubst-map σ2 σ3
vsubst-map-extensional eq ⊡ = refl
vsubst-map-extensional eq (σ , x) rewrite vsubst-map-extensional eq σ | eq x = refl

ext-functorality : ∀ {γ δ ψ} (σ1 : vsubst γ δ) (σ2 : vsubst ψ γ) (t : tp) -> ((ext σ1) ∘ (ext σ2)) ≡ ext {T = t} (σ1 ∘ σ2)
ext-functorality σ1 ⊡ t = refl
ext-functorality σ1 (σ , x) t rewrite ext-functorality σ1 σ t | vsubst-app-map (s {S = t}) σ1 x 
     | vsubst-map-functorality (vsubst-app (ext {T = t} σ1)) s σ
     | vsubst-map-functorality (s {S = t}) (vsubst-app σ1) σ
     | vsubst-map-extensional (vsubst-app-map (s {S = t}) σ1) σ = refl

mutual
 rfunctorality : ∀ {γ δ ψ} (σ1 : vsubst γ δ) (σ2 : vsubst ψ γ) {t} (r : rtm ψ t) -> rappSubst σ1 (rappSubst σ2 r) ≡ rappSubst (σ1 ∘ σ2) r
 rfunctorality σ1 σ2 (v y) rewrite vsubst-app-map (vsubst-app σ1) σ2 y = refl
 rfunctorality σ1 σ2 (R · N) rewrite rfunctorality σ1 σ2 R | nfunctorality σ1 σ2 N = refl
 
 nfunctorality : ∀ {γ δ ψ} (σ1 : vsubst γ δ) (σ2 : vsubst ψ γ) {t} (n : ntm ψ t) -> nappSubst σ1 (nappSubst σ2 n) ≡ nappSubst (σ1 ∘ σ2) n
 nfunctorality σ1 σ2 (ƛ {t} R) rewrite nfunctorality (ext σ1) (ext σ2) R | ext-functorality σ1 σ2 t = refl
 nfunctorality σ1 σ2 (neut R) rewrite rfunctorality σ1 σ2 R = refl

lf-vsubst-ext : ∀ {γ δ Γ Δ σ} {t} {T : lf-tp γ t} (θ : lf-vsubst {γ} {δ} Γ σ Δ) -> lf-vsubst (Γ , T) (ext σ) (Δ , (lf-tp-vsubst σ T))
lf-vsubst-ext θ z = {!!}
lf-vsubst-ext θ (s y) = {!!}

lf-vsubst-comma : ∀ {γ δ Γ Δ σ} {t} {T : lf-tp γ t} (θ : lf-vsubst {γ} {δ} Γ σ Δ) -> {m : var δ t} -> lf-var Δ (lf-tp-vsubst σ T) m -> lf-vsubst (Γ , T) (σ , m) Δ
lf-vsubst-comma θ M = {!!}

mutual
 rsubst-lemma : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : vsubst γ δ}
   (θ : lf-vsubst Γ σ Δ)
   {t r} {T : lf-tp γ t} (R : Γ ⊢ r ⇒ T) -> Δ ⊢ (rappSubst σ r) ⇒ (lf-tp-vsubst σ T)
 rsubst-lemma θ (v y) = v (θ y)
 rsubst-lemma θ (R · N) with rsubst-lemma θ R | nsubst-lemma θ N
 ... | w1 | w2 = {!!}

 nsubst-lemma : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : vsubst γ δ}
   (θ : lf-vsubst Γ σ Δ)
   {t n} {T : lf-tp γ t} (N : Γ ⊢ n ⇐ T) -> Δ ⊢ (nappSubst σ n) ⇐ (lf-tp-vsubst σ T)
 nsubst-lemma θ (ƛ N) = ƛ (nsubst-lemma (lf-vsubst-ext θ) N)
 nsubst-lemma θ (neut R) = neut (rsubst-lemma θ R)

lift : ∀ {Γ Δ} -> vsubst Γ Δ -> nSubst Γ Δ
lift σ x = η-exp (v (vsubst-app σ x))

lf-sem2 : ∀ {γ} (Γ : lf-ctx γ) {t} (T : lf-tp γ t) (n : sem γ t) -> Set
lf-sem2 Γ (atom A) n = Γ ⊢ n ⇐ atom A
lf-sem2 Γ (S ⇝ T) n = {γ' : _} {Γ' : lf-ctx γ'} {σ : vsubst _ γ'} (θ : lf-vsubst Γ σ Γ') ->
  {m : sem γ' _} → lf-sem2 Γ' (lf-tp-vsubst σ S) m -> lf-sem2 Γ' (lf-tp-subst  (nExtend nId (reify m)) (lf-tp-vsubst (ext σ) T)) (n γ' σ m)

lf-wkn : ∀ {γ} {Γ : lf-ctx γ} {s} {S : lf-tp γ s} -> lf-vsubst Γ wkn (Γ , S)
lf-wkn = {!!}

mutual 
 lf-reflect : ∀ {γ t} {T : lf-tp γ t} {Γ : lf-ctx γ} {r : rtm γ t} -> (Γ ⊢ r ⇒ T) -> lf-sem2 Γ T (reflect r)
 lf-reflect {T = atom A} R = neut R
 lf-reflect {T = S ⇝ T} R = λ θ x → lf-reflect ((rsubst-lemma θ R) · lf-reify x)

 lf-reify : ∀ {γ t} {T : lf-tp γ t} {Γ : lf-ctx γ} {n : sem γ t} -> lf-sem2 Γ T n -> (Γ ⊢ (reify n) ⇐ T)
 lf-reify {T = atom A} N = N
 lf-reify {T = S ⇝ T} N with lf-reify (N lf-wkn (lf-reflect (v z)))
 ... | w = ƛ {!!}

