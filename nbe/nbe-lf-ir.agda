module nbe-lf-ir where
open import eq

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

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

vsubst : ctx -> ctx -> Set
vsubst Γ Δ = ∀ {u} -> var Γ u -> var Δ u

mutual 
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)

import cc
open module cc1 = cc ctx hiding (tp)

sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = ntm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = s

_,,_ : ∀ {Γ Δ T} -> vsubst Γ Δ -> var Δ T -> vsubst (Γ , T) Δ
_,,_ σ x z = x
_,,_ σ x (s y) = σ y

ext : ∀ {T Γ Δ} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ = (s ∘ σ) ,, z

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (σ y)
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

unEmbed : ∀ {Γ Δ} -> subst Γ Δ -> nSubst Γ Δ
unEmbed θ x = reify (θ x)

postulate
 lf-atomic-tp : (Γ : ctx) -> Set
 ≪_≫a : ∀ {γ : ctx} -> lf-atomic-tp γ -> atomic_tp
 lf-tp-vsubst-atomic : ∀ {γ δ : ctx} (σ : vsubst γ δ) (A : lf-atomic-tp γ) -> lf-atomic-tp δ
 lf-tp-subst-atomic : ∀ {γ δ : ctx} (θ : nSubst γ δ) (A : lf-atomic-tp γ) -> lf-atomic-tp δ

mutual
 data lf-tp (Γ : ctx) : Set where
  atom : ∀ (A : lf-atomic-tp Γ) -> lf-tp Γ
  _⇝_ : ∀ (S : lf-tp Γ) -> (T : lf-tp (Γ , ≪ S ≫t)) -> lf-tp Γ
 ≪_≫t : ∀ {Γ : ctx} -> lf-tp Γ -> tp
 ≪ atom A ≫t = atom ≪ A ≫a
 ≪ S ⇝ T ≫t = ≪ S ≫t ⇝ ≪ T ≫t

--≪_-subst-_≫t : ∀ {γ δ} (σ : vsubst γ δ) (S : lf-tp γ) -> ≪ lf-tp-vsubst σ S ≫t ≡ ≪ S ≫t
--≪ σ -subst- S ≫t = ?
-- Maybe if I generalize lf-tp-vsubst to a general traversal, I can prove this lemma first?

lf-tp-vsubst' : ∀ {γ δ : ctx} (σ : vsubst γ δ) (S : lf-tp γ) -> Σ {lf-tp δ} (λ T -> ≪ T ≫t ≡ ≪ S ≫t) 
lf-tp-vsubst' σ (atom A) = (atom (lf-tp-vsubst-atomic σ A)) , {!!}
lf-tp-vsubst' {γ} {δ} σ (S ⇝ T) with lf-tp-vsubst' σ S | lf-tp-vsubst' (ext σ) T
... | S' , eq1 | T' , eq2  = (S' ⇝ ≡-subst (λ x → lf-tp (δ , x)) (≡-sym eq1) T') , {!!}

lf-tp-vsubst : ∀ {γ δ : ctx} (σ : vsubst γ δ) (S : lf-tp γ) -> lf-tp δ
lf-tp-vsubst σ (atom A) = atom (lf-tp-vsubst-atomic σ A)
lf-tp-vsubst σ (S ⇝ T) = (lf-tp-vsubst σ S) ⇝ (lf-tp-vsubst (ext σ) {!!})

≪_-subst-_≫t : ∀ {γ δ} (σ : vsubst γ δ) (S : lf-tp γ) -> ≪ lf-tp-vsubst σ S ≫t ≡ ≪ S ≫t
≪ σ -subst- S ≫t = {!!}

lf-tp-vsubst-id :  ∀ {γ : ctx} (S : lf-tp γ) -> lf-tp-vsubst id S ≡ S
lf-tp-vsubst-id (atom A) = {!!}
lf-tp-vsubst-id (S ⇝ T) = {!!}

lf-tp-subst : ∀ {γ δ : ctx} (θ : nSubst γ δ) (S : lf-tp γ) -> lf-tp δ
lf-tp-subst θ (atom A) = atom (lf-tp-subst-atomic θ A)
lf-tp-subst θ (S ⇝ T) = (lf-tp-subst θ S) ⇝ {!!} -- (lf-tp-subst θ S) ⇝ (lf-tp-subst (n-ext θ) T)

lf-tp-subst-≪≫ : ∀ {γ δ : ctx} (θ : nSubst γ δ) (S : lf-tp γ) -> ≪ lf-tp-subst θ S ≫t ≡ ≪ S ≫t
lf-tp-subst-≪≫ θ S = {!!}

lf-tp-wkn : ∀ {Γ : ctx} (t : tp) (S : lf-tp Γ) -> lf-tp (Γ , t)
lf-tp-wkn t S = lf-tp-vsubst wkn S

{- Compare this style with not indexing by everything. Involves induction-recursion everywhere?
   I suspect there may be more preservation lemmas? -}
mutual
 data lf-ctx : Set where
  ⊡ : lf-ctx
  _,_ : ∀ (Γ : lf-ctx) (T : lf-tp (≪ Γ ≫c)) -> lf-ctx
 ≪_≫c : lf-ctx -> ctx
 ≪ ⊡ ≫c = ⊡
 ≪ Γ , T ≫c = ≪ Γ ≫c , ≪ T ≫t


data lf-var : ∀ (Γ : lf-ctx) (T : lf-tp (≪ Γ ≫c)) -> Set where
 z : ∀ {Γ T} -> lf-var (Γ , T) (lf-tp-wkn ≪ T ≫t T)
 s : ∀ {Γ T U} -> lf-var Γ T  -> lf-var (Γ , U) (lf-tp-wkn ≪ U ≫t T)

≪_≫v : ∀ {Γ} {T} -> lf-var Γ T -> var ≪ Γ ≫c ≪ T ≫t
≪_≫v {.(Γ , T)} {.(lf-tp-vsubst wkn T)} (z {Γ} {T}) = ≡-subst (λ x → var ≪ Γ , T ≫c x) (≡-sym ≪ wkn -subst- _ ≫t) z
≪_≫v {.(Γ , U)} {.(lf-tp-vsubst wkn T)} (s {Γ} {T} {U} y) = ≡-subst (λ x → var ≪ Γ , U ≫c x) (≡-sym ≪ wkn -subst- T ≫t) (s (≪_≫v {Γ} {T} y))

mutual
 data _⊢⇒_ Γ : ∀ (T : lf-tp ≪ Γ ≫c) -> Set where
  v : ∀ {T} -> lf-var Γ T -> Γ ⊢⇒ T
  _·_ : ∀ {T S} -> (R : Γ ⊢⇒ (T ⇝ S)) -> (N : Γ ⊢⇐ T)
                -> Γ ⊢⇒ (lf-tp-subst (n-single ≪ N ≫n) S)
 data _⊢⇐_ Γ : ∀ (T : lf-tp ≪ Γ ≫c) -> Set where
  ƛ : ∀ {T S}-> (N : (Γ , T) ⊢⇐ S) -> Γ ⊢⇐ (T ⇝ S)
  neut : ∀ {A} -> (R : Γ ⊢⇒ (atom A)) -> Γ ⊢⇐ (atom A)

 ≪_≫n : ∀ {Γ T} (N : Γ ⊢⇐ T) -> ntm ≪ Γ ≫c ≪ T ≫t
 ≪ ƛ N ≫n = ƛ ≪ N ≫n
 ≪ neut R ≫n = neut ≪ R ≫r
 ≪_≫r : ∀ {Γ T} (R : Γ ⊢⇒ T) -> rtm ≪ Γ ≫c ≪ T ≫t
 ≪ v y ≫r = v ≪ y ≫v
 ≪_≫r {Γ} (_·_ {T} R N) = ≡-subst (λ x → rtm ≪ Γ ≫c (≪ T ≫t ⇝ x)) (≡-sym (lf-tp-subst-≪≫ (n-single ≪ N ≫n) _)) ≪ R ≫r · ≪ N ≫n

mutual
 data lf-vsubst (Δ : lf-ctx) : ∀ (Γ : lf-ctx) -> Set where
  ⊡ : lf-vsubst Δ ⊡
  _,_ : ∀ {Γ : lf-ctx} -> (σ : lf-vsubst Δ Γ) -> ∀ {U}-> lf-var Δ (lf-tp-vsubst ≪ σ ≫s U) -> lf-vsubst Δ (Γ , U)
 ≪_≫s : ∀ {Δ Γ} -> lf-vsubst Δ Γ -> vsubst ≪ Γ ≫c ≪ Δ ≫c
 ≪ σ ≫s = {!!}

{-vsubst' : ctx -> ctx -> Set
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
 rsubst-lemma θ (R · N) with (rsubst-lemma θ R) | (nsubst-lemma θ N)
 ... | w1 | w2 = {!!}

 nsubst-lemma : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : vsubst γ δ}
   (θ : lf-vsubst Γ σ Δ)
   {t n} {T : lf-tp γ t} (N : Γ ⊢ n ⇐ T) -> Δ ⊢ (nappSubst σ n) ⇐ (lf-tp-vsubst σ T)
 nsubst-lemma θ (ƛ N) = ƛ (nsubst-lemma (lf-vsubst-ext θ) N)
 nsubst-lemma θ (neut R) = neut (rsubst-lemma θ R)

lift : ∀ {Γ Δ} -> vsubst Γ Δ -> nSubst Γ Δ
lift σ x = η-exp (v (vsubst-app σ x)) -}

data conn {γ} : lf-tp γ -> tp -> Set where
 atom : ∀ A -> conn (atom A) (atom ≪ A ≫a)
 _⇝_ : ∀ {S s T t} -> conn S s -> conn T t -> conn (S ⇝ T) (t ⇝ s)

mutual
 lf-sem : ∀ Γ (T : lf-tp ≪ Γ ≫c) -> Set
 lf-sem Γ (atom A') = Γ ⊢⇐ atom A'
 lf-sem Γ (T ⇝ S) = {Γ' : _} (θ : lf-vsubst Γ' Γ) → (s : lf-sem Γ' (lf-tp-vsubst ≪ θ ≫s T)) → lf-sem Γ' {!!}

 ≪_≫sem : ∀ {Γ T} -> lf-sem Γ T -> sem ≪ Γ ≫c ≪ T ≫t
 ≪_≫sem {Γ} {atom A} M = ≪ M ≫n
 ≪_≫sem {Γ} {S ⇝ T} M = λ Γ' σ x → {!!} {- !!! Crap contravariance! -}


-- lf-sem Γ (atom A) = Γ ⊢⇐ atom A
-- lf-sem Γ (S ⇝ T) = ∀ {Γ'} (θ : lf-vsubst Γ' Γ) ->
--  (s : lf-sem Γ' (lf-tp-vsubst ≪ θ ≫s S)) -> lf-sem Γ' (lf-tp-subst (nExtend nId (reify {!!})) (lf-tp-vsubst (ext ≪ θ ≫s) T))
 
 --≪_≫sem : ∀ {Γ T} -> lf-sem Γ T -> sem ≪ Γ ≫c ≪ T ≫t
-- ≪ M ≫sem = {!!}

{- lf-wkn : ∀ {γ} {Γ : lf-ctx γ} {s} {S : lf-tp γ s} -> lf-vsubst Γ wkn (Γ , S)
lf-wkn = {!!}

mutual 
 lf-reflect : ∀ {γ t} {T : lf-tp γ t} {Γ : lf-ctx γ} {r : rtm γ t} -> (Γ ⊢ r ⇒ T) -> lf-sem Γ T (reflect r)
 lf-reflect {T = atom A} R = neut R
 lf-reflect {T = S ⇝ T} R = λ θ x → lf-reflect ((rsubst-lemma θ R) · lf-reify x)

 lf-reify : ∀ {γ t} {T : lf-tp γ t} {Γ : lf-ctx γ} {n : sem γ t} -> lf-sem Γ T n -> (Γ ⊢ (reify n) ⇐ T)
 lf-reify {T = atom A} N = N
 lf-reify {T = S ⇝ T} N with lf-reify (N lf-wkn (lf-reflect (v z)))
 ... | w = ƛ {!!} -- Okay I'm gonna have to write a solver for these problems or something

lf-subst : ∀ {γ δ} (Γ : lf-ctx γ) (Δ : lf-ctx δ) (θ : subst γ δ) -> Set
lf-subst {γ} Γ Δ θ = ∀ {t} {T : lf-tp γ t} {x : var γ t} -> lf-var Γ T x -> lf-sem Δ (lf-tp-subst (unEmbed θ) T) (θ x)

lf-id : ∀ {γ} {Γ : lf-ctx γ} -> lf-vsubst Γ id Γ
lf-id {γ} {Γ} {u} {U} x rewrite lf-tp-vsubst-id U = {!!}

mutual
 lf-srSubst : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : subst γ δ} {t r} {T : lf-tp γ t}
    -> (Γ ⊢ r ⇒ T) -> lf-subst Γ Δ σ -> lf-sem Δ (lf-tp-subst (unEmbed σ) T) (srSubst σ r)
 lf-srSubst (v y) θ = θ y
 lf-srSubst {σ = σ} (_·_ {T = T} R N) θ with lf-srSubst R θ lf-id | lf-sSubst N θ
 ... | w1 | w2 = {!!}

 lf-sSubst : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : subst γ δ} {t n} {T : lf-tp γ t}
    -> (Γ ⊢ n ⇐ T) -> lf-subst Γ Δ σ -> lf-sem Δ (lf-tp-subst (unEmbed σ) T) (sSubst σ n)
 lf-sSubst {γ} {δ} {Γ} {Δ} {σ} {t ⇝ s1} {ƛ n} {T ⇝ S} (ƛ N) θ = λ θ' x → {!!}
 lf-sSubst (neut R) θ = lf-srSubst R θ -}

 -- Maybe I'll have an easier time if I Σ-up the T's in the derivations, and prove after the
 -- fact that they're equal?