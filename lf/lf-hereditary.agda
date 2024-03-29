module lf-hereditary where
open import Relation.Binary.PropositionalEquality hiding ([_])


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
 data spine (Γ : ctx) : (T S : tp) -> Set where
  ε : ∀ {ρ} -> spine Γ ρ ρ
  _,_ : ∀ {τ σ ρ} -> (S : spine Γ σ ρ) -> (N : ntm Γ τ)  -> spine Γ (τ ⇝ σ) ρ
  π₁ : ∀ {T S ρ} -> spine Γ T ρ -> spine Γ (T × S) ρ
  π₂ : ∀ {T S ρ} -> spine Γ S ρ -> spine Γ (T × S) ρ
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  ▹ : ∀ {T A} -> (x : var Γ T) -> (S : spine Γ T (atom A)) -> ntm Γ (atom A)
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T × S)
  tt : ntm Γ unit
  z : ntm Γ (atom nat)
  s : (N : ntm Γ (atom nat)) -> ntm Γ (atom nat)
  nil : ntm Γ (atom list)
  cons : (N : ntm Γ (atom nat)) -> (L : ntm Γ (atom list)) -> ntm Γ (atom list)

vsubst-app : ∀ {Γ Δ U} -> vsubst Γ Δ -> var Γ U -> var Δ U
vsubst-app ⊡ ()
vsubst-app (σ , x) z = x
vsubst-app (σ , x) (s y) = vsubst-app σ y

vsubst-map : ∀ {Δ Γ ψ} -> (∀ {U} -> var Δ U -> var Γ U) -> vsubst ψ Δ -> vsubst ψ Γ
vsubst-map σ1 ⊡ = ⊡
vsubst-map σ1 (σ , x) = (vsubst-map σ1 σ) , (σ1 x)

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
σ1 ∘ σ2 = vsubst-map (vsubst-app σ1) σ2

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ = (vsubst-map s σ) , z

id : ∀ {Γ} -> vsubst Γ Γ
id {⊡} = ⊡
id {Γ , T} = ext id

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = vsubst-map s id

mutual
 rappSubst : ∀ {Γ Δ S U} -> vsubst Δ Γ -> spine Δ S U -> spine Γ S U
 rappSubst σ ε = ε
 rappSubst σ (R , N) = rappSubst σ R , nappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (▹ x R) = ▹ (vsubst-app σ x) (rappSubst σ R)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt
 nappSubst σ z = z
 nappSubst σ (s N) = s (nappSubst σ N)
 nappSubst σ nil = nil
 nappSubst σ (cons N L) = cons (nappSubst σ N) (nappSubst σ L)

{-
concatSp : ∀ {ρ Γ τ σ} -> spine Γ ρ σ -> spine Γ σ τ -> spine Γ ρ τ
concatSp ε S2 = S2
concatSp (S , N) S2 = concatSp S S2 , N
concatSp (π₁ y) S2 = π₁ (concatSp y S2)
concatSp (π₂ y) S2 = π₂ (concatSp y S2)

appSp : ∀ {ρ Γ τ σ} -> spine Γ ρ (σ ⇝ τ) -> ntm Γ σ -> spine Γ ρ τ
appSp S N = concatSp S (ε , N)

π₁Sp : ∀ {ρ Γ τ σ} -> spine Γ ρ (σ × τ) -> spine Γ ρ σ
π₁Sp S = concatSp S (π₁ ε)

π₂Sp : ∀ {ρ Γ τ σ} -> spine Γ ρ (σ × τ) -> spine Γ ρ τ
π₂Sp S = concatSp S (π₂ ε)

η-expand : ∀ {T Γ U} -> var Γ U -> spine Γ U T -> ntm Γ T
η-expand {atom A} x S = ▹ x S
η-expand {T ⇝ S} x S' = ƛ (η-expand (s x) (appSp (rappSubst wkn S') (η-expand z ε)))
η-expand {T × S} x S' = < η-expand x (π₁Sp S') , η-expand x (π₂Sp S') >
η-expand {unit} x S = tt

nv : ∀ {Γ T} -> var Γ T -> ntm Γ T
nv x = η-expand x ε
-}

lcons : tp -> ctx -> ctx
lcons T ⊡ = ⊡ , T
lcons T (Γ , U) = (lcons T Γ) , U

_++_ : ctx -> ctx -> ctx
Γ1 ++ ⊡ = Γ1
Γ1 ++ (Γ2 , T) = (Γ1 ++ Γ2) , T

{-
baz : ∀ Γ Δ U -> ((Δ , U) ++ Γ) ≡ (Δ ++ lcons U Γ)
baz ⊡ Δ U = refl
baz (Γ , T) Δ U rewrite baz Γ Δ U = refl

quux : ∀ Γ -> (⊡ ++ Γ) ≡ Γ
quux ⊡ = refl
quux (Γ , T) rewrite quux Γ = refl -}

wkn* : ∀ Δ Γ -> vsubst Δ (Δ ++ Γ)
wkn* Δ ⊡ = id
wkn* Δ (Γ , T) = vsubst-map s (wkn* Δ Γ)

wkn*l : ∀ Δ Γ -> vsubst Γ (Δ ++ Γ)
wkn*l Δ ⊡ = ⊡
wkn*l Δ (Γ , T) = (vsubst-map s (wkn*l Δ Γ)) , z

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

lf-tp-wkn : ∀ {Γ : ctx} (t : tp) {s} (S : lf-tp Γ s) -> lf-tp (Γ , t) s
lf-tp-wkn t S = lf-tp-vsubst wkn S


{-lf-vsubst : ∀ {γ δ} (Γ : lf-ctx γ) (σ : vsubst γ δ) (Δ : lf-ctx δ) -> Set
lf-vsubst {γ} {δ} Γ σ Δ = ∀ {u} {U : lf-tp γ u} {x : var γ u} (X : lf-var Γ U x) -> lf-var Δ (lf-tp-vsubst σ U) (vsubst-app σ x) -}

--lf-nSubst : ∀ {γ δ} (Γ : lf-ctx γ) (σ : nSubst γ δ) (Δ : lf-ctx δ) -> Set
--lf-nSubst {γ} {δ} Γ σ Δ = ∀ {u} {U : lf-tp γ u} {x : var γ u} (X : lf-var Γ U x) -> Δ ⊢ (nSubst-app σ x) ⇐ (lf-tp-subst σ U)

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
 rfunctorality : ∀ {γ δ ψ} (σ1 : vsubst γ δ) (σ2 : vsubst ψ γ) {t} {u} (r : spine ψ t u)
   -> rappSubst σ1 (rappSubst σ2 r) ≡ rappSubst (σ1 ∘ σ2) r
 rfunctorality σ1 σ2 ε = refl
 rfunctorality σ1 σ2 (R , N) rewrite rfunctorality σ1 σ2 R | nfunctorality σ1 σ2 N = refl
 rfunctorality σ1 σ2 (π₁ R) rewrite rfunctorality σ1 σ2 R = refl
 rfunctorality σ1 σ2 (π₂ R) rewrite rfunctorality σ1 σ2 R = refl
 
 nfunctorality : ∀ {γ δ ψ} (σ1 : vsubst γ δ) (σ2 : vsubst ψ γ) {t} (n : ntm ψ t) -> nappSubst σ1 (nappSubst σ2 n) ≡ nappSubst (σ1 ∘ σ2) n
 nfunctorality σ1 σ2 (ƛ {t} R) rewrite nfunctorality (ext σ1) (ext σ2) R | ext-functorality σ1 σ2 t = refl
 nfunctorality σ1 σ2 (▹ x R) rewrite vsubst-app-map (vsubst-app σ1) σ2 x | rfunctorality σ1 σ2 R = refl
 nfunctorality σ1 σ2 < M , N > rewrite nfunctorality σ1 σ2 M | nfunctorality σ1 σ2 N = refl
 nfunctorality σ1 σ2 tt = refl
 nfunctorality σ1 σ2 z = refl
 nfunctorality σ1 σ2 (s N) rewrite nfunctorality σ1 σ2 N = refl
 nfunctorality σ1 σ2 nil = refl
 nfunctorality σ1 σ2 (cons N L) rewrite nfunctorality σ1 σ2 N | nfunctorality σ1 σ2 L = refl

lf-vsubst-ext : ∀ {γ δ Γ Δ σ} {t} {T : lf-tp γ t} (θ : lf-vsubst {γ} {δ} Γ σ Δ) -> lf-vsubst (Γ , T) (ext σ) (Δ , (lf-tp-vsubst σ T))
lf-vsubst-ext θ z = {!!}
lf-vsubst-ext θ (s y) = {!!} -}

--lf-nSubst-ext : ∀ {γ δ Γ Δ σ} {t} {T : lf-tp γ t} (θ : lf-nSubst {γ} {δ} Γ σ Δ) -> lf-nSubst (Γ , T) (n-ext σ) (Δ , (lf-tp-subst σ T))
--lf-nSubst-ext θ x = {!!}

{-mutual
 rsubst-lemma : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : vsubst γ δ}
   (θ : lf-vsubst Γ σ Δ) {t} {T : lf-tp γ t} {u} {U : lf-tp γ u} {r}
   (R : Γ ⊢ U ◂ r ⇒ T) -> Δ ⊢ (lf-tp-vsubst σ U) ◂ (rappSubst σ r) ⇒ (lf-tp-vsubst σ T)
 rsubst-lemma θ ε = ε
 rsubst-lemma θ (R , N) with rsubst-lemma θ R | nsubst-lemma θ N
 ... | w1 | w2 = {!!} , {!!}
 rsubst-lemma θ (π₁ R) = π₁ (rsubst-lemma θ R)
 rsubst-lemma θ (π₂ R) = π₂ (rsubst-lemma θ R)

 nsubst-lemma : ∀ {γ δ} {Γ : lf-ctx γ} {Δ : lf-ctx δ} {σ : vsubst γ δ}
   (θ : lf-vsubst Γ σ Δ)
   {t n} {T : lf-tp γ t} (N : Γ ⊢ n ⇐ T) -> Δ ⊢ (nappSubst σ n) ⇐ (lf-tp-vsubst σ T)
 nsubst-lemma θ (ƛ N) = ƛ (nsubst-lemma (lf-vsubst-ext θ) N)
 nsubst-lemma θ (▹ x R) = ▹ (θ x) (rsubst-lemma θ R)
 nsubst-lemma θ < M , N > = < (nsubst-lemma θ M) , (nsubst-lemma θ N) >
 nsubst-lemma θ tt = tt
 nsubst-lemma θ z = z
 nsubst-lemma θ (s N) = s (nsubst-lemma θ N)
 nsubst-lemma θ nil = nil
 nsubst-lemma θ (cons N L) = cons (nsubst-lemma θ N) (nsubst-lemma θ L) -}
{-
n-ext-functorality : ∀ {γ δ ψ} (σ1 : nSubst γ δ) (σ2 : nSubst ψ γ) (t : tp) -> ((n-ext σ1) ∘₂ (n-ext σ2)) ≡ n-ext {T = t} (σ1 ∘₂ σ2)
n-ext-functorality σ1 ⊡ t = {!!}
n-ext-functorality σ1 (σ , N) t = {!!}

nsubst-dia-distrib : ∀ {γ δ} (σ : nSubst γ δ) {t s} (N : ntm γ t) (S : spine γ t s) -> ([ σ ] (N ◆ S)) ≡ (([ σ ] N) ◆ (<< σ >> S))
nsubst-dia-distrib σ N ε = refl
nsubst-dia-distrib σ (ƛ y) (S , N') rewrite nsubst-dia-distrib σ (y [[ z := N' ]]) S = {!!}
nsubst-dia-distrib σ < M , N > (π₁ y) = nsubst-dia-distrib σ M y
nsubst-dia-distrib σ < M , N > (π₂ y) = nsubst-dia-distrib σ N y  

nsubst-app-distrib : ∀ {γ δ ψ} (σ1 : nSubst γ δ) (σ2 : nSubst ψ γ) {t} (x : var ψ t) -> [ σ1 ] (nSubst-app σ2 x) ≡ nSubst-app (σ1 ∘₂ σ2) x
nsubst-app-distrib σ1 ⊡ ()
nsubst-app-distrib σ1 (σ2 , N) z = refl
nsubst-app-distrib σ1 (σ2 , N) (s y) = nsubst-app-distrib σ1 σ2 y

mutual
 rfunctor : ∀ {γ δ ψ} (σ1 : nSubst γ δ) (σ2 : nSubst ψ γ) {t} {u} (r : spine ψ t u)
   -> << σ1 >> (<< σ2 >> r) ≡ << σ1 ∘₂ σ2 >> r
 rfunctor σ1 σ2 ε = refl
 rfunctor σ1 σ2 (S , N) rewrite rfunctor σ1 σ2 S | nfunctor σ1 σ2 N = refl
 rfunctor σ1 σ2 (π₁ y) rewrite rfunctor σ1 σ2 y = refl
 rfunctor σ1 σ2 (π₂ y) rewrite rfunctor σ1 σ2 y = refl
 
 nfunctor : ∀ {γ δ ψ} (σ1 : nSubst γ δ) (σ2 : nSubst ψ γ) {t} (n : ntm ψ t) -> [ σ1 ] ([ σ2 ] n) ≡ [ σ1 ∘₂ σ2 ] n
 nfunctor σ1 σ2 (ƛ {t} y) rewrite nfunctor (n-ext σ1) (n-ext σ2) y | n-ext-functorality σ1 σ2 t = refl
 nfunctor σ1 σ2 (▹ x S) rewrite nsubst-dia-distrib σ1 (nSubst-app σ2 x) (<< σ2 >> S) | nsubst-app-distrib σ1 σ2 x | rfunctor σ1 σ2 S = refl
 nfunctor σ1 σ2 < M , N > rewrite nfunctor σ1 σ2 M | nfunctor σ1 σ2 N = refl
 nfunctor σ1 σ2 tt = refl
 nfunctor σ1 σ2 z = refl
 nfunctor σ1 σ2 (s N) rewrite nfunctor σ1 σ2 N = refl
 nfunctor σ1 σ2 nil = refl
 nfunctor σ1 σ2 (cons N L) rewrite nfunctor σ1 σ2 N | nfunctor σ1 σ2 L = refl -}

wkv2 : ∀ {Γ} Δ {σ τ} (x : var (Γ ++ Δ) τ) -> var ((Γ , σ) ++ Δ) τ
wkv2 ⊡ x = s x
wkv2 (Γ' , τ) z = z
wkv2 (Γ' , T) (s y) = s (wkv2 Γ' y) 

thatone : ∀ {Γ} Δ {σ} -> var ((Γ , σ) ++ Δ) σ
thatone ⊡ = z
thatone (Γ' , T) = s (thatone Γ')

data eqV2 {Γ} : ∀ {τ} σ Δ -> var ((Γ , σ) ++ Δ) τ -> Set where
 same2 : ∀ {σ Δ} -> eqV2 σ Δ (thatone Δ)
 diff2 : ∀ {τ σ Δ} (x : var (Γ ++ Δ) τ) -> eqV2 σ Δ (wkv2 Δ x)

eq2 : ∀ {Γ} Δ {σ τ} (x : var ((Γ , σ) ++ Δ) τ) -> eqV2 σ Δ x
eq2 ⊡ z = same2
eq2 ⊡ (s y) = diff2 y
eq2 (Γ' , .τ) {σ} {τ} z = diff2 z
eq2 (Γ' , T) (s y) with eq2 Γ' y
eq2 (Γ , _) (s .(thatone Γ)) | same2 = same2
eq2 (Γ , _) (s .(wkv2 Γ x)) | diff2 x = diff2 (s x)

mutual
 nsub : ∀ {Γ1} Γ2 {τ σ} -> ntm ((Γ1 , σ) ++ Γ2) τ -> ntm Γ1 σ -> ntm (Γ1 ++ Γ2) τ
 nsub Γ (ƛ {T} y) M = ƛ (nsub (Γ , T) y M)
 nsub Γ (▹ x S) M with eq2 Γ x
 nsub Γ (▹ .(thatone Γ) S) M | same2 = dia (nappSubst (wkn* _ Γ) M) (rsub Γ S M)
 nsub Γ (▹ .(wkv2 Γ x) S) M | diff2 x = ▹ x (rsub Γ S M)
 nsub Γ < M , N > M' = < nsub Γ M M' , nsub Γ N M' >
 nsub Γ tt M = tt
 nsub Γ z M = z
 nsub Γ (s N) M = s (nsub Γ N M)
 nsub Γ nil M = nil
 nsub Γ (cons N L) M = cons (nsub Γ N M) (nsub Γ L M)

 rsub  : ∀ {Γ1} Γ2 {τ σ ρ} -> spine ((Γ1 , σ) ++ Γ2) τ ρ -> ntm Γ1 σ -> spine (Γ1 ++ Γ2) τ ρ
 rsub Γ ε N = ε
 rsub Γ (S , N) N' = (rsub Γ S N') , (nsub Γ N N')
 rsub Γ (π₁ y) N = π₁ (rsub Γ y N)
 rsub Γ (π₂ y) N = π₂ (rsub Γ y N)

 dia : ∀ {Γ τ σ} -> ntm Γ σ -> spine Γ σ τ -> ntm Γ τ
 dia N ε = N
 dia (ƛ y) (S , N') = dia (nsub ⊡ y N') S
 dia < M , N > (π₁ y) = dia M y
 dia < M , N > (π₂ y) = dia N y

data lf-ctx : ctx -> Set where
 ⊡ : lf-ctx ⊡
 _,_ : ∀ {γ} (Γ : lf-ctx γ) -> {t : tp} -> (T : lf-tp γ t) -> lf-ctx (γ , t)


data ctx-suffix (γ : ctx) : ctx -> Set where
 ⊡ : ctx-suffix γ ⊡
 _,_ : ∀ {δ} (Γ : ctx-suffix γ δ) -> {t : tp} -> (T : lf-tp (γ ++ δ) t) -> ctx-suffix γ (δ , t)

{-lf-ctx : ctx -> Set
lf-ctx γ = ctx-suffix ⊡ γ
-}

lf-tp-wkn2 : ∀ δ {γ} t {s} (S : lf-tp (γ ++ δ) s) -> lf-tp ((γ , t) ++ δ) s
lf-tp-wkn2 δ t (atom A) = {!!}
lf-tp-wkn2 δ t (S ⇝ T) = (lf-tp-wkn2 δ t S) ⇝ (lf-tp-wkn2 (δ , _) t T)
lf-tp-wkn2 δ t (S × T) = lf-tp-wkn2 δ t S × lf-tp-wkn2 δ t T
lf-tp-wkn2 δ t unit = unit

data lf-var : ∀ {γ} (Γ : lf-ctx γ) {t} (T : lf-tp γ t) (x : var γ t) -> Set where
 z : ∀ {γ Γ t T} -> lf-var {γ , t} (Γ , T) (lf-tp-wkn2 ⊡ t T) z
 s : ∀ {γ Γ t T u U x} -> lf-var {γ} Γ {t} T x -> lf-var (Γ , U) (lf-tp-wkn2 ⊡ u T) (s x)


_+++_ : ∀ {γ δ} (Γ : lf-ctx γ) -> (Δ : ctx-suffix γ δ) -> lf-ctx (γ ++ δ)
Γ +++ ⊡ = Γ
Γ +++ (Γ' , T) = (Γ +++ Γ') , T

lf-atp-sing-sub2 : ∀ {Γ t s} Δ -> lf-atomic-tp ((Γ , s) ++ Δ) t -> ntm Γ s -> lf-atomic-tp (Γ ++ Δ) t
lf-atp-sing-sub2 Δ lf-nat' N = lf-nat'
lf-atp-sing-sub2 Δ (lf-vec' N) N' = lf-vec' (nsub Δ N N')

lf-tp-sing-sub2 : ∀ {Γ t σ} Δ -> lf-tp ((Γ , σ) ++ Δ) t -> ntm Γ σ -> lf-tp (Γ ++ Δ) t
lf-tp-sing-sub2 Δ (atom A) N = atom (lf-atp-sing-sub2 Δ A N)
lf-tp-sing-sub2 Δ (S ⇝ T) N = (lf-tp-sing-sub2 Δ S N) ⇝ (lf-tp-sing-sub2 (Δ , _) T N)
lf-tp-sing-sub2 Δ (S × T) N = (lf-tp-sing-sub2 Δ S N) × (lf-tp-sing-sub2 Δ T N)
lf-tp-sing-sub2 Δ unit N = unit

mutual
 data _⊢_◂_⇒_ {γ} (Γ : lf-ctx γ) {u} (U : lf-tp γ u) : ∀ {t}  (r : spine γ t u) (T : lf-tp γ t) -> Set where
  ε : Γ ⊢ U ◂ ε ⇒ U
  _,_ : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp (γ , t) s} {r n} ->
         (R : Γ ⊢ U ◂ r ⇒ (lf-tp-sing-sub2 ⊡ S n))
      -> (N : Γ ⊢ n ⇐ T)
      ->      Γ ⊢ U ◂ (r , n) ⇒ (T ⇝ S)
  π₁ : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp γ s} {r} ->
         (R : Γ ⊢ U ◂ r ⇒ T)
       ->     Γ ⊢ U ◂ (π₁ r) ⇒ (T × S)
  π₂ : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp γ s} {r} ->
         (R : Γ ⊢ U ◂ r ⇒ S)
       ->     Γ ⊢ U ◂ (π₂ r) ⇒ (T × S)
 data _⊢_⇐_ {γ} (Γ : lf-ctx γ) : ∀ {t} (n : ntm γ t) (T : lf-tp γ t) -> Set where
  ƛ : ∀ {t} {T : lf-tp γ t} {s} {S : lf-tp (γ , t) s} {n} ->
         (N : (Γ , T) ⊢    n  ⇐ S)
      ->       Γ      ⊢ (ƛ n) ⇐ (T ⇝ S)
  ▹ : ∀ {t} {a} {A : lf-atomic-tp γ a} {r} {x} {T} ->
         (X : lf-var Γ {t} T x)
         (R : Γ ⊢ (atom A) ◂ r ⇒ T)
       ->     Γ ⊢ (▹ x r) ⇐ (atom A)
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


suffix-wkn : ∀ δ {γ} s (Δ : ctx-suffix γ δ) -> ctx-suffix (γ , s) δ
suffix-wkn ⊡ S ⊡ = ⊡
suffix-wkn (δ , t) S (Γ , T) = (suffix-wkn δ S Γ) , lf-tp-wkn2 δ S T

lf-wkv : ∀ {γ} {Γ : lf-ctx γ} {δ} (Δ : ctx-suffix γ δ) {s} {S : lf-tp γ s} {t} {T : lf-tp (γ ++ δ) t} {x} (X : lf-var (Γ +++ Δ) T x)
 -> lf-var ((Γ , S) +++ (suffix-wkn δ s Δ)) (lf-tp-wkn2 δ s T) (wkv2 δ x)
lf-wkv ⊡ x = s x
lf-wkv (Γ' , τ) z = {!!} -- z
lf-wkv (Γ' , T) (s y) = {!!} --s (lf-wkv Γ' y) 

lf-thatone : ∀ {γ} {Γ : lf-ctx γ} {s} {δ} (Δ : ctx-suffix (γ , s) δ) {S : lf-tp γ s} -> lf-var ((Γ , S) +++ Δ) {!!} (thatone δ)
lf-thatone ⊡ = z
lf-thatone (Γ' , T) = s (lf-thatone Γ')

data lf-eqV {γ} {Γ : lf-ctx γ} : ∀ {s} (S : lf-tp γ s) {δ} (Δ : ctx-suffix (γ , s) δ) {t} {T : lf-tp ((γ , s) ++ δ) t}
 {x : var ((γ , s) ++ δ) t} -> lf-var ((Γ , S) +++ Δ) T x -> Set where
 same : ∀ {σ Δ} -> lf-eqV σ Δ (lf-thatone Δ)
 before : ∀ {σ Δ T} {x} (X : lf-var Γ T x) -> lf-eqV σ Δ (lf-wkv Δ X)

suffix-sub : ∀ {δ γ t} (N : ntm γ t) -> (Δ : ctx-suffix (γ , t) δ) -> ctx-suffix γ δ
suffix-sub N ⊡ = ⊡
suffix-sub {δ , t} N (Γ , T) = (suffix-sub N Γ) , (lf-tp-sing-sub2 δ T N)

mutual
 nsublem2 : ∀ {γ δ} {Γ : lf-ctx γ} {s} (Δ : ctx-suffix (γ , s) δ) {t} {S : lf-tp γ s} {T : lf-tp ((γ , s) ++ δ) t} {n m} ->
     ((Γ , S) +++ Δ) ⊢ n ⇐ T
  -> Γ ⊢ m ⇐ S
  -> (Γ +++ (suffix-sub m Δ)) ⊢ nsub δ n m ⇐ (lf-tp-sing-sub2 δ T m)
 nsublem2 Δ (ƛ {t} {T} N) M = ƛ (nsublem2 (Δ , T) N M)
 nsublem2 {δ = δ} Δ {n = ▹ x r} (▹ X R) M with eq2 δ x
 nsublem2 {δ = δ} Δ {n = ▹ .(thatone δ) r} (▹ X R) M | same2 = {!!}
 nsublem2 {δ = δ} Δ {n = ▹ .(wkv2 δ x) r} (▹ X R) M | diff2 x = ▹ {!!} {!!}
 nsublem2 Δ < M , N > M' = < nsublem2 Δ M M' , nsublem2 Δ N M' >
 nsublem2 Δ tt M = tt
 nsublem2 Δ z M = z 
nsublem2 Δ (s N) M = s (nsublem2 Δ N M)
 nsublem2 Δ nil M = nil
 nsublem2 Δ (cons N L) M = cons (nsublem2 Δ N M) (nsublem2 Δ L M)

 rsublem2 : ∀ {γ δ} {Γ : lf-ctx γ} {s} (Δ : ctx-suffix (γ , s) δ) {t} {S : lf-tp γ s} {T : lf-tp ((γ , s) ++ δ) t}
     {u} {U : lf-tp ((γ , s) ++ δ) u} {r m} ->
     ((Γ , S) +++ Δ) ⊢ U ◂ r ⇒ T
  -> Γ ⊢ m ⇐ S
  -> (Γ +++ (suffix-sub m Δ)) ⊢ (lf-tp-sing-sub2 δ U m) ◂ (rsub δ r m) ⇒ (lf-tp-sing-sub2 δ T m)
 rsublem2 Δ ε M = ε
 rsublem2 Δ (R , N) M = {!!} , (nsublem2 Δ N M)
 rsublem2 Δ (π₁ R) M = π₁ (rsublem2 Δ R M)
 rsublem2 Δ (π₂ R) M = π₂ (rsublem2 Δ R M)


 