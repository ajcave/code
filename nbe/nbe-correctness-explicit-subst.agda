module nbe-correctness-explicit-subst where

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

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

postulate
 funext : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g
 funext-imp : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> _≡_ { {x : A} -> B x} (λ {x} -> f x) (λ {x} -> g x)

cong-app1 : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> f ≡ g -> (x : A) -> f x ≡ g x
cong-app1 refl x = refl

cong-app : ∀ {A B : Set} {f g : A -> B} -> f ≡ g -> {x y : A} -> x ≡ y -> f x ≡ g y
cong-app refl refl = refl 

cong : ∀ {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong1/2 : ∀ {A B C : Set} (f : A -> B -> C) -> {x y : A} -> x ≡ y -> (z : B) -> f x z ≡ f y z
cong1/2 f refl z = refl 

cong2 : ∀ {A B C : Set} (f : A -> B -> C) -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> f x z ≡ f y w
cong2 f refl refl = refl

eq-ind : ∀ {A} (P : A -> Set) -> {x y : A} -> x ≡ y -> P x -> P y
eq-ind P refl t = t 

eq-ind2 : ∀ {A B} (P : A -> B -> Set) -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> P x z -> P y w
eq-ind2 P refl refl t = t

eq-sub1 : ∀ {A C} (P : A -> C) {t} -> {x y : A} -> x ≡ y -> P y ≡ t -> P x ≡ t
eq-sub1 P refl p = p 

eq-sub2 : ∀ {A B C} (P : A -> B -> C) {t} -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> P y w ≡ t -> P x z ≡ t
eq-sub2 P refl refl p = p

trans : ∀ {A} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

sym : ∀ {A} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

record Unit : Set where
 constructor tt

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
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)


sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = ntm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

_∘₁_ : ∀ {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘₁ g) x = f (g x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)

var-dom-prop : ∀ {Γ T} (P : ∀ {U : tp} (x : var (Γ , T) U) -> Set) -> (∀ {U} (x : var Γ U) -> P (s x)) -> P z -> ∀ {U} (x : var (Γ , T) U) -> P x
var-dom-prop P p q z = q
var-dom-prop P p q (s y) = p y

var-dom-eq' : ∀ {A : tp -> Set} {Γ T} (f g : ∀ {U} (x : var (Γ , T) U) -> A U) -> (∀ {U} (x : var Γ U) -> f (s x) ≡ g (s x)) -> f z ≡ g z -> ∀ {U} (x : var (Γ , T) U) -> f x ≡ g x
var-dom-eq' f g p q z = q
var-dom-eq' f g p q (s y) = p y

var-dom-eq : ∀ {A : tp -> Set} {Γ T} {f g : ∀ {U} (x : var (Γ , T) U) -> A U} -> (∀ {U} (x : var Γ U) -> f (s x) ≡ g (s x)) -> f z ≡ g z -> _≡_ { ∀ {U} -> var (Γ , T) U -> A U } f g
var-dom-eq {f = f} {g = g} p q = funext-imp (λ U -> funext (λ x -> var-dom-eq' f g p q x))

ext-funct : ∀ {Γ1 Γ2 Γ3 U S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (x : var (Γ1 , U) S) -> ((ext σ1) ∘ (ext σ2)) x ≡ ext (σ1 ∘ σ2) x
ext-funct σ1 σ2 z = refl
ext-funct σ1 σ2 (s y) = refl

mutual
 rappSubst-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : rtm Γ1 S)
  -> rappSubst σ1 (rappSubst σ2 R) ≡ rappSubst (σ1 ∘ σ2) R
 rappSubst-funct σ1 σ2 (v y) = refl
 rappSubst-funct σ1 σ2 (R · N) = cong2 _·_ (rappSubst-funct σ1 σ2 R) (nappSubst-funct σ1 σ2 N)
 nappSubst-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (N : ntm Γ1 S)
  -> nappSubst σ1 (nappSubst σ2 N) ≡ nappSubst (σ1 ∘ σ2) N
 nappSubst-funct σ1 σ2 (ƛ N) = cong ƛ (trans (nappSubst-funct (ext σ1) (ext σ2) N) (cong (λ (α : vsubst _ _) → nappSubst α N) (funext-imp (λ U → funext (λ x' → ext-funct σ1 σ2 x')))))
 nappSubst-funct σ1 σ2 (neut R) = cong neut (rappSubst-funct σ1 σ2 R)

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> ext id x ≡ x
ext-id z = refl
ext-id (s y) = refl

mutual
 rappSubst-id : ∀ {Γ S} (R : rtm Γ S) -> rappSubst id R ≡ R
 rappSubst-id (v y) = refl
 rappSubst-id (R · N) = cong2 _·_ (rappSubst-id R) (nappSubst-id N)
 nappSubst-id : ∀ {Γ S} (N : ntm Γ S) -> nappSubst id N ≡ N
 nappSubst-id (ƛ N) = cong ƛ (trans (cong (λ (α : vsubst _ _) → nappSubst α N) (funext-imp (λ U → funext (λ x → ext-id x)))) (nappSubst-id N))
 nappSubst-id (neut R) = cong neut (rappSubst-id R)


appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = nappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = s

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
 data tm : (Γ : ctx) (T : tp) -> Set where
  v : ∀ {Γ T} -> var Γ T -> tm Γ T
  --_·_ : ∀ {Γ T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
  app : ∀ {T S} -> tm ((⊡ , (T ⇝ S)) , T) S
  ƛ : ∀ {Γ T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
  [_] : ∀ {Γ Δ T} -> sub Δ Γ -> tm Δ T -> tm Γ T

 sub : (Γ1 Γ2 : ctx) -> Set
 sub Γ1 Γ2 = ∀ {T} -> var Γ1 T -> tm Γ2 T

_◦_ : ∀ {Γ1 Γ2 Γ3} -> vsubst Γ2 Γ3 -> subst Γ1 Γ2 -> subst Γ1 Γ3
(σ ◦ θ) = λ x ->  appSubst _ σ (θ x)

-- Traditional nbe
-- This is taking tm Γ T into a Yoneda-like Hom space
eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
--eval θ (M · N) = eval θ M _ id (eval θ N)
eval θ app = θ (s z) _ id (θ z)
eval θ (ƛ M) = λ _ σ s -> eval (extend (σ ◦ θ) s) M
eval θ ([ σ ] M) = eval (λ x → eval θ (σ x)) M


nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval (λ x → reflect (v x)) M)

_,,_ : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> tm Γ2 T -> sub (Γ1 , T) Γ2
(σ ,, M) z = M
(σ ,, M) (s y) = σ y

⊡₁ : ∀ {Γ} -> sub ⊡ Γ
⊡₁ ()

_·₁_ : ∀ {Γ T S} (M : tm Γ (T ⇝ S)) (N : tm Γ T) -> tm Γ S
M ·₁ N = [ ((⊡₁ ,, M) ,, N) ] app

mutual
 data _≈_ : ∀ {Γ} {T} -> tm Γ T -> tm Γ T -> Set where
  v : ∀ {T Γ} (x : var Γ T) -> (v x) ≈ (v x)
  app : ∀ {T S} -> (app {T} {S}) ≈ app
  --_·_ : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 N2 : tm Γ T} -> M1 ≈ M2 -> N1 ≈ N2 -> (M1 · N1) ≈ (M2 · N2)
  ƛ : ∀ {T S Γ} {M1 M2 : tm (Γ , T) S} -> M1 ≈ M2 -> (ƛ M1) ≈ (ƛ M2)
  [_] : ∀ {Δ T Γ} {σ1 σ2 : sub Δ Γ} -> (σ1 ≈s σ2) -> {M1 M2 : tm Δ T} -> M1 ≈ M2 -> [ σ1 ] M1 ≈ [ σ2 ] M2
  β : ∀ {T S Γ} (M : tm (Γ , T) S) (N : tm Γ T) -> (ƛ M ·₁ N) ≈ [ v ,, N ] M
  η : ∀ {T S Γ} (M : tm Γ (T ⇝ S)) -> M ≈ (ƛ ([ v ∘₁ s ] M ·₁ (v z)))
  idL : ∀ {T Γ} (M : tm Γ T) -> [ v ] M ≈ M
  idRπ : ∀ {Δ T Γ} (σ : sub Δ Γ) (x : var Δ T) -> [ σ ] (v x) ≈ (σ x)
  assoc : ∀ {Γ' Γ'' T Γ} (σ1 : sub Γ' Γ) (σ2 : sub Γ'' Γ') (M : tm Γ'' T) -> [ σ1 ] ([ σ2 ] M) ≈ [ [ σ1 ] ∘₁ σ2 ] M
  ≈-trans : ∀ {T Γ} {M N P : tm Γ T} -> M ≈ N -> N ≈ P -> M ≈ P
  ≈-sym : ∀ {T Γ} {M N : tm Γ T} -> M ≈ N -> N ≈ M

 _≈s_ : ∀ {Γ1 Γ2} (σ1 σ2 : sub Γ1 Γ2) -> Set
 _≈s_ σ1 σ2 = ∀ {U} (x : var _ U) -> σ1 x ≈ σ2 x
 -- I think we get the η law for products (contexts) automatically?

≈s-trans : ∀ {T Γ} {M N P : sub Γ T} -> M ≈s N -> N ≈s P -> M ≈s P
≈s-trans p q x = ≈-trans (p x) (q x)

mutual
 ≈-refl : ∀ {Γ T} {M : tm Γ T} -> M ≈ M
 ≈-refl {M = v y} = v y
 ≈-refl {M = app} = app --≈-refl · ≈-refl
 ≈-refl {M = ƛ M} = ƛ ≈-refl
 ≈-refl {M = [ σ ] M} = [ ≈s-refl σ ] ≈-refl

 ≈s-refl : ∀ {Γ1 Γ2} (σ : sub Γ1 Γ2) -> σ ≈s σ
 ≈s-refl σ x = ≈-refl 

Pr : ∀ {Γ} T (t : sem Γ T) -> Set 
Pr (atom A) t = Unit
Pr (T ⇝ S) f = (Δ : _) (σ : vsubst _ Δ) (t : sem Δ T) -> Pr T t -> Pr S (f Δ σ t) *
 ((Δ' : _) (ρ : vsubst Δ Δ') → appSubst _ ρ (f Δ σ t) ≡ f Δ' (ρ ∘ σ) (appSubst _ ρ t))

niceSubst : (Γ Δ : ctx) (θ : subst Γ Δ) -> Set
niceSubst Γ Δ θ = ∀ {U} x -> Pr U (θ x)

niceExtend : ∀ {Γ Δ T} {θ : subst Γ Δ} (ρ : niceSubst Γ Δ θ) {M : sem Δ T} -> Pr T M -> niceSubst (Γ , T) Δ (extend θ M)
niceExtend ρ t z = t
niceExtend ρ t (s y) = ρ y

PrClosed : ∀ {Γ Δ} U (σ : vsubst Γ Δ) {M : sem Γ U} -> Pr U M -> Pr U (appSubst U σ M)
PrClosed (atom A) σ t = tt
PrClosed {Γ} {Δ} (T ⇝ S) σ f = λ Δ' σ' t' x → _*_.fst (f _ _ _ x) , (λ Δ'' ρ → _*_.snd (f _ _ _ x) Δ'' ρ)

_◦n_ : ∀ {Γ1 Γ2 Γ3} (σ : vsubst Γ2 Γ3) {θ : subst Γ1 Γ2} -> niceSubst Γ1 Γ2 θ -> niceSubst Γ1 Γ3 (σ ◦ θ)
(σ ◦n ρ) x = PrClosed _ σ (ρ x)

appFunct : ∀ {T Γ1 Γ2 Γ3} (σ : vsubst Γ1 Γ2) (σ' : vsubst Γ2 Γ3) (t : sem Γ1 T) -> appSubst T (σ' ∘ σ) t ≡ appSubst T σ' (appSubst T σ t)
appFunct {atom A} σ σ' t = sym (nappSubst-funct σ' σ t)
appFunct {T ⇝ S} σ σ' t = refl

appFunct-id : ∀ {T Γ} (t : sem Γ T) -> appSubst T id t ≡ t
appFunct-id {atom A} t = nappSubst-id t
appFunct-id {T ⇝ S} t = refl 

blah2 : ∀ {Γ1 Γ2 Γ3 T} (σ : vsubst Γ2 Γ3) (θ : subst Γ1 Γ2) (t : sem Γ2 T) {U} (x : var (Γ1 , T) U) -> (σ ◦ (extend θ t)) x ≡ (extend (σ ◦ θ) (appSubst _ σ t)) x
blah2 σ θ t z = refl
blah2 σ θ t (s y) = refl

mutual
 nice : ∀ {Γ Δ T} (M : tm Γ T) (θ : subst Γ Δ) (θnice : niceSubst Γ Δ θ) -> Pr T (eval θ M)
 nice (v y) θ θnice = θnice y
 nice app θ θnice = _*_.fst (θnice (s z) _ id (θ z) (θnice z))
 nice {Γ} {Δ1} {T ⇝ S} (ƛ M) θ θnice = λ Δ σ t x → (nice M (extend (σ ◦ θ) t) (niceExtend (σ ◦n θnice) x))
  , λ Δ' ρ → trans (nice2 M (extend (σ ◦ θ) t) (niceExtend (σ ◦n θnice) x) ρ) (cong (λ (α : subst _ _) → eval α M) (funext-imp (λ U → funext (λ x0 → trans (blah2 ρ (σ ◦ θ) t x0) (cong (λ (α : subst _ _) → extend α (appSubst T ρ t) x0) (funext-imp (λ U' → funext (λ x' → sym (appFunct σ ρ (θ x'))))))))))
 nice ([ σ ] M) θ θnice = nice M (λ {T} x → eval θ (σ x)) (λ x → nice (σ x) θ θnice)

 nice2 : ∀ {Γ Δ T} (M : tm Γ T) (θ : subst Γ Δ) (θnice : niceSubst Γ Δ θ) {Δ'} (σ : vsubst Δ Δ') -> appSubst T σ (eval θ M) ≡ eval (σ ◦ θ) M
 nice2 (v y) θ θnice σ = refl
 nice2 app θ θnice σ = _*_.snd (θnice (s z) _ id (θ z) (θnice z)) _ σ
 nice2 (ƛ M) θ θnice σ = funext (λ Δ'' → funext (λ σ' → funext (λ t →
   cong (λ (α : subst _ _) -> eval (extend α t) M) (funext-imp (λ T → funext (λ x → appFunct σ _ (θ x)))))))
 nice2 ([_] y y') θ θnice σ = trans (nice2 y' (λ {T} x → eval θ (y x)) (λ x → nice (y x) θ θnice) σ) (cong (λ (α : subst _ _) → eval α y') (funext-imp (λ x → funext (λ x' → nice2 (y x') θ θnice σ))))

-- Oh yay a PER
_≃_ : ∀ {T Γ} (M N : sem Γ T) -> Set
_≃_ {atom A} M N = M ≡ N
_≃_ {T ⇝ S} M N = ∀ Δ (σ : vsubst _ Δ) t1 t2 → (prt1 : Pr T t1) -> (prt2 : Pr T t2) -> (t1≃t2 : t1 ≃ t2) → M Δ σ t1 ≃ N Δ σ t2

≃-sym : ∀ {T Γ} {M N : sem Γ T} -> M ≃ N -> N ≃ M
≃-sym {atom A} p = sym p
≃-sym {T ⇝ S} p = λ Δ σ t1 t2 prt1 prt2 t1≃t2 → ≃-sym {S} (p Δ σ t2 t1 prt2 prt1 (≃-sym {T} t1≃t2))

≃-trans : ∀ {T Γ} {M N P : sem Γ T} -> M ≃ N -> N ≃ P -> M ≃ P
≃-trans {atom A} p1 p2 = trans p1 p2
≃-trans {T ⇝ S} p1 p2 = λ Δ σ t1 t2 prt1 prt2 t1≃t2 → ≃-trans {S} (p1 Δ σ t1 t1 prt1 prt1 (≃-trans t1≃t2 (≃-sym t1≃t2))) (p2 Δ σ t1 t2 prt1 prt2 t1≃t2)

≃≡-trans : ∀ {T Γ} {M N P : sem Γ T} -> M ≃ N -> N ≡ P -> M ≃ P
≃≡-trans p refl = p

≡≃-trans : ∀ {T Γ} {M N P : sem Γ T} -> M ≡ N -> N ≃ P -> M ≃ P
≡≃-trans refl p = p

≃-blah : ∀ {T Γ} {M N : sem Γ T} -> M ≃ N -> M ≃ M
≃-blah p = ≃-trans p (≃-sym p)

_≃s_ : ∀ {Γ1 Γ2} (σ1 σ2 : subst Γ1 Γ2) -> Set
_≃s_ σ1 σ2 = ∀ {U} (x : var _ U) -> σ1 x ≃ σ2 x

≃s-sym : ∀ {T Γ} {M N : subst Γ T} -> M ≃s N -> N ≃s M
≃s-sym p x = ≃-sym (p x)

≃s-blah : ∀ {T Γ} {M N : subst Γ T} -> M ≃s N -> M ≃s M
≃s-blah p x = ≃-blah (p x)

extend-≃ : ∀ {Γ1 Γ2 T} {σ1 σ2 : subst Γ1 Γ2} (σ1≃σ2 : σ1 ≃s σ2) {t1 t2 : sem Γ2 T} (t1≃t2 : t1 ≃ t2) -> extend σ1 t1 ≃s extend σ2 t2
extend-≃ σ1≃σ2 t1≃t2 z = t1≃t2
extend-≃ σ1≃σ2 t1≃t2 (s y) = σ1≃σ2 y

appSubst-≃ : ∀ {T Γ1 Γ2} (ρ : vsubst Γ1 Γ2) {σ1 σ2 : sem Γ1 T} (σ1≃σ2 : σ1 ≃ σ2) -> (appSubst T ρ σ1) ≃ (appSubst T ρ σ2)
appSubst-≃ {atom A} ρ refl = refl
appSubst-≃ {T ⇝ S} ρ σ1≃σ2 = λ Δ σ t1 t2 prt1 prt2 t1≃t2 → σ1≃σ2 _ (σ ∘ ρ) t1 t2 prt1 prt2 t1≃t2

_◦≃_ : ∀ {Γ1 Γ2 Γ3} (ρ : vsubst Γ2 Γ3) {σ1 σ2 : subst Γ1 Γ2} (σ1≃σ2 : σ1 ≃s σ2) -> (ρ ◦ σ1) ≃s (ρ ◦ σ2)
(ρ ◦≃ (σ1≃σ2)) x = appSubst-≃ ρ (σ1≃σ2 x)

≃-refl : ∀ {T Γ1 Γ2} (σ1 σ2 : subst Γ1 Γ2) (σ1≃σ2 : σ1 ≃s σ2) (σ1n : niceSubst Γ1 Γ2 σ1) (σ2n : niceSubst Γ1 Γ2 σ2)
 (M : tm Γ1 T) -> (eval σ1 M) ≃ (eval σ2 M)
≃-refl σ1 σ2 σ1≃σ2 σ1n σ2n (v y) = σ1≃σ2 y
≃-refl σ1 σ2 σ1≃σ2 σ1n σ2n app = σ1≃σ2 (s z) _ id (σ1 z) (σ2 z) (σ1n z) (σ2n z) (σ1≃σ2 z)
≃-refl σ1 σ2 σ1≃σ2 σ1n σ2n (ƛ y) = λ Δ σ t1 t2 prt1 prt2 t1≃t2 → ≃-refl (extend (σ ◦ σ1) t1) (extend (σ ◦ σ2) t2) (extend-≃ (σ ◦≃ σ1≃σ2) t1≃t2) (niceExtend (σ ◦n σ1n) prt1) (niceExtend (σ ◦n σ2n) prt2) y
≃-refl σ1 σ2 σ1≃σ2 σ1n σ2n ([_] y y') = ≃-refl (λ {T} x → eval σ1 (y x)) (λ {T} x → eval σ2 (y x)) (λ x → ≃-refl σ1 σ2 σ1≃σ2 σ1n σ2n (y x)) (λ x → nice (y x) σ1 σ1n) (λ x → nice (y x) σ2 σ2n) y'

soundness1 : ∀ {Γ3 T Γ2} (σ1 σ2 : subst Γ2 Γ3) (σ1≃σ2 : σ1 ≃s σ2) (θ1 : niceSubst Γ2 Γ3 σ1) (θ2 : niceSubst Γ2 Γ3 σ2) (M1 M2 : tm Γ2 T)
   -> M1 ≈ M2 -> (eval σ1 M1) ≃ (eval σ2 M2)
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 .(v x) .(v x) (v x) = σ1≃σ2 x
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 .(ƛ M1) .(ƛ M2) (ƛ {T} {S} {Γ} {M1} {M2} y) = λ Δ σ t1 t2 prt1 prt2 t1≃t2 → soundness1 (extend (σ ◦ σ1) t1) (extend (σ ◦ σ2) t2) (extend-≃ (σ ◦≃ σ1≃σ2) t1≃t2) (niceExtend (σ ◦n θ1) prt1) (niceExtend (σ ◦n θ2) prt2) M1 M2 y
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 .app .app app = σ1≃σ2 (s z) _ id (σ1 z) (σ2 z) (θ1 z) (θ2 z) (σ1≃σ2 z)
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 .([ σ3 ] M1) .([ σ4 ] M2) ([_] {_} {_} {Γ} {σ3} {σ4} y {M1} {M2} y') = soundness1 (λ x → eval σ1 (σ3 x)) (λ x → eval σ2 (σ4 x)) (λ x → soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 (σ3 x) (σ4 x) (y x)) (λ x → nice (σ3 x) σ1 θ1) (λ x → nice (σ4 x) σ2 θ2) M1 M2 y'
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 .([ (⊡₁ ,, ƛ M) ,, N ] app) .([ v ,, N ] M) (β M N) = ≃-refl (extend (id ◦ σ1) (eval σ1 N)) (λ {T} x → eval σ2 ((v ,, N) x)) (var-dom-prop (λ x → extend (id ◦ σ1) (eval σ1 N) x ≃ eval σ2 ((v ,, N) x)) (λ x → ≡≃-trans (appFunct-id (σ1 x)) (σ1≃σ2 x)) (≃-refl σ1 σ2 σ1≃σ2 θ1 θ2 N)) (niceExtend (id ◦n θ1) (nice N σ1 θ1)) (var-dom-prop (λ x → Pr _ (eval σ2 ((v ,, N) x))) θ2 (nice N σ2 θ2)) M
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 M1 .(ƛ ([ (⊡₁ ,, [ (v ∘₁ s) ] M1) ,, v z ] app)) (η .M1) = λ Δ σ t1 t2 prt1 prt2 t1≃t2 → ≃≡-trans (≃-refl σ1 σ2 σ1≃σ2 θ1 θ2 M1 Δ σ t1 t2 prt1 prt2 t1≃t2) (cong-app1 (cong-app1 (cong-app1 (nice2 M1 σ2 θ2 σ) _) id) t2)
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 .([ v ] M2) M2 (idL .M2) = ≃-refl σ1 σ2 σ1≃σ2 θ1 θ2 M2
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 .([ σ ] (v x)) .(σ x) (idRπ σ x) = ≃-refl σ1 σ2 σ1≃σ2 θ1 θ2 (σ x)
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 .([ σ3 ] ([ σ4 ] M)) .([ ([ σ3 ] ∘₁ σ4) ] M) (assoc σ3 σ4 M) = ≃-refl (λ {T} x → eval (λ {T'} x' → eval σ1 (σ3 x')) (σ4 x)) (λ {T} x → eval (λ {T'} x' → eval σ2 (σ3 x')) (σ4 x)) (λ x → ≃-refl (λ {T} x' → eval σ1 (σ3 x')) (λ {T} x' → eval σ2 (σ3 x')) (λ x' → ≃-refl σ1 σ2 σ1≃σ2 θ1 θ2 (σ3 x')) (λ x' → nice (σ3 x') σ1 θ1) (λ x' → nice (σ3 x') σ2 θ2) (σ4 x)) (λ x → nice (σ4 x) (λ {T} x' → eval σ1 (σ3 x')) (λ x' → nice (σ3 x') σ1 θ1)) (λ x → nice (σ4 x) (λ {T} x' → eval σ2 (σ3 x')) (λ x' → nice (σ3 x') σ2 θ2)) M
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 M P (≈-trans {N = N} M≃N N≃P) = 
  ≃-trans (soundness1 σ1 σ1 (≃s-blah σ1≃σ2) θ1 θ1 M N M≃N)
          (soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 N P N≃P)
soundness1 σ1 σ2 σ1≃σ2 θ1 θ2 M N (≈-sym M≈N) = ≃-sym (soundness1 σ2 σ1 (λ x → ≃-sym (σ1≃σ2 x)) θ2 θ1 N M M≈N)



reflect-nice : ∀ {T Γ Δ} (ρ : vsubst Γ Δ) (R : rtm Γ T) -> appSubst T ρ (reflect R) ≡ reflect (rappSubst ρ R)
reflect-nice {atom A} ρ R = refl
reflect-nice {T ⇝ S} ρ R = funext (λ Δ' → funext (λ σ → funext (λ x → cong (λ α → reflect (α · reify x)) (sym (rappSubst-funct _ ρ R)))))

mutual
 reify-nice : ∀ {T Γ Δ} (ρ : vsubst Γ Δ) (t : sem Γ T) (p : Pr T t) -> nappSubst ρ (reify t) ≡ reify (appSubst T ρ t)
 reify-nice {atom A} ρ t p = refl
 reify-nice {T ⇝ S} ρ t p with p _ wkn (reflect (v z)) (reflect-nice2 (v z))
 ... | q1 , q2 = cong ƛ (trans (reify-nice (ext ρ) (t (_ , T) wkn (reflect (v z))) q1) (cong reify (trans (q2 (_ , T) (ext ρ)) (cong (λ α → t _ (wkn ∘ ρ) α) (reflect-nice (ext ρ) (v z))))))

 reflect-nice2 : ∀ {T Γ} (R : rtm Γ T) -> Pr T (reflect R)
 reflect-nice2 {atom A} R = tt
 reflect-nice2 {T ⇝ S} R = λ Δ σ t x → (reflect-nice2 (rappSubst σ R · reify t)) , (λ Δ' ρ → trans (reflect-nice ρ (rappSubst σ R · reify t)) (cong2 (λ α β' → reflect (α · β')) (rappSubst-funct ρ σ R) (reify-nice ρ t x)))

mutual
 reflect-nice3 : ∀ {T Γ} (R : rtm Γ T) -> reflect R ≃ reflect R
 reflect-nice3 {atom A} R = refl
 reflect-nice3 {T ⇝ S} R = λ Δ σ t1 t2 prt1 prt2 t1≃t2 → eq-ind
   (λ α → reflect (rappSubst σ R · reify t1) ≃ reflect (rappSubst σ R · α))
   (reify-nice2 t1≃t2) (reflect-nice3 (rappSubst σ R · reify t1))

 reify-nice2 : ∀ {T Γ} {t1 t2 : sem Γ T} (t1≃t2 : t1 ≃ t2) -> reify t1 ≡ reify t2
 reify-nice2 {atom A} t1≃t2 = t1≃t2
 reify-nice2 {T ⇝ S} t1≃t2 =
  cong ƛ (reify-nice2 (t1≃t2 _ wkn (reflect (v z)) (reflect (v z)) (reflect-nice2 (v z)) (reflect-nice2 (v z)) (reflect-nice3 (v z))))

soundness' : ∀ {Γ T} {M1 M2 : tm Γ T} -> M1 ≈ M2 -> (nbe M1) ≡ (nbe M2)
soundness' H = reify-nice2 (soundness1 _ _ (λ x → reflect-nice3 (v x)) (λ x → reflect-nice2 (v x)) (λ x → reflect-nice2 (v x)) _ _ H)

-- TODO: Now just get rid of funext and funext-imp

≈-refl' : ∀ {Γ T} {M1 M2 : tm Γ T} -> M1 ≡ M2 -> M1 ≈ M2
≈-refl' refl = ≈-refl

≈≡-trans : ∀ {Γ T} {M N P : tm Γ T} -> M ≡ N -> N ≈ P -> M ≈ P
≈≡-trans refl p = p

≡≈-trans : ∀ {Γ T} {M N P : tm Γ T} -> M ≈ N -> N ≡ P -> M ≈ P
≡≈-trans p refl = p

{-
[]v-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]v ([ σ2 ]v R) ≡ [ σ1 ∘ σ2 ]v R
[]v-funct σ1 σ2 (v y) = refl
[]v-funct σ1 σ2 (y · y') = cong2 _·_ ([]v-funct σ1 σ2 y) ([]v-funct σ1 σ2 y')
[]v-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]v-funct (ext σ1) (ext σ2) y) (cong (λ (α : vsubst _ _) → [ α ]v y) (var-dom-eq (λ x → refl) refl)))

[]vn-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]v ([ σ2 ] R) ≡ [ [ σ1 ]v ∘₁ σ2 ] R
[]vn-funct σ1 σ2 (v y) = refl
[]vn-funct σ1 σ2 (y · y') = cong2 _·_ ([]vn-funct σ1 σ2 y) ([]vn-funct σ1 σ2 y')
[]vn-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]vn-funct (ext σ1) (sub-ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → trans ([]v-funct (ext σ1) s (σ2 x)) (sym ([]v-funct s σ1 (σ2 x)))) refl)))

[]nv-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ]v R) ≡ [ σ1 ∘₁ σ2 ] R
[]nv-funct σ1 σ2 (v y) = refl
[]nv-funct σ1 σ2 (y · y') = cong2 _·_ ([]nv-funct σ1 σ2 y) ([]nv-funct σ1 σ2 y')
[]nv-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]nv-funct (sub-ext σ1) (ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → refl) refl)))

[]-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ] R) ≡ [ [ σ1 ] ∘₁ σ2 ] R
[]-funct σ1 σ2 (v y) = refl
[]-funct σ1 σ2 (y · y') = cong2 _·_ ([]-funct σ1 σ2 y) ([]-funct σ1 σ2 y')
[]-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]-funct (sub-ext σ1) (sub-ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → trans ([]nv-funct (sub-ext σ1) s (σ2 x)) (sym ([]vn-funct s σ1 (σ2 x)))) refl)))

sub-ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> (sub-ext v) x ≡ v x
sub-ext-id z = refl
sub-ext-id (s y) = refl

[]-id : ∀ {Γ T} {M : tm Γ T} -> [ v ] M ≡ M
[]-id {M = v y} = refl
[]-id {M = M · N} = cong2 _·_ []-id []-id
[]-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : sub _ _) → [ α ] M) (funext-imp (λ x → funext (λ x' → sub-ext-id x')))) []-id)

vsimp : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (N : tm Γ T) {U} (x : var (Γ , T) U) -> ((v ,, [ σ ]v N) ∘₁ (ext σ)) x ≡ ([ σ ]v ∘₁ (v ,, N)) x
vsimp σ N z = refl
vsimp σ N (s y) = refl

simp : ∀ {Γ Δ T} (σ : sub Γ Δ) (N : tm Γ T) {U} (x : var (Γ , T) U) -> ([ v ,, [ σ ] N ] ∘₁ (sub-ext σ)) x ≡ ([ σ ] ∘₁ (v ,, N)) x
simp σ N z = refl
simp σ N (s y) = trans ([]nv-funct _ _ (σ y)) []-id

-- What would this whole proof look like if we used explicit substitutions?
-- We would need to prove more equations about semantic values, but less of this?
[_]v≈ : ∀ {Γ Δ T} (σ : vsubst Γ Δ) {M1 M2 : tm Γ T} -> M1 ≈ M2 -> [ σ ]v M1 ≈ [ σ ]v M2
[_]v≈ σ (v x) = v (σ x)
[_]v≈ σ (M · N) = [ σ ]v≈ M · [ σ ]v≈ N
[_]v≈ σ (ƛ M) = ƛ ([ ext σ ]v≈ M)
[_]v≈ σ (β M N) = ≈-trans (β _ _) (≈-refl' (trans ([]nv-funct (v ,, [ σ ]v N) (ext σ) M) (trans (cong (λ (α : sub _ _) → [ α ] M) (funext-imp (λ x → funext (λ x' → vsimp σ N x')))) (sym ([]vn-funct σ (v ,, N) M)))))
[_]v≈ σ {M1} (η .M1) = ≈-trans (η _) (ƛ (≈-refl' (trans ([]v-funct s σ M1) (sym ([]v-funct (ext σ) s M1))) · (v z)))
[_]v≈ σ (≈-trans M≈N N≈P) = ≈-trans ([ σ ]v≈ M≈N) ([ σ ]v≈ N≈P)
[_]v≈ σ (≈-sym M≈N) = ≈-sym ([ σ ]v≈ M≈N)

≈s-ext : ∀ {Γ Δ T} {σ1 σ2 : sub Γ Δ} -> σ1 ≈s σ2 -> (sub-ext {T = T} σ1) ≈s (sub-ext σ2)
≈s-ext p z = v z
≈s-ext p (s y) = [ s ]v≈ (p y)

[_]≈c : ∀ {Γ Δ T} {σ1 σ2 : sub Γ Δ} (σ1≈σ2 : σ1 ≈s σ2) (M : tm Γ T) -> [ σ1 ] M ≈ [ σ2 ] M
[_]≈c p (v y) = p y
[_]≈c p (M · N) = [ p ]≈c M · [ p ]≈c N
[_]≈c p (ƛ M) = ƛ ([ ≈s-ext p ]≈c M)

[_]≈ : ∀ {Γ Δ T} {σ1 σ2 : sub Γ Δ} (σ1≈σ2 : σ1 ≈s σ2) {M1 M2 : tm Γ T} -> M1 ≈ M2 -> [ σ1 ] M1 ≈ [ σ2 ] M2
[_]≈ σ1≈σ2 (v x) = σ1≈σ2 x
[_]≈ σ1≈σ2 (M · N) = ([ σ1≈σ2 ]≈ M) · ([ σ1≈σ2 ]≈ N)
[_]≈ σ1≈σ2 (ƛ M) = ƛ ([ ≈s-ext σ1≈σ2 ]≈ M)
[_]≈ σ1≈σ2 (β M N) = ≈-trans (β _ _) (≈≡-trans ([]-funct _ _ M) (≡≈-trans ([ (λ x → ≈≡-trans (simp _ N x) ([ σ1≈σ2 ]≈c ((v ,, N) x))) ]≈c M) (sym ([]-funct _ _ M))))
[_]≈ σ1≈σ2 {M1} (η .M1) = ≈-trans (η _) (ƛ (≈≡-trans ([]vn-funct _ _ M1) (≡≈-trans ([ (λ x → [ s ]v≈ (σ1≈σ2 x)) ]≈c M1) (sym ([]nv-funct _ _ M1))) · (v z)))
[_]≈ {σ2 = σ2} σ1≈σ2 (≈-trans M≈N N≈P) = ≈-trans ([ σ1≈σ2 ]≈ M≈N) ([ ≈s-refl σ2 ]≈ N≈P)
[_]≈ σ1≈σ2 (≈-sym M≈N) = ≈-sym ([ (λ x → ≈-sym (σ1≈σ2 x)) ]≈ M≈N)

[_]≈c2 : ∀ {Γ Δ T} (σ : sub Γ Δ) {M1 M2 : tm Γ T} -> M1 ≈ M2 -> [ σ ] M1 ≈ [ σ ] M2
[ σ ]≈c2 p = [ ≈s-refl σ ]≈ p
-}
mutual
 ninj : ∀ {Γ T} -> ntm Γ T -> tm Γ T
 ninj (ƛ M) = ƛ (ninj M)
 ninj (neut R) = rinj R
 rinj : ∀ {Γ T} -> rtm Γ T -> tm Γ T
 rinj (v x) = v x
 rinj (R · N) = (rinj R) ·₁ (ninj N)


hurgh : ∀ {Γ T S} (σ1 σ2 : sub ((⊡ , T) , S) Γ) -> σ1 z ≈ σ2 z -> σ1 (s z) ≈ σ2 (s z) -> σ1 ≈s σ2
hurgh σ1 σ2 p q z = p
hurgh σ1 σ2 p q (s z) = q
hurgh σ1 σ2 p q (s (s ()))

_·₂_ : ∀ {Γ T S} {M1 M2 : tm Γ (T ⇝ S)} -> M1 ≈ M2 -> {N1 N2 : tm Γ T} -> N1 ≈ N2 -> (M1 ·₁ N1) ≈ (M2 ·₁ N2)
M ·₂ N = [ hurgh ((⊡₁ ,, _) ,, _) ((⊡₁ ,, _) ,, _) N M ] app 


≈-[]-app : ∀ {Γ Δ T S} (σ : sub Δ Γ) (M : tm Δ (T ⇝ S)) (N : tm Δ T) -> [ σ ] (M ·₁ N) ≈ ([ σ ] M ·₁ [ σ ] N)
≈-[]-app σ M N = ≈-trans (assoc σ ((⊡₁ ,, M) ,, N) app) ([ hurgh ([ σ ] ∘₁ ((⊡₁ ,, M) ,, N)) ((⊡₁ ,, [ σ ] M) ,, [ σ ] N) ≈-refl ≈-refl ] ≈-refl)

blahgh : ∀ {Γ Δ T S} (σ : sub Δ Γ) (M : tm (Δ , T) S) -> [ σ ] (ƛ M) ≈ ƛ ([ ([ v ∘₁ s ] ∘₁ σ) ,, v z ] M)
blahgh σ M = ≈-trans (η _) (ƛ {!!})

[_]c : ∀ {Δ T Γ} (σ1 : sub Δ Γ) -> {M1 M2 : tm Δ T} -> M1 ≈ M2 -> [ σ1 ] M1 ≈ [ σ1 ] M2
[ σ ]c p = [ ≈s-refl σ ] p


mutual
 []v-comm-ninj : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (N : ntm Γ T) -> [ v ∘₁ σ ] (ninj N) ≈ ninj (nappSubst σ N)
 []v-comm-ninj σ (ƛ M) = ≈-trans (blahgh (v ∘₁ σ) _) (ƛ (≈-trans ([ var-dom-prop
                                                                      (λ x → (([ v ∘₁ s ] ∘₁ (v ∘₁ σ)) ,, v z) x ≈ v (ext σ x)) (λ x → idRπ (v ∘₁ s) (σ x)) (v z) ] ≈-refl) ([]v-comm-ninj (ext σ) M)))
 []v-comm-ninj σ (neut R) = []v-comm-rinj σ R
 []v-comm-rinj : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (R : rtm Γ T) -> [ v ∘₁ σ ] (rinj R) ≈ rinj (rappSubst σ R)
 []v-comm-rinj σ (v y) = idRπ (v ∘₁ σ) y --refl
 []v-comm-rinj σ (R · N) = ≈-trans (≈-[]-app (v ∘₁ σ) (rinj R) (ninj N)) (([]v-comm-rinj σ R) ·₂ ([]v-comm-ninj σ N))

{-
≈-η-expand : ∀ {T Γ} (R : rtm Γ T) -> (rinj R) ≈ (ninj (reify (reflect R)))
≈-η-expand {atom A} R = ≈-refl
≈-η-expand {T ⇝ S} R = ≈-trans (η (rinj R)) (ƛ (≈-trans (≈-refl' ([]v-comm-rinj s R) · ≈-η-expand (v z)) (≈-η-expand _)))
-}


≈-η-expand : ∀ {T Γ} (R : rtm Γ T) -> (rinj R) ≈ (ninj (reify (reflect R)))
≈-η-expand {atom A} R = ≈-refl
≈-η-expand {T ⇝ S} R = ≈-trans (η (rinj R)) (ƛ (≈-trans (([]v-comm-rinj s R) ·₂ (≈-η-expand (v z))) (≈-η-expand _)))


GL : (Γ : ctx) (T : tp) (t : sem Γ T) -> Set
GL Γ (atom A) t = Unit
GL Γ (T ⇝ S) t = ∀ Δ (σ : vsubst Γ Δ) (p : sem Δ T) (glp : GL Δ T p) (prp : Pr T p) → (GL Δ S (t Δ σ p)
  * (((ninj (reify (appSubst _ σ t))) ·₁ (ninj (reify p))) ≈ ninj (reify (t Δ σ p))))

appSubstGL : ∀ {T Γ2 Γ3} (ρ : vsubst Γ2 Γ3) {t : sem Γ2 T} -> GL Γ2 T t -> GL Γ3 T (appSubst T ρ t)
appSubstGL {atom A} ρ glt = tt
appSubstGL {T ⇝ S} ρ glt = λ Δ σ p glp prp → glt Δ (σ ∘ ρ) p glp prp

GLs : ∀ {Γ Δ} -> (σ : subst Γ Δ) -> Set
GLs σ = ∀ {U} (x : var _ U) -> GL _ U (σ x)

_◦g_ : ∀ {Γ1 Γ2 Γ3} (ρ : vsubst Γ2 Γ3) {σ : subst Γ1 Γ2} -> GLs σ -> GLs (ρ ◦ σ)
(ρ ◦g θ) x = appSubstGL ρ (θ x)

glExt : ∀ {Γ Δ T} {σ : subst Γ Δ} (θ : GLs σ) {t : sem Δ T} -> GL Δ T t -> GLs (extend σ t)
glExt θ p z = p
glExt θ p (s y) = θ y

reflect-GL : ∀ {T Γ} (R : rtm Γ T) -> GL Γ T (reflect R)
reflect-GL {atom A} R = tt
reflect-GL {T ⇝ S} R = λ Δ σ p glp prp → (reflect-GL (rappSubst σ R · reify p)) , (≈-trans (β _ _) (≈-trans (≈-trans ([ ≈s-refl (v ,, ninj (reify p)) ] (≈-sym (≈-η-expand _))) (≈-[]-app (v ,, ninj (reify p)) (rinj (rappSubst (wkn ∘ σ) R))
                                                                                                                                                                                   (ninj (reify (reflect (v z)))))) (≈-trans (≈-trans ([ ≈s-refl (v ,, ninj (reify p)) ] (≈-trans (≈-refl' (cong rinj (sym (rappSubst-funct s σ R)))) (≈-sym ([]v-comm-rinj s (rappSubst σ R))))) (≈-trans (assoc (v ,, ninj (reify p)) (v ∘₁ s) _) (≈-trans ([ (λ x → idRπ (v ,, ninj (reify p)) (s x)) ] ≈-refl) (idL (rinj (rappSubst σ R))))) ·₂ (≈-trans ([ ≈s-refl (v ,, ninj (reify p)) ] (≈-sym (≈-η-expand (v z)))) (idRπ (v ,, ninj (reify p)) z))) (≈-η-expand _))))

expand-sub : ∀ {Γ Δ T} (σ : sub (Γ , T) Δ) -> σ ≈s ((σ ∘₁ s) ,, σ z)
expand-sub σ z = ≈-refl
expand-sub σ (s y) = ≈-refl

_,,₂_ : ∀ {Γ T Δ} {σ1 σ2 : sub Γ Δ} -> σ1 ≈s σ2 -> (M : tm Δ T) -> (σ1 ,, M) ≈s (σ2 ,, M)
_,,₂_ p M z = ≈-refl
_,,₂_ p M (s y) = p y

blagh : ∀ {Γ Δ T} (σ1 σ2 : sub (Γ , T) Δ) -> (σ1 ∘₁ s) ≈s (σ2 ∘₁ s) -> (σ1 z) ≈ (σ2 z) -> σ1 ≈s σ2
blagh σ1 σ2 p1 p2 z = p2
blagh σ1 σ2 p1 p2 (s y) = p1 y

mutual
 allGL : ∀ {Γ Δ T} (σ : subst Γ Δ) (θ : GLs σ) (ρ : niceSubst _ _ σ) (M : tm Γ T) -> GL Δ T (eval σ M)
 allGL σ θ ρ (v y) = θ y
 allGL σ θ ρ app = _*_.fst (θ (s z) _ id (σ z) (θ z) (ρ z))
 allGL σ θ ρ (ƛ y) = λ Δ σ' p glp prp → (allGL (extend (σ' ◦ σ) p) (glExt (σ' ◦g θ) glp) (niceExtend (σ' ◦n ρ) prp) y) , {!!}
 allGL σ θ ρ ([_] y y') = allGL (λ {T} x → eval σ (y x)) (λ x → allGL σ θ ρ (y x)) (λ x → nice (y x) σ ρ) y'

 completeness : ∀ {Γ Δ T} (σ : subst Γ Δ) (θ : GLs σ) (ρ : niceSubst _ _ σ) (M : tm Γ T)
   -> ([ (ninj ∘₁ (reify ∘₁ σ)) ] M) ≈ ninj (reify (eval σ M))
 completeness σ θ ρ (v y) = idRπ (λ {T} x → ninj (reify (σ x))) y
 completeness σ θ ρ app = ≈-trans (≈-trans ([ expand-sub (ninj ∘₁ (reify ∘₁ σ)) ] app) (≈-trans ([ (≈s-trans (expand-sub (ninj ∘₁ (reify ∘₁ (σ ∘₁ s)))) ((λ ()) ,,₂ _)) ,,₂ ninj (reify (σ z)) ] app) (≈-refl ·₂ ≈-refl))) (_*_.snd (θ (s z) _ id (σ z) (θ z) (ρ z)))
 completeness σ θ ρ (ƛ y) = ≈-trans (blahgh (λ {T} x → ninj (reify (σ x))) y) (ƛ (≈-trans ([ blagh (([ v ∘₁ s ] ∘₁ (ninj ∘₁ (reify ∘₁ σ))) ,, v z) (ninj ∘₁ (reify ∘₁ extend (s ◦ σ) (reflect (v z)))) (λ x → {!!}) (≈-η-expand (v z)) ] ≈-refl) (completeness (extend (wkn ◦ σ) (reflect (v z))) (glExt (wkn ◦g θ) (reflect-GL (v z))) (niceExtend (wkn ◦n ρ) (reflect-GL (v z))) y)))
 completeness σ θ ρ ([_] y y') = ≈-trans (assoc _ y y') (≈-trans ([ (λ x → completeness σ θ ρ (y x)) ] ≈-refl) (completeness (λ {T} x → eval σ (y x)) (λ x → allGL σ θ ρ (y x)) (λ x → nice (y x) σ ρ) y'))

{-


mutual
 allGL : ∀ {Γ Δ T} (σ : subst Γ Δ) (θ : GLs σ) (ρ : niceSubst _ _ σ) (M : tm Γ T) -> GL Δ T (eval σ M)
 allGL σ θ ρ (v y) = θ y
 allGL σ θ ρ (M · N) = _*_.fst (allGL σ θ ρ M _ id (eval σ N) (allGL σ θ ρ N) (nice N σ ρ))
 allGL σ θ ρ (ƛ M) = λ Δ σ' p x prp → (allGL (extend (σ' ◦ σ) p) (glExt (σ' ◦g θ) x) (niceExtend (σ' ◦n ρ) prp) M) ,
  ≈-trans (β _ _) (≈-trans (≈-trans (≈-sym ([ v ,, ninj (reify p) ]≈c2 (completeness _ (glExt ((wkn ∘ σ') ◦g θ) (reflect-GL (v z))) (niceExtend ((s ∘ σ') ◦n ρ) (reflect-nice2 (v z))) M))) (≈≡-trans ([]-funct _ _ M) ([ blagh
     ([ v ,, ninj (reify p) ] ∘₁ (ninj ∘₁ (reify ∘₁ extend ((s ∘ σ') ◦ σ) (reflect (v z)))))
     (ninj ∘₁ (reify ∘₁ extend (σ' ◦ σ) p))
     (λ x' → ≈-refl' (trans (cong [ v ,, ninj (reify p) ] (trans (cong ninj (trans (cong reify (appFunct σ' s _)) (sym (reify-nice s (appSubst _ σ' (σ x')) (PrClosed _ σ' (ρ x')))))) (sym ([]v-comm-ninj s (reify (appSubst _ σ' (σ x'))))))) (trans ([]nv-funct _ _ (ninj (reify (appSubst _ σ' (σ x'))))) []-id)))
     (≈-sym (≈-trans ≈-refl ([ v ,, ninj (reify p) ]≈c2 (≈-η-expand (v z))))) ]≈c M)))
    (completeness (extend (σ' ◦ σ) p) (glExt (σ' ◦g θ) x) (niceExtend (σ' ◦n ρ) prp) M))

 completeness : ∀ {Γ Δ T} (σ : subst Γ Δ) (θ : GLs σ) (ρ : niceSubst _ _ σ) (M : tm Γ T)
   -> ([ (ninj ∘₁ (reify ∘₁ σ)) ] M) ≈ ninj (reify (eval σ M))
 completeness σ θ ρ (v y) = ≈-refl
 completeness σ θ ρ (M · N) = ≈-trans ((completeness σ θ ρ M) · (completeness σ θ ρ N)) (_*_.snd (allGL σ θ ρ M _ id (eval σ N) (allGL σ θ ρ N) (nice N σ ρ)))
 completeness σ θ ρ (ƛ M) = ƛ (≈-trans ([ blagh (sub-ext (ninj ∘₁ (reify ∘₁ σ)))
                                         (ninj ∘₁ (reify ∘₁ extend (wkn ◦ σ) (reflect (v z)))) (λ x → ≈-refl' (trans ([]v-comm-ninj s (reify (σ x))) (cong ninj (reify-nice s (σ x) (ρ x))))) (≈-η-expand (v z)) ]≈c M) (completeness (extend (wkn ◦ σ) (reflect (v z))) (glExt (wkn ◦g θ) (reflect-GL (v z))) (niceExtend (s ◦n ρ) (reflect-nice2 (v z))) M))

completeness' : ∀ {Γ T} (M : tm Γ T) -> M ≈ (ninj (nbe M))
completeness' M = ≈-trans (≈≡-trans (sym []-id) ([ (λ x → ≈-η-expand (v x)) ]≈c M)) (completeness (reflect ∘₁ v) (λ x → reflect-GL (v x)) (λ x → reflect-nice2 (v x)) M)

-- This is the form completeness would take if we didn't include ≈-sym
completeness'' : ∀ {Γ T} (M N : tm Γ T) -> nbe M ≡ nbe N -> (M ≈ ninj (nbe M)) * (N ≈ ninj (nbe M))
completeness'' M N p = ((completeness' M) , (eq-ind (λ α → N ≈ ninj α) (sym p) (completeness' N)))

-- Church-Rosser is actually an easy corollary (according to Dyber)! (or at least it would be if we didn't include ≈-sym... :( )
cr : ∀ {Γ T} (M N P : tm Γ T) -> M ≈ N -> M ≈ P -> Σ (λ (Q : tm Γ T) -> (N ≈ Q) * (P ≈ Q))
cr M N P p1 p2 = (ninj (nbe M)) ,
 (eq-ind (λ α → N ≈ ninj α) (sym (soundness' p1)) (completeness' N) ,
  eq-ind (λ α → P ≈ ninj α) (sym (soundness' p2)) (completeness' P))

completeness''' : ∀ {Γ T} (M N : tm Γ T) -> nbe M ≡ nbe N -> M ≈ N
completeness''' M N p = ≈-trans (completeness' M) (≈-sym (eq-ind (λ α → N ≈ ninj α) (sym p) (completeness' N)))

-}

-- TODO: We should be able to get rid of ≈-sym... Check the Dyber paper?
-- TODO: Try an explicit substitution language for tm. I suspect it's simpler
-- TODO: Try a more conventional (weak) normalization proof and strong normalization