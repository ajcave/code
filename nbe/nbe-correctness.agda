module nbe-correctness where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

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
wkn x = s x

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

-- Here we have "hereditary substitution"
mutual
 srSubst : ∀ {Γ Δ T} -> subst Γ Δ -> rtm Γ T -> sem Δ T
 srSubst θ (v y) = θ y
 srSubst θ (R · N) = srSubst θ R _ id (sSubst θ N)

 sSubst : ∀ {Γ Δ T} -> subst Γ Δ -> ntm Γ T -> sem Δ T
 sSubst θ (ƛ M) = λ Δ σ s → sSubst (extend (λ x → appSubst _ σ (θ x)) s) M
 sSubst θ (neut y) = srSubst θ y

nSubst : ctx -> ctx -> Set
nSubst Γ Δ = ∀ {S} -> var Γ S -> ntm Δ S
cut : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Γ T -> ntm Δ T
cut θ t = reify (sSubst (λ x → sSubst (λ x' → reflect (v x')) (θ x)) t)

nv : ∀ {Γ T} -> var Γ T -> ntm Γ T
nv x = reify (reflect (v x))

nExtend : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Δ T -> nSubst (Γ , T) Δ
nExtend θ N z = N
nExtend θ N (s y) = θ y

nId : ∀ {Γ} -> nSubst Γ Γ
nId x = nv x

napp : ∀ {Γ T S} -> ntm Γ (T ⇝ S) -> ntm Γ T -> ntm Γ S
napp (ƛ N) M = cut (nExtend nId M) N

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)

complete : ∀ {Γ T} -> tm Γ T -> ntm Γ T
complete (v y) = nv y
complete (M · N) = napp (complete M) (complete N)
complete (ƛ M) = ƛ (complete M)

_◦_ : ∀ {Γ1 Γ2 Γ3} -> vsubst Γ2 Γ3 -> subst Γ1 Γ2 -> subst Γ1 Γ3
(σ ◦ θ) = λ x ->  appSubst _ σ (θ x)

-- Traditional nbe
-- This is taking tm Γ T into a Yoneda-like Hom space
eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
eval θ (M · N) = eval θ M _ id (eval θ N)
eval θ (ƛ M) = λ _ σ s -> eval (extend (σ ◦ θ) s) M

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval (λ x → reflect (v x)) M)

[_]v : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_]v σ (v y) = v (σ y)
[_]v σ (M · N) = [ σ ]v M · [ σ ]v N
[_]v σ (ƛ M) = ƛ ([ ext σ ]v M)

sub : (Γ1 Γ2 : ctx) -> Set
sub Γ1 Γ2 = ∀ {T} -> var Γ1 T -> tm Γ2 T

sub-ext : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> sub (Γ1 , T) (Γ2 , T)
sub-ext σ z = v z
sub-ext σ (s y) = [ s ]v (σ y)

[_] : ∀ {Γ1 Γ2 T} (σ : sub Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_] σ (v y) = σ y
[_] σ (M · N) = [ σ ] M · [ σ ] N
[_] σ (ƛ M) = ƛ ([ sub-ext σ ] M)

_,,_ : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> tm Γ2 T -> sub (Γ1 , T) Γ2
(σ ,, M) z = M
(σ ,, M) (s y) = σ y

-- Why not just use an explicit substitution calculus?
data _≈_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 v : ∀ {T} (x : var Γ T) -> (v x) ≈ (v x)
 _·_ : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 N2 : tm Γ T} -> M1 ≈ M2 -> N1 ≈ N2 -> (M1 · N1) ≈ (M2 · N2)
 ƛ : ∀ {T S} {M1 M2 : tm (Γ , T) S} -> M1 ≈ M2 -> (ƛ M1) ≈ (ƛ M2)
 β : ∀ {T S} (M : tm (Γ , T) S) (N : tm Γ T) -> ((ƛ M) · N) ≈ [ v ,, N ] M
 η : ∀ {T S} (M : tm Γ (T ⇝ S)) -> M ≈ (ƛ ([ s ]v M · (v z)))

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
 nice (M · N) θ θnice = _*_.fst (nice M θ θnice _ _ _ (nice N θ θnice))
 nice {Γ} {Δ1} {T ⇝ S} (ƛ M) θ θnice = λ Δ σ t x → (nice M (extend (σ ◦ θ) t) (niceExtend (σ ◦n θnice) x))
  , λ Δ' ρ → trans (nice2 M (extend (σ ◦ θ) t) (niceExtend (σ ◦n θnice) x) ρ) (cong (λ (α : subst _ _) → eval α M) (funext-imp (λ U → funext (λ x0 → trans (blah2 ρ (σ ◦ θ) t x0) (cong (λ (α : subst _ _) → extend α (appSubst T ρ t) x0) (funext-imp (λ U' → funext (λ x' → sym (appFunct σ ρ (θ x'))))))))))

 nice2 : ∀ {Γ Δ T} (M : tm Γ T) (θ : subst Γ Δ) (θnice : niceSubst Γ Δ θ) {Δ'} (σ : vsubst Δ Δ') -> appSubst T σ (eval θ M) ≡ eval (σ ◦ θ) M
 nice2 (v y) θ θnice σ = refl
 nice2 (M · N) θ θnice σ =
    trans (_*_.snd (nice M θ θnice _ id (eval θ N) (nice N θ θnice)) _ σ)
   (trans (cong (λ α → eval θ M _ σ α) (nice2 N θ θnice σ))
          (cong-app1 (cong-app1 (cong-app1 (nice2 M θ θnice σ) _) id) (eval (σ ◦ θ) N)))
 nice2 (ƛ M) θ θnice σ = funext (λ Δ'' → funext (λ σ' → funext (λ t →
   cong (λ (α : subst _ _) -> eval (extend α t) M) (funext-imp (λ T → funext (λ x → appFunct σ _ (θ x)))))))

_•v_ : ∀ {Γ1 Γ2 Γ3} (σ1 : subst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) -> subst Γ1 Γ3
(σ1 •v σ2) x = σ1 (σ2 x)

blahv : ∀ {Γ1 Γ2 Γ3 T} (σ : subst Γ2 Γ3) (s : sem Γ3 T) (σ' : vsubst Γ1 Γ2) {U} (x : var (Γ1 , T) U)
 -> (((extend σ s) •v (ext σ')) x) ≡ (extend (σ •v σ') s x)
blahv σ t σ' z = refl
blahv σ t σ' (s y) = refl

compv : ∀ {Γ3 T Γ1 Γ2} (σ1 : vsubst Γ1 Γ2) (σ2 : subst Γ2 Γ3) (M : tm Γ1 T) -> (eval σ2 ([ σ1 ]v M)) ≡ (eval (σ2 •v σ1) M)
compv σ1 σ2 (v y) = refl
compv σ1 σ2 (M · N) = cong2 (λ α β' → α _ id β') (compv σ1 σ2 M) (compv σ1 σ2 N)
compv σ1 σ2 (ƛ M) = funext (λ Δ' → funext (λ σ → funext (λ t → trans (compv (ext σ1) (extend (_ ◦ σ2) t) M) (cong (λ (α : subst _ _) → eval α M) (funext-imp (λ T → funext (λ x → blahv (_ ◦ σ2) t σ1 x)))))))

_•_ : ∀ {Γ1 Γ2 Γ3} (σ1 : subst Γ2 Γ3) (σ2 : sub Γ1 Γ2) -> subst Γ1 Γ3
(σ1 • σ2) x = eval σ1 (σ2 x) 

blah : ∀ {Γ1 Γ2 Γ3 T} (σ : subst Γ2 Γ3) (s : sem Γ3 T) (σ' : sub Γ1 Γ2) {U} (x : var (Γ1 , T) U)
 -> (((extend σ s) • (sub-ext σ')) x) ≡ (extend (σ • σ') s x)
blah σ s' σ' z = refl
blah σ s' σ' (s y) = compv s (extend σ s') (σ' y)

blah' : ∀ {Γ1 Γ2 Γ3 T} (σ : subst Γ2 Γ3) (s : sem Γ3 T) (σ' : sub Γ1 Γ2)
 -> _≡_ {subst (Γ1 , T) Γ3} ((extend σ s) • (sub-ext σ')) (extend (σ • σ') s)
blah' σ s' σ' = funext-imp (λ U → funext (λ x → blah σ s' σ' x))

-- this is a kind of functoriality (wrap the M up in extensionality/an equivalence relation)
comp : ∀ {Γ3 T Γ1 Γ2} (σ1 : sub Γ1 Γ2) (σ2 : subst Γ2 Γ3) (θ : niceSubst Γ2 Γ3 σ2) (M : tm Γ1 T)
 -> (eval σ2 ([ σ1 ] M)) ≡ (eval (σ2 • σ1) M)
comp σ1 σ2 θ (v y) = refl
comp {Γ3} σ1 σ2 θ (M · N) = eq-sub2 (λ x y → x Γ3 id y) (comp σ1 σ2 θ M) (comp σ1 σ2 θ N) refl
comp σ1 σ2 θ (ƛ M) = funext (λ Δ' → funext (λ σ → funext (λ x → trans (comp (sub-ext σ1) (extend (_ ◦ σ2) x) (niceExtend (_ ◦n θ) {!!}) M) (cong (λ (α : subst _ _) → eval α M) (funext-imp (λ T → funext (λ x' → trans (blah (_ ◦ σ2) x σ1 x') (cong (λ (α : subst _ _) → extend α x x') (funext-imp (λ U → funext (λ x1 → sym (nice2 (σ1 x1) σ2 θ _))))))))))))

sem-η : ∀ {Γ Δ T S} (M1 : tm Γ (T ⇝ S)) (σ : subst Γ Δ) (θ : niceSubst Γ Δ σ) Δ' (σ' : vsubst Δ Δ') (s' : sem Δ' T) (nice : Pr _ s')
  -> (eval σ M1 Δ' σ' s') ≡ (eval (extend (σ' ◦ σ) s') ([ s ]v M1) Δ' id s')
sem-η M1 σ θ Δ' σ' s' nice = trans (cong-app1 (cong-app1 (cong-app1 (nice2 M1 σ θ σ') _) id) s') (sym (eq-sub1 (λ x' → x' Δ' id s') (compv s (extend (_ ◦ σ) s') M1) refl))

eval-extend : ∀ {Γ Δ T} (σ : subst Γ Δ) (N : tm Γ T) {U} (x : var (Γ , T) U) -> extend σ (eval σ N) x ≡ eval σ ((v ,, N) x)
eval-extend σ N z = refl
eval-extend σ N (s y) = refl

sem-β : ∀ {Γ Δ T S} (M : tm (Γ , T) S) (N : tm Γ T) (σ : subst Γ Δ) (θ : niceSubst Γ Δ σ)
 -> (eval (extend (id ◦ σ) (eval σ N)) M) ≡ (eval σ ([ v ,, N ] M))
sem-β M N σ θ = trans (cong1/2 eval (funext-imp (λ T → funext (λ x → trans (cong (λ (α : subst _ _) → extend α (eval σ N) x) (funext-imp (λ U → funext (λ x' → appFunct-id (σ x'))))) (eval-extend σ N x)))) M) (sym (comp (v ,, N) σ θ M))

-- If we're feeling ambitious we could try to do this without functional extensionality by defining an equivalence
-- relation by induction on the type
soundness : ∀ {Γ Δ T} {M1 M2 : tm Γ T} (σ : subst Γ Δ) (θ : niceSubst Γ Δ σ) -> M1 ≈ M2 -> (eval σ M1) ≡ (eval σ M2)
soundness σ θ (v x) = refl
soundness {Γ} {Δ} σ θ (M · N) = cong-app (cong-app1 (cong-app1 (soundness σ θ M) Δ) id) (soundness σ θ N)
soundness σ θ (ƛ M) = funext (λ Δ → funext (λ wkn → funext (λ x → soundness _ (niceExtend (_ ◦n θ) {!!}) M)))
soundness σ θ (β M N) = sem-β M N σ θ
soundness {Γ} {Δ} {T ⇝ S} {M1} σ θ (η .M1) = funext (λ Δ' → funext (λ σ' → funext (λ s' → sem-η M1 σ θ Δ' _ s' {!!})))

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

soundness' : ∀ {Γ T} {M1 M2 : tm Γ T} -> M1 ≈ M2 -> (nbe M1) ≡ (nbe M2)
soundness' H = cong reify (soundness _ (λ x → reflect-nice2 (v x)) H)

GL : (Γ : ctx) (T : tp) (t : sem Γ T) -> Set
GL Γ (atom A) t = Unit
GL Γ (T ⇝ S) t = (p : sem Γ T) → GL Γ T p → (GL Γ S (t _ id p) * ((napp (reify t) (reify p)) ≡ (reify (t _ id p))))

