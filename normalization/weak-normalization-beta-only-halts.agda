module weak-normalization-beta-only-halts where
open import Relation.Binary.PropositionalEquality hiding ([_])

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

data _+_ (A B : Set) : Set where 
 inl : A -> A + B
 inr : B -> A + B

{-data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x -}

postulate
 funext : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g
 funext-imp : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> _≡_ {_} { {x : A} -> B x} (λ {x} -> f x) (λ {x} -> g x)

cong-app1 : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> f ≡ g -> (x : A) -> f x ≡ g x
cong-app1 refl x = refl

cong-app : ∀ {A B : Set} {f g : A -> B} -> f ≡ g -> {x y : A} -> x ≡ y -> f x ≡ g y
cong-app refl refl = refl 

{-cong : ∀ {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl -}

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

{-trans : ∀ {A} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl -}

{-sym : ∀ {A} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl -}

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
  neut : ∀ {A} -> rtm Γ A -> ntm Γ A


{-sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = ntm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S -}

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


var-dom-eq' : ∀ {A : tp -> Set} {Γ T} (f g : ∀ {U} (x : var (Γ , T) U) -> A U) -> (∀ {U} (x : var Γ U) -> f (s x) ≡ g (s x)) -> f z ≡ g z -> ∀ {U} (x : var (Γ , T) U) -> f x ≡ g x
var-dom-eq' f g p q z = q
var-dom-eq' f g p q (s y) = p y

var-dom-eq : ∀ {A : tp -> Set} {Γ T} {f g : ∀ {U} (x : var (Γ , T) U) -> A U} -> (∀ {U} (x : var Γ U) -> f (s x) ≡ g (s x)) -> f z ≡ g z -> _≡_ {_} { ∀ {U} -> var (Γ , T) U -> A U } f g
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

{-
appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = nappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s -}

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = s

{-
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
-}
data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)

{-
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
-}

[_]v : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_]v σ (v y) = v (σ y)
[_]v σ (M · N) = [ σ ]v M · [ σ ]v N
[_]v σ (ƛ M) = ƛ ([ ext σ ]v M)

sub : (Γ1 Γ2 : ctx) -> Set
sub Γ1 Γ2 = ∀ {T} -> var Γ1 T -> tm Γ2 T

_,,_ : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> tm Γ2 T -> sub (Γ1 , T) Γ2
(σ ,, M) z = M
(σ ,, M) (s y) = σ y

sub-ext : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> sub (Γ1 , T) (Γ2 , T)
sub-ext σ = (λ x -> [ s ]v (σ x)) ,, v z

[_] : ∀ {Γ1 Γ2 T} (σ : sub Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_] σ (v y) = σ y
[_] σ (M · N) = [ σ ] M · [ σ ] N
[_] σ (ƛ M) = ƛ ([ sub-ext σ ] M)


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

sub-ext-idv : ∀ {Γ T U} (x : var (Γ , T) U) -> (ext id) x ≡ x
sub-ext-idv z = refl
sub-ext-idv (s y) = refl

[]v-id : ∀ {Γ T} {M : tm Γ T} -> [ id ]v M ≡ M
[]v-id {M = v y} = refl
[]v-id {M = M · N} = cong2 _·_ []v-id []v-id
[]v-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : vsubst _ _) → [ α ]v M) (funext-imp (λ x → funext (λ x' → sub-ext-idv x')))) []v-id)

sub-ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> (sub-ext v) x ≡ v x
sub-ext-id z = refl
sub-ext-id (s y) = refl

[]-id : ∀ {Γ T} {M : tm Γ T} -> [ v ] M ≡ M
[]-id {M = v y} = refl
[]-id {M = M · N} = cong2 _·_ []-id []-id
[]-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : sub _ _) → [ α ] M) (funext-imp (λ x → funext (λ x' → sub-ext-id x')))) []-id)

[]v-eq-[] : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (t : tm Γ T) -> [ σ ]v t ≡ [ v ∘₁ σ ] t
[]v-eq-[] σ (v y) = refl
[]v-eq-[] σ (y · y') = cong2 _·_ ([]v-eq-[] σ y) ([]v-eq-[] σ y')
[]v-eq-[] σ (ƛ y) = cong ƛ (trans ([]v-eq-[] (ext σ) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → refl) refl))) 

-- Why not just use an explicit substitution calculus?
data _→*_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 v : ∀ {T} (x : var Γ T) -> (v x) →* (v x)
 _·_ : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 N2 : tm Γ T} -> M1 →* M2 -> N1 →* N2 -> (M1 · N1) →* (M2 · N2)
 ƛ : ∀ {T S} {M1 M2 : tm (Γ , T) S} -> M1 →* M2 -> (ƛ M1) →* (ƛ M2)
 β : ∀ {T S} (M : tm (Γ , T) S) (N : tm Γ T) -> ((ƛ M) · N) →* [ v ,, N ] M
-- η : ∀ {T S} (M : tm Γ (T ⇝ S)) -> M →* (ƛ ([ s ]v M · (v z)))
 →*-trans : ∀ {T} {M N P : tm Γ T} -> M →* N -> N →* P -> M →* P

→*≡-trans : ∀ {Γ T} {M N P : tm Γ T} -> M →* N -> N ≡ P -> M →* P
→*≡-trans p refl = p

→*-refl : ∀ {Γ T} {M : tm Γ T} -> M →* M
→*-refl {M = v y} = v y
→*-refl {M = M · N} = →*-refl · →*-refl
→*-refl {M = ƛ M} = ƛ →*-refl

→*-refl' : ∀ {Γ T} {M1 M2 : tm Γ T} -> M1 ≡ M2 -> M1 →* M2
→*-refl' refl = →*-refl

vsimp : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (N : tm Γ T) {U} (x : var (Γ , T) U) -> ((v ,, [ σ ]v N) ∘₁ (ext σ)) x ≡ ([ σ ]v ∘₁ (v ,, N)) x
vsimp σ N z = refl
vsimp σ N (s y) = refl

→*-subst : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) {M1 M2 : tm Γ1 T} -> M1 →* M2 -> [ σ ]v M1 →* [ σ ]v M2
→*-subst σ (v x) = →*-refl
→*-subst σ (y · y') = (→*-subst σ y) · (→*-subst σ y')
→*-subst σ (ƛ y) = ƛ (→*-subst (ext σ) y)
→*-subst σ (β M N) = →*-trans (β _ _) (→*-refl' (trans ([]nv-funct (v ,, [ σ ]v N) (ext σ) M) (trans (cong (λ (α : sub _ _) → [ α ] M) (funext-imp (λ x → funext (λ x' → vsimp σ N x')))) (sym ([]vn-funct σ (v ,, N) M)))))
--→*-subst σ {M1} (η .M1) = →*-trans (η _) (ƛ (→*-refl' (trans ([]v-funct s σ M1) (sym ([]v-funct (ext σ) s M1))) · (v z)))
→*-subst σ (→*-trans y y') = →*-trans (→*-subst σ y) (→*-subst σ y')

mutual
 ninj : ∀ {Γ T} -> ntm Γ T -> tm Γ T
 ninj (ƛ M) = ƛ (ninj M)
 ninj (neut R) = rinj R
 rinj : ∀ {Γ T} -> rtm Γ T -> tm Γ T
 rinj (v x) = v x
 rinj (R · N) = (rinj R) · (ninj N)

mutual
 []v-comm-ninj : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (N : ntm Γ T) -> [ σ ]v (ninj N) ≡ ninj (nappSubst σ N)
 []v-comm-ninj σ (ƛ M) = cong ƛ ([]v-comm-ninj (ext σ) M)
 []v-comm-ninj σ (neut R) = []v-comm-rinj σ R
 []v-comm-rinj : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (R : rtm Γ T) -> [ σ ]v (rinj R) ≡ rinj (rappSubst σ R)
 []v-comm-rinj σ (v y) = refl
 []v-comm-rinj σ (R · N) = cong2 _·_ ([]v-comm-rinj σ R) ([]v-comm-ninj σ N)

halts : ∀ {Γ T} (t : tm Γ T) -> Set
halts {Γ} {T} t = Σ (λ (n : ntm Γ T) → t →* ninj n)

halts-closed : ∀ {T Γ} {t t' : tm Γ T} -> (t →* t') -> halts t' -> halts t
halts-closed p (fst , snd) = fst , (→*-trans p snd)

reduce : ∀ Γ T -> tm Γ T -> Set
reduce Γ (atom A) t = Σ (λ (n : ntm Γ (atom A)) → t →* ninj n)
reduce Γ (T ⇝ S) t = halts t * (∀ Δ (σ : vsubst Γ Δ) (x : tm Δ T) -> reduce Δ T x -> reduce Δ S (([ σ ]v t) · x))

reduce-closed : ∀ {T Γ} {t t' : tm Γ T} -> (t →* t') -> reduce Γ T t' -> reduce Γ T t
reduce-closed {atom A} p h = halts-closed p h
reduce-closed {T ⇝ S} p (h , x) =  halts-closed p h , λ Δ σ x' x0 → reduce-closed (→*-subst σ p · →*-refl) (x Δ σ x' x0)

reduce-ext : ∀ {Γ Δ} {σ : ∀ {U} (x : var Γ U) -> tm Δ U} (θ : ∀ {U} (x : var Γ U) -> reduce Δ U (σ x)) {T} {t : tm Δ T} (w : reduce Δ T t) ->
 ∀ {U} (x : var (Γ , T) U) -> reduce Δ U ((σ ,, t) x)
reduce-ext θ w z = w
reduce-ext θ w (s y) = θ y

halts-funct : ∀ {T Γ Δ} (σ : vsubst Γ Δ) {t : tm Γ T} (w : halts t) -> halts ([ σ ]v t)
halts-funct σ (N , p) = (nappSubst σ N) , (eq-ind (_→*_ ([ σ ]v _)) ([]v-comm-ninj σ N) (→*-subst σ p))

reduce-funct : ∀ {T Γ Δ} (σ : vsubst Γ Δ) {t : tm Γ T} (w : reduce Γ T t) -> reduce Δ T ([ σ ]v t)
reduce-funct {atom A} σ h = halts-funct σ h
reduce-funct {T ⇝ S} σ (h , w) = halts-funct σ h , λ Δ σ' x x' → eq-ind (reduce Δ S) (cong2 _·_ (sym ([]v-funct σ' σ _)) refl) (w Δ (σ' ∘ σ) x x')

mutual
 reflect : ∀ {T Γ} (r : rtm Γ T) -> reduce Γ T (rinj r)
 reflect {atom A} r = (neut r) , →*-refl
 reflect {T ⇝ S} r = ((neut r) , →*-refl) , λ Δ σ x x' -> reduce-closed (→*-refl · (Σ.snd (reify x x'))) (eq-ind (reduce Δ S) (cong2 _·_ (sym ([]v-comm-rinj σ r)) refl) (reflect (rappSubst σ r · Σ.fst (reify x x'))))

 reify : ∀ {T Γ} (t : tm Γ T) -> reduce Γ T t -> halts t
 reify {atom A} t p = p
 reify {T ⇝ S} t (p , _) = p 


halts-ƛ : ∀ {Γ T S} {M : tm (Γ , T) S} -> halts M -> halts (ƛ M)
halts-ƛ (N , p) = (ƛ N) , (ƛ p)

thm : ∀ {Γ Δ T} (σ : ∀ {U} (x : var Γ U) -> tm Δ U) (θ : ∀ {U} (x : var Γ U) -> reduce Δ U (σ x)) (t : tm Γ T) -> reduce Δ T ([ σ ] t)
thm σ θ (v y) = θ y
thm σ θ (M · N) = eq-ind (reduce _ _) (cong2 _·_ []v-id refl) ((_*_.snd (thm σ θ M)) _ id ([ σ ] N) (thm σ θ N))
thm σ θ (ƛ M) with thm (sub-ext σ) (reduce-ext (λ x0 -> reduce-funct s (θ x0)) (reflect (v z))) M
... | q = halts-ƛ (reify _ q) , (λ Δ σ' x x' → reduce-closed (β _ _) (eq-ind (reduce Δ _)
  (trans (trans (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x0 → trans ([]v-eq-[] σ' (σ x0))
    (sym ([]nv-funct ((v ,, x) ∘₁ ext σ') s (σ x0)))) refl))
    (sym ([]-funct   ((v ,, x) ∘₁ ext σ') (sub-ext σ) M)))
    (sym ([]nv-funct  (v ,, x) (ext σ') ([ sub-ext σ ] M))))
  (thm (([ σ' ]v ∘₁ σ) ,, x) (reduce-ext (λ x0 → reduce-funct σ' (θ x0)) x') M)))

done : ∀ {Γ T} (t : tm Γ T) -> halts t
done t = reify t (eq-ind (reduce _ _) []-id (thm v (λ x → reflect (v x)) t))

{- Compare to (nbe/)weak-normalization-beta-only
   Conclusion: it's more natural to include "halts" in the ⇝ case of reducibility than it is to do M x halts implies M halts
