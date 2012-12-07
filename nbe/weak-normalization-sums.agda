module weak-normalization-sums where
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

postulate
 funext : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g
 funext-imp : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> _≡_ {_} { {x : A} -> B x} (λ {x} -> f x) (λ {x} -> g x)

cong-app1 : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> f ≡ g -> (x : A) -> f x ≡ g x
cong-app1 refl x = refl

cong-app : ∀ {A B : Set} {f g : A -> B} -> f ≡ g -> {x y : A} -> x ≡ y -> f x ≡ g y
cong-app refl refl = refl 

cong1/2 : ∀ {A B C : Set} (f : A -> B -> C) -> {x y : A} -> x ≡ y -> (z : B) -> f x z ≡ f y z
cong1/2 f refl z = refl 

cong2 : ∀ {A B C : Set} (f : A -> B -> C) -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> f x z ≡ f y w
cong2 f refl refl = refl

eq-ind : ∀ {A : Set} (P : A -> Set) -> {x y : A} -> x ≡ y -> P x -> P y
eq-ind P refl t = t 

eq-ind2 : ∀ {A B : Set} (P : A -> B -> Set) -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> P x z -> P y w
eq-ind2 P refl refl t = t

eq-sub1 : ∀ {A C : Set} (P : A -> C) {t} -> {x y : A} -> x ≡ y -> P y ≡ t -> P x ≡ t
eq-sub1 P refl p = p 

eq-sub2 : ∀ {A B C : Set} (P : A -> B -> C) {t} -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> P y w ≡ t -> P x z ≡ t
eq-sub2 P refl refl p = p

record Unit : Set where
 constructor tt

postulate
 atomic_tp : Set

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp
 _+_ : (T S : tp) -> tp

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
  case : ∀ {T S C} -> rtm Γ (T + S) -> ntm (Γ , T) C -> ntm (Γ , S) C -> rtm Γ C
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ A -> ntm Γ A
  inl : ∀ {T S} -> ntm Γ T -> ntm Γ (T + S)
  inr : ∀ {T S} -> ntm Γ S -> ntm Γ (T + S)


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
 rappSubst σ (case M N1 N2) = {!!}
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)
 nappSubst σ (inl M) = {!!}
 nappSubst σ (inr M) = inr {!!}

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
 rappSubst-funct σ1 σ2 (case M N1 N2) = {!!}
 nappSubst-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (N : ntm Γ1 S)
  -> nappSubst σ1 (nappSubst σ2 N) ≡ nappSubst (σ1 ∘ σ2) N
 nappSubst-funct σ1 σ2 (ƛ N) = cong ƛ (trans (nappSubst-funct (ext σ1) (ext σ2) N) (cong (λ (α : vsubst _ _) → nappSubst α N) (funext-imp (λ U → funext (λ x' → ext-funct σ1 σ2 x')))))
 nappSubst-funct σ1 σ2 (neut R) = cong neut (rappSubst-funct σ1 σ2 R)
 nappSubst-funct σ1 σ2 (inl M) = {!!}
 nappSubst-funct σ1 σ2 (inr M) = {!!}

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> ext id x ≡ x
ext-id z = refl
ext-id (s y) = refl

mutual
 rappSubst-id : ∀ {Γ S} (R : rtm Γ S) -> rappSubst id R ≡ R
 rappSubst-id (v y) = refl
 rappSubst-id (R · N) = cong2 _·_ (rappSubst-id R) (nappSubst-id N)
 rappSubst-id (case M N1 N2) = {!!}
 nappSubst-id : ∀ {Γ S} (N : ntm Γ S) -> nappSubst id N ≡ N
 nappSubst-id (ƛ N) = cong ƛ (trans (cong (λ (α : vsubst _ _) → nappSubst α N) (funext-imp (λ U → funext (λ x → ext-id x)))) (nappSubst-id N))
 nappSubst-id (neut R) = cong neut (rappSubst-id R)
 nappSubst-id (inl M) = {!!}
 nappSubst-id (inr M) = {!!}

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = s

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 inl : ∀ {T S} -> tm Γ T -> tm Γ (T + S)
 inr : ∀ {T S} -> tm Γ S -> tm Γ (T + S)
 case : ∀ {T S C} -> tm Γ (T + S) -> tm (Γ , T) C -> tm (Γ , S) C -> tm Γ C

[_]v : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_]v σ (v y) = v (σ y)
[_]v σ (M · N) = [ σ ]v M · [ σ ]v N
[_]v σ (ƛ M) = ƛ ([ ext σ ]v M)
[ σ ]v (case M N1 N2) = case ([ σ ]v M) ([ ext σ ]v N1) ([ ext σ ]v N2)
[ σ ]v (inl M) = inl ([ σ ]v M)
[ σ ]v (inr M) = inr ([ σ ]v M)

sub : (Γ1 Γ2 : ctx) -> Set
sub Γ1 Γ2 = ∀ {T} -> var Γ1 T -> tm Γ2 T

sub-ext : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> sub (Γ1 , T) (Γ2 , T)
sub-ext σ z = v z
sub-ext σ (s y) = [ s ]v (σ y)

[_] : ∀ {Γ1 Γ2 T} (σ : sub Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_] σ (v y) = σ y
[_] σ (M · N) = [ σ ] M · [ σ ] N
[_] σ (ƛ M) = ƛ ([ sub-ext σ ] M)
[ σ ] (case M N1 N2) = case ([ σ ] M) ([ sub-ext σ ] N1) ([ sub-ext σ ] N2)
[ σ ] (inl M) = inl ([ σ ] M)
[ σ ] (inr M) = inr ([ σ ] M)

_,,_ : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> tm Γ2 T -> sub (Γ1 , T) Γ2
(σ ,, M) z = M
(σ ,, M) (s y) = σ y

[]v-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]v ([ σ2 ]v R) ≡ [ σ1 ∘ σ2 ]v R
[]v-funct σ1 σ2 (v y) = refl
[]v-funct σ1 σ2 (y · y') = cong2 _·_ ([]v-funct σ1 σ2 y) ([]v-funct σ1 σ2 y')
[]v-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]v-funct (ext σ1) (ext σ2) y) (cong (λ (α : vsubst _ _) → [ α ]v y) (var-dom-eq (λ x → refl) refl)))
[]v-funct σ1 σ2 _ = {!!}

[]vn-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]v ([ σ2 ] R) ≡ [ [ σ1 ]v ∘₁ σ2 ] R
[]vn-funct σ1 σ2 (v y) = refl
[]vn-funct σ1 σ2 (y · y') = cong2 _·_ ([]vn-funct σ1 σ2 y) ([]vn-funct σ1 σ2 y')
[]vn-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]vn-funct (ext σ1) (sub-ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → trans ([]v-funct (ext σ1) s (σ2 x)) (sym ([]v-funct s σ1 (σ2 x)))) refl)))
[]vn-funct σ1 σ2 _ = {!!}

[]nv-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ]v R) ≡ [ σ1 ∘₁ σ2 ] R
[]nv-funct σ1 σ2 (v y) = refl
[]nv-funct σ1 σ2 (y · y') = cong2 _·_ ([]nv-funct σ1 σ2 y) ([]nv-funct σ1 σ2 y')
[]nv-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]nv-funct (sub-ext σ1) (ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → refl) refl)))
[]nv-funct σ1 σ2 _ = {!!}

[]-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ] R) ≡ [ [ σ1 ] ∘₁ σ2 ] R
[]-funct σ1 σ2 (v y) = refl
[]-funct σ1 σ2 (y · y') = cong2 _·_ ([]-funct σ1 σ2 y) ([]-funct σ1 σ2 y')
[]-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]-funct (sub-ext σ1) (sub-ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → trans ([]nv-funct (sub-ext σ1) s (σ2 x)) (sym ([]vn-funct s σ1 (σ2 x)))) refl)))
[]-funct σ1 σ2 _ = {!!}

sub-ext-idv : ∀ {Γ T U} (x : var (Γ , T) U) -> (ext id) x ≡ x
sub-ext-idv z = refl
sub-ext-idv (s y) = refl

[]v-id : ∀ {Γ T} {M : tm Γ T} -> [ id ]v M ≡ M
[]v-id {M = v y} = refl
[]v-id {M = M · N} = cong2 _·_ []v-id []v-id
[]v-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : vsubst _ _) → [ α ]v M) (funext-imp (λ x → funext (λ x' → sub-ext-idv x')))) []v-id)
[]v-id {M = _} = {!!}

sub-ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> (sub-ext v) x ≡ v x
sub-ext-id z = refl
sub-ext-id (s y) = refl

[]-id : ∀ {Γ T} {M : tm Γ T} -> [ v ] M ≡ M
[]-id {M = v y} = refl
[]-id {M = M · N} = cong2 _·_ []-id []-id
[]-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : sub _ _) → [ α ] M) (funext-imp (λ x → funext (λ x' → sub-ext-id x')))) []-id)
[]-id {M = M} = {!!}

[]v-eq-[] : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (t : tm Γ T) -> [ σ ]v t ≡ [ v ∘₁ σ ] t
[]v-eq-[] σ (v y) = refl
[]v-eq-[] σ (y · y') = cong2 _·_ ([]v-eq-[] σ y) ([]v-eq-[] σ y')
[]v-eq-[] σ (ƛ y) = cong ƛ (trans ([]v-eq-[] (ext σ) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → refl) refl))) 
[]v-eq-[] σ _ = {!!}


data _→₁_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 _·_ : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 N2 : tm Γ T} -> M1 →₁ M2 -> N1 →₁ N2 -> (M1 · N1) →₁ (M2 · N2)
 ƛ : ∀ {T S} {M1 M2 : tm (Γ , T) S} -> M1 →₁ M2 -> (ƛ M1) →₁ (ƛ M2)
 β : ∀ {T S} (M : tm (Γ , T) S) (N : tm Γ T) -> ((ƛ M) · N) →₁ [ v ,, N ] M
 η : ∀ {T S} (M : tm Γ (T ⇝ S)) -> M →₁ (ƛ ([ s ]v M · (v z)))

-- Why not just use an explicit substitution calculus?
data _→*_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 v : ∀ {T} (x : var Γ T) -> (v x) →* (v x)
 _·_ : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 N2 : tm Γ T} -> M1 →* M2 -> N1 →* N2 -> (M1 · N1) →* (M2 · N2)
 ƛ : ∀ {T S} {M1 M2 : tm (Γ , T) S} -> M1 →* M2 -> (ƛ M1) →* (ƛ M2)
 β : ∀ {T S} (M : tm (Γ , T) S) (N : tm Γ T) -> ((ƛ M) · N) →* [ v ,, N ] M
 η : ∀ {T S} (M : tm Γ (T ⇝ S)) -> M →* (ƛ ([ s ]v M · (v z)))
 →*-trans : ∀ {T} {M N P : tm Γ T} -> M →* N -> N →* P -> M →* P
 inl : ∀ {S T} {M M' : tm Γ T} (s : M →* M')         -> (inl {_} {T} {S} M) →* (inl M')
 inr : ∀ {T S} {M M' : tm Γ S} (s : M →* M')         -> (inr {_} {T} M) →* (inr M')
 case : ∀ {T S C} {M M' : tm Γ (T + S)} (S : M →* M') {N1 N1' : tm (Γ , T) C} (S1 : N1 →* N1') {N2 N2'} (S2 : N2 →* N2')
   -> (case M N1 N2) →* (case M' N1' N2')
 β+₁ : ∀ {T S C} (M : tm _ T) (N1 : tm (Γ , T) C) (N2 : tm (Γ , S) C) -> (case (inl M) N1 N2) →* [ v ,, M ] N1
 β+₂ : ∀ {T S C} (M : tm _ S) (N1 : tm (Γ , T) C) (N2 : tm (Γ , S) C) -> (case (inr M) N1 N2) →* [ v ,, M ] N2

→*-refl : ∀ {Γ T} {M : tm Γ T} -> M →* M
→*-refl {M = v y} = v y
→*-refl {M = M · N} = →*-refl · →*-refl
→*-refl {M = ƛ M} = ƛ →*-refl
→*-refl {M = M} = {!!}

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
→*-subst σ {M1} (η .M1) = →*-trans (η _) (ƛ (→*-refl' (trans ([]v-funct s σ M1) (sym ([]v-funct (ext σ) s M1))) · (v z)))
→*-subst σ (→*-trans y y') = →*-trans (→*-subst σ y) (→*-subst σ y')
→*-subst σ q = {!!}

mutual
 ninj : ∀ {Γ T} -> ntm Γ T -> tm Γ T
 ninj (ƛ M) = ƛ (ninj M)
 ninj (neut R) = rinj R
 ninj (inl y) = inl (ninj y)
 ninj (inr y) = inr (ninj y)
 rinj : ∀ {Γ T} -> rtm Γ T -> tm Γ T
 rinj (v x) = v x
 rinj (R · N) = (rinj R) · (ninj N)
 rinj (case y y' y0) = case (rinj y) (ninj y') (ninj y0)

mutual
 []v-comm-ninj : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (N : ntm Γ T) -> [ σ ]v (ninj N) ≡ ninj (nappSubst σ N)
 []v-comm-ninj σ (ƛ M) = cong ƛ ([]v-comm-ninj (ext σ) M)
 []v-comm-ninj σ (neut R) = []v-comm-rinj σ R
 []v-comm-ninj σ M = {!!}
 []v-comm-rinj : ∀ {Γ Δ T} (σ : vsubst Γ Δ) (R : rtm Γ T) -> [ σ ]v (rinj R) ≡ rinj (rappSubst σ R)
 []v-comm-rinj σ (v y) = refl
 []v-comm-rinj σ (R · N) = cong2 _·_ ([]v-comm-rinj σ R) ([]v-comm-ninj σ N)
 []v-comm-rinj σ M = {!!}

halts : ∀ {Γ T} (t : tm Γ T) -> Set
halts {Γ} {T} t = Σ (λ (n : ntm Γ T) → t →* ninj n)

data closure {Γ T} (R : tm Γ T -> Set) : (t : tm Γ T) -> Set where
 ▹ : ∀ t -> R t -> closure R t
 step : ∀ t t' -> t →* t' -> closure R t' -> closure R t
 neut : ∀ t r -> t ≡ rinj r -> closure R t

open import Data.Sum

reduce : ∀ Γ T -> tm Γ T -> Set
reduce Γ (atom A) t = Σ (λ (n : ntm Γ (atom A)) → t →* ninj n)
reduce Γ (T ⇝ S) t = ∀ Δ (σ : vsubst Γ Δ) (x : tm Δ T) -> reduce Δ T x -> reduce Δ S (([ σ ]v t) · x)
reduce Γ (T + S) t = closure (λ t' → (Σ (λ x → (t' ≡ inl x) * reduce Γ T x)) ⊎ Σ (λ x → (t' ≡ inr x) * reduce Γ S x)) t

reduce-closed : ∀ {T Γ} {t t' : tm Γ T} -> (t →* t') -> reduce Γ T t' -> reduce Γ T t
reduce-closed {atom A} p (N , q) = N , (→*-trans p q)
reduce-closed {T ⇝ S} p x = λ Δ σ x' x0 → reduce-closed (→*-subst σ p · →*-refl) (x Δ σ x' x0)
reduce-closed {T + S} p r = step _ _ p r

reduce-ext : ∀ {Γ Δ} {σ : ∀ {U} (x : var Γ U) -> tm Δ U} (θ : ∀ {U} (x : var Γ U) -> reduce Δ U (σ x)) {T} {t : tm Δ T} (w : reduce Δ T t) ->
 ∀ {U} (x : var (Γ , T) U) -> reduce Δ U ((σ ,, t) x)
reduce-ext θ w z = w
reduce-ext θ w (s y) = θ y

reduce-funct : ∀ {T Γ Δ} (σ : vsubst Γ Δ) {t : tm Γ T} (w : reduce Γ T t) -> reduce Δ T ([ σ ]v t)
reduce-funct {atom A} σ (N , p) = (nappSubst σ N) , (eq-ind (_→*_ ([ σ ]v _)) ([]v-comm-ninj σ N) (→*-subst σ p))
reduce-funct {T ⇝ S} σ w = λ Δ σ' x x' → eq-ind (reduce Δ S) (cong2 _·_ (sym ([]v-funct σ' σ _)) refl) (w Δ (σ' ∘ σ) x x')
reduce-funct {T + S} σ w = {!!}

mutual
 reflect : ∀ {T Γ} (r : rtm Γ T) -> reduce Γ T (rinj r)
 reflect {atom A} r = (neut r) , →*-refl
 reflect {T ⇝ S} r = λ Δ σ x x' -> reduce-closed (→*-refl · (Σ.snd (reify x x'))) (eq-ind (reduce Δ S) (cong2 _·_ (sym ([]v-comm-rinj σ r)) refl) (reflect (rappSubst σ r · Σ.fst (reify x x'))))
 reflect {T + S} r = neut (rinj r) r refl

 reify : ∀ {T Γ} (t : tm Γ T) -> reduce Γ T t -> halts t
 reify {atom A} t p = p
 reify {T ⇝ S} t p with reify ([ s ]v t · v z) (p (_ , _) s (v z) (reflect (v z)))
 reify {T ⇝ S} t p | N , q = (ƛ N) , (→*-trans (η t) (ƛ q))
 reify {T + S} .(inl fst) (▹ .(inl fst) (inj₁ (fst , (refl , snd)))) with reify fst snd
 reify {T + S} {Γ} .(inl fst) (▹ .(inl fst) (inj₁ (fst , (refl , snd)))) | fst' , snd' = (inl fst') , inl snd'
 reify {T + S} .(inr fst) (▹ .(inr fst) (inj₂ (fst , (refl , snd)))) with reify fst snd
 ... | fst' , snd' = (inr fst') , inr snd'
 reify {T + S} t (step .t t' y y') with reify t' y'
 reify {T + S} t (step .t t' y y') | fst , snd = fst , (→*-trans y snd)
 reify {T + S} .(rinj r) (neut .(rinj r) r refl) = (neut r) , →*-refl

mutual
 thm : ∀ {Γ Δ T} (σ : ∀ {U} (x : var Γ U) -> tm Δ U) (θ : ∀ {U} (x : var Γ U) -> reduce Δ U (σ x)) (t : tm Γ T) -> reduce Δ T ([ σ ] t)
 thm σ θ (v y) = θ y
 thm σ θ (M · N) = eq-ind (reduce _ _) (cong2 _·_ []v-id refl) ((thm σ θ M) _ id ([ σ ] N) (thm σ θ N))
 thm σ θ (ƛ M) = λ Δ σ' x x' → reduce-closed (β _ _) (eq-ind (reduce Δ _)
  (trans (trans (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x0 → trans ([]v-eq-[] σ' (σ x0))
    (sym ([]nv-funct ((v ,, x) ∘₁ ext σ') s (σ x0)))) refl))
    (sym ([]-funct   ((v ,, x) ∘₁ ext σ') (sub-ext σ) M)))
    (sym ([]nv-funct  (v ,, x) (ext σ') ([ sub-ext σ ] M))))
  (thm (([ σ' ]v ∘₁ σ) ,, x) (reduce-ext (λ x0 → reduce-funct σ' (θ x0)) x') M))
 thm σ θ (inl y) = ▹ _ (inj₁ (_ , (refl , thm σ θ y)))
 thm σ θ (inr y) = ▹ _ (inj₂ (_ , (refl , (thm σ θ y))))
 thm σ θ (case y y' y0) with thm σ θ y
 thm {Γ} {Δ} {T} σ θ (case y y0 y1) | ▹ .([ σ ] y) (inj₁ (fst , (fst' , snd))) =
  eq-ind  (λ α → reduce Δ T (case α ([ sub-ext σ ] y0) ([ sub-ext σ ] y1)))
   (sym fst')
   (reduce-closed (β+₁ fst _ _) (eq-ind (reduce Δ T) {!!} (thm (σ ,, fst) (reduce-ext θ snd) y0)))
 thm σ θ (case y y0 y1) | ▹ .([ σ ] y) (inj₂ y') = {!!}
 thm σ θ (case y y1 y2) | step .([ σ ] y) t' y' y0 = reduce-closed (case y' →*-refl →*-refl) {!!}
 thm {Γ} {Δ} {T} σ θ (case y y0 y1) | neut .([ σ ] y) r y' with reify _ (thm (sub-ext σ) {!!} y0) | reify _ (thm (sub-ext σ) {!!} y1)
 ... | q1 , q1' | q2 , q2' = reduce-closed (case →*-refl q1' q2') (eq-ind (λ α → reduce Δ T (case α (ninj q1) (ninj q2))) (sym y') (reflect (case r q1 q2)))


done : ∀ {Γ T} (t : tm Γ T) -> halts t
done t = reify t (eq-ind (reduce _ _) []-id (thm v (λ x → reflect (v x)) t))

done' : ∀ {T} (t : tm ⊡ T) -> halts t
done' t = reify _ (eq-ind (reduce _ _) []-id (thm v (λ ()) t))