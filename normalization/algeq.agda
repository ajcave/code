module algeq where
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Function

-- Based on Ch 6 of Advanced Topics in Types and Programming Languages

postulate
 funext : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g
 funext-imp : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> _≡_ {_} { {x : A} -> B x} (λ {x} -> f x) (λ {x} -> g x)

record Unit : Set where
 constructor tt

postulate
 atomic_tp : Set

data tp : Set where
 atom : tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

vsubst : ctx -> ctx -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U

↑ : ∀ {Γ T} -> vsubst Γ (Γ , T)
↑ = s

-- _∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
-- (σ1 ∘ σ2) x = σ1 (σ2 x)

_∘₁_ : ∀ {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘₁ g) x = f (g x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

var-dom-eq' : ∀ {A : tp -> Set} {Γ T} (f g : ∀ {U} (x : var (Γ , T) U) -> A U) -> (∀ {U} (x : var Γ U) -> f (s x) ≡ g (s x)) -> f z ≡ g z -> ∀ {U} (x : var (Γ , T) U) -> f x ≡ g x
var-dom-eq' f g p q z = q
var-dom-eq' f g p q (s y) = p y

var-dom-eq : ∀ {A : tp -> Set} {Γ T} {f g : ∀ {U} (x : var (Γ , T) U) -> A U} -> (∀ {U} (x : var Γ U) -> f (s x) ≡ g (s x)) -> f z ≡ g z -> _≡_ {_} { ∀ {U} -> var (Γ , T) U -> A U } f g
var-dom-eq {f = f} {g = g} p q = funext-imp (λ U -> funext (λ x -> var-dom-eq' f g p q x))

ext-funct : ∀ {Γ1 Γ2 Γ3 U S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (x : var (Γ1 , U) S) -> ((ext σ1) ∘ (ext σ2)) x ≡ ext (σ1 ∘ σ2) x
ext-funct σ1 σ2 z = refl
ext-funct σ1 σ2 (s y) = refl

-- id : ∀ {Γ} -> vsubst Γ Γ
-- id x = x

ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> ext id x ≡ x
ext-id z = refl
ext-id (s y) = refl

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = s

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 c : tm Γ atom

[_]v : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_]v σ (v y) = v (σ y)
[_]v σ (M · N) = [ σ ]v M · [ σ ]v N
[_]v σ (ƛ M) = ƛ ([ ext σ ]v M)
[ σ ]v c = c

sub : (Γ1 Γ2 : ctx) -> Set
sub Γ1 Γ2 = ∀ {T} -> var Γ1 T -> tm Γ2 T

_,,_ : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> tm Γ2 T -> sub (Γ1 , T) Γ2
(σ ,, M) z = M
(σ ,, M) (s y) = σ y

sub-ext : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> sub (Γ1 , T) (Γ2 , T)
sub-ext σ = ([ ↑ ]v ∘ σ) ,, (v z)

[_] : ∀ {Γ1 Γ2 T} (σ : sub Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_] σ (v y) = σ y
[_] σ (M · N) = [ σ ] M · [ σ ] N
[_] σ (ƛ M) = ƛ ([ sub-ext σ ] M)
[ σ ] c = c


[]v-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]v ([ σ2 ]v R) ≡ [ σ1 ∘ σ2 ]v R
[]v-funct σ1 σ2 (v y) = refl
[]v-funct σ1 σ2 (y · y') = cong₂ _·_ ([]v-funct σ1 σ2 y) ([]v-funct σ1 σ2 y')
[]v-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]v-funct (ext σ1) (ext σ2) y) (cong (λ (α : vsubst _ _) → [ α ]v y) (var-dom-eq (λ x → refl) refl)))
[]v-funct σ1 σ2 c = refl

[]vn-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]v ([ σ2 ] R) ≡ [ [ σ1 ]v ∘₁ σ2 ] R
[]vn-funct σ1 σ2 (v y) = refl
[]vn-funct σ1 σ2 (y · y') = cong₂ _·_ ([]vn-funct σ1 σ2 y) ([]vn-funct σ1 σ2 y')
[]vn-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]vn-funct (ext σ1) (sub-ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → trans ([]v-funct (ext σ1) s (σ2 x)) (sym ([]v-funct s σ1 (σ2 x)))) refl)))
[]vn-funct σ1 σ2 c = refl

[]nv-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ]v R) ≡ [ σ1 ∘₁ σ2 ] R
[]nv-funct σ1 σ2 (v y) = refl
[]nv-funct σ1 σ2 (y · y') = cong₂ _·_ ([]nv-funct σ1 σ2 y) ([]nv-funct σ1 σ2 y')
[]nv-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]nv-funct (sub-ext σ1) (ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → refl) refl)))
[]nv-funct σ1 σ2 c = refl

[]-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ] R) ≡ [ [ σ1 ] ∘₁ σ2 ] R
[]-funct σ1 σ2 (v y) = refl
[]-funct σ1 σ2 (y · y') = cong₂ _·_ ([]-funct σ1 σ2 y) ([]-funct σ1 σ2 y')
[]-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]-funct (sub-ext σ1) (sub-ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → trans ([]nv-funct (sub-ext σ1) s (σ2 x)) (sym ([]vn-funct s σ1 (σ2 x)))) refl)))
[]-funct σ1 σ2 c = refl

sub-ext-idv : ∀ {Γ T U} (x : var (Γ , T) U) -> (ext id) x ≡ x
sub-ext-idv z = refl
sub-ext-idv (s y) = refl

[]v-id : ∀ {Γ T} {M : tm Γ T} -> [ id ]v M ≡ M
[]v-id {M = v y} = refl
[]v-id {M = M · N} = cong₂ _·_ []v-id []v-id
[]v-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : vsubst _ _) → [ α ]v M) (funext-imp (λ x → funext (λ x' → sub-ext-idv x')))) []v-id)
[]v-id {M = c} = refl

sub-ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> (sub-ext v) x ≡ v x
sub-ext-id z = refl
sub-ext-id (s y) = refl

[]-id : ∀ {Γ T} {M : tm Γ T} -> [ v ] M ≡ M
[]-id {M = v y} = refl
[]-id {M = M · N} = cong₂ _·_ []-id []-id
[]-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : sub _ _) → [ α ] M) (funext-imp (λ x → funext (λ x' → sub-ext-id x')))) []-id)
[]-id {M = c} = refl

data _▹wh_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 ap1 : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 : tm _ T} -> M1 ▹wh M2  -> (M1 · N1) ▹wh (M2 · N1)
 β : ∀ {T S} (M : tm (Γ , T) S) (N : tm Γ T) -> ((ƛ M) · N) ▹wh [ v ,, N ] M

data _→*_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 →*-refl : ∀ {T} {M : tm Γ T} -> M →* M
 →*-trans1 : ∀ {T} {M N P : tm _ T} -> M ▹wh N -> N →* P -> M →* P

→*-trans : ∀ {Γ T} {M N P : tm Γ T} -> M →* N -> N →* P -> M →* P
→*-trans →*-refl u = u
→*-trans (→*-trans1 x t) u = →*-trans1 x (→*-trans t u)

ap1* : ∀ {T S} {M1 M2 : tm ⊡ (T ⇝ S)} {N1 : tm _ T} -> M1 →* M2  -> (M1 · N1) →* (M2 · N1)
ap1* →*-refl = →*-refl
ap1* (→*-trans1 x x₁) = →*-trans1 (ap1 x) (ap1* x₁)

β* : ∀ {T S} {M : tm (⊡ , T) S} {N : tm ⊡ T} -> ((ƛ M) · N) →* [ v ,, N ] M
β* = →*-trans1 (β _ _) →*-refl

data isNormal {Γ} : ∀ {T} (t : tm Γ T) -> Set where
 ƛ : ∀ {T S} (t : tm (Γ , T) S) -> isNormal (ƛ t)
 c : isNormal c

data _⇓_ {Γ T} (M : tm Γ T) : tm Γ T -> Set where
 eval : ∀ {N} -> M →* N -> isNormal N -> M ⇓ N

halts : ∀ {T} (t : tm ⊡ T) -> Set
halts {T} t = ∃ (λ (n : tm _ T) → (t →* n) × isNormal n)

mutual
 data _⊢_>_⇔_ Γ : ∀ T -> tm Γ T -> tm Γ T -> Set where
  qat-base : ∀ {M N P Q} -> M ⇓ P -> N ⇓ Q -> Γ ⊢ atom > P ↔ Q -> Γ ⊢ atom > M ⇔ N
  qat-arrow : ∀ {T₁ T₂} {M N : tm Γ (T₁ ⇝ T₂)} -> (Γ , T₁) ⊢ T₂ > [ ↑ ]v M · (v z) ⇔ ([ ↑ ]v N · (v z))
             -> Γ ⊢ (T₁ ⇝ T₂) > M ⇔ N
 data _⊢_>_↔_ Γ : ∀ T -> tm Γ T -> tm Γ T -> Set where
  qap-var : ∀ {T} {x : var Γ T} -> Γ ⊢ T > (v x) ↔ (v x)
  qap-app : ∀ {T₁ T₂} {M₁ M₂ : tm Γ (T₁ ⇝ T₂)} {N₁ N₂ : tm Γ T₁}
           -> Γ ⊢ (T₁ ⇝ T₂) > M₁ ↔ M₂
           -> Γ ⊢ T₁ > N₁ ⇔ N₂
           -> Γ ⊢ T₂ > (M₁ · N₁) ↔ (M₂ · N₂)
  qap-const : Γ ⊢ atom > c ↔ c

_⊢_>_is_ : ∀ Γ T -> tm Γ T -> tm Γ T -> Set
Γ ⊢ atom > M₁ is M₂ = Γ ⊢ atom > M₁ ⇔ M₂
Γ ⊢ T₁ ⇝ T₂ > M₁ is M₂ = ∀ {Γ'} (w : vsubst Γ Γ') {N₁ N₂ : tm Γ' T₁} →
                           Γ' ⊢ T₁ > N₁ is N₂ → Γ' ⊢ T₂ > [ w ]v M₁ · N₁ is ([ w ]v M₂ · N₂)

cong⊢>is : ∀ {Γ T} {M1 M2 N1 N2} -> M1 ≡ N1 -> M2 ≡ N2 -> Γ ⊢ T > M1 is M2 -> Γ ⊢ T > N1 is N2
cong⊢>is refl refl p = p

monotone : ∀ {Γ Γ'} (w : vsubst Γ Γ') T {M₁ M₂} -> Γ ⊢ T > M₁ is M₂ -> Γ' ⊢ T > ([ w ]v M₁) is ([ w ]v M₂)
monotone w atom p = {!!}
monotone w (T₁ ⇝ T₂) {M₁} {M₂} p = λ w₁ {N₁ N₂} x → cong⊢>is (cong (λ α → α · N₁) (sym ([]v-funct w₁ w M₁)))
                                                          (cong (λ α → α · N₂) (sym ([]v-funct w₁ w M₂)))
                                                 (p (w₁ ∘ w) x)

-- reduce : ∀ T -> tm ⊡ T -> Set
-- reduce atom t = halts t
-- reduce (T ⇝ S) t = halts t × (∀ (x : tm _ T) -> reduce T x -> reduce S (t · x))

-- reduce-closed : ∀ {T} {t t' : tm _ T} -> (t →* t') -> reduce T t' -> reduce T t
-- reduce-closed {atom} p (N , (q1 , q2)) = N , ((→*-trans p q1) , q2)
-- reduce-closed {T ⇝ S} p ((N , (q1 , q2)) , f) = (N , (→*-trans p q1 , q2)) , (λ x rx → reduce-closed (ap1* p) (f x rx))

-- reduce-ext : ∀ {Γ} {σ : ∀ {U} (x : var Γ U) -> tm _ U} (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) {T} {t : tm _ T} (w : reduce T t) ->
--  ∀ {U} (x : var (Γ , T) U) -> reduce U ((σ ,, t) x)
-- reduce-ext θ w z = w
-- reduce-ext θ w (s y) = θ y

-- lemma : ∀ {Γ Δ T S} -> (σ : sub Γ Δ) -> ∀ (N : tm Δ T) (M : tm (Γ , T) S) -> [ σ ,, N ] M ≡ [ v ,, N ] ([ sub-ext σ ] M)
-- lemma σ N M = trans (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x → trans (sym []-id) (sym ([]nv-funct (v ,, N) s (σ x)))) refl)) (sym ([]-funct (v ,, N) (sub-ext σ) M))

-- thm : ∀ {Γ T} (σ : ∀ {U} (x : var Γ U) -> tm ⊡ U) (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) (t : tm Γ T) -> reduce T ([ σ ] t)
-- thm σ θ c = c , (→*-refl , c)
-- thm σ θ (v y) = θ y
-- thm σ θ (M · N) = proj₂ (thm σ θ M) ([ σ ] N) (thm σ θ N)
-- thm σ θ (ƛ {T} {S} M) = (_ , (→*-refl , (ƛ _))) , (λ N redN → reduce-closed {S} β* (subst (reduce _) (lemma σ N M) (thm (σ ,, N) (reduce-ext θ redN) M)))

-- reify : ∀ {T} (t : tm _ T) -> reduce T t -> halts t
-- reify {atom} t p = p
-- reify {T ⇝ S} t (h , _) = h

-- done' : ∀ {T} (t : tm ⊡ T) -> halts t
-- done' {T} t = reify _ (subst (reduce T) []-id (thm v (λ ()) t))
