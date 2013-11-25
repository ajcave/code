module algeq where
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Function
open import Data.Sum

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

→*-refl' : ∀ {Γ T} {M N : tm Γ T} -> M ≡ N -> M →* N
→*-refl' refl = →*-refl

→*-trans : ∀ {Γ T} {M N P : tm Γ T} -> M →* N -> N →* P -> M →* P
→*-trans →*-refl u = u
→*-trans (→*-trans1 x t) u = →*-trans1 x (→*-trans t u)

ap1* : ∀ {Γ} {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 : tm Γ T} -> M1 →* M2  -> (M1 · N1) →* (M2 · N1)
ap1* →*-refl = →*-refl
ap1* (→*-trans1 x x₁) = →*-trans1 (ap1 x) (ap1* x₁)

β* : ∀ {T S} {M : tm (⊡ , T) S} {N : tm ⊡ T} -> ((ƛ M) · N) →* [ v ,, N ] M
β* = →*-trans1 (β _ _) →*-refl

▹wh-wkn : ∀ {Γ} {T} {M N : tm Γ T} -> M ▹wh N -> ∀ {Γ'} {w : vsubst Γ Γ'} -> ([ w ]v M) ▹wh ([ w ]v N)
▹wh-wkn (ap1 p) = ap1 (▹wh-wkn p)
▹wh-wkn (β M N) = λ {Γ'} {w} -> subst₂ _▹wh_ refl {!!} (β ([ ext w ]v M) ([ w ]v N))

→*-wkn : ∀ {Γ} {T} {M N : tm Γ T} -> M →* N -> ∀ {Γ'} {w : vsubst Γ Γ'} -> ([ w ]v M) →* ([ w ]v N)
→*-wkn →*-refl = →*-refl
→*-wkn (→*-trans1 x p) = →*-trans1 (▹wh-wkn x) (→*-wkn p)

mutual
 data isNeutral {Γ} : ∀ {T} (t : tm Γ T) -> Set where
  v : ∀ {T} (x : var Γ T) -> isNeutral (v x)
  _·_ : ∀ {T S} {M : tm Γ (T ⇝ S)} -> isNeutral M -> (N : tm Γ T) -> isNeutral (M · N)
  c : isNeutral c
 data isNormal {Γ} : ∀ {T} (t : tm Γ T) -> Set where
  ▹  : ∀ {T} {M : tm Γ T} -> isNeutral M -> isNormal M
  ƛ : ∀ {T S} (t : tm (Γ , T) S) -> isNormal (ƛ t)

-- data _⇓_ {Γ T} (M : tm Γ T) : tm Γ T -> Set where
--  eval : ∀ {N} -> M →* N -> isNormal N -> M ⇓ N

halts : ∀ {T} (t : tm ⊡ T) -> Set
halts {T} t = ∃ (λ (n : tm _ T) → (t →* n) × isNormal n)

mutual
 data _⊢_>_⇔_ Γ : ∀ T -> tm Γ T -> tm Γ T -> Set where
  qat-base : ∀ {M N P Q} -> M →* P -> N →* Q -> Γ ⊢ atom > P ↔ Q -> Γ ⊢ atom > M ⇔ N
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

cong⊢>⇔ : ∀ {Γ T} {M1 M2 N1 N2} -> M1 ≡ N1 -> M2 ≡ N2 -> Γ ⊢ T > M1 ⇔ M2 -> Γ ⊢ T > N1 ⇔ N2
cong⊢>⇔ refl refl p = p

closed⊢>is : ∀ {Γ T} {M1 M2 N1 N2} -> N1 →* M1 -> N2 →* M2 -> Γ ⊢ T > M1 is M2 -> Γ ⊢ T > N1 is N2
closed⊢>is {Γ} {atom} t1 t2 (qat-base x x₁ x₂) = qat-base (→*-trans t1 x) (→*-trans t2 x₁) x₂
closed⊢>is {Γ} {T ⇝ T₁} t1 t2 p = λ w x → closed⊢>is (ap1* (→*-wkn t1)) (ap1* (→*-wkn t2)) (p w x)

mutual
 ↔monotone : ∀ {Γ Γ'} (w : vsubst Γ Γ') {T} {M₁ M₂} -> Γ ⊢ T > M₁ ↔ M₂ -> Γ' ⊢ T > ([ w ]v M₁) ↔ ([ w ]v M₂)
 ↔monotone w qap-var = qap-var
 ↔monotone w (qap-app p x) = qap-app (↔monotone w p) (⇔monotone w x)
 ↔monotone w qap-const = qap-const

 ⇔monotone : ∀ {Γ Γ'} (w : vsubst Γ Γ') {T} {M₁ M₂} -> Γ ⊢ T > M₁ ⇔ M₂ -> Γ' ⊢ T > ([ w ]v M₁) ⇔ ([ w ]v M₂)
 ⇔monotone w (qat-base x x₁ x₂) = qat-base (→*-wkn x) (→*-wkn x₁) (↔monotone w x₂)
 ⇔monotone w (qat-arrow p) = qat-arrow (cong⊢>⇔ (cong₂ _·_ {!!} refl) (cong₂ _·_ {!!} refl) (⇔monotone (ext w) p))

monotone : ∀ {Γ Γ'} (w : vsubst Γ Γ') T {M₁ M₂} -> Γ ⊢ T > M₁ is M₂ -> Γ' ⊢ T > ([ w ]v M₁) is ([ w ]v M₂)
monotone w atom p = ⇔monotone w p
monotone w (T₁ ⇝ T₂) {M₁} {M₂} p = λ w₁ {N₁ N₂} x → cong⊢>is (cong (λ α → α · N₁) (sym ([]v-funct w₁ w M₁)))
                                                          (cong (λ α → α · N₂) (sym ([]v-funct w₁ w M₂)))
                                                 (p (w₁ ∘ w) x)

-- ↔isNeutral₁ : ∀ {Γ T M N} -> Γ ⊢ T > M ↔ N -> isNeutral M
-- ↔isNeutral₁ qap-var = v _
-- ↔isNeutral₁ (qap-app p x) = ↔isNeutral₁ p · _
-- ↔isNeutral₁ qap-const = c

-- ↔isNeutral₂ : ∀ {Γ T M N} -> Γ ⊢ T > M ↔ N -> isNeutral N
-- ↔isNeutral₂ qap-var = v _
-- ↔isNeutral₂ (qap-app p x) = ↔isNeutral₂ p · _
-- ↔isNeutral₂ qap-const = c

mutual
 reify : ∀ {Γ} T {M₁ M₂} -> Γ ⊢ T > M₁ is M₂ -> Γ ⊢ T > M₁ ⇔ M₂
 reify atom p = p
 reify (T ⇝ T₁) p = qat-arrow (reify T₁ (p ↑ (reflect T qap-var)))

 reflect : ∀ {Γ} T {M₁ M₂} -> Γ ⊢ T > M₁ ↔ M₂ -> Γ ⊢ T > M₁ is M₂
 reflect atom p = qat-base →*-refl →*-refl p
 reflect (T ⇝ T₁) p = λ w x → reflect T₁ (qap-app (↔monotone w p) (reify T x))

_⊢s_>_is_ : ∀ Γ Γ' (σ1 σ2 : sub Γ' Γ) -> Set
Γ ⊢s Γ' > σ1 is σ2 = ∀ {T} (x : var Γ' T) → Γ ⊢ T > (σ1 x) is (σ2 x)

⊢s-pair : ∀ {Γ Γ'} {σ1 σ2 : sub Γ' Γ} {T} {M N} -> Γ ⊢s Γ' > σ1 is σ2 -> Γ ⊢ T > M is N -> Γ ⊢s (Γ' , T) > (σ1 ,, M) is (σ2 ,, N)
⊢s-pair p1 p2 z = p2
⊢s-pair p1 p2 (s x) = p1 x

⊢s-wkn : ∀ {Γ Γ' Γ''} {σ1 σ2 : sub Γ' Γ} {w : vsubst Γ Γ''} -> Γ ⊢s Γ' > σ1 is σ2 -> Γ'' ⊢s Γ' > ([ w ]v ∘ σ1) is ([ w ]v ∘ σ2)
⊢s-wkn p x = monotone _ _ (p x)

⊢s-ext : ∀ {Γ Γ'} {σ1 σ2 : sub Γ' Γ} {T} -> Γ ⊢s Γ' > σ1 is σ2 -> (Γ , T) ⊢s (Γ' , T) > (sub-ext σ1) is (sub-ext σ2)
⊢s-ext p = ⊢s-pair (⊢s-wkn p) (reflect _ qap-var)



mutual
 ⊢↔-sym : ∀ {Γ T M N} -> Γ ⊢ T > M ↔ N -> Γ ⊢ T > N ↔ M
 ⊢↔-sym qap-var = qap-var
 ⊢↔-sym (qap-app p x) = qap-app (⊢↔-sym p) (⊢⇔-sym x)
 ⊢↔-sym qap-const = qap-const

 ⊢⇔-sym : ∀ {Γ T M N} -> Γ ⊢ T > M ⇔ N -> Γ ⊢ T > N ⇔ M
 ⊢⇔-sym (qat-base x x₁ x₂) = qat-base x₁ x (⊢↔-sym x₂)
 ⊢⇔-sym (qat-arrow p) = qat-arrow (⊢⇔-sym p)

⊢is-sym : ∀ {Γ} T {M N} -> Γ ⊢ T > M is N -> Γ ⊢ T > N is M
⊢is-sym atom p = ⊢⇔-sym p
⊢is-sym (T ⇝ T₁) p = λ w x → ⊢is-sym T₁ (p w (⊢is-sym T x))

determinacy : ∀ {Γ T} {M N O : tm Γ T} -> M ▹wh N -> M ▹wh O -> N ≡ O
determinacy (ap1 {N1 = N1} p1) (ap1 p2) = cong (λ α → α · N1) (determinacy p1 p2)
determinacy (ap1 ()) (β M N1)
determinacy (β M N) (ap1 ())
determinacy (β M N) (β .M .N) = refl

determinacy* : ∀ {Γ T} {M N O : tm Γ T} -> M →* N -> M →* O -> (N →* O) ⊎ (O →* N)
determinacy* →*-refl p2 = inj₁ p2
determinacy* (→*-trans1 x p1) →*-refl = inj₂ (→*-trans1 x p1)
determinacy* (→*-trans1 x p1) (→*-trans1 x₁ p2) with determinacy x x₁
... | refl = determinacy* p1 p2

confluence : ∀ {Γ T} {M N O : tm Γ T} -> M →* N -> M →* O -> ∃ (λ P -> (N →* P) × (O →* P))
confluence p1 p2 with determinacy* p1 p2
... | inj₁ q = _ , q , →*-refl
... | inj₂ q = _ , →*-refl , q

neutralNoStep : ∀ {Γ T} {C : Set} {M N O : tm Γ T} -> M ▹wh N -> Γ ⊢ T > M ↔ O -> C
neutralNoStep (ap1 p1) (qap-app p2 x) = neutralNoStep p1 p2
neutralNoStep (β M N) (qap-app () x)

neutralNoStep' : ∀ {Γ T} {C : Set} {M N O : tm Γ T} -> M ▹wh N -> Γ ⊢ T > O ↔ M -> C
neutralNoStep' (ap1 p1) (qap-app p2 x) = neutralNoStep' p1 p2
neutralNoStep' (β M N) (qap-app () x)

neutralNoStep* : ∀ {Γ T} {M N O : tm Γ T} -> M →* N -> Γ ⊢ T > M ↔ O -> M ≡ N
neutralNoStep* →*-refl p2 = refl
neutralNoStep* (→*-trans1 x p1) p2 = neutralNoStep x p2

neutralNoStep*' : ∀ {Γ T} {M N O : tm Γ T} -> M →* N -> Γ ⊢ T > O ↔ M -> M ≡ N
neutralNoStep*' →*-refl p2 = refl
neutralNoStep*' (→*-trans1 x p1) p2 = neutralNoStep' x p2

mutual
 ⊢↔-trans : ∀ {Γ T M N O} -> Γ ⊢ T > M ↔ N -> Γ ⊢ T > N ↔ O -> Γ ⊢ T > M ↔ O
 ⊢↔-trans qap-var qap-var = qap-var
 ⊢↔-trans (qap-app p1 x) (qap-app p2 x₁) = qap-app (⊢↔-trans p1 p2) (⊢⇔-trans x x₁)
 ⊢↔-trans qap-const qap-const = qap-const
 ⊢⇔-trans : ∀ {Γ T M N O} -> Γ ⊢ T > M ⇔ N -> Γ ⊢ T > N ⇔ O -> Γ ⊢ T > M ⇔ O
 ⊢⇔-trans (qat-base x x₂ x₁) (qat-base x₃ x₄ x₅) with confluence x₂ x₃
 ... | N , q0 , q1 with neutralNoStep* q1 x₅ | neutralNoStep*' q0 x₁
 ... | refl | refl = qat-base x x₄ (⊢↔-trans x₁ x₅)
 ⊢⇔-trans (qat-arrow p1) (qat-arrow p2) = qat-arrow (⊢⇔-trans p1 p2)

-- interesting twist...
⊢is-trans : ∀ {Γ} T {M N O} -> Γ ⊢ T > M is N -> Γ ⊢ T > N is O -> Γ ⊢ T > M is O
⊢is-trans atom p1 p2 = ⊢⇔-trans p1 p2
⊢is-trans (T ⇝ T₁) p1 p2 = λ w x → ⊢is-trans T₁ (p1 w x) (p2 w (⊢is-trans T (⊢is-sym T x) x))

⊢sis-sym : ∀ {Γ Γ'} {M N : sub Γ' Γ} -> Γ ⊢s Γ' > M is N -> Γ ⊢s Γ' > N is M
⊢sis-sym p x = ⊢is-sym _ (p x)

⊢sis-trans : ∀ {Γ Γ'} {M N O : sub Γ' Γ} -> Γ ⊢s Γ' > M is N -> Γ ⊢s Γ' > N is O -> Γ ⊢s Γ' > M is O
⊢sis-trans p1 p2 x = ⊢is-trans _ (p1 x) (p2 x)

data _⊢_>_≡_ Γ : ∀ T -> tm Γ T -> tm Γ T -> Set where
  qat-ext : ∀ {T₁ T₂} {M N : tm Γ (T₁ ⇝ T₂)} -> (Γ , T₁) ⊢ T₂ > [ ↑ ]v M · (v z) ≡ ([ ↑ ]v N · (v z))
             -> Γ ⊢ (T₁ ⇝ T₂) > M ≡ N
  qap-var : ∀ {T} {x : var Γ T} -> Γ ⊢ T > (v x) ≡ (v x)
  qap-app : ∀ {T₁ T₂} {M₁ M₂ : tm Γ (T₁ ⇝ T₂)} {N₁ N₂ : tm Γ T₁}
           -> Γ ⊢ (T₁ ⇝ T₂) > M₁ ≡ M₂
           -> Γ ⊢ T₁ > N₁ ≡ N₂
           -> Γ ⊢ T₂ > (M₁ · N₁) ≡ (M₂ · N₂)
  qap-const : Γ ⊢ atom > c ≡ c
  β : ∀ {T₁ T₂} {M₁ N₁ : tm Γ T₁} {M₂ N₂ : tm (Γ , T₁) T₂}
           -> (Γ , T₁) ⊢ T₂ > M₂ ≡ N₂
           -> Γ ⊢ T₁ > M₁ ≡ N₁
           -> Γ ⊢ T₂ > ((ƛ M₂) · M₁) ≡ ([ v ,, N₁ ] N₂)
  qap-sym : ∀ {T} {M N} -> Γ ⊢ T > M ≡ N -> Γ ⊢ T > N ≡ M
  qap-trans : ∀ {T} {M N O} -> Γ ⊢ T > M ≡ N -> Γ ⊢ T > N ≡ O -> Γ ⊢ T > M ≡ O
  ƛ : ∀ {T₁ T₂} {M₁ M₂} -> (Γ , T₁) ⊢ T₂ > M₁ ≡ M₂ -> Γ ⊢ (T₁ ⇝ T₂) > (ƛ M₁) ≡ (ƛ M₂)

⊢>≡-refl : ∀ {Γ T} (M : tm Γ T) -> Γ ⊢ T > M ≡ M
⊢>≡-refl (v x) = qap-var
⊢>≡-refl (M · M₁) = qap-app (⊢>≡-refl M) (⊢>≡-refl M₁)
⊢>≡-refl (ƛ M) = ƛ (⊢>≡-refl M)
⊢>≡-refl c = qap-const

thm : ∀ {Γ T} {M1 M2 : tm Γ T} -> Γ ⊢ T > M1 ≡ M2 -> ∀ {Γ'} (σ1 σ2 : sub Γ Γ') -> Γ' ⊢s Γ > σ1 is σ2 -> Γ' ⊢ T > ([ σ1 ] M1) is ([ σ2 ] M2)
thm {M1 = M1} {M2 = M2} (qat-ext {T₁} {T₂} p) σ1 σ2 σ1isσ2 = λ w {N1} {N2} p0 -> cong⊢>is {!!} {!!} (thm p (([ w ]v ∘ σ1) ,, N1) (([ w ]v ∘ σ2) ,, N2) (⊢s-pair (⊢s-wkn σ1isσ2) p0))
thm qap-var σ1 σ2 σ1isσ2 = σ1isσ2 _
thm (qap-app p p₁) σ1 σ2 σ1isσ2 = cong⊢>is {!!} {!!} (thm p σ1 σ2 σ1isσ2 id (thm p₁ σ1 σ2 σ1isσ2))
thm qap-const σ1 σ2 σ1isσ2 = qat-base →*-refl →*-refl qap-const
thm (β {T₁} {T₂} {M₁} {N₁} {M₂} {N₂} p p₁) σ1 σ2 σ1isσ2 with thm p (σ1 ,, ([ σ1 ] M₁)) (σ2 ,, ([ σ2 ] N₁)) (⊢s-pair σ1isσ2 (thm p₁ σ1 σ2 σ1isσ2))
... | q = closed⊢>is (→*-trans1 (β _ _) (→*-refl' {!!})) (→*-refl' {!!}) q
thm (qap-sym p) σ1 σ2 σ1isσ2 = ⊢is-sym _ (thm p σ2 σ1 (⊢sis-sym σ1isσ2))
thm (qap-trans p p₁) σ1 σ2 σ1isσ2 = ⊢is-trans _ (thm p σ1 σ2 σ1isσ2) (thm p₁ σ2 σ2 (⊢sis-trans (⊢sis-sym σ1isσ2) σ1isσ2)) -- again interesting twist
thm (ƛ p) σ1 σ2 σ1isσ2 = λ w {N1} {N2} x → closed⊢>is (→*-trans1 (β _ _) (→*-refl' {!!})) (→*-trans1 (β _ _) (→*-refl' {!!})) (thm p (([ w ]v ∘ σ1) ,, N1) (([ w ]v ∘ σ2) ,, N2) (⊢s-pair (⊢s-wkn σ1isσ2) x))

id-rel : ∀ {Γ} -> Γ ⊢s Γ > v is v
id-rel {⊡} ()
id-rel {Γ , T} z = reflect T qap-var -- This could go by appealing to ⊢-ext if we had the equations we needed
id-rel {Γ , T} (s x) = monotone ↑ _ (id-rel x)

corollary : ∀ {Γ T} {M1 M2 : tm Γ T} -> Γ ⊢ T > M1 ≡ M2 -> Γ ⊢ T > M1 is M2
corollary d = cong⊢>is []-id []-id (thm d v v id-rel)

completeness : ∀ {Γ T} {M1 M2 : tm Γ T} -> Γ ⊢ T > M1 ≡ M2 -> Γ ⊢ T > M1 ⇔ M2
completeness d = reify _ (corollary d)

▹wh-closed⊢>≡₁ : ∀ {Γ T} {M1 N1} -> N1 ▹wh M1 -> Γ ⊢ T > N1 ≡ M1
▹wh-closed⊢>≡₁ (ap1 t) = qap-app (▹wh-closed⊢>≡₁ t) (⊢>≡-refl _) --qap-trans (qap-app {!!} (⊢>≡-refl _)) p
▹wh-closed⊢>≡₁ (β M N) = β (⊢>≡-refl _) (⊢>≡-refl _)

closed⊢>≡₁ : ∀ {Γ T} {M1 N1} -> N1 →* M1 -> Γ ⊢ T > N1 ≡ M1
closed⊢>≡₁ →*-refl = ⊢>≡-refl _
closed⊢>≡₁ (→*-trans1 x t1) = qap-trans (▹wh-closed⊢>≡₁ x) (closed⊢>≡₁ t1)

mutual
 soundness1 : ∀ {Γ T} {M1 M2 : tm Γ T} -> Γ ⊢ T > M1 ⇔ M2 -> Γ ⊢ T > M1 ≡ M2
 soundness1 (qat-base x x₁ x₂) = qap-trans (closed⊢>≡₁ x) (qap-trans (soundness2 x₂) (qap-sym (closed⊢>≡₁ x₁)))
 soundness1 (qat-arrow p) = qat-ext (soundness1 p)
 
 soundness2 : ∀ {Γ T} {M1 M2 : tm Γ T} -> Γ ⊢ T > M1 ↔ M2 -> Γ ⊢ T > M1 ≡ M2
 soundness2 qap-var = qap-var
 soundness2 (qap-app p x) = qap-app (soundness2 p) (soundness1 x)
 soundness2 qap-const = qap-const

-- Could we derive an algorithm more directly by bypassing ⇔?
-- Hmm. We could just prove weak head normalization (on open terms), and define ⇔. Then do implement conversion
-- test by well-founded induction on ▹wh, lexicographic with type? Maybe some kind of spine-form induction?

-- TODO: Add Unit type