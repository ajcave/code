module algeq-typing-unit where
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
 atom unit : tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> (T : A) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

vsubst : ∀ {A} -> ctx A -> ctx A -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U

↑ : ∀ {A : Set} {Γ} {T : A} -> vsubst Γ (Γ , T)
↑ = s

_∘₁_ : ∀ {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘₁ g) x = f (g x)

ext : ∀ {A : Set} {Γ Δ} {T : A} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

var-dom-eq' : ∀ {A : Unit -> Set} {Γ T} (f g : ∀ {U} (x : var (Γ , T) U) -> A U) -> (∀ {U} (x : var Γ U) -> f (s x) ≡ g (s x)) -> f z ≡ g z -> ∀ {U} (x : var (Γ , T) U) -> f x ≡ g x
var-dom-eq' f g p q z = q
var-dom-eq' f g p q (s y) = p y

var-dom-eq : ∀ {A : Unit -> Set} {Γ T} {f g : ∀ {U} (x : var (Γ , T) U) -> A U} -> (∀ {U} (x : var Γ U) -> f (s x) ≡ g (s x)) -> f z ≡ g z -> _≡_ {_} { ∀ {U} -> var (Γ , T) U -> A U } f g
var-dom-eq {f = f} {g = g} p q = funext-imp (λ U -> funext (λ x -> var-dom-eq' f g p q x))

ext-funct : ∀ {A : Set} {Γ1 Γ2 Γ3 U} {S : A} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (x : var (Γ1 , U) S) -> ((ext σ1) ∘ (ext σ2)) x ≡ ext (σ1 ∘ σ2) x
ext-funct σ1 σ2 z = refl
ext-funct σ1 σ2 (s y) = refl

ext-id : ∀ {A : Set} {Γ T} {U : A} (x : var (Γ , T) U) -> ext id x ≡ x
ext-id z = refl
ext-id (s y) = refl

wkn : ∀ {A : Set} {Γ} {T : A} -> vsubst Γ (Γ , T)
wkn = s

data tm (Γ : ctx Unit) : (T : Unit) -> Set where
 v : var Γ _ -> tm Γ _
 _·_ : tm Γ _ -> tm Γ _ -> tm Γ _
 ƛ : tm (Γ , _) _ -> tm Γ _
 c : tm Γ _
 tt : tm Γ _

[_]v : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_]v σ (v y) = v (σ y)
[_]v σ (M · N) = [ σ ]v M · [ σ ]v N
[_]v σ (ƛ M) = ƛ ([ ext σ ]v M)
[ σ ]v c = c
[ σ ]v tt = tt

sub : (Γ1 Γ2 : ctx Unit) -> Set
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
[ σ ] tt = tt

[]v-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]v ([ σ2 ]v R) ≡ [ σ1 ∘ σ2 ]v R
[]v-funct σ1 σ2 (v y) = refl
[]v-funct σ1 σ2 (y · y') = cong₂ _·_ ([]v-funct σ1 σ2 y) ([]v-funct σ1 σ2 y')
[]v-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]v-funct (ext σ1) (ext σ2) y) (cong (λ (α : vsubst _ _) → [ α ]v y) (var-dom-eq (λ x → refl) refl)))
[]v-funct σ1 σ2 c = refl
[]v-funct σ1 σ2 tt = refl

[]vn-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]v ([ σ2 ] R) ≡ [ [ σ1 ]v ∘₁ σ2 ] R
[]vn-funct σ1 σ2 (v y) = refl
[]vn-funct σ1 σ2 (y · y') = cong₂ _·_ ([]vn-funct σ1 σ2 y) ([]vn-funct σ1 σ2 y')
[]vn-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]vn-funct (ext σ1) (sub-ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → trans ([]v-funct (ext σ1) s (σ2 x)) (sym ([]v-funct s σ1 (σ2 x)))) refl)))
[]vn-funct σ1 σ2 c = refl
[]vn-funct σ1 σ2 tt = refl

[]nv-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ]v R) ≡ [ σ1 ∘₁ σ2 ] R
[]nv-funct σ1 σ2 (v y) = refl
[]nv-funct σ1 σ2 (y · y') = cong₂ _·_ ([]nv-funct σ1 σ2 y) ([]nv-funct σ1 σ2 y')
[]nv-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]nv-funct (sub-ext σ1) (ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → refl) refl)))
[]nv-funct σ1 σ2 c = refl
[]nv-funct σ1 σ2 tt = refl

[]-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ] R) ≡ [ [ σ1 ] ∘₁ σ2 ] R
[]-funct σ1 σ2 (v y) = refl
[]-funct σ1 σ2 (y · y') = cong₂ _·_ ([]-funct σ1 σ2 y) ([]-funct σ1 σ2 y')
[]-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]-funct (sub-ext σ1) (sub-ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → trans ([]nv-funct (sub-ext σ1) s (σ2 x)) (sym ([]vn-funct s σ1 (σ2 x)))) refl)))
[]-funct σ1 σ2 c = refl
[]-funct σ1 σ2 tt = refl

sub-ext-idv : ∀ {A : Set} {Γ T} {U : A} (x : var (Γ , T) U) -> (ext id) x ≡ x
sub-ext-idv z = refl
sub-ext-idv (s y) = refl

[]v-id : ∀ {Γ T} {M : tm Γ T} -> [ id ]v M ≡ M
[]v-id {M = v y} = refl
[]v-id {M = M · N} = cong₂ _·_ []v-id []v-id
[]v-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : vsubst _ _) → [ α ]v M) (funext-imp (λ x → funext (λ x' → sub-ext-idv x')))) []v-id)
[]v-id {M = c} = refl
[]v-id {M = tt} = refl

sub-ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> (sub-ext v) x ≡ v x
sub-ext-id z = refl
sub-ext-id (s y) = refl

[]-id : ∀ {Γ T} {M : tm Γ T} -> [ v ] M ≡ M
[]-id {M = v y} = refl
[]-id {M = M · N} = cong₂ _·_ []-id []-id
[]-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : sub _ _) → [ α ] M) (funext-imp (λ x → funext (λ x' → sub-ext-id x')))) []-id)
[]-id {M = c} = refl
[]-id {M = tt} = refl

data _▹wh_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 ap1 : ∀ {M1 M2 : tm Γ _} {N1 : tm _ _} -> M1 ▹wh M2  -> (M1 · N1) ▹wh (M2 · N1)
 β : ∀ (M : tm (Γ , _) _) (N : tm Γ _) -> ((ƛ M) · N) ▹wh [ v ,, N ] M

data _→*_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 →*-refl : ∀ {T} {M : tm Γ T} -> M →* M
 →*-trans1 : ∀ {T} {M N P : tm _ T} -> M ▹wh N -> N →* P -> M →* P

→*-refl' : ∀ {Γ T} {M N : tm Γ T} -> M ≡ N -> M →* N
→*-refl' refl = →*-refl

→*-trans : ∀ {Γ T} {M N P : tm Γ T} -> M →* N -> N →* P -> M →* P
→*-trans →*-refl u = u
→*-trans (→*-trans1 x t) u = →*-trans1 x (→*-trans t u)

ap1* : ∀ {Γ} {M1 M2 : tm Γ _} {N1 : tm Γ _} -> M1 →* M2  -> (M1 · N1) →* (M2 · N1)
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

⌊_⌋ : ctx tp -> ctx Unit
⌊ ⊡ ⌋ = ⊡
⌊ Γ , T ⌋ = ⌊ Γ ⌋ , _

lookup : ∀ (Γ : ctx tp) (x : var ⌊ Γ ⌋ _) -> tp
lookup ⊡ ()
lookup (Γ , T) z = T
lookup (Γ , T) (s x) = lookup Γ x

mutual
 data _⊢_>_⇔_ (Γ : ctx tp) : ∀ (T : tp) -> tm ⌊ Γ ⌋ _ -> tm ⌊ Γ ⌋ _ -> Set where
  qat-base : ∀ {M N P Q} -> M →* P -> N →* Q -> Γ ⊢ atom > P ↔ Q -> Γ ⊢ atom > M ⇔ N
  qat-arrow : ∀ {T₁ T₂} {M N} -> (Γ , T₁) ⊢ T₂ > [ ↑ ]v M · (v z) ⇔ ([ ↑ ]v N · (v z))
             -> Γ ⊢ (T₁ ⇝ T₂) > M ⇔ N
  qat-unit : ∀ {M N} -> Γ ⊢ unit > M ⇔ N
 data _⊢_>_↔_ Γ : ∀ (T : tp) -> tm ⌊ Γ ⌋ _ -> tm ⌊ Γ ⌋ _ -> Set where
  qap-var : ∀ x -> Γ ⊢ (lookup Γ x) > (v x) ↔ (v x)
  qap-app : ∀ {T₁ T₂} {M₁ M₂ N₁ N₂}
           -> Γ ⊢ (T₁ ⇝ T₂) > M₁ ↔ M₂
           -> Γ ⊢ T₁ > N₁ ⇔ N₂
           -> Γ ⊢ T₂ > (M₁ · N₁) ↔ (M₂ · N₂)
  qap-const : Γ ⊢ atom > c ↔ c

_⊢w_>_ : ∀ Γ' Γ (w : vsubst ⌊ Γ ⌋ ⌊ Γ' ⌋) -> Set
Γ' ⊢w Γ > w = ∀ x -> lookup Γ x ≡ (lookup Γ' (w x))


_⊢_>_is_ : ∀ Γ T -> tm ⌊ Γ ⌋ _ -> tm ⌊ Γ ⌋ _ -> Set
Γ ⊢ atom > M₁ is M₂ = Γ ⊢ atom > M₁ ⇔ M₂
Γ ⊢ T₁ ⇝ T₂ > M₁ is M₂ = ∀ {Γ'} {w : vsubst ⌊ Γ ⌋ ⌊ Γ' ⌋} (W : Γ' ⊢w Γ > w) {N₁ N₂} →
                           Γ' ⊢ T₁ > N₁ is N₂ → Γ' ⊢ T₂ > [ w ]v M₁ · N₁ is ([ w ]v M₂ · N₂)
Γ ⊢ unit > M₁ is M₂ = Unit

cong⊢>is : ∀ {Γ T} {M1 M2 N1 N2} -> M1 ≡ N1 -> M2 ≡ N2 -> Γ ⊢ T > M1 is M2 -> Γ ⊢ T > N1 is N2
cong⊢>is refl refl p = p

cong⊢>⇔ : ∀ {Γ T} {M1 M2 N1 N2} -> M1 ≡ N1 -> M2 ≡ N2 -> Γ ⊢ T > M1 ⇔ M2 -> Γ ⊢ T > N1 ⇔ N2
cong⊢>⇔ refl refl p = p

closed⊢>is : ∀ {Γ T} {M1 M2 N1 N2} -> N1 →* M1 -> N2 →* M2 -> Γ ⊢ T > M1 is M2 -> Γ ⊢ T > N1 is N2
closed⊢>is {Γ} {atom} t1 t2 (qat-base x x₁ x₂) = qat-base (→*-trans t1 x) (→*-trans t2 x₁) x₂
closed⊢>is {Γ} {T ⇝ T₁} t1 t2 p = λ w x → closed⊢>is (ap1* (→*-wkn t1)) (ap1* (→*-wkn t2)) (p w x)
closed⊢>is {Γ} {unit} t1 t2 p = tt

⊢w-ext : ∀ {Γ' Γ T} {w : vsubst ⌊ Γ ⌋ ⌊ Γ' ⌋} -> Γ' ⊢w Γ > w -> (Γ' , T) ⊢w (Γ , T) > (ext w)
⊢w-ext d z = refl
⊢w-ext d (s x) = d x

⊢w∘ : ∀ {Γ'' Γ' Γ} {w : vsubst ⌊ Γ ⌋ ⌊ Γ' ⌋} {w' : vsubst ⌊ Γ' ⌋ ⌊ Γ'' ⌋} -> Γ'' ⊢w Γ' > w' -> Γ' ⊢w Γ > w -> Γ'' ⊢w Γ > (w' ∘ w)
⊢w∘ p0 p1 x = trans (p1 x) (p0 _)

⊢w↑ : ∀ {Γ T} -> (Γ , T) ⊢w Γ > ↑
⊢w↑ x = refl

⊢wid : ∀ {Γ} -> Γ ⊢w Γ > id
⊢wid x = refl

mutual
 ↔monotone' : ∀ {Γ Γ'} {w : vsubst _ _} (W : Γ' ⊢w Γ > w) {T} {M₁ M₂} -> Γ ⊢ T > M₁ ↔ M₂ -> Γ' ⊢ T > ([ w ]v M₁) ↔ ([ w ]v M₂)
 ↔monotone' {w = w} W (qap-var x) = subst (λ α → _ ⊢ α > v (w x) ↔ v (w x)) (sym (W x)) (qap-var (w x))
 ↔monotone' w (qap-app p x) = qap-app (↔monotone' w p) (⇔monotone' w x)
 ↔monotone' w qap-const = qap-const

 ⇔monotone' : ∀ {Γ Γ'} {w : vsubst _ _} (W : Γ' ⊢w Γ > w) {T} {M₁ M₂} -> Γ ⊢ T > M₁ ⇔ M₂ -> Γ' ⊢ T > ([ w ]v M₁) ⇔ ([ w ]v M₂)
 ⇔monotone' w (qat-base x x₁ x₂) = qat-base (→*-wkn x) (→*-wkn x₁) (↔monotone' w x₂)
 ⇔monotone' {w = w} W (qat-arrow {T} {S} p) = qat-arrow (cong⊢>⇔ (cong₂ _·_ {!!} refl) (cong₂ _·_ {!!} refl) (⇔monotone' {w = ext w} (⊢w-ext W) p))
 ⇔monotone' w qat-unit = qat-unit

monotone' : ∀ {Γ Γ'} {w : vsubst _ _} (W : Γ' ⊢w Γ > w) T {M₁ M₂} -> Γ ⊢ T > M₁ is M₂ -> Γ' ⊢ T > ([ w ]v M₁) is ([ w ]v M₂)
monotone' w atom p = ⇔monotone' w p
monotone' {w = ww} w (T₁ ⇝ T₂) {M₁} {M₂} p = λ {Γ''} {w₁w} w₁ {N₁ N₂} x → cong⊢>is (cong (λ α → α · N₁) (sym ([]v-funct _ _ M₁)))
                                                          (cong (λ α → α · N₂) (sym ([]v-funct _ _ M₂)))
                                                 (p (⊢w∘ {w = ww} {w' = w₁w} w₁ w) x)
monotone' w unit p = tt

mutual
 reify : ∀ {Γ} T {M₁ M₂} -> Γ ⊢ T > M₁ is M₂ -> Γ ⊢ T > M₁ ⇔ M₂
 reify atom p = p
 reify (T ⇝ T₁) p = qat-arrow (reify T₁ (p ⊢wid (reflect T (qap-var z))))
 reify unit p = qat-unit

 reflect : ∀ {Γ} T {M₁ M₂} -> Γ ⊢ T > M₁ ↔ M₂ -> Γ ⊢ T > M₁ is M₂
 reflect atom p = qat-base →*-refl →*-refl p
 reflect (T ⇝ T₁) p = λ w x → reflect T₁ (qap-app (↔monotone' w p) (reify T x))
 reflect unit p = tt


_⊢s_>_is_ : ∀ Γ Γ' (σ1 σ2 : sub ⌊ Γ' ⌋  ⌊ Γ ⌋) -> Set
Γ ⊢s Γ' > σ1 is σ2 = ∀ x → Γ ⊢ (lookup Γ' x) > (σ1 x) is (σ2 x)

⊢s-is-pair : ∀ {Γ Γ'} {σ1 σ2} {T} {M N} -> Γ ⊢s Γ' > σ1 is σ2 -> Γ ⊢ T > M is N -> Γ ⊢s (Γ' , T) > (σ1 ,, M) is (σ2 ,, N)
⊢s-is-pair p1 p2 z = p2
⊢s-is-pair p1 p2 (s x) = p1 x

⊢s-wkn : ∀ {Γ Γ' Γ''} {σ1 σ2 : sub ⌊ Γ' ⌋ ⌊ Γ ⌋} {w} (W : Γ'' ⊢w Γ > w) -> Γ ⊢s Γ' > σ1 is σ2 -> Γ'' ⊢s Γ' > ([ w ]v ∘ σ1) is ([ w ]v ∘ σ2)
⊢s-wkn W p x = monotone' W _ (p x)

⊢s-is-ext : ∀ {Γ Γ'} {σ1 σ2 : sub ⌊ Γ' ⌋ ⌊ Γ ⌋} {T} -> Γ ⊢s Γ' > σ1 is σ2 -> (Γ , T) ⊢s (Γ' , T) > (sub-ext σ1) is (sub-ext σ2)
⊢s-is-ext {T = T} p = ⊢s-is-pair (⊢s-wkn (⊢w↑ {T = T}) p) (reflect _ (qap-var z))

mutual
 ⊢↔-sym : ∀ {Γ T M N} -> Γ ⊢ T > M ↔ N -> Γ ⊢ T > N ↔ M
 ⊢↔-sym (qap-var x) = qap-var x
 ⊢↔-sym (qap-app p x) = qap-app (⊢↔-sym p) (⊢⇔-sym x)
 ⊢↔-sym qap-const = qap-const

 ⊢⇔-sym : ∀ {Γ T M N} -> Γ ⊢ T > M ⇔ N -> Γ ⊢ T > N ⇔ M
 ⊢⇔-sym (qat-base x x₁ x₂) = qat-base x₁ x (⊢↔-sym x₂)
 ⊢⇔-sym (qat-arrow p) = qat-arrow (⊢⇔-sym p)
 ⊢⇔-sym qat-unit = qat-unit

⊢is-sym : ∀ {Γ} T {M N} -> Γ ⊢ T > M is N -> Γ ⊢ T > N is M
⊢is-sym atom p = ⊢⇔-sym p
⊢is-sym (T ⇝ T₁) p = λ w x → ⊢is-sym T₁ (p w (⊢is-sym T x))
⊢is-sym unit p = tt

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

neutralNoStep : ∀ {Γ T} {C : Set} {M N O} -> M ▹wh N -> Γ ⊢ T > M ↔ O -> C
neutralNoStep (ap1 p1) (qap-app p2 x) = neutralNoStep p1 p2
neutralNoStep (β M N) (qap-app () x)

neutralNoStep' : ∀ {Γ T} {C : Set} {M N O} -> M ▹wh N -> Γ ⊢ T > O ↔ M -> C
neutralNoStep' (ap1 p1) (qap-app p2 x) = neutralNoStep' p1 p2
neutralNoStep' (β M N) (qap-app () x)

neutralNoStep* : ∀ {Γ T} {M N O} -> M →* N -> Γ ⊢ T > M ↔ O -> M ≡ N
neutralNoStep* →*-refl p2 = refl
neutralNoStep* (→*-trans1 x p1) p2 = neutralNoStep x p2

neutralNoStep*' : ∀ {Γ T} {M N O} -> M →* N -> Γ ⊢ T > O ↔ M -> M ≡ N
neutralNoStep*' →*-refl p2 = refl
neutralNoStep*' (→*-trans1 x p1) p2 = neutralNoStep' x p2

-- I think this differs from lemma 3.3.(4) of HP05 because of a bug there? (in the appeal to 3.3.(4) in proof of transitivity)
-- Think of this as a "synth" rule
↔≡tp : ∀ {Γ T T' M N O} -> Γ ⊢ T > M ↔ N -> Γ ⊢ T' > N ↔ O -> T ≡ T'
↔≡tp (qap-var x) (qap-var .x) = refl
↔≡tp (qap-app p1 x) (qap-app p2 x₁) with ↔≡tp p1 p2
↔≡tp (qap-app p1 x) (qap-app p2 x₁) | refl = refl
↔≡tp qap-const qap-const = refl


lem0 : ∀ {Γ T} {M M1' M2' N1' N2'} -> M →* M1' -> M →* M2' -- -> N →* N1' -> N →* N2'
 -> Γ ⊢ T > M1' ↔ N1' -> Γ ⊢ T > M2' ↔ N2' -> M1' ≡ M2'
lem0 p1 p2 p5 p6 with confluence p1 p2
lem0 p1 p2 p5 p6 | M'' , (s1 , s2) with neutralNoStep* s1 p5 | neutralNoStep* s2 p6
lem0 p1 p2 p5 p6 | M'' , s1 , s2 | refl | refl = refl

lem1 : ∀ {Γ T} {M M1' M2' N1' N2'} -> M →* M1' -> M →* M2' 
 -> Γ ⊢ T > N1' ↔ M1' -> Γ ⊢ T > M2' ↔ N2' -> M1' ≡ M2'
lem1 p1 p2 p5 p6 = lem0 p1 p2 (⊢↔-sym p5) p6

mutual
 ⊢↔-trans : ∀ {Γ T M N O} -> Γ ⊢ T > M ↔ N -> Γ ⊢ T > N ↔ O -> Γ ⊢ T > M ↔ O
 ⊢↔-trans (qap-var x) (qap-var .x) = qap-var x
 ⊢↔-trans (qap-app p1 x) (qap-app p2 x₁) with ↔≡tp p1 p2
 ... | refl = qap-app (⊢↔-trans p1 p2) (⊢⇔-trans x x₁)
 ⊢↔-trans qap-const qap-const = qap-const
 ⊢⇔-trans : ∀ {Γ T M N O} -> Γ ⊢ T > M ⇔ N -> Γ ⊢ T > N ⇔ O -> Γ ⊢ T > M ⇔ O
 ⊢⇔-trans (qat-base x x₂ x₁) (qat-base x₃ x₄ x₅) with lem1 x₂ x₃ x₁ x₅
 ⊢⇔-trans (qat-base x x₂ x₁) (qat-base x₃ x₄ x₅) | refl = qat-base x x₄ (⊢↔-trans x₁ x₅)
 ⊢⇔-trans (qat-arrow p1) (qat-arrow p2) = qat-arrow (⊢⇔-trans p1 p2)
 ⊢⇔-trans qat-unit qat-unit = qat-unit

-- interesting twist...
⊢is-trans : ∀ {Γ} T {M N O} -> Γ ⊢ T > M is N -> Γ ⊢ T > N is O -> Γ ⊢ T > M is O
⊢is-trans atom p1 p2 = ⊢⇔-trans p1 p2
⊢is-trans (T ⇝ T₁) p1 p2 = λ w x → ⊢is-trans T₁ (p1 w x) (p2 w (⊢is-trans T (⊢is-sym T x) x))
⊢is-trans unit p1 p2 = tt

⊢sis-sym : ∀ {Γ Γ'} {M N : sub ⌊ Γ' ⌋ ⌊ Γ ⌋} -> Γ ⊢s Γ' > M is N -> Γ ⊢s Γ' > N is M
⊢sis-sym p x = ⊢is-sym _ (p x)

⊢sis-trans : ∀ {Γ Γ'} {M N O : sub ⌊ Γ' ⌋ ⌊ Γ ⌋} -> Γ ⊢s Γ' > M is N -> Γ ⊢s Γ' > N is O -> Γ ⊢s Γ' > M is O
⊢sis-trans p1 p2 x = ⊢is-trans _ (p1 x) (p2 x)

data _⊢_∶_ (Γ : ctx tp) : (M : tm ⌊ Γ ⌋ _) (T : tp) -> Set where
 v : ∀ x -> Γ ⊢ (v x) ∶ (lookup Γ x)
 _·_ : ∀ {T S M N} -> Γ ⊢ M ∶ (T ⇝ S) -> Γ ⊢ N ∶ T -> Γ ⊢ (M · N) ∶ S
 ƛ : ∀ {T S M} -> (Γ , T) ⊢ M ∶ S -> Γ ⊢ (ƛ M) ∶ (T ⇝ S)
 c : Γ ⊢ c ∶ atom
 tt : Γ ⊢ tt ∶ unit

data _⊢_>_≡_ Γ : ∀ T -> tm ⌊ Γ ⌋ _ -> tm ⌊ Γ ⌋ _ -> Set where
  qat-ext : ∀ {T₁ T₂} {M N} -> (Γ , T₁) ⊢ T₂ > [ ↑ ]v M · (v z) ≡ ([ ↑ ]v N · (v z))
             -> Γ ⊢ (T₁ ⇝ T₂) > M ≡ N
  qap-var : ∀ x -> Γ ⊢ (lookup Γ x) > (v x) ≡ (v x)
  qap-app : ∀ {T₁ T₂} {M₁ M₂} {N₁ N₂}
           -> Γ ⊢ (T₁ ⇝ T₂) > M₁ ≡ M₂
           -> Γ ⊢ T₁ > N₁ ≡ N₂
           -> Γ ⊢ T₂ > (M₁ · N₁) ≡ (M₂ · N₂)
  qap-const : Γ ⊢ atom > c ≡ c
  β : ∀ {T₁ T₂} {M₁ N₁} {M₂ N₂}
           -> (Γ , T₁) ⊢ T₂ > M₂ ≡ N₂
           -> Γ ⊢ T₁ > M₁ ≡ N₁
           -> Γ ⊢ T₂ > ((ƛ M₂) · M₁) ≡ ([ v ,, N₁ ] N₂)
  qap-sym : ∀ {T} {M N} -> Γ ⊢ T > M ≡ N -> Γ ⊢ T > N ≡ M
  qap-trans : ∀ {T} {M N O} -> Γ ⊢ T > M ≡ N -> Γ ⊢ T > N ≡ O -> Γ ⊢ T > M ≡ O
  ƛ : ∀ {T₁ T₂} {M₁ M₂} -> (Γ , T₁) ⊢ T₂ > M₁ ≡ M₂ -> Γ ⊢ (T₁ ⇝ T₂) > (ƛ M₁) ≡ (ƛ M₂)
  qap-unit : ∀ {M N} -> Γ ⊢ M ∶ unit -> Γ ⊢ N ∶ unit -> Γ ⊢ unit > M ≡ N

thm : ∀ {Γ T} {M1 M2} -> Γ ⊢ T > M1 ≡ M2 -> ∀ {Γ'} (σ1 σ2 : sub ⌊ Γ ⌋ ⌊ Γ' ⌋) -> Γ' ⊢s Γ > σ1 is σ2 -> Γ' ⊢ T > ([ σ1 ] M1) is ([ σ2 ] M2)
thm {M1 = M1} {M2 = M2} (qat-ext {T₁} {T₂} p) σ1 σ2 σ1isσ2 = λ {Γ''} {w} W {N1} {N2} p0 -> cong⊢>is {!!} {!!} (thm p (([ w ]v ∘ σ1) ,, N1) (([ w ]v ∘ σ2) ,, N2) (⊢s-is-pair (⊢s-wkn W σ1isσ2) p0))
thm (qap-var x) σ1 σ2 σ1isσ2 = σ1isσ2 x
thm (qap-app p p₁) σ1 σ2 σ1isσ2 = cong⊢>is {!!} {!!} (thm p σ1 σ2 σ1isσ2 (λ x → refl) (thm p₁ σ1 σ2 σ1isσ2))
thm qap-const σ1 σ2 σ1isσ2 = qat-base →*-refl →*-refl qap-const
thm (β {T₁} {T₂} {M₁} {N₁} {M₂} {N₂} p p₁) σ1 σ2 σ1isσ2 with thm p (σ1 ,, ([ σ1 ] M₁)) (σ2 ,, ([ σ2 ] N₁)) (⊢s-is-pair σ1isσ2 (thm p₁ σ1 σ2 σ1isσ2))
... | q = closed⊢>is (→*-trans1 (β _ _) (→*-refl' {!!})) (→*-refl' {!!}) q
thm (qap-sym p) σ1 σ2 σ1isσ2 = ⊢is-sym _ (thm p σ2 σ1 (⊢sis-sym σ1isσ2))
thm (qap-trans p p₁) σ1 σ2 σ1isσ2 = ⊢is-trans _ (thm p σ1 σ2 σ1isσ2) (thm p₁ σ2 σ2 (⊢sis-trans (⊢sis-sym σ1isσ2) σ1isσ2)) -- again interesting twist
thm (ƛ p) σ1 σ2 σ1isσ2 = λ {Γ''} {w} W {N1} {N2} x → closed⊢>is (→*-trans1 (β _ _) (→*-refl' {!!})) (→*-trans1 (β _ _) (→*-refl' {!!})) (thm p (([ _ ]v ∘ σ1) ,, N1) (([ _ ]v ∘ σ2) ,, N2) (⊢s-is-pair (⊢s-wkn W σ1isσ2) x))
thm (qap-unit d1 d2) σ1 σ2 σ1isσ2 = tt

id-rel : ∀ {Γ} -> Γ ⊢s Γ > v is v
id-rel {⊡} ()
id-rel {Γ , T} z = reflect T (qap-var z) -- This could go by appealing to ⊢-ext if we had the equations we needed
id-rel {Γ , T} (s x) = monotone' {w = ↑} (⊢w↑ {T = T}) (lookup Γ x) (id-rel x)

corollary : ∀ {Γ T} {M1 M2} -> Γ ⊢ T > M1 ≡ M2 -> Γ ⊢ T > M1 is M2
corollary d = cong⊢>is []-id []-id (thm d v v id-rel)

completeness : ∀ {Γ T} {M1 M2} -> Γ ⊢ T > M1 ≡ M2 -> Γ ⊢ T > M1 ⇔ M2
completeness d = reify _ (corollary d)


_⊢s_>_ : ∀ Γ' Γ (w : sub ⌊ Γ ⌋ ⌊ Γ' ⌋) -> Set
Γ' ⊢s Γ > σ = ∀ x -> Γ' ⊢ (σ x) ∶ (lookup Γ x)


-- Only reflexive on well-typed terms
⊢>≡-refl : ∀ {Γ T M} -> Γ ⊢ M ∶ T -> Γ ⊢ T > M ≡ M
⊢>≡-refl (v x) = qap-var x
⊢>≡-refl (M · M₁) = qap-app (⊢>≡-refl M) (⊢>≡-refl M₁)
⊢>≡-refl (ƛ M) = ƛ (⊢>≡-refl M)
⊢>≡-refl c = qap-const
⊢>≡-refl tt = qap-unit tt tt

[]v-typing : ∀ {Γ Γ' T M} (σ : vsubst ⌊ Γ ⌋ ⌊ Γ' ⌋) -> Γ' ⊢w Γ > σ -> Γ ⊢ M ∶ T -> Γ' ⊢ ([ σ ]v M) ∶ T
[]v-typing σ d1 (v x) = subst (λ α → _ ⊢ v (σ x) ∶ α) (sym (d1 x)) (v (σ x))
[]v-typing σ d1 (d2 · d3) = ([]v-typing σ d1 d2) · ([]v-typing σ d1 d3)
[]v-typing σ d1 (ƛ d2) = ƛ ([]v-typing (ext σ) (⊢w-ext d1) d2)
[]v-typing σ d1 c = c
[]v-typing σ1 d1 tt = tt


⊢sid : ∀ {Γ} -> Γ ⊢s Γ > v
⊢sid x = v x

⊢s-pair : ∀ {Γ' Γ M T} {σ : sub ⌊ Γ ⌋ ⌊ Γ' ⌋} -> Γ' ⊢s Γ > σ -> Γ' ⊢ M ∶ T -> Γ' ⊢s (Γ , T) > (σ ,, M)
⊢s-pair d1 d2 z = d2
⊢s-pair d1 d2 (s x) = d1 x

⊢s-ext : ∀ {Γ' Γ T} {σ : sub ⌊ Γ ⌋ ⌊ Γ' ⌋} -> Γ' ⊢s Γ > σ -> (Γ' , T) ⊢s (Γ , T) > (sub-ext σ)
⊢s-ext d z = v z
⊢s-ext {T = T} d (s x) = []v-typing ↑ (⊢w↑ {T = T}) (d x)

[]s-typing : ∀ {Γ Γ' T M} (σ : sub ⌊ Γ ⌋ ⌊ Γ' ⌋) -> Γ' ⊢s Γ > σ -> Γ ⊢ M ∶ T -> Γ' ⊢ ([ σ ] M) ∶ T
[]s-typing σ d1 (v x) = d1 x
[]s-typing σ d1 (d2 · d3) = ([]s-typing σ d1 d2) · ([]s-typing σ d1 d3)
[]s-typing σ d1 (ƛ d2) = ƛ ([]s-typing (sub-ext σ) (⊢s-ext d1) d2)
[]s-typing σ d1 c = c
[]s-typing σ d1 tt = tt

▹wh-tp-preserve : ∀ {Γ T M N} -> Γ ⊢ M ∶ T -> M ▹wh N -> Γ ⊢ N ∶ T
▹wh-tp-preserve (p₁ · p) (ap1 q) = ▹wh-tp-preserve p₁ q · p
▹wh-tp-preserve ((ƛ p) · p₁) (β M N) = []s-typing (v ,, N) (⊢s-pair v p₁) p

▹wh-closed⊢>≡₁ : ∀ {Γ T} {M1 N1} -> Γ ⊢ N1 ∶ T -> N1 ▹wh M1 -> Γ ⊢ T > N1 ≡ M1
▹wh-closed⊢>≡₁ (p · q) (ap1 t) = qap-app (▹wh-closed⊢>≡₁ p t) (⊢>≡-refl q)
▹wh-closed⊢>≡₁ ((ƛ p) · q) (β M N) = β (⊢>≡-refl p) (⊢>≡-refl q)

→*-tp-preserve : ∀ {Γ T M N} -> Γ ⊢ M ∶ T -> M →* N -> Γ ⊢ N ∶ T
→*-tp-preserve d →*-refl = d
→*-tp-preserve d (→*-trans1 x q) = →*-tp-preserve (▹wh-tp-preserve d x) q

closed⊢>≡₁ : ∀ {Γ T} {M1 N1} -> Γ ⊢ N1 ∶ T -> N1 →* M1 -> Γ ⊢ T > N1 ≡ M1
closed⊢>≡₁ p →*-refl = ⊢>≡-refl p
closed⊢>≡₁ p (→*-trans1 x t1) = qap-trans (▹wh-closed⊢>≡₁ p x) (closed⊢>≡₁ (▹wh-tp-preserve p x) t1)

mutual
 soundness1 : ∀ {Γ T} {M1 M2} -> Γ ⊢ M1 ∶ T -> Γ ⊢ M2 ∶ T -> Γ ⊢ T > M1 ⇔ M2 -> Γ ⊢ T > M1 ≡ M2
 soundness1 p1 p2 (qat-base x x₁ x₂) = qap-trans (closed⊢>≡₁ p1 x) (qap-trans (soundness2 (→*-tp-preserve p1 x) (→*-tp-preserve p2 x₁) x₂) (qap-sym (closed⊢>≡₁ p2 x₁)))
 soundness1 p1 p2 (qat-arrow {T} {S} p) = qat-ext (soundness1 ([]v-typing ↑ (⊢w↑ {T = T}) p1 · (v z)) ([]v-typing ↑ (⊢w↑ {T = T}) p2 · (v z)) p)
 soundness1 p1 p2 qat-unit = qap-unit p1 p2
 
 soundness2 : ∀ {Γ T S U} {M1 M2} -> Γ ⊢ M1 ∶ T -> Γ ⊢ M2 ∶ S -> Γ ⊢ U > M1 ↔ M2 -> Γ ⊢ T > M1 ≡ M2
 soundness2 (v .x) (v x) (qap-var .x) = qap-var x
 soundness2 (p0 · p1) (q0 · q1) (qap-app p x) with soundness2' p0 q0 p
 ... | (refl , refl) = qap-app (soundness2 p0 q0 p) (soundness1 p1 q1 x)
 soundness2 c c qap-const = qap-const

 soundness2' : ∀ {Γ T S U} {M1 M2} -> Γ ⊢ M1 ∶ T -> Γ ⊢ M2 ∶ S -> Γ ⊢ U > M1 ↔ M2 -> (T ≡ U) × (S ≡ U)
 soundness2' (v .x) (v x) (qap-var .x) = refl , refl
 soundness2' (p1 · p2) (p3 · p4) (qap-app d x) with soundness2' p1 p3 d
 ... | (refl , refl) = refl , refl
 soundness2' c c qap-const = refl , refl

open import Relation.Nullary

⇝-inj1 : ∀ {T1 T2 S1 S2} -> (T1 ⇝ S1) ≡ (T2 ⇝ S2) -> T1 ≡ T2
⇝-inj1 refl = refl

⇝-inj2 : ∀ {T1 T2 S1 S2} -> (S1 ⇝ T1) ≡ (S2 ⇝ T2) -> T1 ≡ T2
⇝-inj2 refl = refl

suc-inj : ∀ {A : Set} {Γ : ctx A} {T} {U} {x y : var Γ T} -> (s {A} {Γ} {T} {U} x) ≡ (s y) -> x ≡ y
suc-inj refl = refl

var-dec : ∀ {A : Set} {Γ : ctx A} {T} (x y : var Γ T) -> Dec (x ≡ y)
var-dec z z = yes refl
var-dec z (s y) = no (λ ())
var-dec (s x) z = no (λ ())
var-dec (s x) (s y) with var-dec x y
var-dec (s x) (s .x) | yes refl = yes refl
var-dec (s x) (s y) | no ¬p = no (λ x₁ → ¬p (suc-inj x₁))

↔v-inj : ∀ {Γ T x y} -> Γ ⊢ T > (v x) ↔ (v y) -> x ≡ y
↔v-inj (qap-var x) = refl


mutual
 dec1 : ∀ {Γ T T'} {M M' N N'} -> Γ ⊢ T > M ↔ M' -> Γ ⊢ T' > N ↔ N' -> Dec (∃ (λ S -> (Γ ⊢ S > M ↔ N)))
 dec1 (qap-var x) (qap-var x₁) with var-dec x x₁
 dec1 (qap-var x) (qap-var .x) | yes refl = yes (_ , qap-var x)
 dec1 (qap-var x) (qap-var x₁) | no ¬p = no (λ {(S , y) → ¬p (↔v-inj y)})
 dec1 (qap-var x) (qap-app p2 x₁) = no (λ {(S , ())})
 dec1 (qap-var x) qap-const = no (λ {(S , ())})
 dec1 (qap-app p1 x) (qap-var x₁) = no (λ {(S , ())})
 dec1 (qap-app p1 x) (qap-app p2 x₁) with dec1 p1 p2
 dec1 (qap-app p1 x) (qap-app p2 x₁) | yes (S , p) with ↔≡tp p p2 | ↔≡tp (⊢↔-sym p) p1
 dec1 (qap-app p1 x) (qap-app p2 x₁) | yes (T₁ ⇝ T , p) | refl | refl with dec2 x x₁
 dec1 (qap-app p1 x) (qap-app p2 x₁) | yes (T₁ ⇝ T , p) | refl | refl | yes q = yes (T , qap-app p q)
 dec1 (qap-app p1 x) (qap-app p2 x₁) | yes (T₁ ⇝ T , p) | refl | refl | no ¬q = no (λ {(T' , qap-app q0 q1)  → ¬q (subst (λ α → _ ⊢ α > _ ⇔ _) (⇝-inj1 (↔≡tp q0 p2)) q1)})
 dec1 (qap-app p1 x) (qap-app p2 x₁) | no ¬p = no (λ {(S , qap-app q0 q1) → ¬p (_ , q0)})
 dec1 (qap-app p1 x) qap-const = no (λ {(S , ())})
 dec1 qap-const (qap-var x) = no (λ {(S , ())})
 dec1 qap-const (qap-app p2 x) = no (λ {(S , ())})
 dec1 qap-const qap-const = yes (atom , qap-const)

 dec2 : ∀ {Γ T} {M M' N N'} -> Γ ⊢ T > M ⇔ M' -> Γ ⊢ T > N ⇔ N' -> Dec (Γ ⊢ T > M ⇔ N)
 dec2 (qat-base x x₁ x₂) (qat-base x₃ x₄ x₅) with dec1 x₂ x₅
 dec2 (qat-base x x₁ x₂) (qat-base x₃ x₄ x₅) | yes (S , q) with ↔≡tp q x₅
 dec2 (qat-base x x₁ x₂) (qat-base x₃ x₄ x₅) | yes (.atom , q) | refl = yes (qat-base x x₃ q)
 dec2 {Γ} (qat-base x x₁ x₂) (qat-base x₃ x₄ x₅) | no ¬p = no (λ {(qat-base q0 q1 q2) → ¬p (atom , subst₂ (λ α β₁ → Γ ⊢ atom > α ↔ β₁) (lem0 q0 x q2 x₂) (lem1 q1 x₃ q2 x₅) q2)})
 dec2 (qat-arrow p1) (qat-arrow p2) with dec2 p1 p2
 dec2 (qat-arrow p1) (qat-arrow p2) | yes p = yes (qat-arrow p)
 dec2 (qat-arrow p1) (qat-arrow p2) | no ¬p = no (λ {(qat-arrow p3) → ¬p p3})
 dec2 qat-unit qat-unit = yes qat-unit

⇔-dec : ∀ {Γ T} {M N} -> Γ ⊢ M ∶ T -> Γ ⊢ N ∶ T -> Dec (Γ ⊢ T > M ⇔ N)
⇔-dec d1 d2 = dec2 (completeness (⊢>≡-refl d1)) (completeness (⊢>≡-refl d2))

≡-dec : ∀ {Γ T} {M N} -> Γ ⊢ M ∶ T -> Γ ⊢ N ∶ T -> Dec (Γ ⊢ T > M ≡ N)
≡-dec d1 d2 with ⇔-dec d1 d2
≡-dec d1 d2 | yes p = yes (soundness1 d1 d2 p)
≡-dec d1 d2 | no ¬p = no (λ x → ¬p (completeness x))

-- Could we derive an algorithm more directly by bypassing ⇔?
-- Hmm. We could just prove weak head normalization (on open terms), and define ⇔. Then do implement conversion
-- test by well-founded induction on ▹wh, lexicographic with type? Maybe some kind of spine-form induction?

-- TODO: Add Unit type
-- This business with untyped terms and assuming that w is 'well-typed' looks tricky for Beluga (schemas)
-- Maybe the intrinsically typed version is easier? How to repair it?