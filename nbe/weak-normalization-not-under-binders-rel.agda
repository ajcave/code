module weak-normalization-not-under-binders-rel where
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

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

vsubst : ctx -> ctx -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

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

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> ext id x ≡ x
ext-id z = refl
ext-id (s y) = refl

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = s

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)

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

data _→*_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 v : ∀ {T} (x : var Γ T) -> (v x) →* (v x)
 _·_ : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 N2 : tm Γ T} -> M1 →* M2 -> N1 →* N2 -> (M1 · N1) →* (M2 · N2)
 ƛ : ∀ {T S} {M1 M2 : tm (Γ , T) S} -> M1 →* M2 -> (ƛ M1) →* (ƛ M2)
 β : ∀ {T S} (M : tm (Γ , T) S) (N : tm Γ T) -> ((ƛ M) · N) →* [ v ,, N ] M
 η : ∀ {T S} (M : tm Γ (T ⇝ S)) -> M →* (ƛ ([ s ]v M · (v z)))
 →*-trans : ∀ {T} {M N P : tm Γ T} -> M →* N -> N →* P -> M →* P

→*-refl : ∀ {Γ T} {M : tm Γ T} -> M →* M
→*-refl {M = v y} = v y
→*-refl {M = M · N} = →*-refl · →*-refl
→*-refl {M = ƛ M} = ƛ →*-refl

data isNormal {Γ} : ∀ {T} (t : tm Γ T) -> Set where
 ƛ : ∀ {T S} (t : tm (Γ , T) S) -> isNormal (ƛ t)

halts : ∀ {Γ T} (t : tm Γ T) -> Set
halts {Γ} {T} t = Σ (λ (n : tm Γ T) → (t →* n) * isNormal n)

reduce : ∀ Γ T -> tm Γ T -> Set
reduce Γ (atom A) t = Σ (λ (n : tm Γ _) → (t →* n) * isNormal n)
reduce Γ (T ⇝ S) t = (Σ (λ (n : tm Γ _) → (t →* n) * isNormal n)) * (∀ (x : tm Γ T) -> reduce Γ T x -> reduce Γ S (t · x))

reduce-closed : ∀ {T Γ} {t t' : tm Γ T} -> (t →* t') -> reduce Γ T t' -> reduce Γ T t
reduce-closed {atom A} p (N , (q1 , q2)) = N , ((→*-trans p q1) , q2)
reduce-closed {T ⇝ S} p ((N , (q1 , q2)) , f) = (N , (→*-trans p q1 , q2)) , (λ x rx → reduce-closed (p · →*-refl) (f x rx))

reduce-ext : ∀ {Γ Δ} {σ : ∀ {U} (x : var Γ U) -> tm Δ U} (θ : ∀ {U} (x : var Γ U) -> reduce Δ U (σ x)) {T} {t : tm Δ T} (w : reduce Δ T t) ->
 ∀ {U} (x : var (Γ , T) U) -> reduce Δ U ((σ ,, t) x)
reduce-ext θ w z = w
reduce-ext θ w (s y) = θ y

lemma : ∀ {Γ Δ T S} -> (σ : sub Γ Δ) -> ∀ (N : tm Δ T) (M : tm (Γ , T) S) -> [ σ ,, N ] M ≡ [ v ,, N ] ([ sub-ext σ ] M)
lemma σ N M = trans (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x → trans (sym []-id) (sym ([]nv-funct (v ,, N) s (σ x)))) refl)) (sym ([]-funct (v ,, N) (sub-ext σ) M))

init : ∀ {Γ} -> sub ⊡ Γ
init ()

data IsInstantiation : ∀ {Γ A} -> tm Γ A -> tm ⊡ A -> Set where
 ⊡ : ∀ {A} {M : tm ⊡ A} -> IsInstantiation M M
 _,_ : ∀ {Γ A B U R} {M : tm (Γ , A) B} -> (i : IsInstantiation ([ v ,, ([ init ] U) ] M) R) -> (r : reduce ⊡ _ U) -> IsInstantiation M R

data IsApp {Γ A B} : tm Γ (A ⇝ B) -> tm Γ A -> tm ⊡ B -> Set where
 yep : ∀ {M M' N N'} -> (i1 : IsInstantiation M M') -> (i2 : IsInstantiation N N') -> IsApp M N (M' · N')

invApp : ∀ {Γ A B} {M : tm Γ (A ⇝ B)} {N R} -> IsInstantiation (M · N) R -> IsApp M N R
invApp ⊡ = yep ⊡ ⊡
invApp (i , r) with invApp i
invApp (i , r) | yep i1 i2 = yep (i1 , r) (i2 , r)

data IsLam {Γ A B} : tm (Γ , A) B -> tm ⊡ (A ⇝ B) -> Set where
 yep : ∀ {M M'} -> (∀ U -> reduce ⊡ _ U -> IsInstantiation M ([ init ,, U ] M')) -> IsLam M (ƛ M')

invLam : ∀ {Γ A B} {M : tm (Γ , A) B} {R} -> IsInstantiation (ƛ M) R -> IsLam M R
invLam {M = M} ⊡ = yep (λ U x → eq-ind (λ α → IsInstantiation α ([ init ,, U ] M)) (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ ()) (trans (sym []-id) (cong (λ (α : sub _ _) → [ α ] U) (funext-imp (λ x' → funext (λ ()))))))) ⊡ , x)
invLam {Γ , A'} {A} {B} {M} (_,_ {U = V} i r) with invLam i
... | yep {._} {M'} f = yep g
      where g : ∀ (U : tm ⊡ A) (redU : reduce ⊡ A U) -> _
            g U x with f U x
            g U x | (_,_ {U = V2} i' r') = (eq-ind (λ α → IsInstantiation α ([ init ,, U ] M')) (trans (sym (lemma _ _ M)) (trans (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x' → refl) (trans (cong (λ (α : sub _ _) → [ α ] V2) (funext-imp (λ x' → funext (λ ())))) (sym ([]-funct _ _ V2))))) (sym ([]-funct _ _ M)))) i' , r) , r'

thm-v : ∀ {Γ T} (y : var Γ T) {n} -> IsInstantiation (v y) n -> reduce ⊡ T n
thm-v z (i , r) = {!r!}
thm-v (s y) (i , r) = thm-v y i

thm : ∀ {Γ T} (t : tm Γ T) {n} -> IsInstantiation t n -> reduce ⊡ T n
thm (v y) i = thm-v y i
thm (M · N) i with invApp i
... | yep i1 i2 = _*_.snd (thm M i1) _ (thm N i2)
thm (ƛ M) i = {!!}

{-reify : ∀ {T Γ} (t : tm Γ T) -> reduce Γ T t -> halts t
reify {atom A} t p = p
reify {T ⇝ S} t p = _*_.fst p

done' : ∀ {T} (t : tm ⊡ T) -> halts t
done' t = reify _ (eq-ind (reduce _ _) []-id (thm v (λ ()) t))
-}