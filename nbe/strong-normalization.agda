module strong-normalization where

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

cong : ∀ {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong2 : ∀ {A B C : Set} (f : A -> B -> C) -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> f x z ≡ f y w
cong2 f refl refl = refl

eq-ind : ∀ {A} (P : A -> Set) -> {x y : A} -> x ≡ y -> P x -> P y
eq-ind P refl t = t 

eq-ind2 : ∀ {A B} (P : A -> B -> Set) -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> P x z -> P y w
eq-ind2 P refl refl t = t

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

var-dom-eq : ∀ {A : tp -> Set} {Γ T} {f g : ∀ {U} (x : var (Γ , T) U) -> A U} -> (∀ {U} (x : var Γ U) -> f (s x) ≡ g (s x)) -> f z ≡ g z -> _≡_ { ∀ {U} -> var (Γ , T) U -> A U } f g
var-dom-eq {f = f} {g = g} p q = funext-imp (λ U -> funext (λ x -> var-dom-eq' f g p q x))

ext-funct : ∀ {Γ1 Γ2 Γ3 U S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (x : var (Γ1 , U) S) -> ((ext σ1) ∘ (ext σ2)) x ≡ ext (σ1 ∘ σ2) x
ext-funct σ1 σ2 z = refl
ext-funct σ1 σ2 (s y) = refl

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> ext id x ≡ x
ext-id z = refl
ext-id (s y) = refl

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

_,,_ : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> tm Γ2 T -> sub (Γ1 , T) Γ2
(σ ,, M) z = M
(σ ,, M) (s y) = σ y

sub-ext : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> sub (Γ1 , T) (Γ2 , T)
sub-ext σ = ([ s ]v ∘₁ σ) ,, v z

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
[]v-eq-[] σ M = trans (sym []-id) ([]nv-funct v σ M)

data _→₁_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 _·l_ : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} -> M1 →₁ M2 -> (N1 : tm Γ T) -> (M1 · N1) →₁ (M2 · N1)
 _·r_ : ∀ {T S} (M1 : tm Γ (T ⇝ S)) {N1 N2 : tm Γ T} -> N1 →₁ N2 -> (M1 · N1) →₁ (M1 · N2)
 ƛ : ∀ {T S} {M1 M2 : tm (Γ , T) S} -> M1 →₁ M2 -> (ƛ M1) →₁ (ƛ M2)
 β : ∀ {T S} (M : tm (Γ , T) S) (N : tm Γ T) -> ((ƛ M) · N) →₁ [ v ,, N ] M

→₁≡-trans : ∀ {Γ T} {M N P : tm Γ T} -> M →₁ N -> N ≡ P -> M →₁ P
→₁≡-trans p refl = p

→₁-subst : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) {M1 M2 : tm Γ1 T} -> M1 →₁ M2 -> [ σ ]v M1 →₁ [ σ ]v M2
→₁-subst σ (y ·l N1) = →₁-subst σ y ·l [ σ ]v N1
→₁-subst σ (M1 ·r y) = [ σ ]v M1 ·r →₁-subst σ y
→₁-subst σ (ƛ y) = ƛ (→₁-subst (ext σ) y)
→₁-subst σ (β M N) = →₁≡-trans (β _ _) (trans ([]nv-funct (v ,, [ σ ]v N) (ext σ) M) (trans (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x → refl) refl)) (sym ([]vn-funct σ (v ,, N) M))))

→₁-subst2 : ∀ {Γ1 Γ2 T} (σ : sub Γ1 Γ2) {M1 M2 : tm Γ1 T} -> M1 →₁ M2 -> [ σ ] M1 →₁ [ σ ] M2
→₁-subst2 σ (y ·l N1) = →₁-subst2 σ y ·l [ σ ] N1
→₁-subst2 σ (M1 ·r y) = [ σ ] M1 ·r →₁-subst2 σ y
→₁-subst2 σ (ƛ y) = ƛ (→₁-subst2 (sub-ext σ) y)
→₁-subst2 σ (β M N) = →₁≡-trans (β _ _) (trans ([]-funct (v ,, [ σ ] N) (sub-ext σ) M) (trans (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x → trans ([]nv-funct (v ,, [ σ ] N) s (σ x)) []-id) refl)) (sym ([]-funct σ (v ,, N) M))))

data sn {Γ T} (M : tm Γ T) : Set where
 sn-intro : (∀ {M'} -> M →₁ M' -> sn M') -> sn M 

reduce : ∀ Γ T -> tm Γ T -> Set
reduce Γ (atom A) t = sn t
reduce Γ (T ⇝ S) t = ∀ Δ (σ : vsubst Γ Δ) (x : tm Δ T) -> reduce Δ T x -> reduce Δ S (([ σ ]v t) · x)

reduce-ext : ∀ {Γ Δ} {σ : ∀ {U} (x : var Γ U) -> tm Δ U} (θ : ∀ {U} (x : var Γ U) -> reduce Δ U (σ x)) {T} {t : tm Δ T} (w : reduce Δ T t) ->
 ∀ {U} (x : var (Γ , T) U) -> reduce Δ U ((σ ,, t) x)
reduce-ext θ w z = w
reduce-ext θ w (s y) = θ y

-- For some reason I started doing this in CPS style. Really it says ∃ t'' s.t. [ σ ]v t'' ≡ t (and also substitutes this into the →₁)
grar : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) {t : tm Γ1 T} {t'} -> [ σ ]v t →₁ t' -> (C : (t'' : _) -> Set) -> (∀ t'' -> t →₁ t'' -> C ([ σ ]v t'')) -> C t'
grar σ {v y} () C f
grar σ {v y · y'} (() ·l .([ σ ]v y')) C f
grar σ {v y · y'} (.(v (σ y)) ·r y0) C f = grar σ {y'} y0 (λ t'' → C (v (σ y) · t'')) (λ t'' x → f (v y · t'') ((v y) ·r x))
grar σ {(y · y') · y0} (y1 ·l .([ σ ]v y0)) C f = grar σ {y · y'} y1 (λ t'' → C (t'' · [ σ ]v y0)) (λ t'' x → f (t'' · y0) (x ·l y0))
grar σ {(y · y') · y0} (.([ σ ]v y · [ σ ]v y') ·r y1) C f = grar σ {y0} y1 (λ t'' → C (([ σ ]v y · [ σ ]v y') · t'')) (λ t'' x → f ((y · y') · t'') ((y · y') ·r x))
grar σ {ƛ y · y'} (y0 ·l .([ σ ]v y')) C f = grar σ y0 (λ t'' → C (t'' · [ σ ]v y')) (λ t'' x → f (t'' · y') (x ·l y'))
grar σ {ƛ y · y'} (.(ƛ ([ ext σ ]v y)) ·r y0) C f = grar σ y0 (λ t'' → C ([ σ ]v (ƛ y) · t'')) (λ t'' x → f (ƛ y · t'') ((ƛ y) ·r x))
grar σ {ƛ y · y'} (β .([ ext σ ]v y) .([ σ ]v y')) C f = eq-ind C (trans ([]vn-funct σ (v ,, y') y) (trans (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → refl) refl)) (sym ([]nv-funct (v ,, [ σ ]v y') (ext σ) y)))) (f _ (β _ _))
grar σ {ƛ y} (ƛ y') C f = grar (ext σ) y' (λ t'' → C (ƛ t'')) (λ t'' x → f (ƛ t'') (ƛ x))

sn-vsubst : ∀ {T Γ Δ} (σ : vsubst Γ Δ) {t : tm Γ T} (w : sn t) -> sn ([ σ ]v t)
sn-vsubst σ (sn-intro y) = sn-intro (λ x → grar σ x sn (λ t'' x' → sn-vsubst σ (y x'))) 

reduce-funct : ∀ {T Γ Δ} (σ : vsubst Γ Δ) {t : tm Γ T} (w : reduce Γ T t) -> reduce Δ T ([ σ ]v t)
reduce-funct {atom A} σ q = sn-vsubst σ q 
reduce-funct {T ⇝ S} σ w = λ Δ σ' x x' → eq-ind (reduce Δ S) (cong2 _·_ (sym ([]v-funct σ' σ _)) refl) (w Δ (σ' ∘ σ) x x')

data neutral {Γ} : ∀ {T} -> tm Γ T -> Set where
 v : ∀ {T} (x : var Γ T) -> neutral (v x)
 _·_ : ∀ {T S} (M : tm Γ (T ⇝ S)) (N : tm Γ T) -> neutral (M · N)

neutral-funct : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) (t : tm Γ1 T) -> neutral t -> neutral ([ σ ]v t)
neutral-funct σ (v y) r = v (σ y)
neutral-funct σ (y · y') r = [ σ ]v y · [ σ ]v y'
neutral-funct σ (ƛ y) ()

reduce-closed : ∀ {T Γ} {t t' : tm Γ T} -> (t →₁ t') -> reduce Γ T t -> reduce Γ T t'
reduce-closed {atom A} q (sn-intro y) = y q
reduce-closed {T ⇝ S} q r = λ Δ σ x x' → reduce-closed (→₁-subst σ q ·l x) (r Δ σ x x')

g : ∀ {Γ T S} {t : tm Γ (T ⇝ S)} (p : neutral t) x {s} (x' : (t · x) →₁ s) (C : (s' : _) -> Set) (f1 : ∀ t' -> t →₁ t' -> C (t' · x)) (f2 : ∀ x' -> x →₁ x' -> C (t · x')) -> C s
g p x (y ·l .x) C f1 f2 = f1 _ y
g {Γ} {T'} {S'} {t'} p x (.t' ·r y) C f1 f2 = f2 _ y
g () x (β M .x) C f1 f2

sn-app : ∀ {Γ T S} (t : tm Γ (T ⇝ S)) -> sn ([ s ]v t · v z) -> sn t
sn-app t (sn-intro y) = sn-intro (λ x → sn-app _ (y (→₁-subst s x ·l (v z))))

mutual
 reify : ∀ {T Γ} (t : tm Γ T) -> reduce Γ T t -> sn t
 reify {atom A} t r = r
 reify {T ⇝ S} t r = sn-app t (reify ([ s ]v t · v z) (r _ s (v z) (reflect (v z) (v z) (λ ()))))

 -- Ah, this comes from sticking "reduce" in for "sn" in the definition of sn..
 -- It looks a little like the standard technique for showing accessibility?
 reflect : ∀ {T Γ} (t : tm Γ T) -> neutral t -> (∀ {t'} -> t →₁ t' -> reduce Γ T t') -> reduce Γ T t
 reflect {atom A} t n f = sn-intro f
 reflect {T ⇝ S} t n f = λ Δ σ u red-u → h Δ σ u (reify u red-u) red-u
  where h : ∀ Δ (σ : vsubst _ Δ) u -> sn u -> reduce _ T u -> reduce _ S ([ σ ]v t · u)
        h Δ σ u (sn-intro y) red-u = reflect ([ σ ]v t · u) ([ σ ]v t · u) (λ x → g (neutral-funct σ t n) u x (reduce Δ S) (λ t'' p → grar σ p (λ s' → reduce Δ S (s' · u)) (λ t0 p2 → f p2 Δ σ u red-u)) (λ u' p → h Δ σ u' (y p) (reduce-closed p red-u)))


mutual
 abs : ∀ {Γ T S} {M : tm (Γ , T) S} {u} -> sn M -> sn u -> reduce Γ T u -> (∀ {u} -> reduce Γ T u -> reduce Γ S ([ v ,, u ] M)) -> reduce Γ S ((ƛ M) · u)
 abs sn-m sn-n ru f = reflect _ (_ · _) (λ x → abs2 sn-m sn-n ru f x)

 abs2 : ∀ {Γ T S} {M : tm (Γ , T) S} {u} -> sn M -> sn u -> reduce Γ T u -> (∀ {u} -> reduce Γ T u -> reduce Γ S ([ v ,, u ] M)) -> ∀ {t'} -> ((ƛ M) · u) →₁ t' -> reduce Γ S t'
 abs2 {Γ} {T} {S} {M} {u} (sn-intro y) sn-n ru f (ƛ y' ·l .u) = abs (y y') sn-n ru (λ x → reduce-closed (→₁-subst2 (v ,, _) y') (f x))
 abs2 {Γ} {T} {S} {M} sn-m (sn-intro y') ru f (.(ƛ M) ·r y) = abs sn-m (y' y) (reduce-closed y ru) f
 abs2 {Γ} {T} {S} {M} {u} sn-m sn-n ru f (β .M .u) = f ru

thm : ∀ {Γ Δ T} (σ : ∀ {U} (x : var Γ U) -> tm Δ U) (θ : ∀ {U} (x : var Γ U) -> reduce Δ U (σ x)) (t : tm Γ T) -> reduce Δ T ([ σ ] t)
thm σ θ (v y) = θ y
thm σ θ (M · N) = eq-ind (reduce _ _) (cong2 _·_ []v-id refl) ((thm σ θ M) _ id ([ σ ] N) (thm σ θ N))
thm σ θ (ƛ {T} {S} M) = λ Δ σ' x x' → reflect (ƛ ([ ext σ' ]v ([ sub-ext σ ] M)) · x) (ƛ ([ ext σ' ]v ([ sub-ext σ ] M)) · x)
   (λ x0 → reduce-closed x0 (abs (reify _
   (eq-ind (reduce (Δ , T) S)
    (sym (trans ([]vn-funct (ext σ') (sub-ext σ) M)
     (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x1 →
     trans ([]v-funct (ext σ') s (σ x1))
      (sym ([]v-funct s σ' (σ x1)))) refl))))
   (thm (sub-ext ([ σ' ]v ∘₁ σ)) (reduce-ext (λ x1 → reduce-funct s (reduce-funct σ' (θ x1))) (reflect (v z) (v z) (λ ()))) M)))
   (reify _ x') x'
   (λ {u} x1 →
   eq-ind (reduce Δ S)
   (trans (trans (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x2 → trans ([]v-eq-[] σ' (σ x2))
     (sym ([]nv-funct ((v ,, u) ∘₁ ext σ') s (σ x2)))) refl))
     (sym ([]-funct   ((v ,, u) ∘₁ ext σ') (sub-ext σ) M)))
     (sym ([]nv-funct (v ,, u) (ext σ') ([ sub-ext σ ] M))))
  (thm (([ σ' ]v ∘₁ σ) ,, u) (reduce-ext (λ x2 → reduce-funct σ' (θ x2)) x1) M))))

done : ∀ {Γ T} (t : tm Γ T) -> sn t
done t = reify t (eq-ind (reduce _ _) []-id (thm v (λ x → reflect (v x) (v x) (λ ())) t))

-- Cool, now we could write an evaluator using any strategy (cbv, cbn...) with an "irrelevant" sn argument
-- which witnesses its termination (well-founded induction on the step relation)