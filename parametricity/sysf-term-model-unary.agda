{-# OPTIONS --type-in-type #-}
module sysf-term-model-unary where

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

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

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

record Σ_ {A : Set}(B : A -> Set) : Set where
  constructor _,_ 
  field
    fst : A
    snd : B fst

record _*_ (A : Set) (B : Set) : Set where
  constructor _,_ 
  field
    fst : A
    snd : B

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (x : A) -> ctx A

data var {A : Set} : ∀ (Δ : ctx A) (x : A) -> Set where
 z : ∀ {Δ T} -> var (Δ , T) T
 s : ∀ {Δ T S} -> var Δ T -> var (Δ , S) T

record unit : Set where
 constructor tt

lctx = ctx unit

data tp (Δ : lctx) : Set where
 v : var Δ _ -> tp Δ 
 _⇒_ : ∀ (T : tp Δ) -> (S : tp Δ) -> tp Δ
 Π : ∀ (T : tp (Δ , _)) -> tp Δ

tctx : lctx -> Set
tctx Δ = ctx (tp Δ)

{-var : ∀ {Δ : lctx} (Γ : tctx Δ) (T : tp Δ) -> Set
var {Δ} Γ T = gvar {tp Δ} Γ T -}

map : ∀ {A B} (f : A -> B) -> ctx A -> ctx B
map f ⊡ = ⊡
map f (Γ , x) = map f Γ , f x 

gsubst : ∀ {A} (Γ : ctx A) (F : A -> Set) -> Set
gsubst Γ F = ∀ {U : _} -> (x : var Γ U) -> F U

gksubst : ∀ {A} (Γ : ctx A) (F : Set) -> Set
gksubst Γ F = gsubst Γ (λ _ -> F)

gvsubst : ∀ {A} (Γ Δ : ctx A) -> Set
gvsubst Γ Δ = gsubst Γ (var Δ)

tvsubst : ∀ Δ1 Δ2 -> Set
tvsubst Δ1 Δ2 = gvsubst Δ1 Δ2

tsubst : ∀ Δ1 Δ2 -> Set
tsubst Δ1 Δ2 = gsubst Δ1 (λ _ -> tp Δ2)

_∘_ : ∀ {A : Set} {B : Set} {C : Set} (g : B -> C) (f : A -> B) -> A -> C
(g ∘ f) x = g (f x)

extend' : ∀ {A} {Γ T} (P : ∀ {U : A} (x : var (Γ , T) U) -> Set) -> (∀ {U} (x : var Γ U) -> P (s x)) -> P z -> ∀ {U} (x : var (Γ , T) U) -> P x
extend' P p q z = q
extend' P p q (s y) = p y

extend : ∀ {A Γ} (F : A -> Set) {U} -> gsubst Γ F -> F U -> gsubst (Γ , U) F
extend F σ x z = x
extend F σ x (s y) = σ y

_,,_ : ∀ {A} {Δ1 Δ2 : ctx A} {U : A} -> gvsubst Δ1 Δ2 -> var Δ2 U -> gvsubst (Δ1 , U) Δ2
_,,_ = extend (λ U -> var _ U)

_×_ : ∀ {Δ1 Δ2 l m} -> tvsubst Δ1 Δ2 -> var (Δ2 , l) m -> tvsubst (Δ1 , m) (Δ2 , l)
(σ × y) = (s ∘ σ) ,, y

[_]tv : ∀ {Δ1 Δ2} -> tvsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[ σ ]tv (v y) = v (σ y)
[ σ ]tv (T ⇒ S) = [ σ ]tv T ⇒ [ σ ]tv S
[ σ ]tv (Π T) = Π ([ σ × z ]tv T)

_,,,_ : ∀ {Δ1} {U} {S} -> gksubst Δ1 S -> S -> gksubst (Δ1 , U) S
_,,,_ {S = S} = extend (λ _ -> S)

_××_ : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp (Δ2 , _) -> tsubst (Δ1 , _) (Δ2 , _)
(θ ×× y) = ([ s ]tv ∘ θ) ,,, y

[_]t : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[ θ ]t (v y) = θ y
[ θ ]t (T ⇒ S) = [ θ ]t T ⇒ [ θ ]t S
[ θ ]t (Π T) = Π ([ θ ×× v z ]t T)

id : ∀ {A : Set} -> A -> A
id x = x

data tm (Γ : ctx unit) : Set where
 v : var Γ _ -> tm Γ
 ƛ : tm (Γ , tt) -> tm Γ
 _·_ : tm Γ -> tm Γ -> tm Γ

ext : ∀ {Γ Δ T} -> gvsubst Γ Δ -> gvsubst (Γ , T) (Δ , T)
ext σ = extend (var (_ , tt)) (s ∘ σ) z

[_]v : ∀ {Γ1 Γ2} (σ : gvsubst Γ1 Γ2) -> (M : tm Γ1) -> tm Γ2
[_]v σ (v y) = v (σ y)
[_]v σ (M · N) = [ σ ]v M · [ σ ]v N
[_]v σ (ƛ M) = ƛ ([ (s ∘ σ) ,, z ]v M)

sub : ∀ Γ1 Γ2 -> Set
sub Γ1 Γ2 = gksubst Γ1 (tm Γ2)

sub-ext : ∀ {Γ1 Γ2} -> sub Γ1 Γ2 -> sub (Γ1 , tt) (Γ2 , tt)
sub-ext σ z = v z
sub-ext σ (s y) = [ s ]v (σ y)

[_] : ∀ {Γ1 Γ2} (σ : sub Γ1 Γ2) -> (M : tm Γ1) -> tm Γ2
[_] σ (v y) = σ y
[_] σ (M · N) = [ σ ] M · [ σ ] N
[_] σ (ƛ M) = ƛ ([ sub-ext σ ] M)

[]v-cong : ∀ {Γ1 Γ2} (σ1 σ2 : gvsubst Γ1 Γ2) (p : (x : var Γ1 tt) -> σ1 x ≡ σ2 x) (M : tm Γ1) -> [ σ1 ]v M ≡ [ σ2 ]v M
[]v-cong σ1 σ2 p (v y) = cong v (p y)
[]v-cong σ1 σ2 p (ƛ y) = cong ƛ ([]v-cong (ext σ1) (ext σ2) (extend' (λ x → ext σ1 x ≡ ext σ2 x) (λ x → cong s (p x)) refl) y)
[]v-cong σ1 σ2 p (y · y') = cong2 _·_ ([]v-cong σ1 σ2 p y) ([]v-cong σ1 σ2 p y')

[]-cong : ∀ {Γ1 Γ2} (σ1 σ2 : sub Γ1 Γ2) (p : (x : var Γ1 tt) -> σ1 x ≡ σ2 x) (M : tm Γ1) -> [ σ1 ] M ≡ [ σ2 ] M
[]-cong σ1 σ2 p (v y) = p y
[]-cong σ1 σ2 p (ƛ y) = cong ƛ ([]-cong (sub-ext σ1) (sub-ext σ2) (extend' (λ x → sub-ext σ1 x ≡ sub-ext σ2 x) (λ x → cong [ s ]v (p x)) refl) y)
[]-cong σ1 σ2 p (y · y') = cong2 _·_ ([]-cong σ1 σ2 p y) ([]-cong σ1 σ2 p y')

[]v-funct : ∀ {Γ1 Γ2 Γ3} (σ1 : gvsubst Γ2 Γ3) (σ2 : gvsubst Γ1 Γ2) (R : tm Γ1)
  -> [ σ1 ]v ([ σ2 ]v R) ≡ [ σ1 ∘ σ2 ]v R
[]v-funct σ1 σ2 (v y) = refl
[]v-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]v-funct (ext σ1) (ext σ2) y) ([]v-cong (ext σ1 ∘ ext σ2) (ext (σ1 ∘ σ2))
  (extend' (λ x → (ext σ1 ∘ ext σ2) x ≡ ext (σ1 ∘ σ2) x) (λ x → refl) refl) y))
[]v-funct σ1 σ2 (y · y') = cong2 _·_ ([]v-funct σ1 σ2 y) ([]v-funct σ1 σ2 y')

[]vn-funct : ∀ {Γ1 Γ2 Γ3} (σ1 : gvsubst Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1)
  -> [ σ1 ]v ([ σ2 ] R) ≡ [ [ σ1 ]v ∘ σ2 ] R
[]vn-funct σ1 σ2 (v y) = refl
[]vn-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]vn-funct (ext σ1) (sub-ext σ2) y) ([]-cong ([ ext σ1 ]v ∘ sub-ext σ2) (sub-ext ([ σ1 ]v ∘ σ2))
 (extend' (λ x → ([ ext σ1 ]v ∘ sub-ext σ2) x ≡ sub-ext ([ σ1 ]v ∘ σ2) x)
          (λ x → trans ([]v-funct (ext σ1) s (σ2 x)) (sym ([]v-funct s σ1 (σ2 x))))
          refl)
 y))
[]vn-funct σ1 σ2 (y · y') = cong2 _·_ ([]vn-funct σ1 σ2 y) ([]vn-funct σ1 σ2 y')

[]nv-funct : ∀ {Γ1 Γ2 Γ3} (σ1 : sub Γ2 Γ3) (σ2 : gvsubst Γ1 Γ2) (R : tm Γ1)
  -> [ σ1 ] ([ σ2 ]v R) ≡ [ σ1 ∘ σ2 ] R
[]nv-funct σ1 σ2 (v y) = refl
[]nv-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]nv-funct (sub-ext σ1) (ext σ2) y) ([]-cong (sub-ext σ1 ∘ ext σ2) (sub-ext (σ1 ∘ σ2))
  (extend' (λ x → (sub-ext σ1 ∘ ext σ2) x ≡ sub-ext (σ1 ∘ σ2) x) (λ x → refl) refl) y))
[]nv-funct σ1 σ2 (y · y') = cong2 _·_ ([]nv-funct σ1 σ2 y) ([]nv-funct σ1 σ2 y')

[]-funct : ∀ {Γ1 Γ2 Γ3} (σ1 : sub Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1)
  -> [ σ1 ] ([ σ2 ] R) ≡ [ [ σ1 ] ∘ σ2 ] R
[]-funct σ1 σ2 (v y) = refl
[]-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]-funct (sub-ext σ1) (sub-ext σ2) y) ([]-cong ([ sub-ext σ1 ] ∘ sub-ext σ2) (sub-ext ([ σ1 ] ∘ σ2))
  (extend' (λ x → ([ sub-ext σ1 ] ∘ sub-ext σ2) x ≡ sub-ext ([ σ1 ] ∘ σ2) x)
     (λ x → trans ([]nv-funct (sub-ext σ1) s (σ2 x)) (sym ([]vn-funct s σ1 (σ2 x))))
     refl)
  y))
[]-funct σ1 σ2 (y · y') = cong2 _·_ ([]-funct σ1 σ2 y) ([]-funct σ1 σ2 y')

sub-ext-idv : ∀ {Γ T U} (x : var (Γ , T) U) -> (ext id) x ≡ x
sub-ext-idv z = refl
sub-ext-idv (s y) = refl

[]v-id : ∀ {Γ} {M : tm Γ} -> [ id ]v M ≡ M
[]v-id {M = v y} = refl
[]v-id {M = M · N} = cong2 _·_ []v-id []v-id
[]v-id {M = ƛ M} = cong ƛ (trans ([]v-cong (ext id) id sub-ext-idv M) []v-id)

sub-ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> (sub-ext v) x ≡ v x
sub-ext-id z = refl
sub-ext-id (s y) = refl

[]-id : ∀ {Γ} {M : tm Γ} -> [ v ] M ≡ M
[]-id {M = v y} = refl
[]-id {M = M · N} = cong2 _·_ []-id []-id
[]-id {M = ƛ M} = cong ƛ (trans ([]-cong (sub-ext v) v sub-ext-id M) []-id)

data _≈_ {Γ} : tm Γ -> tm Γ -> Set where
 v : ∀ (x : var Γ _) -> (v x) ≈ (v x)
 _·_ : ∀ {M1 M2} {N1 N2} -> M1 ≈ M2 -> N1 ≈ N2 -> (M1 · N1) ≈ (M2 · N2)
 ƛ : ∀ {M1 M2} -> M1 ≈ M2 -> (ƛ M1) ≈ (ƛ M2)
 β : ∀ M N -> ((ƛ M) · N) ≈ [ v ,,, N ] M
 η : ∀ M -> M ≈ (ƛ ([ s ]v M · (v z)))
 ≈-trans : ∀ {M N P} -> M ≈ N -> N ≈ P -> M ≈ P
 ≈-sym : ∀ {M N} -> M ≈ N -> N ≈ M

≈-refl : ∀ {Γ} {M : tm Γ} -> M ≈ M
≈-refl {M = v y} = v y
≈-refl {M = M · N} = ≈-refl · ≈-refl
≈-refl {M = ƛ M} = ƛ ≈-refl

≈≡-trans : ∀ {Γ} {M N P : tm Γ} -> M ≈ N -> N ≡ P -> M ≈ P
≈≡-trans p refl = p

data _,_⊢_∶_ (Δ : lctx) {γ : ctx unit} (Γ : gksubst γ (tp Δ)) : tm γ -> tp Δ -> Set where
 v : (x : var γ _) -> Δ , Γ ⊢ (v x) ∶ (Γ x)
 ƛ : ∀ {T S M} -> Δ , (Γ ,,, T) ⊢ M ∶ S -> Δ , Γ ⊢ ƛ M ∶ (T ⇒ S)
 Λ : ∀ {T : tp (Δ , _)} {M} -> (Δ , tt) , ([ s ]tv ∘ Γ) ⊢ M ∶ T -> Δ , Γ ⊢ M ∶ (Π T)
 _·_ : ∀ {T S M N} -> Δ , Γ ⊢ M ∶ (T ⇒ S) -> Δ , Γ ⊢ N ∶ T -> Δ , Γ ⊢ (M · N) ∶ S
 _$_ : ∀ {T : tp (Δ , _)} {M} -> Δ , Γ ⊢ M ∶ (Π T) -> (S : tp Δ)
         -> Δ , Γ ⊢ M ∶ ([ v ,,, S ]t T)

rtype : Set₁
rtype = tm ⊡ -> Set

record good (R : rtype) : Set where
 constructor isgood
 field
  respect : ∀ {M1 M2} -> M1 ≈ M2 -> R M2 -> R M1

⟦_⟧t : ∀ {Δ} (T : tp Δ) (θ : gksubst Δ rtype) -> rtype
⟦_⟧t (v y) θ M1 = θ y M1
⟦_⟧t (T ⇒ S) θ M1 = ∀ {N1} → ⟦ T ⟧t θ N1 → ⟦ S ⟧t θ (M1 · N1)
⟦_⟧t (Π T) θ M1 = (R : _) → good R → ⟦ T ⟧t (θ ,,, R) M1

_<->_ : Set -> Set -> Set
A <-> B = (A -> B) * (B -> A)

<->-refl : ∀ {A} -> A <-> A
<->-refl = id , id

<->-trans : ∀ {A B C} -> A <-> B -> B <-> C -> A <-> C
<->-trans (y , y') (y0 , y1) = (λ x → y0 (y x)) , (λ x → y' (y1 x))

_<->-cong-→_ : ∀ {T1 T2 S1 S2} -> T1 <-> T2 -> S1 <-> S2 -> (T1 → S1) <-> (T2 → S2)
_<->-cong-→_ (y , y') (y0 , y1) = (λ x x' → y0 (x (y' x'))) , (λ x x' → y1 (x (y x')))

<->-cong-expl : ∀ {A} {T1 T2 : A -> Set} -> (∀ x -> T1 x <-> T2 x) -> (∀ x -> T1 x) <-> (∀ x -> T2 x)
<->-cong-expl f = (λ x x' → _*_.fst (f x') (x x')) , (λ x x' → _*_.snd (f x') (x x'))

<->-cong-impl : ∀ {A} {T1 T2 : A -> Set} -> (∀ x -> T1 x <-> T2 x) -> (∀ {x} -> T1 x) <-> (∀ {x} -> T2 x)
<->-cong-impl f = (λ x → λ {x'} → _*_.fst (f x') x) , λ x → λ {x'} → _*_.snd (f x') x

_≃_ : ∀ (R S : rtype) -> Set
R ≃ S = ∀ {M1} -> (R M1) <-> (S M1)

≃-refl : ∀ {R} -> R ≃ R
≃-refl = <->-refl

_≃s_ : ∀ {Δ : ctx unit} (R S : gksubst Δ rtype) -> Set
R ≃s S = ∀ x -> (R x) ≃ (S x)

⟦_⟧t-cong : ∀ {Δ} (T : tp Δ) (θ1 θ2 : gksubst Δ rtype) -> (∀ x -> θ1 x ≃ θ2 x) -> ⟦ T ⟧t θ1 ≃ ⟦ T ⟧t θ2
⟦_⟧t-cong (v y) θ1 θ2 f = f y
⟦_⟧t-cong (T ⇒ S) θ1 θ2 f = <->-cong-impl (λ N1 → ⟦ T ⟧t-cong θ1 θ2 f <->-cong-→ ⟦ S ⟧t-cong θ1 θ2 f)
⟦_⟧t-cong (Π T) θ1 θ2 f = <->-cong-expl (λ R → <->-cong-expl (λ Rgood → ⟦ T ⟧t-cong (θ1 ,,, R) (θ2 ,,, R)
   (extend' (λ x → (θ1 ,,, R) x ≃ (θ2 ,,, R) x) f <->-refl)))

f1' : ∀ {Δ1 Δ2} (σ : tvsubst Δ1 Δ2) (θ : gksubst Δ2 rtype) R -> ((θ ,,, R) ∘ (σ × z)) ≃s ((θ ∘ σ) ,,, R)
f1' σ θ R z = <->-refl
f1' σ θ R (s y) = <->-refl

⟦⟧tv-subst : ∀ {Δ1 Δ2} (σ : tvsubst Δ1 Δ2) T (θ : gksubst Δ2 rtype)
  -> (⟦ [ σ ]tv T ⟧t θ) ≃ (⟦ T ⟧t (θ ∘ σ))
⟦⟧tv-subst σ (v y) θ = <->-refl
⟦⟧tv-subst σ (T ⇒ S) θ = <->-cong-impl (λ N1 → (⟦⟧tv-subst σ T θ) <->-cong-→ (⟦⟧tv-subst σ S θ))
⟦⟧tv-subst σ (Π T) θ = <->-cong-expl (λ R → <->-cong-expl (λ Rgood → <->-trans (⟦⟧tv-subst (σ × z) T (θ ,,, R)) (⟦ T ⟧t-cong ((θ ,,, R) ∘ (σ × z)) ((θ ∘ σ) ,,, R) (f1' σ θ R))))

_•_ : ∀ {Δ1 Δ2} (θ : gksubst Δ2 rtype) (σ : tsubst Δ1 Δ2) -> gksubst Δ1 rtype
(θ • σ) x = ⟦ σ x ⟧t θ

f2' : ∀ {Δ1 Δ2} (σ : tsubst Δ1 Δ2) (θ : gksubst Δ2 rtype) R -> ((θ ,,, R) • (σ ×× (v z))) ≃s ((θ • σ) ,,, R)
f2' σ θ R z = <->-refl
f2' σ θ R (s y) = ⟦⟧tv-subst s (σ y) (θ ,,, R)

⟦⟧t-subst : ∀ {Δ1 Δ2} (σ : tsubst Δ1 Δ2) T (θ : gksubst Δ2 rtype)
  -> (⟦ [ σ ]t T ⟧t θ) ≃ (⟦ T ⟧t (θ • σ))
⟦⟧t-subst σ (v y) θ = <->-refl
⟦⟧t-subst σ (T ⇒ S) θ = <->-cong-impl (λ N1 → (⟦⟧t-subst σ T θ) <->-cong-→ (⟦⟧t-subst σ S θ))
⟦⟧t-subst σ (Π T) θ = <->-cong-expl (λ R → <->-cong-expl (λ Rgood → <->-trans (⟦⟧t-subst (σ ×× v z) T (θ ,,, R)) (⟦ T ⟧t-cong ((θ ,,, R) • (σ ×× v z)) ((θ • σ) ,,, R) (f2' σ θ R))))

⟦_⟧t-good : ∀ {Δ} (T : tp Δ) (θ : gksubst Δ rtype) (θgood : (x : var Δ _) -> good (θ x)) -> good (⟦ T ⟧t θ)
⟦_⟧t-good (v y) θ θgood = θgood y
⟦_⟧t-good (T ⇒ S) θ θgood with ⟦ T ⟧t-good θ θgood | ⟦ S ⟧t-good θ θgood
⟦_⟧t-good (T ⇒ S) θ θgood | isgood y | isgood y' = isgood (λ x x0 x1 → y' (x · ≈-refl) (x0 x1))
⟦_⟧t-good (Π T) θ θgood = isgood (λ M1≈M2 x0 R Rgood → good.respect (⟦ T ⟧t-good (θ ,,, R) (extend' (good ∘ (θ ,,, R)) θgood Rgood)) M1≈M2 (x0 R Rgood))

thm : ∀ {γ Δ M T} (Γ : gksubst γ (tp Δ)) (θ : gksubst Δ rtype) (θgood : (x : var Δ _) -> good (θ x))
 -> (σ1 : sub γ ⊡) -> (σgood : (x : var γ _) -> ⟦ Γ x ⟧t θ (σ1 x)) -> Δ , Γ ⊢ M ∶ T -> ⟦ T ⟧t θ ([ σ1 ] M)
thm Γ θ θgood σ1 σgood (v x) = σgood x
thm Γ θ θgood σ1 σgood (ƛ {T} {S} {m} y) = λ {N1} x → good.respect (⟦ S ⟧t-good θ θgood)
  (≈≡-trans (β _ _) (trans ([]-funct (v ,,, N1) (sub-ext σ1) m) ([]-cong ([ v ,,, N1 ] ∘ sub-ext σ1) (σ1 ,,, N1)
    (extend' (λ x' → ([ v ,,, N1 ] ∘ sub-ext σ1) x' ≡ (σ1 ,,, N1) x')
       (λ x' → trans ([]nv-funct (v ,,, N1) s (σ1 x')) []-id)
       refl) m)))
  (thm (Γ ,,, T) θ θgood (σ1 ,,, N1) (extend' (λ x' → ⟦ (Γ ,,, T) x' ⟧t θ ((σ1 ,,, N1) x')) σgood x) y)
thm Γ θ θgood σ1 σgood (Λ M) = λ R Rgood → thm ([ s ]tv ∘ Γ) (θ ,,, R) (extend' (good ∘ (θ ,,, R)) θgood Rgood) σ1 (λ x → _*_.snd (⟦⟧tv-subst s (Γ x) (θ ,,, R)) (σgood x)) M
thm Γ θ θgood σ1 σgood (M · N) = thm Γ θ θgood σ1 σgood M (thm Γ θ θgood σ1 σgood N)
thm Γ θ θgood σ1 σgood (_$_ {T} {m} M S) with thm Γ θ θgood σ1 σgood M (⟦ S ⟧t θ) (⟦ S ⟧t-good θ θgood)
... | q = _*_.snd (⟦⟧t-subst (v ,,, S) T θ) (_*_.snd (⟦ T ⟧t-cong (λ x -> ⟦ (v ,,, S) x ⟧t θ) (θ ,,, (⟦ S ⟧t θ))
  (extend' (λ x → (θ • (v ,,, S)) x ≃ (θ ,,, ⟦ S ⟧t θ) x)
           (λ x → <->-refl) <->-refl)) q)

⊡s : ∀ {A B : Set} -> gksubst (⊡ {B}) A
⊡s ()

-- TODO: Try generalizing to open terms, presheaf style
thm' : ∀ {Δ M T} (θ : gksubst Δ rtype) (θgood : (x : var Δ _) -> good (θ x))
 -> Δ , ⊡s ⊢ M ∶ T -> ⟦ T ⟧t θ M
thm' {T = T} θ θgood M = eq-ind (⟦ T ⟧t θ) []-id (thm ⊡s θ θgood v (λ ()) M)

thm'' : ∀ {m T} -> ⊡ , ⊡s ⊢ m ∶ T -> ⟦ T ⟧t ⊡s m
thm'' {m} {T} M = thm' {⊡} {m} {T} ⊡s (λ ()) M

test : ∀ {m} -> ⊡ , ⊡s ⊢ m ∶ (Π ((v z) ⇒ (v z))) -> (n : _) → (m · n) ≈ n
test d n = thm'' d (λ x → x ≈ n) (isgood ≈-trans) ≈-refl
-- TODO: Literate Agda this file. Then you can accidentally write a paper

--Ah, the advantage of doing it for a general set-theoretic model is that we could interpret
--system F functions in Agda, and get the Agda-level theorem about them
-- Try it for rank-1 polymorphism (actually no quantifiers, just type variables)
-- (Then we don't need set-in-set)
-- Try also with recursive types (stay predicative)
--Then it really is a DSL for "theorems for free"!
--Is there an alternate route to this? 
-- Show parametricity for the term model, then show soundness of the interpretation into Agda
-- Yes, this seems like it would work, and is easier
--Try to do the same thing that those online "calculate my free theorem" tools do
-- automatically with type-level computation (reduce it, instantiating all relations to be functions -- map)