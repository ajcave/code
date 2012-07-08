{-# OPTIONS --type-in-type #-}
module sysf-term-model where

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

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

data tpctx (Δ : lctx) : (γ : ctx unit) -> Set where
 ⊡ : tpctx Δ ⊡
 _,_ : ∀ {γ} (Γ : tpctx Δ γ) -> (T : tp Δ) -> tpctx Δ (γ , tt)

lookup : ∀ {Δ} {γ : ctx unit} -> (Γ : tpctx Δ γ) -> var γ tt -> tp Δ
lookup ⊡ ()
lookup (Γ , T) z = T
lookup (Γ , T) (s y) = lookup Γ y

tpmap : ∀ {Δ1 Δ2 : lctx} {γ : ctx unit} -> (f : tp Δ1 -> tp Δ2) -> tpctx Δ1 γ  -> tpctx Δ2 γ
tpmap f ⊡ = ⊡
tpmap f (Γ , T) = (tpmap f Γ) , (f T)

data _,_⊢_∶_ (Δ : lctx) {γ : ctx unit} (Γ : tpctx Δ γ) : tm γ -> tp Δ -> Set where
 v : (x : var γ _) -> Δ , Γ ⊢ (v x) ∶ (lookup Γ x)
 ƛ : ∀ {T S M} -> Δ , (Γ , T) ⊢ M ∶ S -> Δ , Γ ⊢ ƛ M ∶ (T ⇒ S)
 Λ : ∀ {T : tp (Δ , _)} {M} -> (Δ , tt) , (tpmap [ s ]tv Γ) ⊢ M ∶ T -> Δ , Γ ⊢ M ∶ (Π T)
 _·_ : ∀ {T S M N} -> Δ , Γ ⊢ M ∶ (T ⇒ S) -> Δ , Γ ⊢ N ∶ T -> Δ , Γ ⊢ (M · N) ∶ S
 _$_ : ∀ {T : tp (Δ , _)} {M} -> Δ , Γ ⊢ M ∶ (Π T) -> (S : tp Δ)
         -> Δ , Γ ⊢ M ∶ ([ v ,,, S ]t T)

rtype : Set₁
rtype = tm ⊡ -> tm ⊡ -> Set

record good (R : rtype) : Set where
 constructor isgood
 field
  respect : ∀ {M1 M2 N1 N2} -> M1 ≈ M2 -> N1 ≈ N2 -> R M2 N2 -> R M1 N1

-- The Church encoding of *weak* existentials
-- because strong impredicative existentials (record) are inconsistent
-- This should allow the proof to be fairly directly translated into
-- Coq --impredicative-set
∃ : ∀ {R : Set₁} (P : R -> Set) -> Set
∃ P = ∀ C -> (∀ A -> P A -> C) -> C

∃-intro : ∀ {R} {P : R -> Set} -> (A : R) -> P A -> ∃ P
∃-intro A p = λ C x → x A p

∃-elim : ∀ {R} {P : R -> Set} -> ∃ P -> ∀ (C : Set) -> (∀ A -> P A -> C) -> C
∃-elim p C f = p C f

goodR : Set₁
goodR = ∃ good

⟦_⟧t : ∀ {Δ} (T : tp Δ) (θ : gksubst Δ rtype) -> rtype
⟦_⟧t (v y) θ M1 M2 = θ y M1 M2
⟦_⟧t (T ⇒ S) θ M1 M2 = ∀ {N1 N2} → ⟦ T ⟧t θ N1 N2 → ⟦ S ⟧t θ (M1 · N1) (M2 · N2)
⟦_⟧t (Π T) θ M1 M2 = (R : _) → good R → ⟦ T ⟧t (θ ,,, R) M1 M2

⟦_⟧t-good : ∀ {Δ} (T : tp Δ) (θ : gksubst Δ rtype) (θgood : (x : var Δ _) -> good (θ x)) -> good (⟦ T ⟧t θ)
⟦_⟧t-good (v y) θ θgood = θgood y
⟦_⟧t-good (T ⇒ S) θ θgood with ⟦ T ⟧t-good θ θgood | ⟦ S ⟧t-good θ θgood
⟦_⟧t-good (T ⇒ S) θ θgood | isgood y | isgood y' = isgood (λ x x' x0 x1 → y' (x · ≈-refl) (x' · ≈-refl) (x0 x1))
⟦_⟧t-good (Π T) θ θgood = isgood (λ M1≈M2 N1≈N2 x0 R Rgood → good.respect (⟦ T ⟧t-good (θ ,,, R) (extend' (good ∘ (θ ,,, R)) θgood Rgood)) M1≈M2 N1≈N2 (x0 R Rgood))

thm : ∀ {Δ γ M T} {Γ : tpctx Δ γ} (θ : gksubst Δ rtype) (θgood : (x : var Δ _) -> good (θ x))
 -> (σ1 σ2 : sub γ ⊡) -> (σgood : (x : var γ _) -> ⟦ lookup Γ x ⟧t θ (σ1 x) (σ2 x)) -> Δ , Γ ⊢ M ∶ T -> ⟦ T ⟧t θ ([ σ1 ] M) ([ σ2 ] M)
thm θ θgood σ1 σ2 σgood (v x) = σgood x
thm {Γ = Γ} θ θgood σ1 σ2 σgood (ƛ {T} {S} y) = λ {N1} {N2} x → good.respect (⟦ S ⟧t-good θ θgood)
  (≈-trans (β _ _) {!≈-refl'!})
  {!!}
  (thm θ θgood (σ1 ,,, N1) (σ2 ,,, N2) (extend' (λ x' → ⟦ lookup (Γ , T) x' ⟧t θ ((σ1 ,,, N1) x') ((σ2 ,,, N2) x')) σgood x) y)
thm θ θgood σ1 σ2 σgood (Λ M) = λ R Rgood → thm (θ ,,, R) (extend' (good ∘ (θ ,,, R)) θgood Rgood) σ1 σ2 {!!} M
thm θ θgood σ1 σ2 σgood (M · N) = thm θ θgood σ1 σ2 σgood M (thm θ θgood σ1 σ2 σgood N)
thm θ θgood σ1 σ2 σgood (M $ S) = {!!}