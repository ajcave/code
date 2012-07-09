{-# OPTIONS --type-in-type #-}
module sysf-term-model where

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

[]-id : ∀ {Γ} {M : tm Γ} -> [ v ] M ≡ M
[]-id {M = M} = {!!}

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

{-data tpctx (Δ : lctx) : (γ : ctx unit) -> Set where
 ⊡ : tpctx Δ ⊡
 _,_ : ∀ {γ} (Γ : tpctx Δ γ) -> (T : tp Δ) -> tpctx Δ (γ , tt)

lookup : ∀ {Δ} {γ : ctx unit} -> (Γ : tpctx Δ γ) -> var γ tt -> tp Δ
lookup ⊡ ()
lookup (Γ , T) z = T
lookup (Γ , T) (s y) = lookup Γ y

tpmap : ∀ {Δ1 Δ2 : lctx} {γ : ctx unit} -> (f : tp Δ1 -> tp Δ2) -> tpctx Δ1 γ  -> tpctx Δ2 γ
tpmap f ⊡ = ⊡
tpmap f (Γ , T) = (tpmap f Γ) , (f T) -}

data _,_⊢_∶_ (Δ : lctx) {γ : ctx unit} (Γ : gksubst γ (tp Δ)) : tm γ -> tp Δ -> Set where
 v : (x : var γ _) -> Δ , Γ ⊢ (v x) ∶ (Γ x)
 ƛ : ∀ {T S M} -> Δ , (Γ ,,, T) ⊢ M ∶ S -> Δ , Γ ⊢ ƛ M ∶ (T ⇒ S)
 Λ : ∀ {T : tp (Δ , _)} {M} -> (Δ , tt) , ([ s ]tv ∘ Γ) ⊢ M ∶ T -> Δ , Γ ⊢ M ∶ (Π T)
 _·_ : ∀ {T S M N} -> Δ , Γ ⊢ M ∶ (T ⇒ S) -> Δ , Γ ⊢ N ∶ T -> Δ , Γ ⊢ (M · N) ∶ S
 _$_ : ∀ {T : tp (Δ , _)} {M} -> Δ , Γ ⊢ M ∶ (Π T) -> (S : tp Δ)
         -> Δ , Γ ⊢ M ∶ ([ v ,,, S ]t T)

rtype : Set₁
rtype = tm ⊡ -> tm ⊡ -> Set

record good (R : rtype) : Set where
 constructor isgood
 field
  respect : ∀ {M1 M2 N1 N2} -> M1 ≈ M2 -> N1 ≈ N2 -> R M2 N2 -> R M1 N1

⟦_⟧t : ∀ {Δ} (T : tp Δ) (θ : gksubst Δ rtype) -> rtype
⟦_⟧t (v y) θ M1 M2 = θ y M1 M2
⟦_⟧t (T ⇒ S) θ M1 M2 = ∀ {N1 N2} → ⟦ T ⟧t θ N1 N2 → ⟦ S ⟧t θ (M1 · N1) (M2 · N2)
⟦_⟧t (Π T) θ M1 M2 = (R : _) → good R → ⟦ T ⟧t (θ ,,, R) M1 M2

_<->_ : Set -> Set -> Set
A <-> B = (A -> B) * (B -> A)

<->-refl : ∀ {A} -> A <-> A
<->-refl = id , id

mutual
 ⟦_⟧t-cong : ∀ {Δ} (T : tp Δ) (θ1 θ2 : gksubst Δ rtype) -> (∀ x M1 M2 -> (θ1 x M1 M2 <-> θ2 x M1 M2)) -> ∀ M1 M2 -> (⟦ T ⟧t θ1 M1 M2 <-> ⟦ T ⟧t θ2 M1 M2)
 ⟦_⟧t-cong (v y) θ1 θ2 f M1 M2 = f y M1 M2
 ⟦_⟧t-cong (T ⇒ S) θ1 θ2 f M1 M2 = (λ x x' → _*_.fst (⟦ S ⟧t-cong θ1 θ2 f _ _) (x (_*_.snd (⟦ T ⟧t-cong θ1 θ2 f _ _) x')))
                                , (λ x x' → _*_.snd (⟦ S ⟧t-cong θ1 θ2 f _ _) (x (_*_.fst (⟦ T ⟧t-cong θ1 θ2 f _ _) x')))
 ⟦_⟧t-cong (Π T) θ1 θ2 f M1 M2 =
     (λ x R x' → _*_.fst (⟦ T ⟧t-cong (θ1 ,,, R) (θ2 ,,, R)
      (extend' (λ x0 → (M3 M4 : _) → (θ1 ,,, R) x0 M3 M4 <-> (θ2 ,,, R) x0 M3 M4)
               f (λ M3 M4 → id , id)) M1 M2) (x R x'))
   , (λ x R x' → _*_.snd (⟦ T ⟧t-cong (θ1 ,,, R) (θ2 ,,, R)
      (extend' (λ x0 → (M3 M4 : _) → (θ1 ,,, R) x0 M3 M4 <-> (θ2 ,,, R) x0 M3 M4)
               f (λ M3 M4 → id , id)) M1 M2) (x R x')) 

f1 : ∀ {Δ1 Δ2} (σ : tvsubst Δ1 Δ2) (θ : gksubst Δ2 rtype) R x' → (M1 M2 : _) → ((θ ∘ σ) ,,, R) x' M1 M2 <-> ((θ ,,, R) ∘ (σ × z)) x' M1 M2 
f1 σ θ R z M1 M2 = <->-refl
f1 σ θ R (s y) M1 M2 = <->-refl

mutual
 ⟦⟧tv-subst-fwd : ∀ {Δ1 Δ2} (σ : tvsubst Δ1 Δ2) T (θ : gksubst Δ2 rtype) {M1 M2}
  -> (⟦ [ σ ]tv T ⟧t θ) M1 M2 -> (⟦ T ⟧t (θ ∘ σ)) M1 M2
 ⟦⟧tv-subst-fwd σ (v y) θ t = t
 ⟦⟧tv-subst-fwd σ (T ⇒ S) θ t = λ x → ⟦⟧tv-subst-fwd σ S θ (t (⟦⟧tv-subst-bwd σ T θ x))
 ⟦⟧tv-subst-fwd σ (Π T) θ t = λ R x → _*_.snd (⟦ T ⟧t-cong ((θ ∘ σ) ,,, R) ((θ ,,, R) ∘ (σ × z)) (f1 σ θ R) _ _)
  (⟦⟧tv-subst-fwd (σ × z) T (θ ,,, R) (t R x))

 ⟦⟧tv-subst-bwd : ∀ {Δ1 Δ2} (σ : tvsubst Δ1 Δ2) T (θ : gksubst Δ2 rtype) {M1 M2} 
  -> (⟦ T ⟧t (θ ∘ σ)) M1 M2 -> (⟦ [ σ ]tv T ⟧t θ) M1 M2
 ⟦⟧tv-subst-bwd σ (v y) θ t = t
 ⟦⟧tv-subst-bwd σ (T ⇒ S) θ t = λ x → ⟦⟧tv-subst-bwd σ S θ (t (⟦⟧tv-subst-fwd σ T θ x))
 ⟦⟧tv-subst-bwd σ (Π T) θ t = λ R x → ⟦⟧tv-subst-bwd (σ × z) T (θ ,,, R) (_*_.fst (⟦ T ⟧t-cong ((θ ∘ σ) ,,, R) ((θ ,,, R) ∘ (σ × z))
   (f1 σ θ R) _ _) (t R x))

mutual
 ⟦⟧t-subst-fwd : ∀ {Δ1 Δ2} (σ : tsubst Δ1 Δ2) T (θ : gksubst Δ2 rtype) {M1 M2}
  -> (⟦ [ σ ]t T ⟧t θ) M1 M2 -> (⟦ T ⟧t (λ x -> ⟦ σ x ⟧t θ)) M1 M2
 ⟦⟧t-subst-fwd σ (v y) θ t = t
 ⟦⟧t-subst-fwd σ (T ⇒ S) θ t = λ x → ⟦⟧t-subst-fwd σ S θ (t (⟦⟧t-subst-bwd σ T θ x))
 ⟦⟧t-subst-fwd σ (Π T) θ t = λ R x → {!⟦⟧t-subst-fwd !} {-
  where f : ∀ R -> good R -> {!!}
        f R x with ⟦⟧t-subst-fwd (σ ×× v z) T (θ ,,, R) (t R x)
        ... | q = {!!} -}

 ⟦⟧t-subst-bwd : ∀ {Δ1 Δ2} (σ : tsubst Δ1 Δ2) T (θ : gksubst Δ2 rtype) {M1 M2} 
  -> (⟦ T ⟧t (λ x -> ⟦ σ x ⟧t θ)) M1 M2 -> (⟦ [ σ ]t T ⟧t θ) M1 M2
 ⟦⟧t-subst-bwd σ (v y) θ t = t
 ⟦⟧t-subst-bwd σ (T ⇒ S) θ t = λ x → ⟦⟧t-subst-bwd σ S θ (t (⟦⟧t-subst-fwd σ T θ x))
 ⟦⟧t-subst-bwd {Δ1} {Δ2} σ (Π T) θ {M1} {M2} t = λ R x → ⟦⟧t-subst-bwd (σ ×× v z) T (θ ,,, R) (_*_.fst (⟦ T ⟧t-cong ((λ x' → ⟦ σ x' ⟧t θ) ,,, R) (λ x' → ⟦ (σ ×× v z) x' ⟧t (θ ,,, R)) (extend'
                                                                                                                                                                                          (λ x' →
                                                                                                                                                                                             (M3 M4 : _) →
                                                                                                                                                                                             ((λ x0 → ⟦ σ x0 ⟧t θ) ,,, R) x' M3 M4 <->
                                                                                                                                                                                             (λ x0 → ⟦ (σ ×× v z) x0 ⟧t (θ ,,, R)) x' M3 M4)
                                                                                                                                                                                          {!!} (λ M3 M4 → <->-refl)) M1 M2) (t R x))

⟦_⟧t-good : ∀ {Δ} (T : tp Δ) (θ : gksubst Δ rtype) (θgood : (x : var Δ _) -> good (θ x)) -> good (⟦ T ⟧t θ)
⟦_⟧t-good (v y) θ θgood = θgood y
⟦_⟧t-good (T ⇒ S) θ θgood with ⟦ T ⟧t-good θ θgood | ⟦ S ⟧t-good θ θgood
⟦_⟧t-good (T ⇒ S) θ θgood | isgood y | isgood y' = isgood (λ x x' x0 x1 → y' (x · ≈-refl) (x' · ≈-refl) (x0 x1))
⟦_⟧t-good (Π T) θ θgood = isgood (λ M1≈M2 N1≈N2 x0 R Rgood → good.respect (⟦ T ⟧t-good (θ ,,, R) (extend' (good ∘ (θ ,,, R)) θgood Rgood)) M1≈M2 N1≈N2 (x0 R Rgood))

thm : ∀ {γ Δ M T} (Γ : gksubst γ (tp Δ)) (θ : gksubst Δ rtype) (θgood : (x : var Δ _) -> good (θ x))
 -> (σ1 σ2 : sub γ ⊡) -> (σgood : (x : var γ _) -> ⟦ Γ x ⟧t θ (σ1 x) (σ2 x)) -> Δ , Γ ⊢ M ∶ T -> ⟦ T ⟧t θ ([ σ1 ] M) ([ σ2 ] M)
thm Γ θ θgood σ1 σ2 σgood (v x) = σgood x
thm Γ θ θgood σ1 σ2 σgood (ƛ {T} {S} y) = λ {N1} {N2} x → good.respect (⟦ S ⟧t-good θ θgood)
  (≈-trans (β _ _) {!≈-refl'!})
  {!!}
  (thm (Γ ,,, T) θ θgood (σ1 ,,, N1) (σ2 ,,, N2) (extend' (λ x' → ⟦ (Γ ,,, T) x' ⟧t θ ((σ1 ,,, N1) x') ((σ2 ,,, N2) x')) σgood x) y)
thm Γ θ θgood σ1 σ2 σgood (Λ M) = λ R Rgood → thm ([ s ]tv ∘ Γ) (θ ,,, R) (extend' (good ∘ (θ ,,, R)) θgood Rgood) σ1 σ2 {!!} M
thm Γ θ θgood σ1 σ2 σgood (M · N) = thm Γ θ θgood σ1 σ2 σgood M (thm Γ θ θgood σ1 σ2 σgood N)
thm Γ θ θgood σ1 σ2 σgood (_$_ {T} {m} M S) with thm Γ θ θgood σ1 σ2 σgood M (⟦ S ⟧t θ) (⟦ S ⟧t-good θ θgood)
... | q = ⟦⟧t-subst-bwd (v ,,, S) T θ (_*_.snd (⟦ T ⟧t-cong (λ x -> ⟦ (v ,,, S) x ⟧t θ) (θ ,,, (⟦ S ⟧t θ))
  (extend' (λ x → (M1 M2 : _) → ⟦ (v ,,, S) x ⟧t θ M1 M2 <-> (θ ,,, ⟦ S ⟧t θ) x M1 M2)
           (λ x M1 M2 → <->-refl) (λ M1 M2 → <->-refl)) ([ σ1 ] m) ([ σ2 ] m)) q)

⊡s : ∀ {A B : Set} -> gksubst (⊡ {B}) A
⊡s ()

-- TODO: Try generalizing to open term, presheaf style
thm' : ∀ {Δ M T} (θ : gksubst Δ rtype) (θgood : (x : var Δ _) -> good (θ x))
 -> Δ , ⊡s ⊢ M ∶ T -> ⟦ T ⟧t θ M M
thm' {T = T} θ θgood M = eq-ind2 (⟦ T ⟧t θ) []-id []-id (thm ⊡s θ θgood v v (λ ()) M)

thm'' : ∀ {m T} -> ⊡ , ⊡s ⊢ m ∶ T -> ⟦ T ⟧t ⊡s m m
thm'' {m} {T} M = thm' {⊡} {m} {T} ⊡s (λ ()) M

test : ∀ {m} -> ⊡ , ⊡s ⊢ m ∶ (Π ((v z) ⇒ (v z))) -> (n : _) → (m · n) ≈ n
test d n = _*_.fst (thm'' d (λ x x' → (x ≈ n) * (x' ≈ n)) (isgood (λ M1≈M2 N1≈N2 x0 → (≈-trans M1≈M2 (_*_.fst x0)) , (≈-trans N1≈N2 (_*_.snd x0)))) (≈-refl , ≈-refl))
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