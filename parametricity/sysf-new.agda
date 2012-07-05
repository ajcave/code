{-# OPTIONS --type-in-type #-}
module sysf-new where


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

data tm (Δ : lctx) (Γ : tctx Δ) : tp Δ -> Set where
 v : ∀ {T : tp Δ} -> var Γ T -> tm Δ Γ T
 ƛ : ∀ {T S : tp Δ} -> tm Δ (Γ , T) S -> tm Δ Γ (T ⇒ S)
 Λ : ∀ {T : tp (Δ , _)} -> tm (Δ , _) (map [ s ]tv Γ) T -> tm Δ Γ (Π T)
 _·_ : ∀ {T : tp Δ} {S : tp Δ} -> tm Δ Γ (T ⇒ S) -> tm Δ Γ T -> tm Δ Γ S
 _$_ : ∀ {T : tp (Δ , _)} -> tm Δ Γ (Π T) -> (S : tp Δ)
         -> tm Δ Γ ([ v ,,, S ]t T)

⟦_⟧t : ∀ {Δ} (T : tp Δ) (θ : gksubst Δ Set) -> Set
⟦_⟧t (v y) θ = θ y
⟦_⟧t (T ⇒ S) θ = ⟦ T ⟧t θ → ⟦ S ⟧t θ
⟦_⟧t (Π T) θ = (S : _) → ⟦ T ⟧t (θ ,,, S)

⟦_⟧ : ∀ {Δ Γ T} (t : tm Δ Γ T) (θ : gksubst Δ Set) -> (σ : gsubst Γ (λ U -> ⟦ U ⟧t θ)) -> ⟦ T ⟧t θ
⟦_⟧ (v y) θ σ = σ y
⟦_⟧ (ƛ M) θ σ = λ x → ⟦ M ⟧ θ (extend (λ U → ⟦ U ⟧t θ) σ x)
⟦_⟧ (Λ M) θ σ = λ A → ⟦ M ⟧ (θ ,,, A) (λ x → {!!})
⟦_⟧ (M · N) θ σ = {!!}
⟦_⟧ (M $ S) θ σ = {!!} 