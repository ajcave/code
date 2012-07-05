{-# OPTIONS --type-in-type #-}
module sysf-new where

data nat : Set where
 z : nat
 s : nat -> nat

data Fin : nat -> Set where
 z : ∀ {n} -> Fin (s n)
 s : ∀ {n} -> Fin n -> Fin (s n)

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

data tvar {A : Set} : ∀ (Δ : ctx A) (x : A) -> Set where
 z : ∀ {Δ T} -> tvar (Δ , T) T
 s : ∀ {Δ T S} -> tvar Δ T -> tvar (Δ , S) T

record unit : Set where
 constructor tt

lctx = ctx unit

data tp (Δ : lctx) : Set where
 v : tvar Δ _ -> tp Δ 
 _⇒_ : ∀ (T : tp Δ) -> (S : tp Δ) -> tp Δ
 Π : ∀ (T : tp (Δ , _)) -> tp Δ

tctx : lctx -> Set
tctx Δ = ctx (tp Δ)

var : ∀ {Δ : lctx} (Γ : tctx Δ) (T : tp Δ) -> Set
var {Δ} Γ T = tvar {tp Δ} Γ T

tctxM : ∀ {A B} (f : A -> B) -> ctx A -> ctx B
tctxM f ⊡ = ⊡
tctxM f (Γ , x) = tctxM f Γ , f x 

gsubst : ∀ {A} (Γ : ctx A) (F : A -> Set) -> Set
gsubst Γ F = ∀ {U : _} -> (x : tvar Γ U) -> F U

gvsubst : ∀ {A} (Γ Δ : ctx A) -> Set
gvsubst Γ Δ = gsubst Γ (tvar Δ)

tvsubst : ∀ Δ1 Δ2 -> Set
tvsubst Δ1 Δ2 = gvsubst Δ1 Δ2

tsubst : ∀ Δ1 Δ2 -> Set
tsubst Δ1 Δ2 = ∀ {l} -> (T : tvar Δ1 l) -> tp Δ2

_∘_ : ∀ {A : Set} {B : Set} {C : Set} (g : B -> C) (f : A -> B) -> A -> C
(g ∘ f) x = g (f x)

_,,_ : ∀ {Δ1 Δ2 l} -> tvsubst Δ1 Δ2 -> tvar Δ2 l -> tvsubst (Δ1 , l) Δ2
_,,_ σ x z = x
_,,_ σ x (s y) = σ y

_,,,_ : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp Δ2 -> tsubst (Δ1 , _) Δ2
(θ ,,, T) z = T
(θ ,,, T) (s y) = θ y

_×_ : ∀ {Δ1 Δ2 l m} -> tvsubst Δ1 Δ2 -> tvar (Δ2 , l) m -> tvsubst (Δ1 , m) (Δ2 , l)
(σ × y) = (s ∘ σ) ,, y

[_] : ∀ {Δ1 Δ2} -> tvsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[ σ ] (v y) = v (σ y)
[ σ ] (T ⇒ S) = [ σ ] T ⇒ [ σ ] S
[ σ ] (Π T) = Π ([ σ × z ] T)

_××_ : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp (Δ2 , _) -> tsubst (Δ1 , _) (Δ2 , _)
(θ ×× y) = ([ s ] ∘ θ) ,,, y

[[_]] : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[[ θ ]] (v y) = θ y
[[ θ ]] (T ⇒ S) = [[ θ ]] T ⇒ [[ θ ]] S
[[ θ ]] (Π T) = Π ([[ θ ×× v z ]] T)

… : ∀ {A : Set} -> A -> A
… x = x

data tm (Δ : lctx) (Γ : tctx Δ) : tp Δ -> Set where
 v : ∀ {T : tp Δ} -> var Γ T -> tm Δ Γ T
 ƛ : ∀ {T S : tp Δ} -> tm Δ (Γ , T) S -> tm Δ Γ (T ⇒ S)
 Λ : ∀ {T : tp (Δ , _)} -> tm (Δ , _) (tctxM [ s ] Γ) T -> tm Δ Γ (Π T)
 _·_ : ∀ {T : tp Δ} {S : tp Δ} -> tm Δ Γ (T ⇒ S) -> tm Δ Γ T -> tm Δ Γ S
 _$_ : ∀ {T : tp (Δ , _)} -> tm Δ Γ (Π T) -> (S : tp Δ)
         -> tm Δ Γ ([[ (v ∘ …) ,,, S ]] T)