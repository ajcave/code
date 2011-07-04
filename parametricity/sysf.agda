{-# OPTIONS --type-in-type #-}
module sysf where

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

lctx = ctx unit

data tp (Δ : lctx) : Set where
 v : tvar Δ _ -> tp Δ 
 _⇒_ : ∀ (T : tp Δ) -> (S : tp Δ) -> tp Δ
 Π : ∀ (T : tp (Δ , _)) -> tp Δ

data tctx (Δ : lctx) : Set where
 ⊡ : tctx Δ
 _,_ : ∀ (Γ : tctx Δ) -> (T : tp Δ) -> tctx Δ

data var {Δ : lctx} : ∀ (Γ : tctx Δ) (T : tp Δ) -> Set where
 z : ∀ {Γ} {T : tp Δ} -> var (Γ , T) T
 s : ∀ {Γ} {T : tp Δ} {S : tp Δ} -> var Γ T -> var (Γ , S) T

tctxM : ∀ {Δ1 Δ2} (f : tp Δ1 -> tp Δ2) -> tctx Δ1 -> tctx Δ2
tctxM f ⊡ = ⊡
tctxM f (Γ , x) = tctxM f Γ , f x 
 
tvsubst : ∀ Δ1 Δ2 -> Set
tvsubst Δ1 Δ2 = ∀ {x : _ } (T : tvar Δ1 x) -> tvar Δ2 x

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

tuple : nat -> Set
tuple n = Fin n -> Set

∧_ : ∀ {n} (A : Fin n -> Set) -> Set
∧ A = ∀ i -> A i

⇔_ : ∀ {n} (A : Fin n -> Set) -> Set
⇔_ A = ∧ A -> Set

data Rel (n : nat) : Set where
 rel : ∀ {A : Fin n -> Set} -> ⇔ A -> Rel n

S : ∀ {A : Set} {B : A -> Set} {C : (x : A) -> B x -> Set}
 (f : (x : A) -> (y : B x) -> C x y) (g : (x : A) -> B x) -> ((x : A) -> C x (g x))
S f g i = f i (g i)

-- interesting how the S combinator shows up naturally here
_⇒·_ : ∀ {n} {A : tuple n} {B : tuple n} -> ⇔ A -> ⇔ B -> ⇔ (λ i -> A i → B i)
(A ⇒· B) f = ∀ a → A a → B (S f a)

Π·_ : ∀ {n} {F : Fin n -> Set -> Set}
 -> (FF : ∀ {A : tuple n} -> ⇔ A -> ⇔ (S F A))
 -> ⇔ (λ i -> ∀ A -> F i A)
(Π· FF) g = ∀ {A} (AA : ⇔ A) → FF AA (S g A)

〚_〛 : (Δ : lctx) -> nat -> Set
〚 ⊡ 〛 n = unit
〚 Δ , l 〛 n = (〚 Δ 〛 n) * (Rel n)

〚_〛₁ : (Δ : lctx) -> nat -> Set
〚 ⊡ 〛₁ n = unit
〚 Δ , l 〛₁ n = (〚 Δ 〛₁ n) * Set

proj : ∀ {Δ : lctx} {n} -> (Δ' : 〚 Δ 〛 n) -> (i : Fin n) -> 〚 Δ 〛₁ n
proj {⊡} Δ' i = _
proj {Δ , l} (Δ' , rel {A} α) i = proj Δ' i , A i

vari : ∀ {n} {Δ : lctx} (Δ' : 〚 Δ 〛₁ n) (α : tvar Δ _) -> Set
vari (Δ' , α) (z ) = α
vari (Δ' , α) (s y) = vari Δ' y

tpi : ∀ {n} {Δ : lctx} (Δ' : 〚 Δ 〛₁ n) (T : tp Δ) -> Set
tpi Δ' (v y) = vari Δ' y
tpi Δ' (T ⇒ S) = tpi Δ' T → tpi Δ' S
tpi Δ' (Π T) = (A : Set) → tpi ( Δ' , A) T

vconv : ∀ {n} {Δ : lctx} (Δ' : 〚 Δ 〛 n) (y : tvar Δ _) -> ((∀ i -> vari (proj Δ' i) y) -> Set)
vconv {Δ = ⊡} _ ()
vconv {Δ = Δ , t} (Δ' , α) z with α
vconv {Δ = Δ , t} (Δ' , α) z | rel y = y
vconv {Δ = Δ , t} (Δ' , α) (s y) = ? -- vconv Δ' y

conv : ∀ {n} {Δ : lctx} (Δ' : 〚 Δ 〛 n) (T : tp Δ) -> ((∀ i -> tpi (proj Δ' i) T) -> Set)
conv Δ' (v y) = vconv Δ' y
conv Δ' (T ⇒ S) = (conv Δ' T) ⇒· (conv Δ' S)
conv {Δ = Δ} Δ' (Π T) =  Π· (λ AA -> conv (Δ' , rel AA) T )

