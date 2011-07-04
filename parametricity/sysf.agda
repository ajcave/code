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
 constructor tt

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

-- TODO: Dammit! This is just (tvar Δ -> Set). Same below.
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
vari (Δ' , α) z = α
vari (Δ' , α) (s y) = vari Δ' y

tpi : ∀ {n} {Δ : lctx} (Δ' : 〚 Δ 〛₁ n) (T : tp Δ) -> Set
tpi Δ' (v y) = vari Δ' y
tpi Δ' (T ⇒ S) = tpi Δ' T → tpi Δ' S
tpi Δ' (Π T) = (A : Set) → tpi ( Δ' , A) T

vconv : ∀ {Δ : lctx} {n} (Δ' : 〚 Δ 〛 n) (y : tvar Δ _) -> ((∀ i -> vari (proj Δ' i) y) -> Set)
vconv {⊡} _ ()
vconv {Δ , t} (Δ' , rel α) z = α
vconv {Δ , t} (Δ' , rel α) (s β) = vconv Δ' β

conv : ∀ {Δ : lctx} {n} (Δ' : 〚 Δ 〛 n) (T : tp Δ) -> ((∀ i -> tpi (proj Δ' i) T) -> Set)
conv Δ' (v y) = vconv Δ' y
conv Δ' (T ⇒ S) = (conv Δ' T) ⇒· (conv Δ' S)
conv Δ' (Π T) =  Π· (λ AA -> conv (Δ' , rel AA) T)

〚_〛₂ : ∀ {Δ : lctx} (Γ : tctx Δ) -> (n : nat) -> (Δ' : 〚 Δ 〛 n) -> Set
〚 ⊡ 〛₂ n Δ' = unit
〚 Γ , T 〛₂ n Δ' = (〚 Γ 〛₂ n Δ') * (Σ_ {∀ i -> tpi (proj Δ' i) T} (conv Δ' T))

〚_〛₂' : ∀ {Δ : lctx} (Γ : tctx Δ) -> (n : nat) -> (Δ' : 〚 Δ 〛₁ n) -> Set
〚 ⊡ 〛₂' n Δ' = unit
〚 Γ , T 〛₂' n Δ' = (〚 Γ 〛₂' n Δ') * (tpi Δ' T)

tproj : ∀ {Δ : lctx} {Γ : tctx Δ} {n} -> (Δ' : 〚 Δ 〛 n) -> (Γ' : 〚 Γ 〛₂ n Δ') -> (i : Fin n) -> 〚 Γ 〛₂' n (proj Δ' i)
tproj {Δ} {⊡} Δ' Γ' i = _
tproj {Δ} {Γ , T} Δ' (Γ' , (T' , _)) i = (tproj Δ' Γ' i) , T' i

vtmi : ∀ {Δ} {Γ} {n} (Δ' : 〚 Δ 〛₁ n) (Γ' : 〚 Γ 〛₂' n Δ') {T : tp Δ} (y : var Γ T) -> tpi Δ' T
vtmi Δ' (Γ' , T) z = T
vtmi Δ' (Γ' , T) (s y) = vtmi Δ' Γ' y

lem1 : ∀ {Δ} {n} (Δ' : 〚 Δ 〛₁ n) (A : _) (T : _) -> tpi (Δ' , A) ([ s ] T) ≡ tpi Δ' T
lem1 Δ' A (v y) = refl
lem1 Δ' A (T ⇒ S) rewrite lem1 Δ' A T | lem1 Δ' A S = refl
lem1 Δ' A (Π T) = {!!}

--lem1' : ∀ {Δ} {n} (Δ' : 〚 Δ 〛 n) (A : _) (T : _) -> tpi (Δ' , A) ([ s ] T) ≡ tpi Δ' T
--lem1' Δ' A (v y) = refl
--lem1' Δ' A (T ⇒ S) rewrite lem1' Δ' A T | lem1' Δ' A S = refl
--lem1' Δ' A (Π T) = {!!}

lem : ∀ {Δ} Γ {n} (Δ' : 〚 Δ 〛₁ n) (A : _) ->  〚 tctxM [ s ] Γ 〛₂' n (Δ' , A) ≡ 〚 Γ 〛₂' n Δ'
lem ⊡ Δ' A = refl
lem (Γ , T) Δ' A rewrite lem Γ Δ' A | lem1 Δ' A T = refl

lem2 : ∀ {Δ} Γ {n} (Δ' : 〚 Δ 〛 n) (AA : _) ->  〚 tctxM [ s ] Γ 〛₂ n (Δ' , AA) ≡ 〚 Γ 〛₂ n Δ'
lem2 ⊡ Δ' A = refl
lem2 (Γ , T) Δ' A  rewrite lem2 Γ Δ' A = {!!}

tmi : ∀ {Δ} {Γ} {n} (Δ' : 〚 Δ 〛₁ n) (Γ' : 〚 Γ 〛₂' n Δ') {T : tp Δ} (t : tm Δ Γ T) -> tpi Δ' T
tmi Δ' Γ' (v y) = vtmi Δ' Γ' y
tmi Δ' Γ' (ƛ M) = λ x → tmi Δ' (Γ' , x) M
tmi {Γ = Γ} Δ' Γ' (Λ M) = λ A → tmi (Δ' , A) (rw A) M
  where rw : (A : Set) -> 〚 tctxM [ s ] Γ 〛₂' _ (Δ' , A)
        rw A rewrite lem Γ Δ' A = Γ'
tmi Δ' Γ' (M · N) = tmi Δ' Γ' M (tmi Δ' Γ' N)
tmi Δ' Γ' (M $ U) with tmi Δ' Γ' M | tpi Δ' U
... | w | q = {!!}

tvconv : ∀ {Δ} {Γ} {n} (Δ' : 〚 Δ 〛 n) (Γ' : 〚 Γ 〛₂ n Δ') {T : tp Δ} (y : var Γ T) -> (conv Δ' T (λ i -> vtmi (proj Δ' i) (tproj Δ' Γ' i) y))
tvconv Δ' (Γ' , (T' , Tr)) z = Tr
tvconv Δ' (Γ' , T) (s y0) = tvconv Δ' Γ' y0

tconv : ∀ {Δ} {Γ} {n} (Δ' : 〚 Δ 〛 n) (Γ' : 〚 Γ 〛₂ n Δ') {T : tp Δ} (t : tm Δ Γ T) -> (conv Δ' T (λ i -> tmi (proj Δ' i) (tproj Δ' Γ' i) t))
tconv Δ' Γ' (v y) = tvconv Δ' Γ' y
tconv Δ' Γ' (ƛ M) = λ x xr → tconv Δ' (Γ' , (x , xr)) M
tconv {Δ} {Γ} {n} Δ' Γ' (Λ {S} M) = λ {A} AA → tconv {Δ , tt} {tctxM [ s ] Γ} {n} (Δ' , rel AA) (rw A AA) {S} {!!}
  where rw : (A : Fin n -> Set) -> (AA : ((i : Fin n) -> A i) -> Set) -> 〚 tctxM [ s ] Γ 〛₂ n (Δ' , (rel AA))
        rw A AA rewrite lem2 Γ Δ' (rel AA) = Γ'
tconv Δ' Γ' (M · N) = tconv Δ' Γ' M _ (tconv Δ' Γ' N)
tconv Δ' Γ' (M $ U) with tconv Δ' Γ' M | conv Δ' U
... | w | q = {!!}

idty : ∀ {Δ} -> tp Δ
idty = Π ((v z) ⇒ (v z))







