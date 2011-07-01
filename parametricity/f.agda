{-# OPTIONS --universe-polymorphism #-}
module f where

data Level : Set where
       zero : Level
       suc  : Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

max : Level → Level → Level
max  zero    m      = m
max (suc n)  zero   = suc n
max (suc n) (suc m) = suc (max n m)
 
{-# BUILTIN LEVELMAX max #-}

record Σ_ {l} {A : Set l}(B : A -> Set l) : Set l where
  constructor _,_ 
  field
    fst : A
    snd : B fst

record _*_ {l} (A : Set l) (B : Set l) : Set l where
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


lctx = ctx Level

data tp (Δ : lctx) : (l : Level) -> Set where
 v : ∀ {l} -> tvar Δ l -> tp Δ l
 _⇒_ : ∀ {l m} (T : tp Δ l) -> (S : tp Δ m) -> tp Δ (max l m)
 Π : ∀ {l m} (T : tp (Δ , l) m) -> tp Δ (suc (max m l))

data tctx (Δ : lctx) : Set where
 ⊡ : tctx Δ
 _,_ : ∀ {l} -> (Γ : tctx Δ) -> (T : tp Δ l) -> tctx Δ

data var {Δ : lctx} : ∀ (Γ : tctx Δ) {l} (T : tp Δ l) -> Set where
 z : ∀ {Γ l} {T : tp Δ l} -> var (Γ , T) T
 s : ∀ {Γ l m} {T : tp Δ m} {S : tp Δ l} -> var Γ T -> var (Γ , S) T

tctxM : ∀ {Δ1 Δ2} (f : ∀ {l} -> tp Δ1 l -> tp Δ2 l) -> tctx Δ1 -> tctx Δ2
tctxM f ⊡ = ⊡
tctxM f (Γ , x) = tctxM f Γ , f x 
 
tvsubst : ∀ Δ1 Δ2 -> Set
tvsubst Δ1 Δ2 = ∀ {l : Level} -> (T : tvar Δ1 l) -> tvar Δ2 l

tsubst : ∀ Δ1 Δ2 -> Set
tsubst Δ1 Δ2 = ∀ {l} -> (T : tvar Δ1 l) -> tp Δ2 l

_∘_ : ∀ {l} {A B C : Set l} (g : B -> C) (f : A -> B) -> A -> C
(g ∘ f) x = g (f x)

_,,_ : ∀ {Δ1 Δ2 l} -> tvsubst Δ1 Δ2 -> tvar Δ2 l -> tvsubst (Δ1 , l) Δ2
_,,_ σ x z = x
_,,_ σ x (s y) = σ y

_,,,_ : ∀ {Δ1 Δ2 l} -> tsubst Δ1 Δ2 -> tp Δ2 l -> tsubst (Δ1 , l) Δ2
(θ ,,, T) z = T
(θ ,,, T) (s y) = θ y

_×_ : ∀ {Δ1 Δ2 l m} -> tvsubst Δ1 Δ2 -> tvar (Δ2 , l) m -> tvsubst (Δ1 , m) (Δ2 , l)
(σ × y) = (s ∘ σ) ,, y

[_] : ∀ {Δ1 Δ2 l} -> tvsubst Δ1 Δ2 -> tp Δ1 l -> tp Δ2 l
[ σ ] (v y) = v (σ y)
[ σ ] (T ⇒ S) = [ σ ] T ⇒ [ σ ] S
[ σ ] (Π T) = Π ([ σ × z ] T)

_××_ : ∀ {Δ1 Δ2 l m} -> tsubst Δ1 Δ2 -> tp (Δ2 , l) m -> tsubst (Δ1 , m) (Δ2 , l)
(θ ×× y) = ([ s ] ∘ θ) ,,, y

[[_]] : ∀ {Δ1 Δ2 l} -> tsubst Δ1 Δ2 -> tp Δ1 l -> tp Δ2 l
[[ θ ]] (v y) = θ y
[[ θ ]] (T ⇒ S) = [[ θ ]] T ⇒ [[ θ ]] S
[[ θ ]] (Π T) = Π ([[ θ ×× v z ]] T)

… : ∀ {A : Set} -> A -> A
… x = x

data tm (Δ : lctx) (Γ : tctx Δ) : ∀ {l} -> tp Δ l -> Set where
 v : ∀ {l} {T : tp Δ l} -> var Γ T -> tm Δ Γ T
 ƛ : ∀ {l} {T S : tp Δ l} -> tm Δ (Γ , T) S -> tm Δ Γ (T ⇒ S)
 Λ : ∀ {l m} {T : tp (Δ , l) m} -> tm (Δ , l) (tctxM [ s ] Γ) T -> tm Δ Γ (Π T)
 _·_ : ∀ {l m} {T : tp Δ l} {S : tp Δ m} -> tm Δ Γ (T ⇒ S) -> tm Δ Γ T -> tm Δ Γ S
 _$_ : ∀ {l m} {T : tp (Δ , l) m} -> tm Δ Γ (Π T) -> (S : tp Δ l)
         -> tm Δ Γ ([[ (v ∘ …) ,,, S ]] T)

nmax : (Δ : lctx) -> Level
nmax ⊡ = zero
nmax (Γ , l) = max l (nmax Γ)

data Lifted {a} (A : Set a) : Set (suc a) where
       lift : A → Lifted A

data _≤_ : Level -> Level -> Set where
 refl : ∀ {l} -> l ≤ l
 s : ∀ {l m} -> l ≤ m -> l ≤ (suc m)

importSet : ∀ {l m} -> l ≤ m -> Set l -> Set m
importSet refl S = S
importSet (s y) S = Lifted (importSet y S)

zero≤all : ∀ l -> zero ≤ l
zero≤all zero = refl
zero≤all (suc y) = s (zero≤all y)

s≤ : ∀ {l m} -> l ≤ m -> suc l ≤ suc m
s≤ refl = refl
s≤ (s y) = s (s≤ y)

max≤left : ∀ l m -> l ≤ (max l m)
max≤left zero m = zero≤all m
max≤left (suc y) zero = refl
max≤left (suc y) (suc y') = s≤ (max≤left y y')

max≤right : ∀ l m -> m ≤ (max l m)
max≤right zero m = refl
max≤right (suc y) zero = zero≤all (suc y)
max≤right (suc y) (suc y') = s≤ (max≤right y y')

_⇔_ : ∀ {l} -> (A B : Set l) -> Set (suc l)
_⇔_ {l} A B = A -> B -> Set l

data Rel (l : Level) : Set (suc l) where
 rel : ∀ {A B : Set l} -> A ⇔ B -> Rel l

_⇒·_ : ∀ {l m} {A A' : Set l} {B B' : Set m} -> A ⇔ A' -> B ⇔ B' -> (A → B) ⇔ (A' → B')
(A ⇒· B) f f' = ∀ a a' → A a a' → B (f a) (f' a')

Π·_ : ∀ {l m} {F F' : Set l -> Set m}
 -> (FF : ∀ {A A' : Set l} -> A ⇔ A' -> F A ⇔ F' A')
 -> (∀ A -> F A) ⇔ (∀ A' -> F' A')
(Π· FF) g g' = ∀ {A A'} (AA : A ⇔ A') → FF AA (g A) (g' A')

〚_〛 : (Δ : lctx) -> Set (suc (nmax Δ))
〚 ⊡ 〛 = Lifted unit
〚 Δ , l 〛 =   importSet (s≤ (max≤right l (nmax Δ))) 〚 Δ 〛
           * importSet (s≤ (max≤left  l (nmax Δ))) (Rel l)

importContent : ∀ {l m} (p : l ≤ m) {A : Set l} (x : A) -> importSet p A
importContent refl x = x
importContent (s y) x = lift (importContent y x) 

blahl : ∀ l (Δ : lctx) (Δ' : 〚 Δ 〛) (T : tp Δ l) -> Set l
blahl l Δ Δ' (v y) = {!!}
blahl .(max l m) Δ Δ' (_⇒_ {l} {m} T S) = blahl l Δ Δ' T → blahl m Δ Δ' S
blahl .(suc (max m l)) Δ Δ' (Π {l} {m} T) = (A : Set l)
  → blahl {!!} (Δ , l) (importContent (s≤ (max≤right l (nmax Δ))) Δ' , importContent (s≤ (max≤left l (nmax Δ))) (rel {!!})) {!!}

conv : ∀ l (Δ : lctx) (Δ' : 〚 Δ 〛) (T : tp Δ l) -> Rel l
conv l Δ Δ' (v y) = {!!}
conv .(max l m) Δ Δ' (_⇒_ {l} {m} T S) = {!!}
conv .(suc (max m l)) Δ Δ' (Π {l} {m} T) = rel (Π· (λ A → {!!}))



