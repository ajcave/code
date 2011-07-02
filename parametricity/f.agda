{-# OPTIONS --universe-polymorphism #-}
module f where

data Level : Set where
       zero : Level
       suc  : Level → Level

data nat : Set where
 z : nat
 s : nat -> nat

data Fin : nat -> Set where
 z : ∀ {n} -> Fin (s n)
 s : ∀ {n} -> Fin n -> Fin (s n)

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO zero  #-}
{-# BUILTIN LEVELSUC  suc   #-}

max : Level → Level → Level
max  zero    m      = m
max (suc n)  zero   = suc n
max (suc n) (suc m) = suc (max n m)
 
{-# BUILTIN LEVELMAX max #-}

data _≡_ {l} {A : Set l} (x : A) : A -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

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

record unit {l}: Set l where


lctx = ctx Level

data tp (Δ : lctx) : (l : Level) -> Set where
 v : ∀ {l} -> tvar Δ l -> tp Δ l
 _⇒_ : ∀ {l m} (T : tp Δ l) -> (S : tp Δ m) -> tp Δ (max l m)
 Π : ∀ {l m} (T : tp (Δ , l) m) -> tp Δ (max m (suc l))

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

_∘_ : ∀ {l m n} {A : Set l} {B : Set m} {C : Set n} (g : B -> C) (f : A -> B) -> A -> C
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

tuple : nat -> (l : Level) -> Set (suc l)
tuple n l = Fin n -> Set l

∧_ : ∀ {n l} (A : Fin n -> Set l) -> Set l
∧ A = ∀ i -> A i

⇔_ : ∀ {l n} (A : Fin n -> Set l) -> Set (suc l)
⇔_ {l} A = ∧ A -> Set l

data Rel (l : Level) (n : nat) : Set (suc l) where
 rel : ∀ {A : Fin n -> Set l} -> ⇔ A -> Rel l n

S : ∀ {l m n} {A : Set l} {B : A -> Set m} {C : (x : A) -> B x -> Set n}
 (f : (x : A) -> (y : B x) -> C x y) (g : (x : A) -> B x) -> ((x : A) -> C x (g x))
S f g i = f i (g i)

-- interesting how the S combinator shows up naturally here
_⇒·_ : ∀ {n l m} {A : tuple n l} {B : tuple n m} -> ⇔ A -> ⇔ B -> ⇔ (λ i -> A i → B i)
(A ⇒· B) f = ∀ a → A a → B (S f a)

Π·_ : ∀ {n l m} {F : Fin n -> Set l -> Set m}
 -> (FF : ∀ {A : tuple n l} -> ⇔ A -> ⇔ (S F A))
 -> ⇔ (λ i -> ∀ A -> F i A)
(Π· FF) g = ∀ {A} (AA : ⇔ A) → FF AA (S g A)

〚_〛 : (Δ : lctx) -> nat -> Set (suc (nmax Δ))
〚 ⊡ 〛 n = unit
〚 Δ , l 〛 n = importSet (s≤ (max≤right l (nmax Δ))) (〚 Δ 〛 n)
           * importSet (s≤ (max≤left  l (nmax Δ))) (Rel l n)

〚_〛₁ : (Δ : lctx) -> nat -> Set (suc (nmax Δ))
〚 ⊡ 〛₁ n = unit
〚 Δ , l 〛₁ n = importSet (s≤ (max≤right l (nmax Δ))) (〚 Δ 〛₁ n)
            * importSet (s≤ (max≤left  l (nmax Δ))) (Set l)


importContent : ∀ {l m} (p : l ≤ m) {A : Set l} (x : A) -> importSet p A
importContent refl x = x
importContent (s y) x = lift (importContent y x) 

data view {l m} (p : l ≤ m) {A : Set l} : importSet p A -> Set l where 
 viewc : (x : A) -> view p (importContent p x)

viewable : ∀ {l m} (p : l ≤ m) {A : Set l} (x : importSet p A) -> view p x
viewable refl x = viewc x
viewable (s p) (lift x) with viewable p x
viewable (s p) (lift .(importContent p x)) | viewc x = viewc x 

grar : ∀ {l m} (p : l ≤ m) {A : Set l} (x : A) -> viewable p (importContent p x) ≡ viewc x
grar refl x = refl
grar (s y) x rewrite grar y x = refl

s≤l : ∀ l m -> suc l ≤ suc (max l (nmax m))
s≤l l m = s≤ (max≤left l (nmax m)) 
s≤r : ∀ l m -> suc (nmax m) ≤ suc (max l (nmax m))
s≤r l m = s≤ (max≤right l (nmax m))

proj : ∀ {Δ : lctx} {n} -> (Δ' : 〚 Δ 〛 n) -> (i : Fin n) -> 〚 Δ 〛₁ n
proj {⊡} Δ' i = _
proj {Δ , l} (Δ' , α) i with viewable (s≤r l Δ) Δ' | viewable (s≤l l Δ) α
proj {Δ , l} (.(importContent (s≤r l Δ) Δ') , .(importContent (s≤l l Δ) (rel AA))) i | viewc Δ' | viewc (rel {A} AA) = (importContent (s≤r l Δ) (proj Δ' i)) , (importContent (s≤l l Δ) (A i))

vari : ∀ {l} {n} {Δ : lctx} (Δ' : 〚 Δ 〛₁ n) (α : tvar Δ l) -> Set l
vari {l} (Δ' , α) (z {Δ}) with viewable (s≤l l Δ) α
vari {l} (Δ' , .(importContent (s≤l l Δ) α)) (z {Δ}) | viewc α = α
vari {l} (Δ' , α) (s {Δ} {.l} {m} y) with viewable (s≤r m Δ) Δ'
vari {l} (.(importContent (s≤r m Δ) Δ') , α) (s {Δ} {.l} {m} y) | viewc Δ' = vari Δ' y

tpi : ∀ {l} {n} {Δ : lctx} (Δ' : 〚 Δ 〛₁ n) (T : tp Δ l) -> Set l
tpi Δ' (v y) = vari Δ' y
tpi Δ' (_⇒_ {l} {m} T S) = tpi Δ' T → tpi Δ' S
tpi {Δ = Δ} Δ' (Π {l} {m} T) = (A : Set l) → tpi ((importContent (s≤r l Δ) Δ') , (importContent (s≤l l Δ) A)) T

vconv : ∀ {l n} {Δ : lctx} (Δ' : 〚 Δ 〛 n) (y : tvar Δ l) -> ((∀ i -> vari (proj Δ' i) y) -> Set l)
vconv Δ' z = {!!}
vconv Δ' (s y) = {!!}

conv : ∀ {l n} {Δ : lctx} (Δ' : 〚 Δ 〛 n) (T : tp Δ l) -> ((∀ i -> tpi (proj Δ' i) T) -> Set l)
conv Δ' (v y) = vconv Δ' y
conv Δ' (T ⇒ S) = (conv Δ' T) ⇒· (conv Δ' S)
conv {Δ = Δ} Δ' (Π {l} {m} T) =  Π· foo
 where foo : ∀ {A : tuple _ l} -> (AA : ⇔ A) -> ((i : Fin _)
               → tpi (importContent (s≤r l Δ) (proj Δ' i) , importContent (s≤l l Δ) (A i)) T) → Set m
       foo AA with conv (importContent (s≤r l Δ) Δ' , importContent (s≤l l Δ) (rel AA) ) T
       ... | w rewrite grar (s≤r l Δ) Δ' | grar (s≤l l Δ) (rel AA) = w



