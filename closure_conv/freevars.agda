module freevars where

data nat : Set where
 z : nat
 s : nat -> nat

data var : (n : nat) -> Set where
 top : ∀ {n} -> var (s n)
 pop : ∀ {n} -> var n -> var (s n)

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

_∘_ : {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘ g) x = f (g x) 

data tm (n : nat) : Set where
 ▹ : (x : var n) -> tm n
 ƛ : (M : tm (s n)) -> tm n 
 _·_ : (M : tm n) -> (N : tm n) -> tm n

sub : nat -> nat -> Set
sub n m = var n -> var m

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

data _+_ (A B : Set) : Set where
 inl : A -> A + B
 inr : B -> A + B

data ⊥ : Set where

id : ∀ {n} -> sub n n
id x = x

! : ∀ {n} -> sub z n
! ()

data inRange {n m} (σ : sub n m) : var m -> Set where
 inr : (x : var n) -> inRange σ (σ x)

nope : ∀ {m} (σ : sub z m) (y : var m) -> inRange σ y -> ⊥
nope σ ._ (inr ()) 


var-dec : ∀ {n} (x y : var n) -> (x ≡ y) + (x ≡ y -> ⊥)
var-dec top top = inl refl
var-dec top (pop y) = inr {!!}
var-dec (pop y) top = inr {!!}
var-dec (pop y) (pop y') with var-dec y y'
var-dec (pop y) (pop .y) | inl refl = inl refl
var-dec (pop y) (pop y') | inr y0 = {!!}

inRange? : ∀ {n m} (σ : sub n m) (y : var m) -> (inRange σ y) + (inRange σ y -> ⊥)
inRange? {z} σ y = inr (nope σ y)
inRange? {s y} σ y' with var-dec (σ top) y'
inRange? {s y} σ .(σ top) | inl refl = inl (inr top)
inRange? {s y} σ y' | inr y0 with inRange? (σ ∘ pop) y'
inRange? {s y} σ .(σ (pop x)) | inr y1 | inl (inr x) = inl (inr (pop x))
inRange? {s y} σ y' | inr y1 | inr y0 = inr {!!}


_,,_ : ∀ {n m} -> sub n m -> var m -> sub (s n) m
_,,_ σ x top = x
_,,_ σ x (pop y) = σ y

ext : ∀ {n m} -> sub n m -> sub (s n) (s m)
ext σ top = top
ext σ (pop y) = pop (σ y)

_∪_ : ∀ {k n m} -> sub m n -> sub k n -> Σ (λ r -> (sub m r) * ((sub k r) * (sub r n)))
_∪_ {z} σ1 σ2 = _ , (id , (! , σ1))
_∪_ {s y} σ1 σ2 with σ2 top
_∪_ {s y} σ1 σ2 | q with inRange? σ1 q
_∪_ {s y} σ1 σ2 | .(σ1 x) | inl (inr x) with σ1 ∪ (σ2 ∘ pop)
_∪_ {s y} σ1 σ2 | .(σ1 x) | inl (inr x) | r , (σ' , (σ1' , σ2')) = r , (σ' , ((σ1' ,, (σ' x)) , σ2'))
_∪_ {s y} σ1 σ2 | q | inr y' with σ1 ∪ (σ2 ∘ pop)
_∪_ {s y} σ1 σ2 | q | inr y0 | r , (σ' , (σ1' , σ2')) = (s r) , ((pop ∘ σ') , (ext σ1' , (σ2' ,, (σ2 top))))
-- prove this is a pullback?

fv : ∀ {n} -> tm n -> Σ (λ m -> (sub m n) * tm m)
fv (▹ x) = (s z) , ((λ _ → x) , ▹ top)
fv (ƛ M) with fv M
fv (ƛ M) | m , (σ , M') = {!!}
fv (M · N) with fv M | fv N
fv (M · N) | m1 , (σ1 , M1) | m2 , (σ2 , M2) = {!!} 