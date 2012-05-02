module rev where

data nat : Set where
 z : nat 
 s : nat -> nat

data vec (A : Set) : nat -> Set where
 nil : vec A z
 cons : ∀ {n} -> A -> vec A n -> vec A (s n)

_+_ : nat -> nat -> nat
z + n = n
(s m) + n = s (m + n)

app : ∀ {A n m} -> vec A n -> vec A m -> vec A (n + m)
app nil ys = ys
app (cons y y') ys = cons y (app y' ys)

rev' : ∀ {A n} -> vec A n -> vec A n
rev' nil = nil
rev' (cons y y') with app (rev' y') (cons y nil)
... | w = {!!}

_+2_ : nat -> nat -> nat
z +2 n = n
(s m) +2 n = m +2 (s n)

rev : ∀ {A n m} -> vec A n -> vec A m -> vec A (n +2 m)
rev nil ys = ys
rev (cons y y') ys = rev y' (cons y ys)

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

cong : ∀ {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

trans : ∀ {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

lem : ∀ n m -> s (n + m) ≡ (n + s m)
lem z m = refl
lem (s y) m = cong s (lem y m)

equiv : ∀ n m -> (n + m) ≡ (n +2 m)
equiv z m = refl
equiv (s y) m = trans (lem y m) (equiv y (s m))

lem0 : ∀ n -> n ≡ (n + z)
lem0 z = refl
lem0 (s y) = cong s (lem0 y)

comm : ∀ n m -> (n + m) ≡ (m + n)
comm z m = lem0 m
comm (s y) m = trans (cong s (comm y m)) (lem m y)

assoc : ∀ n m k -> ((n + m) + k) ≡ (n + (m + k))
assoc z m k = refl
assoc (s y) m k = cong s (assoc y m k)