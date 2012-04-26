module insert where

postulate
 A : Set
 _≤_ : A -> A -> Set

data order (x y : A) : Set where
 le : x ≤ y -> order x y
 ge : y ≤ x -> order x y

postulate
 compare : (x y : A) -> order x y

data SList : A -> Set where
 • : ∀ {b} -> SList b
 _≤[_]_ : (x : A) -> {b : A} -> b ≤ x -> SList x -> SList b

insert : (x : A) -> {b : A} -> b ≤ x -> SList b -> SList b
insert x w • = x ≤[ w ] •
insert x w (y ≤[ u ] ys) with compare x y
insert x w (y ≤[ u ] ys) | le v = x ≤[ w ] (y ≤[ v ] ys)
insert x w (y ≤[ u ] ys) | ge v = y ≤[ u ] (insert x v ys)

insert'  : (x : A) -> {b : A} -> b ≤ x -> SList b -> SList b
insert' x w • = x ≤[ {!!} ] •
insert' x w (x' ≤[ y ] y') = {!!}

data SList2 : A -> Set where
 • : ∀ {b} -> SList2 b
 _≤_[_]≤_ : (b : A) -> (x : A) -> b ≤ x -> SList2 x -> SList2 b

insert''  : {b : A} -> (x : A) -> b ≤ x -> SList2 b -> SList2 b
insert'' x w • = _ ≤ x [ w ]≤ •
insert'' x w (b ≤ y [ u ]≤ ys) with compare x y
insert'' x w (b ≤ y [ u ]≤ ys) | le v = b ≤ x [ w ]≤ (x ≤ y [ v ]≤ ys)
insert'' x w (b ≤ y [ u ]≤ ys) | ge v = b ≤ y [ u ]≤ insert'' x v ys

data Nat : Set where 
 z : Nat
 s : Nat -> Nat

data SList3 : Nat -> A -> Set where
 • : ∀ {b} -> SList3 z b
 _≤_[_]≤_ : {n : Nat} -> (b : A) -> (x : A) -> b ≤ x -> SList3 n x -> SList3 (s n) b

-- Can do this with auto!
insert'''  : {n : Nat} {b : A} -> (x : A) -> b ≤ x -> SList3 n b -> SList3 (s n) b
insert''' x w • = _ ≤ x [ w ]≤ •
insert''' x w (b ≤ x' [ y ]≤ y') with compare x x'
insert''' x w (b ≤ x' [ y' ]≤ y0) | le y = b ≤ x [ w ]≤ (x ≤ x' [ y ]≤ y0)
insert''' x w (b ≤ x' [ y' ]≤ y0) | ge y with insert''' x y y0
... | q = b ≤ x' [ y' ]≤ q
