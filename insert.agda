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
 _≤_[_],_ : (b x : A) -> b ≤ x -> SList x -> SList b

insert : (b x : A) -> b ≤ x -> SList b -> SList b
insert b x u • = b ≤ x [ u ], •
insert b x u (.b ≤ y [ v ], ys) with compare x y
insert b x u (.b ≤ y [ v ], ys) | le w = b ≤ x [ u ], (x ≤ y [ w ], ys)
insert b x u (.b ≤ y [ v ], ys) | ge w = b ≤ y [ v ], (insert y x w ys)

min : (x y : A) -> A
min x y with compare x y
min x y | le _ = x
min x y | ge _ = y

insert' : (b x : A) -> SList b -> SList (min b x)
insert' b x xs with compare b x
insert' b x xs | le u = insert b x u xs
insert' b x xs | ge u = x ≤ b [ u ], xs

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

data List (A : Set) : Set where
 • : List A
 _,_ : A -> List A -> List A

insertionSort : List A -> Σ (λ b -> SList b)
insertionSort • = {!!} , •
insertionSort (x , xs) with insertionSort xs
insertionSort (x , xs) | b , ys = min b x , (insert' b x ys)

