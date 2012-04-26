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
 nil : ∀ {b} -> SList b
 cons : (x : A) -> {b : A} -> b ≤ x -> SList x -> SList b

insert : (x : A) -> {b : A} -> b ≤ x -> SList b -> SList b
insert x w nil = cons _ w nil
insert x w (cons y w' ys) with compare x y
insert x w (cons y w' ys) | le w1 = cons x w (cons y w1 ys)
insert x w (cons y w' ys) | ge w2 = cons y w' (insert x w2 ys)