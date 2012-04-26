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
 cons : ∀ {x b} -> b ≤ x -> SList x -> SList b

insert : ∀ {x b} -> b ≤ x -> SList b -> SList b
insert w nil = cons w nil
insert {x} w (cons {y2} w' ys) with compare x y2
insert w (cons {y2} w' ys) | le w1 = cons w (cons w1 ys)
insert w (cons {y2} w' ys) | ge w2 = cons w' (insert w2 ys)