{-# OPTIONS --type-in-type #-}
module nary where
open import helper
open import Data.Bool
open import Data.String

record Unit : Type where
 constructor unit



open import Data.List hiding (zip; product)

zip2 : {a b : Type} -> List a -> List b -> List (a * b)
zip2 (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip2 xs ys
zip2 _ _ = []

zip3 : {a b c : Type} -> List a -> List b -> List c -> List (a * b * c)
zip3 (x ∷ xs) (y ∷ ys) (z ∷ zs) = (x , y , z) ∷ zip3 xs ys zs
zip3 _ _ _ = []

zip4 : {a b c d : Type} -> List a -> List b -> List c -> List d -> List (a * b * c * d)
zip4 (x ∷ xs) (y ∷ ys) (z ∷ zs) (w ∷ ws) = (x , y , z , w) ∷ zip4 xs ys zs ws
zip4 _ _ _ _ = []

-----------
vec : (A : Type) -> number -> Type
vec A zero = Unit
vec A (suc n) = A * (vec A n)

vmap : {A B : Type} -> (A -> B) -> (n : number) -> vec A n -> vec B n
vmap f zero as = unit
vmap f (suc n) (x , xs) = (f x) , (vmap f n xs)

product : (n : number) -> vec Type n -> Type
product zero _ = Unit
product (suc zero) (a , _) = a
product (suc (suc n)) (a , as) = a * product (suc n) as

zip : (n : number) -> {as : vec Type n} -> product n (vmap List n as) -> List (product n as)
zip zero unit = []
zip (suc zero) xs = xs
zip (suc (suc n)) (xs , yss) = zip2 xs (zip (suc n) yss)

example10 = zip 2 ((1 ∷ 2 ∷ 3 ∷ []) , (true ∷ false ∷ true ∷ []))

example11 = zip 3 ((1 ∷ 2 ∷ 3 ∷ []) , (true ∷ false ∷ true ∷ []) , ("foo" ∷ "bar" ∷ "baz" ∷ []))

------




