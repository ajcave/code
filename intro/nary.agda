{-# OPTIONS --type-in-type #-}
module nary where
open import helper

addType : number -> Type
addType 0 = number
addType (suc n) = number -> addType n

addHelper : (n : number) -> number -> addType n
addHelper zero acc = acc
addHelper (suc n) acc = λ x → addHelper n (x + acc)

addMany : (n : number) -> addType n
addMany n = addHelper n 0

example0 : Type
example0 = addType 2

example1 : Type
example1 = addType 10

example2 : number
example2 = addMany 10 0 1 2 3 4 5 6 7 8 9

open import Data.Unit

record _*_ (a' b' : Type) : Type where
 constructor _,_
 field
  fst : a'
  snd : b'

infixr 9 _,_
infixr 9 _*_

open import Data.List

nTuple : (bs : List Type) -> Type
nTuple [] = Unit
nTuple (b ∷ []) = b
nTuple (b ∷ (b2 ∷ bs)) = b * nTuple (b2 ∷ bs)

{-
zipType : (bs : List Type) -> Type
zipType bs = nTuple (map List bs) → List (nTuple bs)

zip2 : {a b : Type} -> List a -> List b -> List (a × b)
zip2 (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip2 xs ys
zip2 _ _ = []

nzip : (bs : List Type) -> zipType bs
nzip [] = λ _ → []
nzip (b ∷ []) = λ x → x
nzip (b ∷ (b2 ∷ bs)) = λ { (xs , yss)  → zip2 xs (nzip (b2 ∷ bs) yss) }

example3 : _
example3 = nzip (number ∷ number ∷ number ∷ [])
   ((1 ∷ 2 ∷ 3 ∷ []) , (4 ∷ 5 ∷ 6 ∷ []) , (7 ∷ 8 ∷ 9 ∷ [])) -}


zipTypeHelper : number -> List Type -> Type
zipTypeHelper zero bs = List (nTuple bs)
--zipType2 (suc zero) b = List b -> List b
zipTypeHelper (suc n) bs = {a : Type} → List a → zipTypeHelper n (a ∷ bs)

zipType : number -> Type
zipType n = zipTypeHelper n []


example4 : _
example4 = zipType 2

example5 = zipType 3


