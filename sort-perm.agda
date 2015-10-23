module sort-perm where
open import Data.Bool
open import Data.List
open import Data.Nat

module Sort (A : Set) (cmp : A -> A -> Bool) where
 
 data plist : List A -> Set where
  [] : plist []
  cons : ∀ {l1 l2} (x : A) -> plist (l1 ++ l2) -> plist (l1 ++ (x ∷ l2))
 
 insert : ∀ {l : List A} (x : A) -> plist l -> plist (x ∷ l)
 insert x [] = cons {[]} x []
 insert x (cons y ys) with cmp x y
 insert x (cons {l1} y ys) | true = cons {[]} x (cons {l1} y ys)
 insert x (cons {l1} y ys) | false = cons {x ∷ l1} y (insert x ys)

 insertionSort : (l : List A) -> plist l
 insertionSort [] = []
 insertionSort (x ∷ l) = insert x (insertionSort l)
 
l = 1 ∷ 5 ∷ 4 ∷ 3 ∷ []

lte : ℕ -> ℕ -> Bool
lte zero zero = true
lte zero (suc m) = true
lte (suc n) zero = false
lte (suc n) (suc m) = lte n m

open module M = Sort ℕ lte

l' = insertionSort l