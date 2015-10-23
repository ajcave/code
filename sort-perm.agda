module sort-perm where
open import Data.Bool
open import Data.List


module _ (A : Set) (cmp : A -> A -> Bool) where
 
 data plist : List A -> Set where
  [] : plist []
  cons : ∀ {l1 l2} (x : A) -> plist (l1 ++ l2) -> plist (l1 ++ (x ∷ l2))
 
 insert : ∀ {l : List A} (x : A) -> plist l -> plist (x ∷ l)
 insert x [] = cons {[]} x []
 insert x (cons y ys) with cmp x y
 insert x (cons {l1} y ys) | true = cons {[]} x (cons {l1} y ys)
 insert x (cons {l1} y ys) | false = cons {x ∷ l1} y (insert x ys)
 