module sort-perm2 where
open import Data.Bool
open import Data.List
open import Data.Nat

lem0 : ∀ {x y} -> x ≤ y -> x ≤ suc y
lem0 z≤n = z≤n
lem0 (s≤s p) = s≤s (lem0 p)

lem : ∀ {x y} -> suc y ≤ x -> y ≤ x
lem (s≤s p) = lem0 p

≤-trans : ∀ {x y z} -> x ≤ y -> y ≤ z -> x ≤ z
≤-trans z≤n z≤n = z≤n
≤-trans z≤n (s≤s q) = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-refl : ∀ {x} -> x ≤ x
≤-refl {zero} = z≤n
≤-refl {suc x} = s≤s ≤-refl

data Cmp (m n : ℕ) : Set where
 lte : m ≤ n -> Cmp m n
 gt : m > n -> Cmp m n

cmp : (m n : ℕ) -> Cmp m n 
cmp zero zero = lte z≤n
cmp zero (suc n) = lte z≤n
cmp (suc m) zero = gt (s≤s z≤n)
cmp (suc m) (suc n) with cmp m n
cmp (suc m) (suc n) | lte x = lte (s≤s x)
cmp (suc m) (suc n) | gt x = gt (s≤s x)

-- lower bound
data lb (b : ℕ) : List ℕ -> Set where
 [] : lb b []
 _∷_ : ∀ {x xs} -> b ≤ x -> lb b xs -> lb b (x ∷ xs)

lb-lem : ∀ {x y l} -> x ≤ y -> lb y l -> lb x l
lb-lem x≤y [] = []
lb-lem x≤y (x₂ ∷ lb) = ≤-trans x≤y x₂ ∷ (lb-lem x≤y lb)

lb-lem2 : ∀ {l1 y l2} -> lb y l1 -> lb y l2 -> lb y (l1 ++ l2)
lb-lem2 [] lb2 = lb2
lb-lem2 (x₁ ∷ lb1) lb2 = x₁ ∷ (lb-lem2 lb1 lb2)

lb-lem3 : ∀ l1 {y l2} -> lb y (l1 ++ l2) -> lb y l2
lb-lem3 [] lb = lb
lb-lem3 (x ∷ l1) (x₁ ∷ lb) = lb-lem3 l1 lb

lb-lem4 : ∀ l1 {y l2} -> lb y (l1 ++ l2) -> lb y l1
lb-lem4 [] lb = []
lb-lem4 (x ∷ l1) (x₁ ∷ lb) = x₁ ∷ (lb-lem4 l1 lb)

lb-lem5 : ∀ l1 {x y l2} -> x ≤ y -> lb y (l1 ++ l2) -> lb x (l1 ++ y ∷ l2) 
lb-lem5 l1 p lb = lb-lem p (lb-lem2 {l1} (lb-lem4 l1 lb) (≤-refl ∷ lb-lem3 l1 lb))

data slist : List ℕ -> Set where
 [] : slist []
 cons : ∀ {l1 l2} (x : ℕ) -> lb x (l1 ++ l2) -> slist (l1 ++ l2) -> slist (l1 ++ (x ∷ l2))

insert : ∀ {l : List ℕ} (x : ℕ) -> slist l -> slist (x ∷ l)
insert x [] = cons {[]} x [] []
insert x (cons y lb ys) with cmp x y
insert x (cons {l1} y lb ys) | lte p = cons {[]} x (lb-lem5 l1 p lb) (cons {l1} y lb ys)
insert x (cons {l1} y lb ys) | gt p = cons {x ∷ l1} y (lem p ∷ lb) (insert x ys)

insertionSort : (l : List ℕ) -> slist l
insertionSort [] = []
insertionSort (x ∷ l) = insert x (insertionSort l)
 