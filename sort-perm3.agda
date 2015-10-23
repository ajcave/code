module sort-perm3 where
open import Data.Bool
open import Data.List
open import Data.Nat
open import Relation.Binary.PropositionalEquality

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

≤-antisym : ∀ {x y} -> x ≤ y -> y ≤ x -> x ≡ y
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

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

lb-lem5 : ∀ {l1 x y l2} -> x ≤ y -> lb y l1 -> lb y l2 -> lb x (l1 ++ y ∷ l2) 
lb-lem5 p lb1 lb2 = lb-lem2 (lb-lem p lb1) (p ∷ (lb-lem p lb2))

data slist : List ℕ -> Set where
 [] : slist []
 cons : ∀ {l1 l2} (x : ℕ) -> lb x l1 -> lb x l2 -> slist (l1 ++ l2) -> slist (l1 ++ (x ∷ l2))

insert : ∀ {l : List ℕ} (x : ℕ) -> slist l -> slist (x ∷ l)
insert x [] = cons x [] [] []
insert x (cons y lb1 lb2 ys) with cmp x y
insert x (cons y lb1 lb2 ys) | lte p = cons x [] (lb-lem5 p lb1 lb2) (cons y lb1 lb2 ys)
insert x (cons y lb1 lb2 ys) | gt p = cons y (lem p ∷ lb1) lb2 (insert x ys)

insertionSort : (l : List ℕ) -> slist l
insertionSort [] = []
insertionSort (x ∷ l) = insert x (insertionSort l)

open import Relation.Binary.PropositionalEquality

⌊_⌋ : ∀ {l} -> slist l -> List ℕ
⌊ [] ⌋ = []
⌊ cons x _ _ xs ⌋ = x ∷ ⌊ xs ⌋

data Perm : List ℕ -> List ℕ -> Set where
 [] : Perm [] []
 _∷_ : ∀ x {xs ys} -> Perm xs ys -> Perm (x ∷ xs) (x ∷ ys)
 swap : ∀ x y l -> Perm (x ∷ y ∷ l) (y ∷ x ∷ l)
 ptrans : ∀ {xs ys zs} -> Perm xs ys -> Perm ys zs -> Perm xs zs

data glb b l : Set where
 yep : lb b l -> (∀ c -> lb c l -> c ≤ b) -> glb b l

lemm : ∀ l1 {x c l2} -> lb c (l1 ++ x ∷ l2) -> c ≤ x
lemm [] (x₁ ∷ lb1) = x₁
lemm (x₁ ∷ l1) (x₂ ∷ lb1) = lemm l1 lb1

lemm1 : ∀ {l1 x l2} -> lb x l1 -> lb x l2 -> glb x (l1 ++ x ∷ l2)
lemm1 {l1} lb1 lb2 = yep (lb-lem2 lb1 (≤-refl ∷ lb2)) (λ c x → lemm l1 x)

glb-uniq : ∀ {x y l} -> glb x l -> glb y l -> x ≡ y
glb-uniq (yep x₁ x₂) (yep x₃ x₄) = ≤-antisym (x₄ _ x₁) (x₂ _ x₃)

lb-perm : ∀ {x l1 l2} -> Perm l1 l2 -> lb x l1 -> lb x l2
lb-perm [] [] = []
lb-perm (x₁ ∷ p) (x₂ ∷ q) = x₂ ∷ (lb-perm p q)
lb-perm (swap x₁ y l) (x₂ ∷ (x₃ ∷ q)) = x₃ ∷ (x₂ ∷ q)
lb-perm (ptrans p p₁) q = lb-perm p₁ (lb-perm p q)

perm-sym : ∀ {l1 l2} -> Perm l1 l2 -> Perm l2 l1
perm-sym [] = []
perm-sym (x ∷ p) = x ∷ (perm-sym p)
perm-sym (swap x y l) = swap y x l
perm-sym (ptrans p p₁) = ptrans (perm-sym p₁) (perm-sym p)

perm-refl : ∀ l -> Perm l l
perm-refl [] = []
perm-refl (x ∷ l) = _ ∷ (perm-refl l)

glb-perm : ∀ {x l1 l2} -> Perm l1 l2 -> glb x l1 -> glb x l2
glb-perm p (yep x₁ x₂) = yep (lb-perm p x₁) (λ c x → x₂ _ (lb-perm (perm-sym p) x))

perm-front : ∀ l1 {x l2} -> Perm (l1 ++ x ∷ l2) (x ∷ (l1 ++ l2))
perm-front [] = _ ∷ perm-refl _
perm-front (y ∷ l1) = ptrans (_ ∷ (perm-front l1)) (swap _ _ (l1 ++ _))

-- data Splits x l1 : List ℕ -> Set where
--  yep : ∀ {l0 l0'} -> Perm l1 (l0 ++ l0') -> Splits x l1 (l0 ++ x ∷ l0')

-- perm-front'' : ∀ {x l1 l2} -> Perm (x ∷ l1) l2 -> Splits x l1 l2
-- perm-front'' (x ∷ p) = yep {l0 = []} p
-- perm-front'' (swap x y l) = yep {l0 = y ∷ []} (perm-refl _)
-- perm-front'' (ptrans p p₁) with perm-front'' p
-- perm-front'' (ptrans p p₁) | yep x₁ = {!!}

-- perm-front' : ∀ {l1 l2 x} -> Perm (x ∷ l1) (x ∷ l2) -> Perm l1 l2
-- perm-front' (x ∷ p) = p
-- perm-front' (swap x .x l) = perm-refl _
-- perm-front' (ptrans p p₁) = {!!}

perm-lem : ∀ {l1 l3 l2 l4 x} -> Perm (l1 ++ x ∷ l2) (l3 ++ x ∷ l4) -> Perm (l1 ++ l2) (l3 ++ l4)
perm-lem {l1} {l3} p with ptrans (perm-sym (perm-front l3)) (ptrans (perm-sym p) (perm-front l1))
... | q0 = {!!}

perm-emp : ∀ {l} -> Perm [] l -> l ≡ []
perm-emp [] = refl
perm-emp (ptrans q q₁) with perm-emp q 
perm-emp (ptrans q q₁) | refl = perm-emp q₁

concat-blah : ∀ (l1 : List ℕ) {x l2} {C : Set} -> [] ≡ (l1 ++ x ∷ l2) -> C
concat-blah [] ()
concat-blah (x ∷ l1) ()

singleton0 : ∀ {l1 l2} -> Perm l1 l2 -> (xs : slist l1) (ys : slist l2) -> ⌊ xs ⌋ ≡ ⌊ ys ⌋
singleton0 p [] [] = refl
singleton0 p [] (cons {l1} x x₁ x₂ ys) = concat-blah l1 (sym (perm-emp p))
singleton0 p (cons {l1} x x₁ x₂ xs) [] = concat-blah l1 (sym (perm-emp (perm-sym p)))
singleton0 p (cons x lb1 lb2 xs) (cons y lb3 lb4 ys) with glb-uniq (lemm1 lb1 lb2) (glb-perm (perm-sym p) (lemm1 lb3 lb4))
singleton0 p (cons {l1} x lb1 lb2 xs) (cons {l3} .x lb3 lb4 ys) | refl with singleton0 (perm-lem {l1} {l3} p) xs ys
... | q  = cong₂ _∷_ refl q
 