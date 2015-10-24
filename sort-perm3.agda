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

data Contains x : List ℕ -> Set where
 yep : ∀ l0 {l0'} -> Contains x (l0 ++ x ∷ l0')

∷inv1 : ∀ {x y : ℕ} {xs ys : List ℕ} -> _≡_ {_} {List ℕ} (x ∷ xs) (y ∷ ys) -> x ≡ y
∷inv1 refl = refl

∷inv2 : ∀ {x y xs ys} -> _≡_ {_} {List ℕ} (x ∷ xs) (y ∷ ys) -> xs ≡ ys
∷inv2 refl = refl

perm-lem6 : ∀ {l1 x l2 r ys} -> r ≡ l1 ++ x ∷ l2 -> Perm r ys -> Contains x ys
perm-lem6 {[]} () []
perm-lem6 {x ∷ l1} () []
perm-lem6 {[]} refl (x ∷ q) = yep []
perm-lem6 {.x₂ ∷ l1} refl (x₂ ∷ q) with perm-lem6 {l1} refl q
perm-lem6 {.x₂ ∷ l1} refl (x₂ ∷ q) | yep l0 = yep (x₂ ∷ l0)
perm-lem6 {[]} refl (swap x y l) = yep (y ∷ [])
perm-lem6 {.x ∷ []} refl (swap x x₁ l2) = yep []
perm-lem6 {.x ∷ .x₁ ∷ l1} refl (swap x x₁ ._) = yep (x₁ ∷ x ∷ l1)
perm-lem6 {l1} p (ptrans q q₁) with perm-lem6 {l1} p q
perm-lem6 p (ptrans q q₁) | yep l0 = perm-lem6 {l0} refl q₁

concat-lem : ∀ (l1 l3 : List ℕ) {x l2 l4} -> l1 ++ x ∷ l2 ≡ l3 ++ x ∷ l4 -> Perm (l1 ++ l2) (l3 ++ l4)
concat-lem [] [] refl = perm-refl _
concat-lem [] (x ∷ l3) refl = perm-front l3
concat-lem (x ∷ l1) [] refl = perm-sym (perm-front l1)
concat-lem (x ∷ l1) (x₁ ∷ l3) p with ∷inv1 p | ∷inv2 p
concat-lem (x ∷ l1) (.x ∷ l3) p | refl | q1 = _ ∷ concat-lem l1 l3 q1

perm-lem7 : ∀ {l1 l3 r1 r2 l2 l4 x} -> r1 ≡ l1 ++ x ∷ l2 -> r2 ≡ l3 ++ x ∷ l4 -> Perm r1 r2 -> Perm (l1 ++ l2) (l3 ++ l4)
perm-lem7 {[]} () p2 []
perm-lem7 {x ∷ l1} () p2 []
perm-lem7 {[]} {[]} refl refl (x ∷ q) = q
perm-lem7 {[]} {.x ∷ l3} refl refl (x ∷ q) = ptrans q (perm-front l3)
perm-lem7 {.x ∷ l1} {[]} refl refl (x ∷ q) = ptrans (perm-sym (perm-front l1)) q
perm-lem7 {.x₁ ∷ l1} {.x₁ ∷ l3} refl refl (x₁ ∷ q) = _ ∷ (perm-lem7 {l1} {l3} refl refl q)
perm-lem7 {[]} {[]} refl refl (swap x .x l) = perm-refl _
perm-lem7 {[]} {.x ∷ []} refl refl (swap x₁ x l4) = perm-refl _
perm-lem7 {[]} {.x ∷ .x₁ ∷ l3} refl refl (swap x₁ x ._) = _ ∷ perm-front l3
perm-lem7 {.x ∷ []} {[]} refl refl (swap x x₁ l2) = perm-refl _
perm-lem7 {.x ∷ .x₁ ∷ l1} {[]} refl refl (swap x x₁ ._) = _ ∷ perm-sym (perm-front l1)
perm-lem7 {.x ∷ []} {.x ∷ []} refl refl (swap x .x l4) = perm-refl _
perm-lem7 {.x ∷ []} {.x₁ ∷ .x ∷ l3} refl refl (swap x x₁ ._) = ptrans (_ ∷ perm-front l3) (swap _ _ _)
perm-lem7 {.x ∷ .x₂ ∷ l1} {.x₂ ∷ []} refl refl (swap x x₂ ._) = ptrans (swap _ _ _) (_ ∷ perm-sym (perm-front l1))
perm-lem7 {.x ∷ .x₁ ∷ l1} {x₂ ∷ x₃ ∷ l3} refl p2 (swap x x₁ ._) with ∷inv1 p2 | ∷inv1 (∷inv2 p2) | ∷inv2 (∷inv2 p2)
perm-lem7 {.x₃ ∷ .x₂ ∷ l1} {.x₂ ∷ .x₃ ∷ l3} refl p2 (swap x₃ x₂ ._) | refl | refl | q2 = ptrans (swap _ _ _) (_ ∷ (_ ∷ concat-lem l1 l3 q2))
perm-lem7 {l1} p1 p2 (ptrans q q₁) with perm-lem6 {l1} p1 q
perm-lem7 {l1} {l3} p1 p2 (ptrans q q₁) | yep l0 = ptrans (perm-lem7 {l1} {l0} p1 refl q) (perm-lem7 {l0} {l3} refl p2 q₁) 

perm-lem : ∀ {l1 l3 l2 l4 x} -> Perm (l1 ++ x ∷ l2) (l3 ++ x ∷ l4) -> Perm (l1 ++ l2) (l3 ++ l4)
perm-lem {l1} {l3} p = perm-lem7 {l1} {l3} refl refl p

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

singleton : ∀ {l} (xs : slist l) -> ⌊ xs ⌋ ≡ ⌊ insertionSort l ⌋
singleton {l} xs = singleton0 (perm-refl _) xs (insertionSort l)
 