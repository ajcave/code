module subsequence where
open import Data.Nat
open import Data.Product
open import Function
open import Data.Stream
open import Coinduction
open import Relation.Binary.PropositionalEquality

-- Sequence : Set -> Set
-- Sequence A = ℕ -> A

-- cons : ∀ {A} -> A -> Sequence A -> Sequence A
-- cons x xs zero = x
-- cons x xs (suc n) = xs n

-- unfold1 : ∀ {C : Set} {A} -> (C -> A × C) -> C -> Sequence A
-- unfold1 f c zero = proj₁ (f c)
-- unfold1 f c (suc n) = unfold1 f (proj₂ (f c)) n

-- hd : ∀ {A} -> Sequence A -> A
-- hd f = f 0

-- tl : ∀ {A} -> Sequence A -> Sequence A
-- tl f = f ∘ suc

-- out : ∀ {A} -> Sequence A -> A × (Sequence A)
-- out s = (hd s) , tl s

-- Agda's coinduction confuses me. I have no idea if this is the right thing.
-- See Termination Checking in the Presence of Nested Inductive and Coinductive Types (Altenkirch and Danielsson)
mutual
 data SubDrop  {A : Set} : Stream A -> Stream A -> Set where
  subDrop : ∀ {xs ys} -> SubDrop xs (tail ys) -> SubDrop xs ys
  subKeep : ∀ {xs ys} -> head xs ≡ head ys -> ∞ (SubDrop (tail xs) (tail ys)) -> SubDrop xs ys

data Dropping : Set where
 subDrop : Dropping -> Dropping
 subKeep : ∞ Dropping -> Dropping

data Eventually (A : Set) : Set where
 next : Eventually A -> Eventually A
 now : A -> Eventually A

data Dropping' : Set where
 wrap : Eventually (∞ Dropping') -> Dropping'

out : Dropping' -> Eventually (∞ Dropping')
out (wrap x) = x

apply : ∀ {A : Set} -> Dropping -> Stream A -> Stream A
apply (subDrop d) (x ∷ xs) = apply d (♭ xs)
apply (subKeep d) (x ∷ xs) = x ∷ ♯ (apply (♭ d) (♭ xs))

corec-stream : ∀ {A : Set} (C : Set) -> (C -> A × C) -> C -> Stream A
corec-stream C f x = (proj₁ (f x)) ∷ (♯ corec-stream C f (proj₂ (f x)))

stutter : ∀ {A : Set} -> Stream A -> Dropping -> Stream A
stutter {A} xs d = corec-stream (Stream A × Dropping) (λ { (xs , d) → (head xs) , (case d of (λ { (subDrop d') → xs , d' ; (subKeep d') -> tail xs , ♭ d' })) }) (xs , d) 

lemma : ∀ {A : Set} (p : Dropping) (xs : Stream A) (d : Dropping) -> Stream A
lemma p xs (subDrop d) = {!!}
lemma p xs (subKeep x) = head xs ∷ ♯ {!!}

-- (subDrop d) = x ∷ ♯ stutter (x ∷ xs) d
--stutter (x ∷ xs) (subKeep d) = x ∷ ♯ stutter (♭ xs) (♭ d)

-- data Bisim {A : Set} : Stream A -> Stream A -> Set where
--  _∷_ : ∀ {x y : A} {xs ys} -> x ≡ y -> ∞ (Bisim (tail xs) (tail ys)) -> Bisim xs ys

-- lem : ∀ {A : Set} (xs : Stream A) (d : Dropping) -> Bisim (apply d (stutter xs d)) xs
-- lem (x ∷ xs) (subDrop d) = lem (x ∷ xs) d
-- lem (x ∷ xs) (subKeep d) = _∷_ {_} {x} {x} refl (♯ lem (♭ xs) (♭ d))

-- lemma : ∀ {A : Set} (p : Dropping) (xs : Stream A) (d : Dropping) -> ∃ (λ β -> SubDrop β (apply d (stutter xs p)) × SubDrop β xs)
-- lemma (subDrop p) (x ∷ xs) (subDrop d) = lemma p (x ∷ xs) d
-- lemma (subDrop p) (x ∷ xs) (subKeep d) = (proj₁ (lemma p (x ∷ xs) (♭ d))) , (subDrop (proj₁ (proj₂ (lemma p (x ∷ xs) (♭ d))))) , proj₂ (proj₂ (lemma p (x ∷ xs) (♭ d)))
-- lemma (subKeep p) (x ∷ xs) (subDrop d) = proj₁ (lemma (♭ p) (♭ xs) d) , (proj₁ (proj₂ (lemma (♭ p) (♭ xs) d)) , (subDrop (proj₂ (proj₂ (lemma (♭ p) (♭ xs) d)))))
-- lemma (subKeep p) (x ∷ xs) (subKeep d) = (x ∷ ♯ (proj₁ (lemma (♭ p) (♭ xs) (♭ d)))) , subKeep refl (♯ (proj₁ (proj₂ (lemma (♭ p) (♭ xs) (♭ d))))) , subKeep refl (♯ (proj₂ (proj₂ (lemma (♭ p) (♭ xs) (♭ d)))))

-- lemma' : ∀ {A : Set} (p : Dropping) (xs : Stream A) (d : Dropping) -> Stream A
-- lemma' (subDrop p) (x ∷ xs) (subDrop d) = lemma' p (x ∷ xs) d
-- lemma' (subDrop p) (x ∷ xs) (subKeep d) = lemma' p (x ∷ xs) (♭ d)
-- lemma' (subKeep p) (x ∷ xs) (subDrop d) = lemma' (♭ p) (♭ xs) d
-- lemma' (subKeep p) (x ∷ xs) (subKeep d) = x ∷ ♯ lemma' (♭ p) (♭ xs) (♭ d)


-- rec-eventually : ∀ {A C : Set} -> (A -> C) -> (C -> C) -> Eventually A -> C
-- rec-eventually f g (next x) = g (rec-eventually f g x)
-- rec-eventually f g (now x) = f x

-- test : ∀ {A : Set} (p : Eventually (∞ Dropping)) (xs : Stream A) (d : Dropping') -> Stream A
-- test x = rec-eventually {!!} (λ testx' xs d → {!!}) x

