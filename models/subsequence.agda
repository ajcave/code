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

apply : ∀ {A : Set} -> Dropping -> Stream A -> Stream A
apply (subDrop d) (x ∷ xs) = apply d (♭ xs)
apply (subKeep d) (x ∷ xs) = x ∷ ♯ (apply (♭ d) (♭ xs))

stutter : ∀ {A : Set} -> Dropping -> Stream A -> Stream A
stutter (subDrop d) (x ∷ xs) = x ∷ ♯ stutter d (x ∷ xs)
stutter (subKeep d) (x ∷ xs) = x ∷ ♯ stutter (♭ d) (♭ xs)

lemma : ∀ {A : Set} (p : Dropping) (xs : Stream A) (d : Dropping) -> ∃ (λ β -> SubDrop β (apply d (stutter p xs)) × SubDrop β xs)
lemma (subDrop p) (x ∷ xs) (subDrop d) = lemma p (x ∷ xs) d
lemma (subDrop p) (x ∷ xs) (subKeep d) = (proj₁ (lemma p (x ∷ xs) (♭ d))) , (subDrop (proj₁ (proj₂ (lemma p (x ∷ xs) (♭ d))))) , proj₂ (proj₂ (lemma p (x ∷ xs) (♭ d)))
lemma (subKeep p) (x ∷ xs) (subDrop d) = proj₁ (lemma (♭ p) (♭ xs) d) , (proj₁ (proj₂ (lemma (♭ p) (♭ xs) d)) , (subDrop (proj₂ (proj₂ (lemma (♭ p) (♭ xs) d)))))
lemma (subKeep p) (x ∷ xs) (subKeep d) = (x ∷ ♯ (proj₁ (lemma (♭ p) (♭ xs) (♭ d)))) , subKeep refl (♯ (proj₁ (proj₂ (lemma (♭ p) (♭ xs) (♭ d))))) , subKeep refl (♯ (proj₂ (proj₂ (lemma (♭ p) (♭ xs) (♭ d)))))

mutual
 lemma1 : ∀ {A : Set} (p : Dropping) (xs : Stream A) (d : Dropping) -> ∃ (λ β -> SubDrop β (apply d (stutter p xs)) × SubDrop β xs)
 lemma1 (subDrop p) (x ∷ xs) d = lemma2 p x xs d
 lemma1 (subKeep p) (x ∷ xs) d = lemma3 p x xs d

 lemma2 : ∀ {A} p (x : A) (xs : ∞ (Stream A)) d →
         ∃ (λ β →
            (SubDrop β (apply d (stutter (subDrop p) (x ∷ xs)))) ×
            (SubDrop β (x ∷ xs)))
 lemma2 p x xs (subDrop d) = lemma1 p (x ∷ xs) d
 lemma2 p x xs (subKeep d) = ?

 lemma3 : ∀ {A} p (x : A) (xs : ∞ (Stream A)) d →
         Σ (Stream A)
         (λ β →
            Σ (SubDrop β (apply d (stutter (subKeep p) (x ∷ xs))))
            (λ x₁ → SubDrop β (x ∷ xs)))
 lemma3 p x xs (subDrop d) = {!!}
 lemma3 p x xs (subKeep d) = (x ∷ ♯ (proj₁ (lemma1 (♭ p) (♭ xs) (♭ d)))) , subKeep refl (♯ (proj₁ (proj₂ (lemma1 (♭ p) (♭ xs) (♭ d))))) , subKeep refl (♯ (proj₂ (proj₂ (lemma1 (♭ p) (♭ xs) (♭ d)))))