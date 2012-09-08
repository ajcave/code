module Product where
open import Level

-- We get better reconstruction when we specialize this..
record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
 constructor _,_
 field
  proj₁ : A
  proj₂ : B

open _×_ public