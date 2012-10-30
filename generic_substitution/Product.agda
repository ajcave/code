module Product where

-- We get better reconstruction when we specialize this..
record _×_ (A B : Set) : Set where
 constructor _,_
 field
  proj₁ : A
  proj₂ : B

open _×_ public