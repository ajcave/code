module sub where

postulate
 O : Set
 zero : O
 _+_ : O -> O -> O
 
 var : O -> O -> Set

mutual
 data _⟹_ : O -> O -> Set where
  v : ∀ {A B} -> var A B -> A ⟹ B
  [_,_] : ∀ {A B C} -> A ⟶ C -> B ⟶ C -> (A + B) ⟹ C
  inl : ∀ {A} {B} -> A ⟹ (A + B)
  inr : ∀ {B} {A} -> B ⟹ (A + B)
  ! : ∀ {A} -> zero ⟹ A
 data _⟶_ : O -> O -> Set where
  id : ∀ {A} -> A ⟶ A
  _∘_ : ∀ {A B C} -> (B ⟹ C) -> (A ⟶ B) -> (A ⟶ C) 

infixr 40 _∘_
infixr 20 _≈_ 
infixr 40 _◇_

_◇_ : ∀ {A B C} -> (B ⟶ C) -> (A ⟶ B) -> (A ⟶ C)
id ◇ g = g
(f ∘ fs) ◇ g = f ∘ (fs ◇ g)

<_> : ∀ {A B} -> (A ⟹ B) -> (A ⟶ B)
< f > = f ∘ id

mutual
 data _≈_ : ∀ {A B} -> A ⟹ B -> A ⟹ B -> Set where
  refl : ∀ {A B} (f : var A B) -> (v f) ≈ (v f)
 data _∼_ : ∀ {A B} -> A ⟶ B -> A ⟶ B -> Set where
  βl : ∀ {A B C} (f : A ⟶ C) (g : B ⟶ C) -> < [ f , g ] > ◇ < inl > ∼ f
  βr : ∀ {A B C} (f : A ⟶ C) (g : B ⟶ C) -> < [ f , g ] > ◇ < inr > ∼ g
  η : ∀ {A B} -> < [ < inl {A} > , < inr {B} > ] > ∼ id
  context : ∀ {A B C D} (i : C ⟶ D) (f g : B ⟶ C) (h : A ⟶ B) -> (f ∼ g) -> (i ◇ f ◇ h) ∼ (i ◇ g ◇ h)
 
  

 
