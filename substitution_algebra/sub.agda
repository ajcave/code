module sub where

postulate
 O : Set
 zero : O
 _+_ : O -> O -> O -- Implement these as summation lists like the composition lists below
 
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
infixr 40 _◇_

_◇_ : ∀ {A B C} -> (B ⟶ C) -> (A ⟶ B) -> (A ⟶ C)
id ◇ g = g
(f ∘ fs) ◇ g = f ∘ (fs ◇ g)

<_> : ∀ {A B} -> (A ⟹ B) -> (A ⟶ B)
< f > = f ∘ id

data _≡_ {A : Set} (x : A) : {B : Set} -> B -> Set where
 refl : x ≡ x

data ⊥ : Set where

¬ : Set -> Set
¬ A = A -> ⊥

mutual
-- infixr 20 _≈_ 
-- data _≈_ : ∀ {A B} -> A ⟹ B -> A ⟹ B -> Set where
--  refl : ∀ {A B} (f : var A B) -> (v f) ≈ (v f)
 data _↝_ : ∀ {A B} -> A ⟶ B -> A ⟶ B -> Set where
--  base : ∀ {A B} (f g : A ⟹ B) -> f ≈ g -> < f > ∼ < g >
  βl : ∀ {A B C} (f : A ⟶ C) (g : B ⟶ C) -> < [ f , g ] > ◇ < inl > ↝ f
  βr : ∀ {A B C} (f : A ⟶ C) (g : B ⟶ C) -> < [ f , g ] > ◇ < inr > ↝ g
  !init : ∀ {A} (f : zero ⟶ A) -> ¬ (A ≡ zero) -> f ↝ < ! >
  !zero : ∀ (f : zero ⟶ zero) -> ¬ (f ≡ (id {zero})) -> f ↝ id
  η : ∀ {A B} -> < [ < inl {A} > , < inr {B} > ] > ↝ id -- I suspect this may cause me pain. Confluence in the presence of this?
 
 data _⇾_ : ∀ {A B} -> A ⟶ B -> A ⟶ B -> Set where
  context : ∀ {A B C D} (i : C ⟶ D) {f g : B ⟶ C} (h : A ⟶ B) -> (f ↝ g) -> (i ◇ f ◇ h) ⇾ (i ◇ g ◇ h)

-- Should I be able to show that if f : A -> C, g : B -> C, h : A + B -> C
-- are such that h ∘ inl = f and h ∘ inr = g then h = [f,g]?
-- This is uniqueness of [f,g]. Is this extensionality? Or just eta?

-- Strongly normalizing
data sn : ∀ {A B} -> A ⟶ B -> Set where
 sni : ∀ {A B} {f : A ⟶ B} -> (∀ {g} -> f ⇾ g -> sn g) -> sn f

{-
idDoesntStep : ∀ {A B} {C : Set} {f g : A ⟶ B} -> f ↝ g -> f ≡ (id {B}) -> C
idDoesntStep (βl f g) ()
idDoesntStep (βr f g) ()
idDoesntStep (!init {B} f y) q = {!q!} -- ???
idDoesntStep (!zero f y) x with y x
... | ()
idDoesntStep η ()

idDoesntStep' : ∀ {A B} {C : Set} {f g : A ⟶ B} -> f ⇾ g -> f ≡ (id {B}) -> C
idDoesntStep' {C = C} (context i f g h y) eq with idDoesntStep {C = C} y
... | w = {!!} -}

allSn : ∀ {A B} (f : A ⟶ B) -> sn f
allSn {A} {B} f = sni foo
 where foo : {f g : A ⟶ B}  -> f ⇾ g -> sn g
       foo (context i h (βl f g)) = {!!}
       foo (context i h (βr f g)) = {!!}
       foo (context i h (!init f y)) = {!!}
       foo (context i h (!zero f y)) = {!!}
       foo (context i h η) = {!!}
--allSn id = sni (λ g → idDoesntStep' g refl)
--allSn (f ∘ g) = {!!}  
 
  

 
