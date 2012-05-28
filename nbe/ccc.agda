{-# OPTIONS --type-in-type #-}
-- This is essentially direct transcription of (the parts that I needed of) Daniel Peeble's Category theory formalization
module ccc where

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

record Category : Set where
 infixr 9 _∘_
 
 field
  Obj : Set
  _⇒_ : Obj -> Obj -> Set
  id : ∀ {A} -> (A ⇒ A)
  _∘_ : ∀ {A B C} -> (B ⇒ C) -> (A ⇒ B) -> (A ⇒ C)

 field
  .assoc : ∀ {A B C D} (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D) -> ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
  .idLeft : ∀ {A B} (f : A ⇒ B) -> (id ∘ f) ≡ f
  .idRight : ∀ {A B} (f : A ⇒ B) -> (f ∘ id) ≡ f

_[_,_] : ∀ (C : Category) (A B : Category.Obj C) -> Set
C [ A , B ] = Category._⇒_ C A B

_[_∘_] : ∀ (C : Category) {X Y Z} (g : C [ Y , Z ])  (f : C [ X , Y ]) -> C [ X , Z ]
C [ g ∘ f ] = Category._∘_ C g f

record Functor (C : Category) (D : Category) : Set where
 private module C = Category C
 private module D = Category D
 
 field
  F₀ : C.Obj -> D.Obj
  F₁ : ∀ {A B} -> C [ A , B ] -> D [ F₀ A , F₀ B ]

  .identity : ∀ {A} -> F₁ (C.id {A}) ≡ D.id
  .homomorphism : ∀ {X Y Z} (f : C [ X , Y ]) (g : C [ Y , Z ]) -> F₁ (C [ g ∘ f ]) ≡ D [ F₁ g ∘ F₁ f ]

record NaturalTransform {C D : Category} (F G : Functor C D) : Set where
 private module C = Category C
 private module D = Category D
 private module F = Functor F
 private module G = Functor G
 open F using (F₀; F₁)
 open G using () renaming (F₀ to G₀; F₁ to G₁)

 field
  η : ∀ X -> D [ F₀ X , G₀ X ]
  .commute : ∀ {X Y} (f : C [ X , Y ]) -> D [ (G₁ f) ∘ (η X) ] ≡ D [ (η Y) ∘ (F₁ f) ]
 
set : Category
set = record {
        Obj = Set;
        _⇒_ = λ A B → A → B;
        id = λ x → x;
        _∘_ = λ f g x → f (g x);
        assoc = λ f g h → refl;
        idLeft = λ f → refl;
        idRight = λ f → refl }



functor-cat : ∀ (C D : Category) -> Category
functor-cat C D = {!!} 
