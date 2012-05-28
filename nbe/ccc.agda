{-# OPTIONS --type-in-type #-}
-- This is essentially direct transcription of (the parts that I needed of) Daniel Peeble's Category theory formalization
module ccc where

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Unit : Set where
 constructor tt

postulate
 funext : ∀ {A B : Set} (f g : A -> B) -> (∀ x -> f x ≡ g x) -> f ≡ g

transitivity : ∀ {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
transitivity refl refl = refl

sym : ∀ {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong2 : ∀ {A B C : Set} (f : A -> B -> C) {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> f x z ≡ f y w
cong2 f refl refl = refl

record Category : Set where
 constructor Cat
 infixr 9 _∘_
 field
  Obj : Set
  _⇒_ : Obj -> Obj -> Set
  id : ∀ {A} -> (A ⇒ A)
  _∘_ : ∀ {A B C} -> (B ⇒ C) -> (A ⇒ B) -> (A ⇒ C)
  assoc : ∀ {A B C D} (f : A ⇒ B) (g : B ⇒ C) (h : C ⇒ D) -> ((h ∘ g) ∘ f) ≡ (h ∘ (g ∘ f))
  idLeft : ∀ {A B} (f : A ⇒ B) -> (id ∘ f) ≡ f
  idRight : ∀ {A B} (f : A ⇒ B) -> (f ∘ id) ≡ f

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

record NaturalTransformation {C D : Category} (F G : Functor C D) : Set where
 constructor Nat
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

-- Need to update my Agda.. no irrelevant projections..
nat-id : ∀ {C D} {F : Functor C D} -> NaturalTransformation F F
nat-id {C} {Cat Obj _⇒_ id _∘_ assoc idLeft idRight} = record { η = λ X → id; commute = λ f → transitivity (idRight _) (sym (idLeft _)) } 

_∘n_ : ∀ {D C} {F G H : Functor C D} (η : NaturalTransformation G H) (ε : NaturalTransformation F G) -> NaturalTransformation F H
_∘n_ {D} {C} {F} {G} {H} (Nat η commute1) (Nat ε commute2) = Nat {C} {D} {F} {H} (λ X → D [ η X ∘ ε X ]) (λ f →
  transitivity (sym (Category.assoc D _ _ _))
 (transitivity (cong2 (Category._∘_ D) (commute1 f) refl) (transitivity (Category.assoc D _ _ _) (transitivity (cong2 (Category._∘_ D) refl (commute2 f)) (sym (Category.assoc D _ _ _)))))) 

functor-cat : ∀ (C D : Category) -> Category
functor-cat C D = record {
                    Obj = Functor C D;
                    _⇒_ = NaturalTransformation;
                    id = nat-id;
                    _∘_ = _∘n_;
                    assoc = λ f g h → {!!};
                    idLeft = λ f → {!!};
                    idRight = λ f → {!!} } 

record CCC (C : Category) : Set where
 private module C = Category C
 open C
 
 field
  _×_ : Obj -> Obj -> Obj
  _⇨_ : Obj -> Obj -> Obj
  ⊤ : Obj
  ! : ∀ {X} -> X ⇒ ⊤ 
  <_,_> : ∀ {X Y Z} (f : X ⇒ Y) (g : X ⇒ Z) -> X ⇒ (Y × Z)
  π₁ : ∀ {X Y} -> (X × Y) ⇒ X
  π₂ : ∀ {X Y} -> (X × Y) ⇒ Y
  ƛ : ∀ {X Y Z} (f : (X × Y) ⇒ Z) -> X ⇒ (Y ⇨ Z)
  eval : ∀ {Y Z} -> ((Y ⇨ Z) × Y) ⇒ Z
  
  η⊤ : ∀ {X} (f : X ⇒ ⊤) -> f ≡ !
  β×₁ : ∀ {X Y Z} (f : X ⇒ Y) (g : X ⇒ Z) -> (π₁ ∘ < f , g >) ≡ f
  β×₂ : ∀ {X Y Z} (f : X ⇒ Y) (g : X ⇒ Z) -> (π₂ ∘ < f , g >) ≡ g
  η× : ∀ {X Y Z} (f : X ⇒ (Y × Z)) -> f ≡ < π₁ ∘ f , π₂ ∘ f >
  β : ∀ {X Y Z} (g : (X × Y) ⇒ Z) -> (eval ∘ < (ƛ g ∘ π₁) , π₂ >) ≡ g
  η : ∀ {X Y Z} (f : X ⇒ (Y ⇨ Z)) -> f ≡ ƛ (eval ∘ < f ∘ π₁ , π₂ >)

 β2 : ∀ {X Y Z} (f : (X × Y) ⇒ Z) (t : X ⇒ Y) -> (eval ∘ < ƛ f , t >) ≡ (f ∘ < id , t >)
 β2 f t = transitivity (cong2 _∘_ refl {w = < ƛ f ∘ π₁ , π₂ > ∘ < id , t >} (sym (transitivity (η× _) (cong2 <_,_> (transitivity (sym (assoc _ _ _)) (transitivity (cong2 _∘_ (β×₁ _ _) refl) (transitivity (assoc _ _ _) (transitivity (cong2 _∘_ refl (β×₁ _ _)) (idRight _)))))
  (transitivity (sym (assoc _ _ _)) (transitivity (cong2 _∘_ (β×₂ _ _) refl) (β×₂ _ _))))))) (transitivity (sym (assoc _ _ _)) (cong2 _∘_ (β _) refl))

SetIsCCC : CCC set
SetIsCCC = record {
             _×_ = _*_;
             _⇨_ = λ A B → A → B;
             ⊤ = Unit;
             ! = λ x → tt;
             <_,_> = λ f g x → f x , g x;
             π₁ = _*_.fst;
             π₂ = _*_.snd;
             ƛ = λ f x y → f (x , y);
             eval = λ fy → _*_.fst fy (_*_.snd fy);
             η⊤ = λ f → refl;
             β×₁ = λ f g → refl;
             β×₂ = λ f g → refl;
             η× = λ f → refl;
             β = λ g → refl;
             η = λ f → refl }