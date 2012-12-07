module colimit where
open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Product
import Function

-- Based on copumpkin's category theory library
postulate
 funext : ∀ {A B : Set} {f g : A -> B} -> (∀ x -> f x ≡ g x) -> f ≡ g

record Category a b : Set (suc (a ⊔ b)) where
 field
  Obj : Set a
  hom : Obj -> Obj -> Set b
  id : ∀ {C} -> hom C C
  _∘_ : ∀ {A B C} -> hom B C -> hom A B -> hom A C
  .idL : ∀ {A B} -> (f : hom A B) -> (id ∘ f) ≡ f
  .idR : ∀ {A B} -> (f : hom A B) -> (f ∘ id) ≡ f
  .assoc : ∀ {A B C D} (f : hom C D) (g : hom B C) (h : hom A B) -> ((f ∘ g) ∘ h) ≡ (f ∘ (g ∘ h))

record Functor {a b c d} (C : Category a b) (D : Category c d) : Set (a ⊔ b ⊔ c ⊔ d) where
 private module C = Category C
 private module D = Category D
 field
  F₀ : C.Obj -> D.Obj
  F₁ : ∀ {X Y} -> C.hom X Y -> D.hom (F₀ X) (F₀ Y)
  .id : ∀ {X} -> F₁ (C.id {X}) ≡ D.id
  .fhom : ∀ {X Y Z} (f : C.hom Y Z) (g : C.hom X Y) -> F₁ (C._∘_ f g) ≡ D._∘_ (F₁ f) (F₁ g)


record Cone {o ℓ} {o′ ℓ′} {C : Category o ℓ} {J : Category o′ ℓ′} (F : Functor J C) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
 module J = Category J
 open Category C
 open Functor F
 field
   N : Obj
   ψ : ∀ X → (hom N (F₀ X))
   .commute : ∀ {X Y} (f : J.hom X Y) → F₁ f ∘ ψ X ≡ ψ Y

record Cocone {o ℓ} {o′ ℓ′} {C : Category o ℓ} {J : Category o′ ℓ′} (F : Functor J C) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
 module J = Category J
 open Category C
 open Functor F
 field
   N : Obj
   ψ : ∀ X → (hom (F₀ X) N)
   .commute : ∀ {X Y} (f : J.hom X Y) → ψ X ≡ ψ Y ∘ F₁ f

record ConeMorphism {o ℓ} {o′ ℓ′} {C : Category o ℓ} {J : Category o′ ℓ′} {F : Functor J C} (c₁ c₂ : Cone F) : Set (ℓ ⊔ o′ ⊔ ℓ′) where
  module c₁ = Cone c₁
  module c₂ = Cone c₂
  module C = Category C
  module J = Category J
  open C
  field
    f : C.hom (c₁.N) (c₂.N)
    .commute : ∀ {X} → c₁.ψ X ≡ c₂.ψ X ∘ f

record CoconeMorphism {o ℓ} {o′ ℓ′} {C : Category o ℓ} {J : Category o′ ℓ′} {F : Functor J C} (c₁ c₂ : Cocone F) : Set (ℓ ⊔ o′ ⊔ ℓ′) where
  module c₁ = Cocone c₁
  module c₂ = Cocone c₂
  module C = Category C
  module J = Category J
  open C
  field
    f : C.hom (c₁.N) (c₂.N)
    .commute : ∀ {X} → f ∘ c₁.ψ X ≡ c₂.ψ X

Cones : ∀ {o ℓ} {o′ ℓ′} {C : Category o ℓ} {J : Category o′ ℓ′} (F : Functor J C) → Category (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) (ℓ ⊔ o′ ⊔ ℓ′)
Cones {C = C} F = record {
   Obj = Cone F;
   hom = ConeMorphism;
   id = record { f = Category.id C; commute = sym (Category.idR C _) };
   _∘_ = _∘′_;
   idL = λ f' → {!!};
   idR = {!!};
   assoc = {!!}
 }
 where 
 infixr 9 _∘′_
 open Category C
 open Cone
 open ConeMorphism

 Obj′ = Cone F
 
 Hom′ : Obj′ → Obj′ → Set _
 Hom′ = ConeMorphism
 
 _∘′_ : ∀ {X Y Z} → Hom′ Y Z → Hom′ X Y → Hom′ X Z
 _∘′_ {X} {Y} {Z} F G = record { f = (f F) ∘ (f G); commute = commute′ }
  where
  .commute′ : ∀ {W} → ψ X W ≡ ψ Z W ∘ (f F ∘ f G)
  commute′ {W} = begin
    ψ X W
     ≡⟨ ConeMorphism.commute G ⟩
    ψ Y W ∘ f G
     ≡⟨ cong (Function.flip _∘_ (f G)) (ConeMorphism.commute F) ⟩
    (ψ Z W ∘ f F) ∘ f G
     ≡⟨ assoc _ _ _ ⟩
    (ψ Z W ∘ (f F ∘ f G)
   ∎)
   where
   open ≡-Reasoning

record Terminal {o ℓ} (C : Category o ℓ) : Set (o ⊔ ℓ) where
  open Category C
  field
    ⊤ : Obj
    ! : ∀ {A} → (hom A ⊤)
    .!-unique : ∀ {A} → (f : hom A ⊤) → ! ≡ f

record Limit {o ℓ} {o′ ℓ′} {C : Category o ℓ} {J : Category o′ ℓ′} (F : Functor J C): Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) where
  field
   terminal : Terminal (Cones F)

record Complete (o ℓ : Level) {o′ ℓ′} (C : Category o′ ℓ′) : Set (suc o ⊔ suc ℓ ⊔ o′ ⊔ ℓ′) where
 field
  limit : ∀ {J : Category o ℓ} (F : Functor J C) → Limit F

ISet : Category (suc zero) zero
ISet = record {
  Obj = Set;
  hom = λ X Y -> X → Y;
  id = λ x → x;
  _∘_ = λ f g -> Function._∘_ f g;
  idL = λ f → refl;
  idR = λ f → refl;
  assoc = λ f g h → refl
 }

ISetComplete : Complete zero zero ISet
ISetComplete = record { limit = λ {J} F → record { terminal = record {
  ⊤ = record { N = Σ (∀ i → Functor.F₀ F i) (λ x → {i j : _} (f : Category.hom J i j) →
                                                     Functor.F₁ F f (x i) ≡ x j);
               ψ = λ i x → proj₁ x i;
               commute = λ f → funext (λ x → proj₂ x f) };
  ! = {!!};
  !-unique = {!!}
 } } }

{-
Cocones : ∀ {o ℓ} {o′ ℓ′} {C : Category o ℓ} {J : Category o′ ℓ′} (F : Functor J C) → Category (o ⊔ ℓ ⊔ o′ ⊔ ℓ′) (ℓ ⊔ o′ ⊔ ℓ′)
Cocones {C = C} F = record {
   Obj = Cocone F;
   hom = CoconeMorphism;
   id = record { f = {!C.id!}; commute = {!!} };
   _∘_ = {!!};
   idL = {!!};
   idR = {!!};
   assoc = {!!} }
-}