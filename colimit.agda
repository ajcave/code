module colimit where
open import Relation.Binary.PropositionalEquality
open import Level
--open import Data.Product
import Function

-- Based on copumpkin's category theory library
postulate
 funext : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g
 magic : ∀ {A : Set} {x y : A} -> .(x ≡ y) -> x ≡ y

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
  constructor _,_
  module c₁ = Cone c₁
  module c₂ = Cone c₂
  module C = Category C
  module J = Category J
  open C
  field
    f : C.hom (c₁.N) (c₂.N)
    .commute : ∀ {X} → c₁.ψ X ≡ c₂.ψ X ∘ f

ConeMorphism-≡ : ∀ {o ℓ} {o′ ℓ′} {C : Category o ℓ} {J : Category o′ ℓ′} {F : Functor J C} {c₁ c₂ : Cone F} {f g : ConeMorphism c₁ c₂}
 -> ConeMorphism.f f ≡ ConeMorphism.f g -> f ≡ g
ConeMorphism-≡ {o} {ℓ} {o′} {ℓ′} {C} {J} {F} {c₁} {c₂} {.f' , commute} {f' , commute'} refl = refl

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

record ∃ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    .proj₂ : B proj₁

open ∃

∃-≡ : ∀ {a b} {A : Set a} {B : A → Set b} {x y : ∃ A B} -> proj₁ x ≡ proj₁ y -> x ≡ y
∃-≡ {x = x₁ , x₂} {y = .x₁ , y₂} refl = refl

ISetComplete : Complete zero zero ISet
ISetComplete = record { limit = λ {J} F → record { terminal = record {
  ⊤ = record { N = ∃ (∀ i → Functor.F₀ F i) (λ x → {i j : _} (f : Category.hom J i j) →
                                                     Functor.F₁ F f (x i) ≡ x j);
               ψ = λ i x → proj₁ x i;
               commute = λ f → funext (λ x → proj₂ x f) };
  ! = λ {A} → record { f = λ x → (λ i → Cone.ψ A i x) , (λ f → cong (Function.flip Function._$_ x) (Cone.commute A f));
                       commute = refl };
  !-unique = {!!} --λ { (f , p) → ConeMorphism-≡ (funext (λ x → ∃-≡ (funext (λ x' → cong (Function.flip Function._$_ x) (magic p))))) }
 } } }

Endofunctor : ∀ {o ℓ} → Category o ℓ → Set _
Endofunctor C = Functor C C

record F-Coalgebra {o ℓ} {C : Category o ℓ} (F : Endofunctor C) : Set (o ⊔ ℓ) where
  constructor _,_
  open Category C
  open Functor F
  field
    A : Obj
    α : hom A (F₀ A)

record F-Coalgebra-Morphism {o ℓ} {C : Category o ℓ} {F : Endofunctor C} (X Y : F-Coalgebra F) : Set ℓ where
  constructor _,_
  open Category C
  module X = F-Coalgebra X
  module Y = F-Coalgebra Y
  open Functor F
  field
    f : hom (X.A) (Y.A)
    .commutes : Y.α ∘ f ≡ F₁ f ∘ X.α

