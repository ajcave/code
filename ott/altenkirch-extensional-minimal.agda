module altenkirch-extensional-minimal where
open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality
module Eq = Relation.Binary.PropositionalEquality
open import Function
open import Level

_≡_ : ∀ {l} {A : Set l} -> A -> A -> Set l
_≡_ = Eq._≡_

record Con : Set₁ where
 field
  set : Set
  eq : set -> set -> Set
  irr : ∀ {x y} -> (p q : eq x y) -> Eq._≡_ p q
  .refl : ∀ x -> eq x x
  .sym : ∀ {x y} -> eq x y -> eq y x
  .trans : ∀ {x y z} -> eq x y -> eq y z -> eq x z

record Morph (X Y : Con) : Set where
 field
  fn : Con.set X -> Con.set Y
  resp : ∀ {x y} -> Con.eq X x y -> Con.eq Y (fn x) (fn y)

record Ty (X : Con) : Set₁ where
 field
  fm : Con.set X -> Con 
  subst : ∀ {x y} -> .(Con.eq X x y) -> Con.set (fm x) -> Con.set (fm y)
  
_[_] : ∀ {X Y} -> Ty Y -> Morph X Y -> Ty X
_[_] {X} {Y} A f = record {
   fm = λ x → Ty.fm A (Morph.fn f x);
   subst = λ p → Ty.subst A (Morph.resp f p)
 }

idM : ∀ {X} -> Morph X X
idM = record { fn = id; resp = id }

[]-id : ∀ {X} (A : Ty X) -> (A [ idM ]) ≡ A
[]-id A = Eq.refl

_∘M_ : ∀ {X Y Z} -> Morph Y Z -> Morph X Y -> Morph X Z
f ∘M g = record { fn = Morph.fn f ∘ Morph.fn g; resp = Morph.resp f ∘ Morph.resp g }

[]-∘ : ∀ {X Y Z} (A : Ty Z) (f : Morph Y Z) (g : Morph X Y) -> (A [ (f ∘M g) ]) ≡ ((A [ f ]) [ g ])
[]-∘ A f g = Eq.refl

record Tm (X : Con) (A : Ty X) : Set where
 field
  tm : ∀ (x : Con.set X) -> Con.set (Ty.fm A x)
  resp : ∀ {x y : Con.set X} (p : Con.eq X x y) -> Con.eq (Ty.fm A y) (Ty.subst A p (tm x)) (tm y)

_[_]tm : ∀ {X Y} {A : Ty X} (t : Tm X A) (f : Morph Y X) -> Tm Y (A [ f ])
t [ f ]tm = record {
  tm = λ x → Tm.tm t (Morph.fn f x);
  resp = (λ {x} {y} p → Tm.resp t (Morph.resp f p))
 }

• : Con
• = record {
  set = ⊤;
  eq = λ x x' → ⊤;
  irr = λ p q -> Eq.refl;
  refl = _;
  sym = _;
  trans = _
 }


Σ-cong : ∀ {a b} {A : Set a} {P : A -> Set b} {x y : Σ A P} (p : (proj₁ x) ≡ (proj₁ y))
 -> (Eq.subst P p (proj₂ x)) ≡ (proj₂ y)
 -> x ≡ y
Σ-cong {a} {b} {A} {P} {.j , .y} {j , y} Eq.refl Eq.refl = Eq.refl

_·_ : (X : Con) -> (A : Ty X) -> Con
X · A = record {
  set = Σ (Con.set X) (λ x → Con.set (Ty.fm A x));
  eq = λ x y → Σ (Con.eq X (proj₁ x) (proj₁ y)) (λ p → Con.eq (Ty.fm A (proj₁ y)) (Ty.subst A p (proj₂ x)) (proj₂ y));
  irr = λ p q → Σ-cong (Con.irr X (proj₁ p) (proj₁ q)) {!!};
  refl = λ x → (Con.refl X _) , {!here we need refl*!} ;
  sym = λ x' → (Con.sym X (proj₁ x')) , {!!}; --(Ty.sym* A (proj₁ x') _ _ (proj₂ x'));
  trans = λ {x} {y} {z} x' x0 → (Con.trans X (proj₁ x') (proj₁ x0)) , {!!}
            -- Con.trans (Ty.fm A (proj₁ z))
            --  (Con.sym (Ty.fm A (proj₁ z)) (Ty.trans* A (proj₁ x') (proj₁ x0) _))
            --  (Con.trans (Ty.fm A (proj₁ z))
            --  (Ty.subst* A (proj₁ x0) _ _)
            --  (proj₂ x0))
 }