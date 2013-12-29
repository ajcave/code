module altenkirch-extensional-prop-irr-field where
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
  irr : ∀ {x y} -> {p q : eq x y} -> Eq._≡_ p q
  refl : ∀ x -> eq x x
  sym : ∀ {x y} -> eq x y -> eq y x
  trans : ∀ {x y z} -> eq x y -> eq y z -> eq x z

record Morph (X Y : Con) : Set where
 field
  fn : Con.set X -> Con.set Y
  resp : ∀ {x y} -> Con.eq X x y -> Con.eq Y (fn x) (fn y)

record Ty (X : Con) : Set₁ where
 field
  fm : Con.set X -> Con 
  subst : ∀ {x y} -> Con.eq X x y -> Con.set (fm x) -> Con.set (fm y)
  .subst* : ∀ {x y} (p : Con.eq X x y) (a b : Con.set (fm x)) -> Con.eq (fm y) (subst p a) (subst p b)
  .refl* : ∀ {x} (a : Con.set (fm x)) -> Con.eq (fm x) (subst (Con.refl X x) a) a
  .trans* : ∀ {x y z} (p : Con.eq X x y) (q : Con.eq X y z) (a : Con.set (fm x))
           -> Con.eq (fm z) (subst q (subst p a)) (subst (Con.trans X p q) a)
  
_[_] : ∀ {X Y} -> Ty Y -> Morph X Y -> Ty X
_[_] {X} {Y} A f = record {
   fm = λ x → Ty.fm A (Morph.fn f x);
   subst = λ p → Ty.subst A (Morph.resp f p);
   subst* = λ p → Ty.subst* A (Morph.resp f p);
   refl* = λ {x} a → Eq.subst (λ α → Con.eq (Ty.fm A (Morph.fn f x)) (Ty.subst A α a) a)
                     (Con.irr Y)
                     (Ty.refl* A a);
   trans* = λ {x} {y} {z} p q a → Eq.subst
                                    (λ α →
                                       Con.eq (Ty.fm A (Morph.fn f z))
                                       (Ty.subst A (Morph.resp f q) (Ty.subst A (Morph.resp f p) a))
                                       (Ty.subst A α a))
                                    (Con.irr Y) (Ty.trans* A (Morph.resp f p) (Morph.resp f q) a)
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
  resp : ∀ {x y : Con.set X} {p : Con.eq X x y} -> Con.eq (Ty.fm A y) (Ty.subst A p (tm x)) (tm y)

_[_]tm : ∀ {X Y} {A : Ty X} (t : Tm X A) (f : Morph Y X) -> Tm Y (A [ f ])
t [ f ]tm = record {
  tm = λ x → Tm.tm t (Morph.fn f x);
  resp = (λ {x} {y} {p} → Tm.resp t) -- Wow
 }