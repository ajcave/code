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
  .subst* : ∀ {x y} (p : Con.eq X x y) (a b : Con.set (fm x)) -> Con.eq (fm y) (subst p a) (subst p b)
  .refl* : ∀ {x} (a : Con.set (fm x)) -> Con.eq (fm x) (subst (Con.refl X x) a) a
  .trans* : ∀ {x y z} (p : Con.eq X x y) (q : Con.eq X y z) (a : Con.set (fm x))
           -> Con.eq (fm z) (subst q (subst p a)) (subst (Con.trans X p q) a)

 .sym* : ∀ {x y} (p : Con.eq X x y) (b : Con.set (fm y)) (a : Con.set (fm x))
           -> Con.eq (fm y) (subst p a) b
           -> Con.eq (fm x) (subst (Con.sym X p) b) a
 sym* {x} {y} p b a d = Con.trans (fm x)
                         (subst* (Con.sym X p) b (subst p a))
                         (Con.trans (fm x)
                         (trans* p (Con.sym X p) a)
                         (Eq.subst (λ α → Con.eq (fm x) (subst α a) a)
                           (Con.irr X (Con.trans X p (Con.sym X p)) (Con.refl X x))
                           (refl* a)))
  
_[_] : ∀ {X Y} -> Ty Y -> Morph X Y -> Ty X
_[_] {X} {Y} A f = record {
   fm = λ x → Ty.fm A (Morph.fn f x);
   subst = λ p → Ty.subst A (Morph.resp f p);
   subst* = λ p → Ty.subst* A (Morph.resp f p);
   refl* = λ {x} a → Eq.subst (λ α → Con.eq (Ty.fm A (Morph.fn f x)) (Ty.subst A α a) a)
                     (Con.irr Y (Con.refl Y (Morph.fn f x)) (Morph.resp f (Con.refl X x)) )
                     (Ty.refl* A a);
   trans* = λ {x} {y} {z} p q a → Eq.subst
                                    (λ α →
                                       Con.eq (Ty.fm A (Morph.fn f z))
                                       (Ty.subst A (Morph.resp f q) (Ty.subst A (Morph.resp f p) a))
                                       (Ty.subst A α a))
                                    (Con.irr Y (Con.trans Y (Morph.resp f p) (Morph.resp f q))
                                               (Morph.resp f (Con.trans X p q)))
                                    (Ty.trans* A (Morph.resp f p) (Morph.resp f q) a)
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

_·_ : (X : Con) -> (A : Ty X) -> Con
X · A = record {
  set = Σ (Con.set X) (λ x → Con.set (Ty.fm A x));
  eq = λ x y → Σ (Con.eq X (proj₁ x) (proj₁ y)) (λ p → Con.eq (Ty.fm A (proj₁ y)) (Ty.subst A p (proj₂ x)) (proj₂ y));
  irr = {!!};
  refl = λ x → (Con.refl X _) , (Ty.refl* A _);
  sym = λ x' → (Con.sym X (proj₁ x')) , (Ty.sym* A (proj₁ x') _ _ (proj₂ x'));
  trans = λ {x} {y} {z} x' x0 → (Con.trans X (proj₁ x') (proj₁ x0)) ,
            Con.trans (Ty.fm A (proj₁ z))
             (Con.sym (Ty.fm A (proj₁ z)) (Ty.trans* A (proj₁ x') (proj₁ x0) _))
             (Con.trans (Ty.fm A (proj₁ z))
             (Ty.subst* A (proj₁ x0) _ _)
             (proj₂ x0))
 }