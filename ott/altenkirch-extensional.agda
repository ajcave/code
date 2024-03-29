module altenkirch-extensional where
open import Data.Unit
open import Data.Product

record Con : Set₁ where
 field
  set : Set
  eq : set -> set -> Set
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
  subst* : ∀ {x y} (p : Con.eq X x y) (a b : Con.set (fm x)) -> Con.eq (fm y) (subst p a) (subst p b)
  refl* : ∀ {x} (a : Con.set (fm x)) -> Con.eq (fm x) (subst (Con.refl X x) a) a
  trans* : ∀ {x y z} (p : Con.eq X x y) (q : Con.eq X y z) (a : Con.set (fm x))
           -> Con.eq (fm z) (subst q (subst p a)) (subst (Con.trans X p q) a)
  
_[_] : ∀ {X Y} -> Ty Y -> Morph X Y -> Ty X
A [ f ] = record {
   fm = λ x → Ty.fm A (Morph.fn f x);
   subst = λ p → Ty.subst A (Morph.resp f p);
   subst* = λ p → Ty.subst* A (Morph.resp f p);
   refl* = λ {x} a → {!Ty.refl* A!};
   trans* = {!!}
 }