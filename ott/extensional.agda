module extensional where
-- Based on Altenkirch's LICS paper

open import Data.Product

record Setoid : Set₁ where
 field
  set : Set
  _∼_ : set -> set -> Set
  refl : ∀ x -> x ∼ x
  sym : ∀ {x y} -> x ∼ y -> y ∼ x
  trans : ∀ {x y z} -> x ∼ y -> y ∼ z -> x ∼ z

open Setoid

eq : ∀ (X : Setoid) (x y : set X) -> Set
eq = _∼_

Con = Setoid

syntax eq X x y = x ∼[ X ] y 

record Morphism (X Y : Setoid) : Set where
 field
  fn : set X -> set Y
  resp : ∀ {x y : set X} -> x ∼[ X ] y -> (fn x) ∼[ Y ] (fn y)

open Morphism

record Ty (X : Con) : Set₁ where
 field
  fm : set X -> Con
  subst : ∀ {x y : set X} -> x ∼[ X ] y -> set (fm x) -> set (fm y)
  subst* : ∀ {x y : set X} (p : x ∼[ X ] y) (a b : set (fm x)) -> a ∼[ fm x ] b
           -> (subst p a) ∼[ fm y ] (subst p b) 
  refl* : ∀ {x : set X} (a : set (fm x)) -> (subst (refl X x) a) ∼[ fm x ] a
  trans* : ∀ {x y z : set X} (p : x ∼[ X ] y) (q : y ∼[ X ] z) (a : set (fm x))
           -> (subst q (subst p a)) ∼[ fm z ] (subst (trans X p q) a)

open Ty

_[_] : ∀ {X Y} (A : Ty Y) (f : Morphism X Y) -> Ty X
A [ f ] = record {
           fm = λ x → fm A (fn f x);
           subst = λ p → subst A (resp f p);
           subst* = λ p → subst* A (resp f p);
           refl* = λ a -> {!!} ;
           trans* = {!!}
          }

record ⊤ : Set where
 constructor 〈〉


⊡ : Con
⊡ = record { set = ⊤; _∼_ = λ x x₁ → ⊤; refl = λ x → 〈〉; sym = λ {x} {y} _ → 〈〉; trans = λ {x} {y} {z} _ _ → 〈〉 }

_·_ : (X : Con) -> (A : Ty X) -> Con
X · A = record { set = Σ (set X) (λ x -> set (fm A x)) ;
                 _∼_ = λ {(x , a) (y , b)  → Σ (x ∼[ X ] y) (λ p → (subst A p a) ∼[ fm A y ] b) };
                 refl = λ x → (refl X _) , {!!};
                 sym = {!!};
                 trans = {!!}
               }

open import Data.Bool
open import Data.Empty

_∼bool_ : (x y : Bool) -> Set
true ∼bool true = ⊤
true ∼bool false = ⊥
false ∼bool true = ⊥
false ∼bool false = ⊤

bool : ∀ {X : Con} -> Ty X
bool = record {
          fm = λ x → record { set = Bool; _∼_ = _∼bool_; refl = {!!}; sym = {!!}; trans = {!!} };
          subst = λ p b → b;
          subst* = {!!};
          refl* = {!!};
          trans* = {!!}
         }

bot : Con
bot = record { set = ⊥; _∼_ = λ x x₁ → ⊤; refl = {!!}; sym = {!!}; trans = {!!} }

El : ∀ (X : Con) -> Ty (X · bool)
El X = record {
        fm = λ { (x , b) -> if b then ⊡ else bot };
        subst = λ { {x , true} {y , true} (x₁ , b1) x2 → x2 ;
                    {x , true} {y , false} (x₁ , ()) x2 ;
                    {x , false} {y , true} (x₁ , ()) x2 ;
                    {x , false} {y , false} (x₁ , b1) x2 → x2 };
        subst* = {!!};
        refl* = {!!};
        trans* = {!!}
       }
{- Conclusion: 
Has to normalize t1 and t2 in t1 =bool t2. If they're the same, great, if not, absurd.
More HoTT-like alternative: normalize proof of t1 =bool t2 to either "refl_true" or refl_false"
Downside: has to compute proofs
-}