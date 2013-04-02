module helper where
open import Relation.Binary.PropositionalEquality public
open ≡-Reasoning public
open import Data.Nat public hiding (_*_)
open import Function public
open import Data.String

number = ℕ

reflexivity : ∀ {a} {A : Set a} {x : A} -> x ≡ x
reflexivity = refl

program : ∀ {a} {A : Set a} {x : A} -> x ≡ x
program = refl

data option a' : Set where
 NONE : option a'
 SOME : (x : a') -> option a'

Type : Set₁
Type = Set

record _*_ (a' b' : Type) : Type where
 constructor _,_
 field
  fst : a'
  snd : b'

infixr 9 _,_
infixr 9 _*_


congruence' : {a' b' : Set} (f : a' -> b') (x y : a') -> x ≡ y -> f x ≡ f y
congruence' f .y y refl = refl

congruence : {a' b' : Set} (f : a' -> b') {x y : a'} -> x ≡ y -> f x ≡ f y
congruence f refl = refl
