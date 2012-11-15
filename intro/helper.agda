module helper where
open import Relation.Binary.PropositionalEquality public
open ≡-Reasoning public
open import Data.Nat public
open import Function public

number = ℕ

reflexivity : ∀ {a} {A : Set a} {x : A} -> x ≡ x
reflexivity = refl

program : ∀ {a} {A : Set a} {x : A} -> x ≡ x
program = refl

data option a' : Set where
 NONE : option a'
 SOME : (x : a') -> option a'