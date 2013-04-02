module string where
open import Data.String
open import Data.Bool
open import Data.Nat
open import Data.Nat.Show
open import Data.Sum
open import Data.Product

t : String
t = "abc"

infixr 9 _⊗_

data Universe : Set where
 bool nat string : Universe
 _⊗_ : (U1 : Universe) -> (U2 : Universe) -> Universe
 _⊕_ : (U1 : Universe) -> (U2 : Universe) -> Universe

decode : Universe -> Set
decode bool = Bool
decode nat = ℕ
decode string = String
decode (U1 ⊗ U2) = decode U1 × decode U2
decode (U1 ⊕ U2) = decode U1 ⊎ decode U2



toString : (U : Universe) -> decode U -> String
toString bool true = "true"
toString bool false = "false"
toString nat n = show n
toString string s = s
toString (U1 ⊗ U2) (x1 , x2) = "(" ++ (toString U1 x1) ++ "," ++ (toString U2 x2) ++ ")"
toString (U1 ⊕ U2) (inj₁ x) = "(Left: " ++ toString U1 x ++ ")"
toString (U1 ⊕ U2) (inj₂ y) = "(Right: " ++ toString U2 y ++ ")"

employee : Universe
employee = string ⊗ bool ⊗ nat
           -- Name, Is Manager, Birth year

john : decode employee
john = "John Smith" , true , 1980




