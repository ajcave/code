module string where
open import helper
open import Data.String
open import Data.Bool
open import Data.Nat
open import Data.Nat.Show
open import Data.Sum
open import Data.Product
open import Data.Unit

t : String
t = "abc"

infixr 9 _⊗_

data Datatype : Type  where
 bool nat string unit : Datatype
 _⊗_ : (U1 : Datatype) -> (U2 : Datatype) -> Datatype
 _of_∣_of_ : (l1 : String) -> (U1 : Datatype) -> (l2 : String) -> (U2 : Datatype) -> Datatype

decode : Datatype -> Type
decode unit = ⊤
decode bool = Bool
decode nat = ℕ
decode string = String
decode (U1 ⊗ U2) = decode U1 × decode U2
decode (l1 of U1 ∣ l2 of U2) = decode U1 ⊎ decode U2



toString : (U : Datatype) -> decode U -> String
toString unit x = "()"
toString bool true = "true"
toString bool false = "false"
toString nat n = show n
toString string s = s
toString (U1 ⊗ U2) (x1 , x2) = "(" ++ (toString U1 x1) ++ "," ++ (toString U2 x2) ++ ")"
toString (l1 of U1 ∣ l2 of U2) (inj₁ x) = "(" ++ l1 ++ " " ++ toString U1 x ++ ")"
toString (l1 of U1 ∣ l2 of U2) (inj₂ y) = "(" ++ l2 ++ " " ++ toString U2 y ++ ")"

employee : Datatype
employee = string ⊗ ("Manager" of string ∣ "NotManager" of unit) ⊗ nat
           -- Name, Is Manager of department, Birth year

john : decode employee
john = "John Smith" , (inj₁ "Cybernetics") , 04
-- Not Y2K compliant...

joe : decode employee
joe = "Joe Smith" , (inj₂ tt) , 04





