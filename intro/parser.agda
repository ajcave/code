module parser where
open import Data.List
open import Data.String
open import Data.Char
open import Data.Bool

Tok = Char

data Parser : (A : Set) -> Set₁ where
 return : ∀ {A} -> (x : A) -> Parser A
 fail : ∀ {A} -> Parser A
 sat : (f : Tok -> Bool) -> Parser Tok 
 _<*>_ : ∀ {A B} -> (pf : Parser (A -> B)) -> (pa : Parser A) -> Parser B
 _<|>_ : ∀ {A} -> (p1 p2 : Parser A) -> Parser A
 fix : ∀ {A} -> (f : Parser A -> Parser A) -> Parser A