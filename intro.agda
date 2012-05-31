module intro where
{-
See http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.EmacsModeKeyCombinations
for a complete list of Agda mode key combinations
See http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.UnicodeInput
for unicode input
-}


{- In SML this would be:
datatype nat = Zero | Succ of nat
-}
data nat : Set where
 zero : nat
 succ : nat -> nat

-- We can have infix operators and unicode
-- type \:: to get ∷
-- Place the cursor over ∷ and hit C-u C-x = to find out how to write it
-- datatype 'a list = Nil | Cons of 'a * 'a list 
data list A : Set where
 [] : list A
 _∷_ : A -> list A -> list A

infixr 9 _∷_ -- cons should be right associative with some arbitrary precedence

example : list nat
example = zero ∷ (succ zero) ∷ (succ (succ zero)) ∷ []