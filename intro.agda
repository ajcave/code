module intro where
{-
Helpful references:
http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.EmacsModeKeyCombinations
http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.UnicodeInput
-}

{- In SML this would be:
datatype nat = Zero | Succ of nat -}
data nat : Set where
 zero : nat
 succ : nat -> nat

{-
We can have fancy ("mixfix") operators and unicode
type \:: to get ∷
Place the cursor over ∷ and hit C-u C-x = to find out how to write it
datatype 'a list = Nil | Cons of 'a * 'a list -}
data list A : Set where
 [] : list A
 _∷_ : (x : A) -> (xs : list A) -> list A
-- Could simply write _∷_ : A -> list A -> list A

infixr 9 _∷_ -- cons should be right associative with some arbitrary precedence

example1 : list nat
example1 = zero ∷ (succ zero) ∷ (succ (succ zero)) ∷ []

-- The {}s mean that A, B and C are passed implicitly
-- Place the cursor in the hole and use C-c C-, to see the goal type and context
-- Use C-c C-c to do a case split
-- Type in the hole and use C-c C-r to attempt to refine
zipWith : {A B C : Set} -> (A -> B -> C) -> list A -> list B -> list C
zipWith f [] [] = []
zipWith f [] (x ∷ xs) = {!!} --??? It's an error, not just a warning to delete this case
zipWith f (x ∷ xs) [] = {!!} --???
zipWith f (x ∷ xs) (x' ∷ xs') = f x x' ∷ zipWith f xs xs'

{-
An equivalent way to write this type signature:
zipWith : ∀ {A B C} -> (A -> B -> C) -> list A -> list B -> list C
-}

data vec A : nat -> Set where
 [] : vec A zero
 _∷_ : {n : nat} -> (x : A) -> (xs : vec A n) -> vec A (succ n)

example2 : vec nat (succ (succ zero))
example2 = zero ∷ zero ∷ []

{- This is a type error: 
example3 : vec nat (succ (succ zero))
example3 = zero ∷ zero ∷ zero ∷ []
-}

-- Now it discards the impossible cases for us!
zipWith2 : {A B C : Set} -> {n : nat} -> (A -> B -> C) -> vec A n -> vec B n -> vec C n
zipWith2 f [] [] = []
zipWith2 f (x ∷ xs) (x' ∷ xs') = f x x' ∷ zipWith2 f xs xs'

-- An equivalent, less verbose type signature
-- Try C-c C-a in the holes ("a" for "auto")
-- The types are so restrictive that it can find the solution!
zipWith3 : ∀ {A B C n} -> (A -> B -> C) -> vec A n -> vec B n -> vec C n
zipWith3 f [] [] = ?
zipWith3 f (x ∷ xs) (x' ∷ xs') = {!!}