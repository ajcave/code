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

_+_ : nat -> nat -> nat
m + n = {!!} 

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

-- The {}s mean that A, B and C are implicit arguments
-- Place the cursor in the hole and use C-c C-, to see the goal type and context
-- Use C-c C-c to do a case split
-- Type in the hole and use C-c C-r to attempt to refine
zipWith : {A B C : Set} -> (A -> B -> C) -> list A -> list B -> list C
zipWith f [] [] = []
zipWith f [] (x ∷ xs) = {!!} --??? It's an error, not just a warning to delete this case
zipWith f (x ∷ xs) [] = {!!} --???
zipWith f (x ∷ xs) (x' ∷ xs') = f x x' ∷ zipWith f xs xs'

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
zipWith3 f [] [] = {!!}
zipWith3 f (x ∷ xs) (x' ∷ xs') = {!!}

data type : Set where
 bool : type
 natural : type

data expr : type -> Set where
 zero : expr natural
 succ : (n : expr natural) -> expr natural 
 if_then_else_ : ∀ {t} (cond : expr bool) (t1 t2 : expr t) -> expr t
 true : expr bool
 false : expr bool
 _⊕_ : ∀ (n m : expr natural) -> expr natural
 _==_ : ∀ {t} (a b : expr t) -> expr bool 

example4 : expr natural
example4 = if ((zero ⊕ succ zero) == (succ zero)) then zero else (succ zero)

{- This is a type error:
example5 : expr natural
example5 = if zero then true else false
-}

data value : type -> Set where
 zero : value natural
 succ : value natural -> value natural
 true : value bool
 false : value bool

_+v_ : value natural -> value natural -> value natural
zero +v m = m
succ n +v m = succ (n +v m)

_=v_ : ∀ {t} -> value t -> value t -> value bool
zero =v zero = true
zero =v succ m = false
succ n =v zero = false
succ n =v succ m = m =v n
true =v true = true
true =v false = false
false =v true = false
false =v false = true

eval : ∀ {t} -> expr t -> value t
eval zero = zero
eval (succ y) = succ (eval y)
eval (if cond then t1 else t2) with eval cond
eval (if cond then t1 else t2) | true = eval t1
eval (if cond then t1 else t2) | false = eval t2 
eval true = true
eval false = false
eval (n ⊕ m) = (eval n) +v (eval m)
eval (a == b) = (eval a) =v (eval b)
-- Notice there are no bad cases: they are ruled out based on their types!

example6 : value natural
example6 = eval example4
-- C-c C-n will let you evaluate a term to *n*ormal form
-- it will show us that example6 is zero, as expected

-- TODO: Talk about termination checking. Possibly with substitution
-- TODO: Talk about proofs! Vector append, vector reversal! Computation in types