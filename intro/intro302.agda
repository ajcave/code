{-# OPTIONS --type-in-type #-}
module intro302 where
open import helper
{-
Helpful references:
http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.EmacsModeKeyCombinations
http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.UnicodeInput
-}














{-
In SML, we could define our own type of lists like this:

 datatype 'a mylist = Nil | Cons of 'a * 'a mylist

In Agda, we write:
-}

data mylist a : Type where
 Nil : mylist a
 Cons : a -> mylist a -> mylist a

mylist-eg = Cons 1 (Cons 2 (Cons 3 Nil))

{-  Compare with SML: 

val mylist-eg = Cons (1, Cons (2, Cons (3, Nil)))

to represent the list [1,2,3]
-}

-- But let's use fancier notation:
data list a : Type where
 [] : list a
 _∷_ : a -> list a -> list a
-- Unicode! Type \:: to get ∷
-- Place the cursor over ∷ and hit C-u C-x = to find out how to write it

infixr 9 _∷_ -- cons should be right associative with some arbitrary precedence (9)

example1 : list number
example1 = 1 ∷ 2 ∷ 3 ∷ []
-- In SML notation: [1,2,3]





{- Example: Incrementing the numbers in a list

In SML, this would be:

incList : int list -> int list
   
fun incList [] = []
  | incList (x::xs) = (x + 1)::(incList xs)  

In Agda:
-}

incList : list number -> list number
incList [] = []
incList (x ∷ xs) = (x + 1) ∷ (incList xs)






{- Example higher order polymorphic function: map

In SML, this would be:

map : ('a -> 'b) -> 'a list -> 'b list

fun map f [] = []
  | map f (x::xs) = (f x)::(map f xs)

In Agda, we write
-}

map : {a : Type} {b : Type} -> (a -> b) -> list a -> list b
map f [] = []
map f (x ∷ xs) = (f x) ∷ map f xs

-- We have to explicitly say we are polymorphic over types "a" and "b":










{- Example: zip

zip [1,2,3] [4,5,6] = [(1,4), (2,5), (3,6)]

Developed interactively: 
 Place the cursor in the hole and use C-c C-, to see the goal type and context
   Use C-c C-c to do a case split
   Type in the hole and use C-c C-r to attempt to refine
-}

zip : {a b : Type} -> list a -> list b -> list (a * b)
zip xs ys = {!!}


{- Problem: What to do with the mismatched cases?
   Maybe these indicate an error we want to catch (as early as possible!) -}

















{- Solution: We _index_ lists by their length

Something of type "vec a n" is a list of exactly n things of type "a"

[] is a list of length 0

If x is an "a" and xs is a list of length n, then x ∷ xs is a list of
 length (1 + n)
-}
data vec a : number -> Type where
 [] : vec a 0
 _∷_ : {n : number} -> a -> vec a n -> vec a (1 + n)

example2 : vec number 2
example2 = 7 ∷ 10 ∷ []

-- This is a type error: 
--example3 : vec number 3
--example3 = 7 ∷ 10 ∷ []




-- Now let's write zip using vec instead of list:
zip' : {a b : Type} -> (n : number) -> vec a n -> vec b n -> vec (a * b) n
zip' n xs ys = {!!}

-- Now it discards the impossible cases for us!
-- Can we even write the mismatched case?
-- Notice that we get extra information we get to help us find the right solution


exampleZ1 = zip' 3 (1 ∷ 2 ∷ 3 ∷ []) ("foo" ∷ "bar" ∷ "baz" ∷ [])

--exampleZ2 = zip' 3 (1 ∷ 2 ∷ 3 ∷ []) ("foo" ∷ "bar" ∷ [])




-- We make n an "implicit" argument by putting it in {}s
zip'' : {a b : Set} -> {n : number} -> vec a n -> vec b n -> vec (a * b) n
zip'' xs ys = {!!}

-- Now we leave the 3 off, and Agda figures it out for us
exampleZ'' = zip'' (1 ∷ 2 ∷ 3 ∷ []) ("foo" ∷ "bar" ∷ "baz" ∷ [])

{- How much choice do we have when writing this function?
   What could we possibly do while still having the same type?
   In fact Agda can find the right program automatically: C-c C-a
-}



-- What happens if we make a mistake when writing zip?
-- (e.g. we forget to use ∷ )
{-
zip-bad : {a b : Type} -> {n : number} -> vec a n -> vec b n -> vec (a * b) n
zip-bad [] [] = []
zip-bad (x ∷ xs) (y ∷ ys) = zip-bad xs ys
-}



-- Agda performs termination checking, and this fails!
zip-bad2 : {a b : Type} ->  list a -> list b -> list (a * b)
zip-bad2 xs ys = zip-bad2 xs ys

-- The termination checking is not perfect:
{-
 inc takes a list and
 adds 0 to the first element
 adds 1 to the second
 adds 2 to the third
 ...
 This terminates, but Agda can't see why!
-}
inc : list number -> list number
inc [] = []
inc (x ∷ xs) = x ∷ inc (map (λ y → y + 1) xs)


-- But usually we can rewrite our functions to pass the termination
-- checker:
inc' : list number -> list number
inc' [] = []
inc' (x ∷ xs) = x ∷ (map (λ y → y + 1) (inc' xs))
-- This is like (machine-checkable!) documentation!
-- It communicates *why* something terminates to readers of your code



{- ============================================= -}
{- hd and tl caused problems in SML. Here we can express
   precisely that they expect an input of length > 0
-}


hd : {a : Type} {n : number} -> vec a (1 + n) -> a
hd (x ∷ xs) = x

tl : {a : Type} {n : number} -> vec a (1 + n) -> vec a n
tl (x ∷ xs) = xs



hd-eg1 = hd (1 ∷ 2 ∷ 3 ∷ [])

--hd-eg2 = hd []


{- Example: map for vectors
   vmap preserves the length!
-}
vmap : {a b : Set} {n : number}
   -> (a -> b) -> vec a n -> vec b n
vmap f [] = []
vmap f (x ∷ xs) = f x ∷ vmap f xs

{-
An m by n matrix can be described as an m length vector
of n length vectors:
-}
matrix : (a : Set) -> number -> number -> Set
matrix a m n = vec (vec a n) m

{- Example: Matrix transpose:

Transposing    xss = [[1,2],
                      [3,4],
                      [5,6]]
gives:
                   [[1,3,5],
                    [2,4,6]]      

We are going to get the first column of the input with:

  vmap hd xss

e.g. This will get [1,3,5]

And the rest of the columns with:

  vmap tl xss

e.g. This will get
  [[2],
   [4],
   [6]]
-}


-- The number of columns of the first matrix = the number of rows of the output
transpose : {a : Set} {n : number} (p : number) -- number of columns of input
  -> matrix a n p -> matrix a p n
transpose zero xss = []
transpose (suc p') xss = (vmap hd xss) ∷ (transpose p' (vmap tl xss))
-- Here we know for sure that hd is safe (and the typechecker can check it!)

-- We can't accidentally forget the base case:
--transpose-bad : {a : Set} {n : number} {p : number} -> matrix a n p -> matrix a p n
--transpose-bad xss = (vmap hd xss) ∷ (transpose (vmap tl xss))


{- Example: Matrix multiplication:
From linear algebra:

You can multiply:

[[1,2],         [[7,8,9,0],
 [3,4],   with   [1,2,3,4]]
 [5,6]]

But you *can't* multiply:

[[1,2],         [[7,8,9,0],
 [3,4],   with   [1,2,3,4],
 [5,6]]          [5,6,7,8]]

Because the dimensions don't line up.

We can express this with dependent types!
-}

mult : ∀ {n m p} -> matrix number m n -> matrix number n p -> matrix number m p
mult xss yss = {!!}


mult-eg1 = mult (   (1 ∷ 2 ∷ [])
                  ∷ (3 ∷ 4 ∷ [])
                  ∷ (5 ∷ 6 ∷ [])
                  ∷ [])

                (   (7 ∷ 8 ∷ 9 ∷ 0 ∷ [])
                  ∷ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
                  ∷ [])
-- This typechecks because the dimensions line up.

-- But this won't, because the dimensions don't line up:
{-
mult-eg2 = mult (   (1 ∷ 2 ∷ [])
                  ∷ (3 ∷ 4 ∷ [])
                  ∷ (5 ∷ 6 ∷ [])
                  ∷ [])

                (   (7 ∷ 8 ∷ 9 ∷ 0 ∷ [])
                  ∷ (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
                  ∷ (5 ∷ 6 ∷ 7 ∷ 8 ∷ [])
                  ∷ [])
-}












{- Example: vector append -}
_++_ : {a : Set} {n m : number} -> vec a n -> vec a m -> vec a (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- We put a computation in the type, and it simplified for us!











-- But it can get hairy
rev-acc : {a : Type} {n m : number} -> vec a n -> vec a m -> vec a (n + m)
rev-acc [] acc = acc
rev-acc (x ∷ xs) acc = {!!} --rev-acc xs (x ∷ acc)

-- Agda can't see that 1 + (n + m) = n + (1 + m)
-- We'd have to *prove* this to Agda
-- Other systems will see this automatically (but have other downsides)








{-=====================================================================-}
{- Example: Arrays

Arrays are a common source of runtime crashes:

e.g. arr[10] when arr is only an array of size 5 --> Crash

Dependent types to the rescue again!
-}



{- bounded n is the type of numbers strictly less than n
   i.e. zero is a "bounded-num 1" and a "bounded-num 2" and a "bounded-num 3", ...
        succ zero is a "bounded-num 2" and a "bounded-num 3", but *not* a "bounded-num 1"
-}
data bounded-num : number -> Set where
 zero : {n : number} -> bounded-num (1 + n)
 succ : {n : number} -> bounded-num n -> bounded-num (1 + n)

{- Given a number n < m and a vector xs of length m, looks up
   the nth element of xs
-}
nth : {a : Type} {m : number} -> bounded-num m -> vec a m -> a
nth zero (x ∷ xs) = x
nth (succ n) (x ∷ xs) = nth n xs

-- No such thing as "index out of bounds" at runtime!
-- This is OK:

good = nth (succ zero) ("foo" ∷ "bar" ∷ [])

-- This is a type error at compile time:

{-
bad : number
bad = nth (succ zero) ("foo" ∷ [])
-}

-- So is this, even though it might be OK sometimes (for n > 0)

{-
first : {a : Type} {n : number} -> vec a n -> a
first xs = nth zero xs
-}


-- This is OK:
maybe-first : {n : number} {a : Type} -> vec a n -> option a
maybe-first {zero} xs = NONE
maybe-first {suc n} xs = SOME (nth zero xs)










-- Converts m into a bounded-num n (if possible)
-- Also known as testing if m < n
_<?_ : (m n : number) -> option (bounded-num n)
zero <? zero = NONE
zero <? suc n = SOME zero
suc n <? zero = NONE
suc n <? suc n' with n <? n'
suc n <? suc n' | NONE = NONE
suc n <? suc n' | SOME x = SOME (succ x)

nth' : {a : Type} (m : number) {n : number} -> vec a n -> option a
nth' m {n} xs with m <? n
nth' m xs | NONE = NONE
nth' m xs | SOME x = SOME (nth x xs)













{-======================================================================================-}

{- An interpreter for Nano-ML in Agda -}

data type : Set where
 Bool : type
 Int : type

{- In SML, we would write something like:

datatype expr =
   Zero
 | Succ of expr
 | If of expr * expr * expr
 | True | False
 | Plus of expr * expr
 | Eq of expr * expr
-}

data expr : type -> Set where
 zero : expr Int
 succ : (n : expr Int) -> expr Int
 if_then_else_ : {t : type} (cond : expr Bool) (t1 : expr t) (t2 : expr t) -> expr t
 true : expr Bool
 false : expr Bool
 _⊕_ : (n : expr Int) (m : expr Int) -> expr Int
 _==_ : {t : type} (t1 : expr t) (t2 : expr t) -> expr Bool 

example4 : expr Int
example4 = if ((zero ⊕ succ zero) == (succ zero)) then zero else (succ zero)

-- This is a type error:
--example5 : expr int
--example5 = if zero then true else false

-- We can *only* represent well-typed expressions!
-- We can't even represent ill-typed expressions!

{- In SML, this would be something like:
datatype value = Zero | Succ of value | True | False
-}
data value : type -> Set where
 zero : value Int
 succ : value Int -> value Int
 true : value Bool
 false : value Bool

_+v_ : value Int -> value Int -> value Int
zero +v m = m
succ y +v m = succ (y +v m)

_=v_ : {t : type} -> value t -> value t -> value Bool
zero =v zero = true
zero =v succ y = false
succ y =v zero = false
succ y =v succ y' = y =v y'
true =v true = true
true =v false = false
false =v true = false
false =v false = true
-- Notice that the ill-typed cases are ruled out!

eval : {t : type} -> expr t -> value t
eval zero = zero
eval (succ n) = succ (eval n)
eval (if cond then t1 else t2) with eval cond
eval (if cond then t1 else t2) | true = eval t1
eval (if cond then t1 else t2) | false = eval t2
eval true = true
eval false = false
eval (n ⊕ m) = eval n +v eval m
eval (t1 == t2) = eval t1 =v eval t2
-- Again the ill-typed cases are ruled out!


example6 : value Int
example6 = eval example4
-- C-c C-n will let you evaluate a term
-- it will show us that example6 is zero, as expected

















{-===============================================================-}
{- Unit tests and proofs -}





-- x ≡' y is inhabited if x and y are actually the same, and uninhabited otherwise
data _≡'_ {a : Type} : a -> a -> Set where
 refl : {x : a} -> x ≡' x
-- refl is short for "reflexivity"

eqtest1 : 0 ≡' 0
eqtest1 = refl

eqtest2 : 0 ≡' 1
eqtest2 = {!!}


test1 : (eval example4) ≡' zero
test1 = refl
-- The type simplified!

bad-test : (eval example4) ≡' (succ zero)
bad-test = {!!}

-- These serve as unit tests!


eqtest3 : (x : number) -> (y : number) -> x + y ≡ y + x
eqtest3 x y = {!!}
-- refl isn't smart enough to see that x + y = y + x! We have to *prove* it to Agda







{-======================================================================-}
{- We can even use Agda as a proof assistant!
   Let's prove our standard example: rev xs = rev-tl xs []
-}

-- Append two lists
_⋆_ : {a : Type} -> list a -> list a -> list a
[] ⋆ ys = ys
(x ∷ xs) ⋆ ys = x ∷ (xs ⋆ ys)

rev : {a : Type} -> list a -> list a
rev [] = []
rev (x ∷ xs) = (rev xs) ⋆ (x ∷ [])

rev-tl : {a : Type} -> list a -> list a -> list a
rev-tl [] acc = acc
rev-tl (x ∷ xs) acc = rev-tl xs (x ∷ acc)


{-
Writing (x : A) -> B x is like saying "For any x : A, it is true that B x holds"!
-}
⋆-associativity : {a : Type} (xs : list a) (ys : list a) (zs : list a)
                  -> xs ⋆ (ys ⋆ zs) ≡ (xs ⋆ ys) ⋆ zs
⋆-associativity xs ys zs = {!!}


lemma1 : {a : Type} (xs : list a) (acc : list a) -> (rev-tl xs acc) ≡ ((rev xs) ⋆ acc)
lemma1 [] acc =
  begin
   rev-tl [] acc
                  ≡⟨ program ⟩
   acc
                  ≡⟨ program ⟩
   [] ⋆ acc       
                  ≡⟨ program ⟩
   (rev []) ⋆ acc
  ∎
lemma1 (x ∷ xs) acc =
  begin
   rev-tl (x ∷ xs) acc
                          ≡⟨ program ⟩
   rev-tl xs (x ∷ acc)
                          ≡⟨ lemma1 xs (x ∷ acc) ⟩ -- Induction is just recursion!
   (rev xs) ⋆ (x ∷ acc)
                          ≡⟨ program ⟩
   (rev xs) ⋆ ((x ∷ []) ⋆ acc)
                          ≡⟨ ⋆-associativity (rev xs) (x ∷ []) acc ⟩
   ((rev xs) ⋆ (x ∷ [])) ⋆ acc
                          ≡⟨ program ⟩
   (rev (x ∷ xs)) ⋆ acc
  ∎

-- What happens if we skip a step?








-- Actually all the "by program" steps are automatic
lemma1' : {a' : Set} (xs : list a') (acc : list a') -> (rev-tl xs acc) ≡ ((rev xs) ⋆ acc)
lemma1' [] acc = refl
lemma1' (x ∷ xs) acc =
  begin
   rev-tl xs (x ∷ acc)
                          ≡⟨ lemma1' xs (x ∷ acc) ⟩
   (rev xs) ⋆ (x ∷ acc)
                          ≡⟨ ⋆-associativity (rev xs) (x ∷ []) acc ⟩
   ((rev xs) ⋆ (x ∷ [])) ⋆ acc
  ∎


{- Let's prove the main theorem using the lemma -}

⋆-unit-right : {a : Type} (xs : list a) -> (xs ⋆ []) ≡ xs
⋆-unit-right xs = {!!}

theorem1' : {a' : Set} (xs : list a') -> rev-tl xs [] ≡ rev xs
theorem1' xs =
  begin
   rev-tl xs []
                  ≡⟨ lemma1' xs [] ⟩
   (rev xs) ⋆ []
                  ≡⟨ ⋆-unit-right (rev xs) ⟩
   rev xs
  ∎











-- Termination checking is even more important when proving theorems:
-- Let's try to prove a false theorem:
theorem1'' : {a' : Set} (xs : list a') -> rev xs ≡ xs
theorem1'' [] =
  begin
    rev []      ≡⟨ program ⟩
    []
  ∎
theorem1'' (x ∷ xs) =
  begin
    rev (x ∷ xs)     ≡⟨ theorem1'' (x ∷ xs) ⟩ -- By "induction"
    (x ∷ xs)
  ∎

{-======================================================================-}
























{-
 Other things we can do with dependent types:
   * Write a serialization library (convert values of arbitary datatypes into strings to save
       to a file)
   * Enforce datastructure invariants with the typechecker
   * Check if database (SQL) queries are well-formed during typechecking (before you ever run them
-}







{-======================================================================-}

-- An alternate way to implement transpose
{-repeat : ∀ {a' n} -> a' -> vec a' n
repeat {n = 0} x = []
repeat {n = suc m} x = x ∷ repeat x

addColumn : ∀ {a' n m} -> vec a' n -> matrix a' n m -> matrix a' n (1 + m)
addColumn xs yss = zipWith (_∷_) xs yss

transpose' : ∀ {a' n m} -> matrix a' n m -> matrix a' m n
transpose' [] = repeat []
transpose' (xs ∷ xss) = addColumn xs (transpose' xss) -}

{- Dot product:
 [1,2,3,4] • [5,6,7,8] = 1*5 + 2*6 + 3*7 + 4*8
-}
{- _•_ : ∀ {n} -> vec number n -> vec number n -> number
[] • [] = 0
(x ∷ xs) • (y ∷ ys) = x * y + xs • ys -}