{-# OPTIONS --type-in-type #-}
module intro302 where
open import helper
{-
Helpful references:
http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.EmacsModeKeyCombinations
http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.UnicodeInput
-}














{-
In SML, this would be:
 datatype 'a list = Nil | Cons of 'a * 'a list
-}

data list a : Set where
 [] : list a
 _∷_ : a -> list a -> list a
-- Unicode! Type \:: to get ∷
-- Place the cursor over ∷ and hit C-u C-x = to find out how to write it

infixr 9 _∷_ -- cons should be right associative with some arbitrary precedence (9)

example1 : list number
example1 = 1 ∷ 2 ∷ 3 ∷ []
-- In SML notation: [1,2,3]





{- In SML, this would be:

incList : int list -> int list
   
fun incList [] = []
  | incList (x::xs) = (x + 1)::(incList xs)  

-}

incList : list number -> list number
incList [] = []
incList (x ∷ xs) = (x + 1) ∷ (incList xs)






{-
 In SML, this would be:

map : ('a -> 'b) -> 'a list -> 'b list

fun map f [] = []
  | map f (x::xs) = (f x)::(map f xs)

-}

map : {a : Type} {b : Type} -> (a -> b) -> list a -> list b
map f [] = []
map f (x ∷ xs) = (f x) ∷ map f xs










{- Place the cursor in the hole and use C-c C-, to see the goal type and context
   Use C-c C-c to do a case split
   Type in the hole and use C-c C-r to attempt to refine
zip [1,2,3] [4,5,6] = [(1,4), (2,5), (3,6)]
-}

zip : {a b : Type} -> list a -> list b -> list (a * b)
zip xs ys = {!!}





















-- Solution: We _index_ lists by their length
data vec a : number -> Set where
 [] : vec a 0
 _∷_ : {n : number} -> a -> vec a n -> vec a (1 + n)

example2 : vec number 2
example2 = 7 ∷ 10 ∷ []

-- This is a type error: 
--example3 : vec number 3
--example3 = 7 ∷ 10 ∷ []




-- Now it discards the impossible cases for us!
-- Notice the extra information we get to help us find the right solution
zip' : {a b : Set} -> (n : number) -> vec a n -> vec b n -> vec (a * b) n
zip' n xs ys = {!!}


exampleZ1 = zip' 3 (1 ∷ 2 ∷ 3 ∷ []) ("foo" ∷ "bar" ∷ "baz" ∷ [])

--exampleZ2 = zip' 3 (1 ∷ 2 ∷ 3 ∷ []) ("foo" ∷ "bar" ∷ [])




-- We make n an "implicit" argument by putting it in {}s
zip'' : {a b : Set} -> {n : number} -> vec a n -> vec b n -> vec (a * b) n
zip'' xs ys = {!!}


-- Now we leave the 3 off, and Agda figures it out for us
exampleZ'' = zip'' (1 ∷ 2 ∷ 3 ∷ []) ("foo" ∷ "bar" ∷ "baz" ∷ [])




hd : {a : Type} {n : number} -> vec a (1 + n) -> a
hd (x ∷ xs) = x

tl : {a : Type} {n : number} -> vec a (1 + n) -> vec a n
tl (x ∷ xs) = xs











-- zipWith f [1,2,3] [4,5,6] = [(f 1 4), (f 2 5), (f 3 6)]
-- e.g. vector-add is just zipWith _+_
-- C-c C-a
zipWith : {a b c : Set} -> {n : number}
          -> (a -> b -> c) -> vec a n -> vec b n -> vec c n
zipWith f xs ys = {!!}




-- This is a type error!
{-
zipWith-bad : {a' b' c' : Set} -> {n : number}
  -> (a' -> b' -> c') -> vec a' n -> vec b' n -> vec c' n
zipWith-bad f [] [] = []
zipWith-bad f (x ∷ xs) (y ∷ ys) = zipWith-bad f xs ys

-}



-- Agda performs termination checking, and this fails!
zipWith-bad2 : {a' b' c' : Set} -> {n : number}
  -> (a' -> b' -> c') -> vec a' n -> vec b' n -> vec c' n
zipWith-bad2 f [] [] = []
zipWith-bad2 f (x ∷ xs) (y ∷ ys) = zipWith-bad2 f (x ∷ xs) (y ∷ ys)










-- It is not perfect:
{-
 inc takes a list and
 adds 0 to the first element
 adds 1 to the second
 adds 2 to the third
 ...
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
-- It communicates *why* something terminates to your coworkers










{- Dot product:
 [1,2,3,4] • [5,6,7,8] = 1*5 + 2*6 + 3*7 + 4*8
-}
{-_•_ : ∀ {n} -> vec number n -> vec number n -> number
[] • [] = 0
(x ∷ xs) • (y ∷ ys) = x * y + xs • ys -}








-- vmap preserves the length!
vmap : {a' b' : Set} {n : number}
   -> (a' -> b') -> vec a' n -> vec b' n
vmap f [] = []
vmap f (x ∷ xs) = f x ∷ vmap f xs











matrix : (a : Set) -> number -> number -> Set
matrix a m n = vec (vec a n) m

{- Transposing:    [[1,2],
                    [3,4],
                    [5,6]]
gives:
                   [[1,3,5],
                    [2,4,6]]      -}

transpose : {m : number} {a : Set} {n : number}
  -> matrix a n m -> matrix a m n
transpose {m = zero}   xss = []
transpose {m = suc m'} xss = (vmap hd xss) ∷ (transpose (vmap tl xss))
-- Here we know for sure that hd is safe (and the typechecker can check it!)

-- We can't accidentally forget the base case:
--transpose-bad :  ∀ {m} {a'} {n} -> matrix a' n m -> matrix a' m n
--transpose-bad xss = (vmap hd xss) ∷ (transpose (vmap tl xss))














-- We can put computations in types, and they simplify
-- Vector append:
_++_ : {a' : Set} {n m : number} -> vec a' n -> vec a' m -> vec a' (n + m)
[] ++ ys = ys
(y ∷ y') ++ ys = y ∷ y' ++ ys

-- We'll see that this lets you prove properties of your functions!













-- But it can get hairy
rev-acc : {a' : Set} {n m : number} -> vec a' n -> vec a' m -> vec a' (n + m)
rev-acc [] acc = acc
rev-acc (x ∷ xs) acc = {!!} --rev-acc xs (x ∷ acc)

-- We'd have to *prove* to Agda that 1 + (n + m) = n + (1 + m)
-- Other systems will solve this automatically (but have other downsides)












{- bounded n is the type of numbers strictly less than n
   i.e. zero is a "bounded-num 1" and a "bounded-num 2" and a "bounded-num 3", ...
        succ zero is a "bounded-num 2" and a "bounded-num 3", but *not* a "bounded-num 1"
-}
data bounded-num : number -> Set where
 zero : {n : number} -> bounded-num (1 + n)
 succ : {n : number} -> bounded-num n -> bounded-num (1 + n)

{- Given a number i < n and a vector xs of length n, looks up
   the ith element of xs
-}
lookup : {a' : Set} {n : number} -> bounded-num n -> vec a' n -> a'
lookup zero (x ∷ xs) = x
lookup (succ i) (x ∷ xs) = lookup i xs

-- No such thing as "index out of bounds"!
-- This is OK:

good : number
good = lookup (succ zero) (1 ∷ 2 ∷ [])

-- This is a type error at compile time:

{-
bad : number
bad = lookup (succ zero) (1 ∷ [])
-}

-- So is this, even though it might be OK sometimes (for n > 0)

{-
first : {a' : Set} {n : number} -> vec a' n -> a'
first xs = lookup zero xs
-}


-- This is OK:
maybe-first : {n : number} {a' : Set} -> vec a' n -> option a'
maybe-first {zero} xs = NONE
maybe-first {suc n} xs = SOME (lookup zero xs)










-- Converts m into a bounded-num n (if possible)
-- Also known as testing if m < n
_<?_ : (m n : number) -> option (bounded-num n)
zero <? zero = NONE
zero <? suc n = SOME zero
suc n <? zero = NONE
suc n <? suc n' with n <? n'
suc n <? suc n' | NONE = NONE
suc n <? suc n' | SOME x = SOME (succ x)

lookup' : {a' : Set} (m : number) {n : number} -> vec a' n -> option a'
lookup' m {n} xs with m <? n
lookup' m xs | NONE = NONE
lookup' m xs | SOME x = SOME (lookup x xs)













{-======================================================================================-}

data type : Set where
 bool : type
 int : type

data expr : type -> Set where
 zero : expr int
 succ : (n : expr int) -> expr int
 if_then_else_ : {t : type} (cond : expr bool) (t1 : expr t) (t2 : expr t) -> expr t
 true : expr bool
 false : expr bool
 _⊕_ : (n : expr int) (m : expr int) -> expr int
 _==_ : {t : type} (t1 : expr t) (t2 : expr t) -> expr bool 

example4 : expr int
example4 = if ((zero ⊕ succ zero) == (succ zero)) then zero else (succ zero)

-- This is a type error:
--example5 : expr natural
--example5 = if zero then true else false


{- In SML, this would be something like:
datatype value = Zero | Succ of value | True | False
-}
data value : type -> Set where
 zero : value int
 succ : value int -> value int
 true : value bool
 false : value bool

_+v_ : value int -> value int -> value int
zero +v m = m
succ y +v m = succ (y +v m)

_=v_ : {t : type} -> value t -> value t -> value bool
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


example6 : value int
example6 = eval example4
-- C-c C-n will let you evaluate a term
-- it will show us that example6 is zero, as expected














-- x ≡' y is inhabited if x and y are actually the same, and uninhabited otherwise
data _≡'_ {a' : Set} : a' -> a' -> Set where
 refl : {x : a'} -> x ≡' x
-- refl is short for "reflexivity"

test1 : (eval example4) ≡' zero
test1 = refl
-- The type simplified!

bad-test : (eval example4) ≡' (succ zero)
bad-test = {!!}

-- These serve as unit tests!










{-======================================================================-}

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



⋆-associativity : ∀ {a : Type} (xs : list a) (ys : list a) (zs : list a)
                  -> xs ⋆ (ys ⋆ zs) ≡ (xs ⋆ ys) ⋆ zs
⋆-associativity xs ys zs = {!!}

⋆-unit-right : ∀ {a : Type} (xs : list a) -> (xs ⋆ []) ≡ xs
⋆-unit-right xs = {!!}

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
mult-transpose : ∀ {n m p} -> matrix number m n -> matrix number p n -> matrix number m p
mult-transpose [] ys = []
mult-transpose (xs ∷ xss) yss = (vmap (λ ys -> xs • ys) yss) ∷ (mult-transpose xss yss)

mult : ∀ {n m p} -> matrix number m n -> matrix number n p -> matrix number m p
mult xss yss = mult-transpose xss (transpose yss)
-}






{-
 Other things we can do with dependent types:
   * Check if database (SQL) queries are well-formed during typechecking (before you ever run them)
   * Write a serialization library (convert values of arbitary datatypes into strings to save
       to a file)
   * Enforce datastructure invariants with the typechecker (e.g. heap invariant from HW1)
 (See string.agda for a universe example)
-}










{-======================================================================-}

-- An alternate way to implement transpose
repeat : ∀ {a' n} -> a' -> vec a' n
repeat {n = 0} x = []
repeat {n = suc m} x = x ∷ repeat x

addColumn : ∀ {a' n m} -> vec a' n -> matrix a' n m -> matrix a' n (1 + m)
addColumn xs yss = zipWith (_∷_) xs yss

transpose' : ∀ {a' n m} -> matrix a' n m -> matrix a' m n
transpose' [] = repeat []
transpose' (xs ∷ xss) = addColumn xs (transpose' xss)
