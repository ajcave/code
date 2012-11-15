module intro302 where
open import helper
{-
Helpful references:
http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.EmacsModeKeyCombinations
http://wiki.portal.chalmers.se/agda/agda.php?n=Docs.UnicodeInput
-}

{-
And unicode! Type \:: to get ∷
Place the cursor over ∷ and hit C-u C-x = to find out how to write it

datatype 'a list = Nil | Cons of 'a * 'a list -}
data list a' : Set where
 [] : list a'
 _∷_ : a' -> list a' -> list a'

infixr 9 _∷_ -- cons should be right associative with some arbitrary precedence

example1 : list number
example1 = 1 ∷ 2 ∷ 3 ∷ []

vector-add : list number -> list number -> list number
vector-add [] [] = []
vector-add (x ∷ xs) (y ∷ ys) = (x + y) ∷ vector-add xs ys
vector-add [] (y ∷ y') = {!!}
vector-add (x ∷ xs) [] = {!!}

-- The {}s mean that A, B and C are implicit arguments
-- Place the cursor in the hole and use C-c C-, to see the goal type and context
-- Use C-c C-c to do a case split
-- Type in the hole and use C-c C-r to attempt to refine
zipWith : {a' b' c' : Set} -> (a' -> b' -> c') -> list a' -> list b' -> list c'
zipWith f xs ys = {!!}

data vec a' : number -> Set where
 [] : vec a' 0
 _∷_ : {n : number} -> a' -> vec a' n -> vec a' (1 + n)

example2 : vec number 2
example2 = zero ∷ zero ∷ []


{- This is a type error: 
example3 : vec nat (succ (succ zero))
example3 = zero ∷ zero ∷ zero ∷ []
-}

hd : {a' : Set} {n : number} -> vec a' (1 + n) -> a'
hd (x ∷ xs) = x

tl : {a' : Set} {n : number} -> vec a' (1 + n) -> vec a' n
tl (x ∷ xs) = xs

-- Now it discards the impossible cases for us!
zipWith2 : {a' b' c' : Set} -> {n : number} -> (a' -> b' -> c') -> vec a' n -> vec b' n -> vec c' n
zipWith2 f [] [] = []
zipWith2 f (x ∷ xs) (x' ∷ xs') = {!!}

-- Can find solution automatically!

zipWith4 : {a' b' c' : Set} -> (n : number) -> (a' -> b' -> c') -> vec a' n -> vec b' n -> vec c' n
zipWith4 zero f [] ys = []
zipWith4 (suc n) f (x ∷ xs) ys = {!!}


_•_ : ∀ {n} -> vec number n -> vec number n -> number
[] • [] = 0
(x ∷ xs) • (y ∷ ys) = x * y + xs • ys

map : ∀ {a' b' n} -> (a' -> b') -> vec a' n -> vec b' n
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs


{-======================================================================================-}

data type : Set where
 bool : type
 natural : type

data expr : type -> Set where
 zero : expr natural
 succ : (n : expr natural) -> expr natural 
 if_then_else_ : {t : type} (cond : expr bool) (t1 : expr t) (t2 : expr t) -> expr t
 true : expr bool
 false : expr bool
 _⊕_ : (n : expr natural) (m : expr natural) -> expr natural
 _==_ : {t : type} (t1 : expr t) (t2 : expr t) -> expr bool 

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

_=v_ : ∀ {t : type} -> value t -> value t -> value bool
t =v u = {!!}
-- Notice that the ill-typed cases are ruled out!

eval : {t : type} -> expr t -> value t
eval x = {!!}
-- Again the ill-typed cases are ruled out!


example6 : value natural
example6 = eval example4
-- C-c C-n will let you evaluate a term to *n*ormal form
-- it will show us that example6 is zero, as expected

{-======================================================================-}

-- We can put computations in types, and they simplify
-- We'll see that this lets you prove properties of your functions!
_++_ : {a' : Set} {n m : number} -> vec a' n -> vec a' m -> vec a' (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- But it can get hairy
rev-acc : {a' : Set} {n m : number} -> vec a' n -> vec a' m -> vec a' (n + m)
rev-acc [] ys = ys
rev-acc (x ∷ xs) ys = {!!} --rev-acc xs (x ∷ ys)


-- Append two lists
_⋆_ : {a' : Set} -> list a' -> list a' -> list a'
[] ⋆ ys = ys
(x ∷ xs) ⋆ ys = x ∷ (xs ⋆ ys)

rev : {a' : Set} -> list a' -> list a'
rev [] = []
rev (x ∷ xs) = (rev xs) ⋆ (x ∷ [])

rev-tl : {a' : Set} -> list a' -> list a' -> list a'
rev-tl [] acc = acc
rev-tl (x ∷ xs) acc = rev-tl xs (x ∷ acc)

congruence : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
congruence f refl = refl

⋆-associativity : ∀ {a' : Set} (xs : list a') (ys : list a') (zs : list a') -> xs ⋆ (ys ⋆ zs) ≡ (xs ⋆ ys) ⋆ zs
⋆-associativity [] ys zs = reflexivity
⋆-associativity (x ∷ xs) ys zs = congruence (_∷_ x) (⋆-associativity xs ys zs)

⋆-unit-right : ∀ {a' : Set} (xs : list a') -> (xs ⋆ []) ≡ xs
⋆-unit-right [] = reflexivity
⋆-unit-right (x ∷ xs) = congruence (_∷_ x) (⋆-unit-right xs)

-- Induction is just recursion!
lemma1 : {a' : Set} (xs : list a') (acc : list a') -> (rev-tl xs acc) ≡ ((rev xs) ⋆ acc)
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
                          ≡⟨ lemma1 xs (x ∷ acc) ⟩
   (rev xs) ⋆ (x ∷ acc)
                          ≡⟨ program ⟩
   (rev xs) ⋆ ((x ∷ []) ⋆ acc)
                          ≡⟨ ⋆-associativity (rev xs) (x ∷ []) acc ⟩
   ((rev xs) ⋆ (x ∷ [])) ⋆ acc
                          ≡⟨ program ⟩
   (rev (x ∷ xs)) ⋆ acc
  ∎

-- Actually all the "by program" steps are automatic
lemma1' : {a' : Set} (xs : list a') (acc : list a') -> (rev-tl xs acc) ≡ ((rev xs) ⋆ acc)
lemma1' [] acc = reflexivity
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

-- TODO: Be very careful with the syntax you use. Be uniform
-- TODO: Show them termination checking and coverage checking (failure)

matrix : ∀ a' -> number -> number -> Set
matrix a' m n = vec (vec a' n) m

mult-transpose : ∀ {n m p} -> matrix number m n -> matrix number p n -> matrix number m p
mult-transpose [] ys = []
mult-transpose (xs ∷ xss) yss = (map (λ ys -> xs • ys) yss) ∷ (mult-transpose xss yss)

repeat : ∀ {a' n} -> a' -> vec a' n
repeat {n = 0} x = []
repeat {n = suc m} x = x ∷ repeat x

addColumn : ∀ {a' n m} -> vec a' n -> matrix a' n m -> matrix a' n (1 + m)
addColumn xs yss = zipWith2 (_∷_) xs yss

transpose : ∀ {a' n m} -> matrix a' n m -> matrix a' m n
transpose [] = repeat []
transpose (xs ∷ xss) = addColumn xs (transpose xss)

mult : ∀ {n m p} -> matrix number m n -> matrix number n p -> matrix number m p
mult xss yss = mult-transpose xss (transpose yss)