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
data list A : Set where
 [] : list A
 _∷_ : A -> list A -> list A
-- Could simply write _∷_ : A -> list A -> list A

infixr 9 _∷_ -- cons should be right associative with some arbitrary precedence

example1 : list number
example1 = 1 ∷ 2 ∷ 3 ∷ []

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

-- Now it discards the impossible cases for us!
zipWith2 : {a' b' c' : Set} -> {n : number} -> (a' -> b' -> c') -> vec a' n -> vec b' n -> vec c' n
zipWith2 f [] [] = []
zipWith2 f (x ∷ xs) (x' ∷ xs') = f x x' ∷ zipWith2 f xs xs'

zipWith4 : {a' b' c' : Set} -> (n : number) -> (a' -> b' -> c') -> vec a' n -> vec b' n -> vec c' n
zipWith4 zero f [] ys = {!!}
zipWith4 (suc n) f (x ∷ xs) ys = {!!}

-- Can find solution automatically!

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
zero =v zero = true
zero =v succ y = false
succ y =v zero = false
succ y =v succ y' = y =v y'
true =v true = {!!}
true =v false = {!!}
false =v true = {!!}
false =v false = {!!}
-- Notice that the ill-typed cases are ruled out!

eval : {t : type} -> expr t -> value t
eval x = {!!}
-- Again the ill-typed cases are ruled out!


example6 : value natural
example6 = eval example4
-- C-c C-n will let you evaluate a term to *n*ormal form
-- it will show us that example6 is zero, as expected

{-======================================================================-}

-- We can put computations in types (unlike present-day Beluga), and they simplify
-- We'll see that this lets you prove properties of your functions!
_++_ : {a' : Set} {n m : number} -> vec a' n -> vec a' m -> vec a' (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- But it can get hairy
rev-acc : {a' : Set} {n m : number} -> vec a' n -> vec a' m -> vec a' (n + m)
rev-acc [] ys = ys
rev-acc (x ∷ xs) ys = {!!} --rev-acc xs (x ∷ ys)

congruence : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
congruence f refl = refl

-- Append two lists
_⋆_ : {a' : Set} -> list a' -> list a' -> list a'
[] ⋆ ys = ys
(x ∷ xs) ⋆ ys = x ∷ (xs ⋆ ys)

⋆-associativity : ∀ {a' : Set} (xs : list a') (ys : list a') (zs : list a') -> xs ⋆ (ys ⋆ zs) ≡ (xs ⋆ ys) ⋆ zs
⋆-associativity [] ys zs = reflexivity
⋆-associativity (x ∷ xs) ys zs = congruence (_∷_ x) (⋆-associativity xs ys zs)

⋆-unit-right : ∀ {a' : Set} (xs : list a') -> (xs ⋆ []) ≡ xs
⋆-unit-right [] = reflexivity
⋆-unit-right (x ∷ xs) = congruence (_∷_ x) (⋆-unit-right xs)

rev : {a' : Set} -> list a' -> list a'
rev [] = []
rev (x ∷ xs) = (rev xs) ⋆ (x ∷ [])

rev-tl : {a' : Set} -> list a' -> list a' -> list a'
rev-tl [] acc = acc
rev-tl (x ∷ xs) acc = rev-tl xs (x ∷ acc)

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