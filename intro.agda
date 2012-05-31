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
 succ : (n : nat) -> nat

-- We can have fancy ("mixfix") operators
_+_ : nat -> nat -> nat
zero + n = n
succ n + m = succ (n + m)

{-
And unicode! Type \:: to get ∷
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
-- This time try C-c C-a in the holes ("a" for "auto")
-- The types are so restrictive that it can find the solution!
zipWith3 : ∀ {A B C n} -> (A -> B -> C) -> vec A n -> vec B n -> vec C n
zipWith3 f [] [] = {!!}
zipWith3 f (x ∷ xs) (x' ∷ xs') = {!!}

{-======================================================================================-}

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
-- Notice that the ill-typed cases are ruled out!

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
-- Again the ill-typed cases are rules out!

example6 : value natural
example6 = eval example4
-- C-c C-n will let you evaluate a term to *n*ormal form
-- it will show us that example6 is zero, as expected

{-======================================================================-}

-- We can put computations in types, and they simplify
_++_ : ∀ {A n m} -> vec A n -> vec A m -> vec A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

-- But it can get hairy
rev-acc : ∀ {A n m} -> vec A n -> vec A m -> vec A (n + m)
rev-acc [] ys = ys
rev-acc (x ∷ xs) ys = {!!} --rev-acc xs (x ∷ ys)

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

congruence : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
congruence f refl = refl

-- By induction on n
plus-succ-lemma : ∀ n m -> (n + (succ m)) ≡ succ (n + m)
plus-succ-lemma zero m = refl
plus-succ-lemma (succ n) m = congruence succ (plus-succ-lemma n m)

-- Or we can use a fancy rewrite feature
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}
plus-succ-lemma2 : ∀ n m -> (n + (succ m)) ≡ succ (n + m)
plus-succ-lemma2 zero m = refl
plus-succ-lemma2 (succ n) m rewrite plus-succ-lemma2 n m = refl

eq-elim : ∀ {A : Set} (P : A -> Set) {x y : A} -> x ≡ y -> P x -> P y
eq-elim P refl t = t

rev-acc2 : ∀ {A n m} -> vec A n -> vec A m -> vec A (n + m)
rev-acc2 [] ys = ys
rev-acc2 {A} {succ n} {m} (x ∷ xs) ys = eq-elim (vec A) (plus-succ-lemma n m) (rev-acc2 xs (x ∷ ys))

-- What if we had defined + differently...
_+₂_ : nat -> nat -> nat
zero +₂ m = m
succ n +₂ m = n +₂ succ m

rev-acc3 : ∀ {A n m} -> vec A n -> vec A m -> vec A (n +₂ m)
rev-acc3 [] ys = ys
rev-acc3 (x ∷ xs) ys = rev-acc3 xs (x ∷ ys)

-- But now maybe elsewhere we need to know that n +₂ m = n + m...
-- Your choice of definitions matters!

{-
Try proving:

plus-zero-lemma : ∀ n -> (n + zero) ≡ n
plus-equiv-lemma : ∀ n m -> (n +₂ m) ≡ (n + m)
plus-commutative : ∀ n m -> (n + m) ≡ (m + n)

Arithmetic is boring? Try showing that list append is associative.
Showing vector append is associative is nasty to even state, I don't recommend it.
-}

{-===================================================================================-}

data tp : Set where
 base : tp
 _⇒_ : (T S : tp) -> tp

infixr 9 _⇒_

-- Just (backwards) lists
data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) (T : tp) -> ctx

data var : ctx -> tp -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

data exp (Γ : ctx) : tp -> Set where
 v : ∀ {T} (x : var Γ T) -> exp Γ T
 _·_ : ∀ {T S} (M : exp Γ (T ⇒ S)) (N : exp Γ T) -> exp Γ S
 ƛ : ∀ {T S} (M : exp (Γ , T) S) -> exp Γ (T ⇒ S)

example7 : ∀ {T} -> exp ⊡ (T ⇒ T)
example7 = ƛ (v top)

example8 : ∀ {T S} -> exp ⊡ ((T ⇒ S) ⇒ T ⇒ S)
example8 = ƛ (ƛ ((v (pop top)) · (v top)))

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> exp Δ T

weakening-subst : ∀ {Γ T} -> subst Γ (Γ , T)
weakening-subst x = v (pop x)

_,,_ : ∀ {Γ Δ T} -> subst Γ Δ -> exp Δ T -> subst (Γ , T) Δ
(σ ,, M) top = M
(σ ,, M) (pop y) = σ y

_∘_ : ∀ {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘ g) x = f (g x)

[_]b : ∀ {Γ Δ T} -> subst Γ Δ -> exp Γ T -> exp Δ T
[ σ ]b (v x) = σ x
[ σ ]b (M · N) = [ σ ]b M · [ σ ]b N
[ σ ]b (ƛ M) = ƛ ([ ([ weakening-subst ]b ∘ σ) ,, (v top) ]b M) -- :(

renamer : ctx -> ctx -> Set
renamer Γ Δ = ∀ {T} -> var Γ T -> var Δ T

-- Extends a substitution σ to become "σ , x/x" 
extendr : ∀ {Γ Δ T} -> renamer Γ Δ -> renamer (Γ , T) (Δ , T)
extendr σ top = top
extendr σ (pop y) = pop (σ y)

[_]r : ∀ {Γ Δ T} -> renamer Γ Δ -> exp Γ T -> exp Δ T
[ σ ]r (v x) = v (σ x)
[ σ ]r (M · N) = [ σ ]r M · [ σ ]r N
[ σ ]r (ƛ M) = ƛ ([ extendr σ ]r M)

extend : ∀ {Γ Δ T} -> subst Γ Δ -> subst (Γ , T) (Δ , T)
extend σ top = v top
extend σ (pop y) = [ pop ]r (σ y)

[_] : ∀ {Γ Δ T} -> subst Γ Δ -> exp Γ T -> exp Δ T
[ σ ] (v x) = σ x
[ σ ] (M · N) = [ σ ] M · [ σ ] N
[ σ ] (ƛ M) = ƛ ([ extend σ ] M) -- :)

-- Fun exercise (read: "Why Beluga exists")
subst-compose-lemma : ∀ {Γ1 Γ2 Γ3 T} (σ1 : subst Γ2 Γ3) (σ2 : subst Γ1 Γ2) (M : exp Γ1 T) -> ([ σ1 ] ([ σ2 ] M)) ≡ ([ [ σ1 ] ∘ σ2 ] M)
subst-compose-lemma σ1 σ2 M = {!!}

{- Hint: You will probably need
trans : ∀ {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

and "congruence" (above)

And lots of lemmas.

You may also find "rewrite" helpful (but not necessary)
-}

{- Exercise: Add the constructs of "expr" (if_then_else, _==_, _⊕_) to exp and extend [_] accordingly  -}

{- Exercise: Define a type of simply-typed lambda calculus values and write an evaluator like before (fairly easy)
If you want to evaluate under binders, you may need to use mutually recursive datatypes and definitions, e.g.
 
mutual
 data foo : Set where
  constr1 : foo
  constr2 : bar -> foo
 data bar : Set where
  constr3 : bar -> foo -> bar
  constr4 : foo -> bar
-}

{- Exercise: Write an evaluator which passes the termination checker (hard!!) -}

{- Exercise: Prove that insertion sort, defined below, produces sorted lists (defined below) -}
data _⊎_ (A B : Set) : Set where
 inl : A -> A ⊎ B
 inr : B -> A ⊎ B 

postulate
 A : Set
 _≤_ : A -> A -> Set
 reflexive : ∀ {a} -> a ≤ a
 transitive : ∀ {a b c} -> a ≤ b -> b ≤ c -> a ≤ c
 antisym : ∀ {a b} -> a ≤ b -> b ≤ a -> a ≡ b

data compare (x y : A) : Set where
 leq : (x≤y : x ≤ y) -> compare x y
 geq : (y≤x : y ≤ x) -> compare x y

postulate
 _≤?_ : ∀ a b -> compare a b

insert : A -> list A -> list A
insert x [] = x ∷ []
insert x (x' ∷ xs) with x ≤? x'
insert x (x' ∷ xs) | leq x≤x' = x ∷ x' ∷ xs
insert x (x' ∷ xs) | geq x'≤x = x' ∷ insert x xs

insertionSort : list A -> list A
insertionSort [] = []
insertionSort (x ∷ xs) = insert x (insertionSort xs)

-- isBoundedSorted b xs is inhabited if and only if xs is sorted and b is less than or equal to
-- all of its elements
data isBoundedSorted : (b : A) (xs : list A) -> Set where
 [] : ∀ {b} -> isBoundedSorted b []
 _∷_ : ∀ {b x} {xs} (b≤x : b ≤ x) (pxs : isBoundedSorted x xs) -> isBoundedSorted b (x ∷ xs)

insertLemma : ∀ {b} x -> b ≤ x -> ∀ xs -> isBoundedSorted b xs -> isBoundedSorted b (insert x xs)
insertLemma x b≤x [] p = b≤x ∷ []
insertLemma x b≤x (x' ∷ xs) (b≤x' ∷ pxs) with x ≤? x'
insertLemma x b≤x (x' ∷ xs) (b≤x' ∷ pxs) | leq x≤x' = b≤x ∷ x≤x' ∷ pxs
insertLemma x b≤x (x' ∷ xs) (b≤x' ∷ pxs) | geq x'≤x = b≤x' ∷ insertLemma x x'≤x xs pxs

insertLemma2 : ∀ {b} x -> x ≤ b -> ∀ xs -> isBoundedSorted b xs -> isBoundedSorted x (insert x xs)
insertLemma2 x x≤b [] [] = reflexive ∷ []
insertLemma2 x x≤b (x' ∷ xs) (b≤x' ∷ pxs) with x ≤? x'
insertLemma2 x x≤b (x' ∷ xs) (b≤x' ∷ pxs) | leq x≤x' = reflexive ∷ (x≤x' ∷ pxs)
insertLemma2 x x≤b (x' ∷ xs) (b≤x' ∷ pxs) | geq x'≤x with antisym x'≤x (transitive x≤b b≤x')
insertLemma2 x x≤b (.x ∷ xs) (b≤x  ∷ pxs) | geq x≤x | refl = reflexive ∷ (insertLemma2 x x≤x xs pxs)

-- xs is sorted if there is some lower bound b such that isBoundedSorted b xs
data isSorted : (xs : list A) -> Set where
 yep : ∀ b {xs} -> (p : isBoundedSorted b xs) -> isSorted xs

-- Unfortunately with these definitions we need to assume that there is some element of A
-- in order to prove that [] is sorted
-- Exercise: Try to fix this. Hint: Use the type A ⊎ Unit for bounds, not A
postulate
 ⊤ : A

insertionSortSorted : ∀ xs -> isSorted (insertionSort xs)
insertionSortSorted [] = yep ⊤ []
insertionSortSorted (x ∷ xs) with insertionSortSorted xs
insertionSortSorted (x ∷ xs) | yep b p with x ≤? b
insertionSortSorted (x ∷ xs) | yep b p | leq x≤b = yep x (insertLemma2 x x≤b (insertionSort xs) p)
insertionSortSorted (x ∷ xs) | yep b p | geq b≤x = yep b (insertLemma x b≤x (insertionSort xs) p)

{- Exercise: Use the following datatype of "intrinsically sorted lists with lower bound"
   to build an insertion sort function which produces sorted lists simply by construction -}
data sblist : (b : A) -> Set where
 [] : ∀ {b} -> sblist b
 _∷_ : ∀ {x b} (b≤x : b ≤ x) (xs : sblist x) -> sblist b

sinsert-geq : ∀ {b} x -> b ≤ x -> sblist b -> sblist b
sinsert-geq x b≤x [] = []
sinsert-geq x b≤x (_∷_ {x'} b≤x' xs) with x ≤? x'
sinsert-geq x b≤x (b≤x' ∷ xs) | leq x≤x' = b≤x ∷ (x≤x' ∷ xs)
sinsert-geq x b≤x (b≤x' ∷ xs) | geq x'≤x = b≤x' ∷ sinsert-geq x x'≤x xs

min : A -> A -> A
min x y with x ≤? y
min x y | leq x≤y = x
min x y | geq y≤x = y

sinsert : ∀ {b} x -> sblist b -> sblist (min x b)
sinsert {b} x xs with x ≤? b
sinsert x xs | leq x≤b = x≤b ∷ xs
sinsert x xs | geq b≤x = sinsert-geq x b≤x xs

min-list : list A -> A
min-list [] = ⊤
min-list (x ∷ xs) = min x (min-list xs)

insertionSort' : (xs : list A) -> sblist (min-list xs)
insertionSort' [] = []
insertionSort' (x ∷ xs) = sinsert x (insertionSort' xs)
