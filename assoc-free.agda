module assoc-free where

data List (A : Set) : Set where
 [] : List A
 _∷_ : (x : A) -> (xs : List A) -> List A 

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

≡-subst : ∀ {A : Set} (P : A -> Set) {a b : A} -> a ≡ b -> P a -> P b
≡-subst P refl x = x

cong : ∀ {A : Set} {B : Set}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

≡-sym : ∀ {A : Set} {a b : A} -> a ≡ b -> b ≡ a
≡-sym refl = refl

_∘_ : ∀ {A B C} -> (f : B -> C) -> (g : A -> B) -> A -> C
(f ∘ g) x = f (g x)

id : ∀ {A : Set} -> A -> A
id x = x

_++_ : ∀ {A} -> List A -> List A -> List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {A} (xs ys zs : List A) -> (xs ++ (ys ++ zs)) ≡ ((xs ++ ys) ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

postulate
 ext : ∀ {A B} {f g : A -> B} -> (∀ x -> f x ≡ g x) -> f ≡ g

record Seq (A : Set) : Set where
   constructor seq
   field
     fun : List A → List A -- What if we use .List A -> List A? By irrelevance/parametricity, it's a _++_ xs...
     .ok : fun ≡ _++_ (fun [])

ε : ∀ {A} → Seq A
ε = seq id refl

_+_ : ∀ {A} → Seq A → Seq A → Seq A
(seq f f✓) + (seq g g✓) = seq (f ∘ g) (f∘g✓ (f []) (g []) f f✓ g g✓)
 where assoc : ∀ {A} (m : List A) {n} → (λ x → m ++ (n ++ x)) ≡ _++_ (m ++ n)
       assoc [] = refl
       assoc (x ∷ xs) = cong (_∘_ (_∷_ x)) (assoc xs)
       .f∘g✓ : ∀ {A} m n (f : List A -> List A) (f✓ : f ≡ _++_ m) g (g✓ : g ≡ _++_ n) → (f ∘ g) ≡ _++_ (f n)
       f∘g✓ {A} m n ._ refl ._ refl = assoc m

+-assoc : ∀ {A} (as bs cs : Seq A) →
   ((as + bs) + cs) ≡ (as + (bs + cs))
+-assoc as bs cs = refl

+-id : ∀ {A} (as bs : Seq A) -> ((as + ε) + bs) ≡ (as + bs)
+-id as bs = refl

+-id2 : ∀ {A} (as : Seq A) -> as ≡ (as + ε)
+-id2 as = refl

-- Now can we reflect products? 

_◁_ : ∀ {A} -> A -> Seq A -> Seq A
a ◁ seq fun as✓ = seq (λ x → a ∷ (fun x)) (cong (_∘_ (_∷_ a)) as✓)

data Case {A : Set} : Seq A → Set where
   [] : Case ε
   _∷_ : ∀ a as → Case (a ◁ as)

++[] : ∀ {A} (l : List A) -> l ≡ (l ++ [])
++[] [] = refl
++[] (x ∷ xs) = cong (_∷_ x) (++[] xs)

lem : ∀ {A} (l : List A) -> Case (seq (_++_ l) (cong _++_ (++[] l)))
lem [] = []
lem (x ∷ xs) = x ∷ seq (_++_ xs) (cong _++_ (++[] xs))

postulate
 rel : ∀ {A} {x y : A} -> .(x ≡ y) -> x ≡ y

case : ∀ {A} (as : Seq A) → Case as
case (seq f f✓) with lem (f [])
... | w rewrite (rel f✓) = w

-- ..So just work with f []?
ids : ∀ {A} → Seq A → Seq A
ids as        with case as
ids .(a ◁ as) | a ∷ as = a ◁ ids as -- I think Jeffrey's worked because the list wasn't hidden in a sigma?
ids .ε        | []     = ε

-- Can we change my solver before to use Agda's function space for it's semantics,
-- instead of a semantic domain of normal terms?