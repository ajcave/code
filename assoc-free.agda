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
     .ok : (Σ (λ list -> fun ≡ _++_ list)) -- Do we still get case?

ε : ∀ {A} → Seq A
ε = seq id ([] , refl)

_+_ : ∀ {A} → Seq A → Seq A → Seq A
(seq f (as , f✓)) + (seq g (bs , g✓)) = seq (f ∘ g) (f bs , ≡-subst (λ x → (x ∘ g) ≡ _++_ (x bs)) (≡-sym f✓) (≡-subst (λ x → (_++_ as ∘ x) ≡ _++_ (as ++ bs)) (≡-sym g✓) (ext (λ x → ++-assoc as bs x))))

+-assoc : ∀ {A} (as bs cs : Seq A) →
   ((as + bs) + cs) ≡ (as + (bs + cs))
+-assoc as bs cs = refl

+-id : ∀ {A} (as bs : Seq A) -> ((as + ε) + bs) ≡ (as + bs)
+-id as bs = refl

+-id2 : ∀ {A} (as : Seq A) -> as ≡ (as + ε)
+-id2 as = refl

-- Now can we reflect products? 

_◁_ : ∀ {A} -> A -> Seq A -> Seq A
a ◁ seq fun (as , as✓) = seq (λ x → a ∷ (fun x)) ((a ∷ as) , (ext (λ x → ≡-subst (λ y → (a ∷ y x) ≡ (a ∷ (as ++ x))) (≡-sym as✓) refl)))

data Case {A : Set} : Seq A → Set where
   [] : Case ε
   _∷_ : ∀ a as → Case (a ◁ as)

case : ∀ {A} (as : Seq A) → Case as
case (seq f (as , as✓)) with f [] -- By inspection?
case (seq f (as , as✓)) | [] = {!!} -- Need fact that [] = f [] = as ++ [] -> as = []
case (seq f (as , as✓)) | x ∷ xs = {!!} -- Need fact that x ∷ xs = f [] = as ++ [] -> as = x ∷ xs

ids : ∀ {A} → Seq A → Seq A
ids as        with case as
ids .(a ◁ as) | a ∷ as = a ◁ ids as -- I think Jeffrey's worked because the list wasn't hidden in a sigma?
ids .ε        | []     = ε