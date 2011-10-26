module assoc-free where

data List (A : Set) : Set where
 [] : List A
 _∷_ : (x : A) -> (xs : List A) -> List A 

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

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
     list : List A
     fun : List A → List A
     .ok : fun ≡ _++_ list

ε : ∀ {A} → Seq A
ε = seq [] id refl

_+_ : ∀ {A} → Seq A → Seq A → Seq A
(seq as f f✓) + (seq bs g g✓) = seq (f bs) (f ∘ g) (≡-subst (λ x → (x ∘ g) ≡ _++_ (x bs)) (≡-sym f✓) (≡-subst (λ x → (_++_ as ∘ x) ≡ _++_ (as ++ bs)) (≡-sym g✓) (ext (λ x → ++-assoc as bs x))))

+-assoc : ∀ {A} (as bs cs : Seq A) →
   ((as + bs) + cs) ≡ (as + (bs + cs))
+-assoc as bs cs = refl
