module eq where

data _≡_ {A : Set} (x : A) : (y : A) -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

≡-subst : ∀ {A : Set} (P : A -> Set) {a b : A} -> a ≡ b -> P a -> P b
≡-subst P refl x = x

≡-sym : ∀ {A : Set} {a b : A} -> a ≡ b -> b ≡ a
≡-sym refl = refl

≡-trans : ∀ {A : Set} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
≡-trans refl refl = refl