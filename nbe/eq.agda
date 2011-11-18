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

≡-cong : ∀ {A : Set} (f : A -> Set) {a b} -> a ≡ b -> f a -> f b
≡-cong f refl x = x

≡-cong1 : ∀ {A B : Set} (f : A -> B) {a1 a2} -> a1 ≡ a2 -> f a1 ≡ f a2
≡-cong1 f refl = refl

≡-cong2 : ∀ {A B C : Set} (f : A -> B -> C) {a1 a2 b1 b2} -> a1 ≡ a2 -> b1 ≡ b2 -> f a1 b1 ≡ f a2 b2
≡-cong2 f refl refl = refl