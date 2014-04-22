module eq where
open import Level

data _≡_ {l} {A : Set l} (x : A) : (y : A) -> Set l where
 refl : x ≡ x

_≋_ : ∀ {A B : Set} (f g : A -> B) -> Set
f ≋ g = ∀ x -> f x ≡ g x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

≡-subst : ∀ {A : Set} (P : A -> Set) {a b : A} -> a ≡ b -> P a -> P b
≡-subst P refl x = x

≡-sym : ∀ {A : Set} {a b : A} -> a ≡ b -> b ≡ a
≡-sym refl = refl

≋-sym : ∀ {A B : Set} {f g : A -> B} -> f ≋ g -> g ≋ f
≋-sym H x = ≡-sym (H x)

≋-refl : ∀ {A B : Set} (f : A -> B) -> f ≋ f
≋-refl f x = refl

≡-trans : ∀ {A : Set} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
≡-trans refl refl = refl

≋-trans : ∀ {A B : Set} {f g h : A -> B} -> f ≋ g -> g ≋ h -> f ≋ h
≋-trans H1 H2 x = ≡-trans (H1 x) (H2 x)

≡-cong : ∀ {A : Set} (f : A -> Set) {a b} -> a ≡ b -> f a -> f b
≡-cong f refl x = x

≡-cong1 : ∀ {A B : Set} (f : A -> B) {a1 a2} -> a1 ≡ a2 -> f a1 ≡ f a2
≡-cong1 f refl = refl

≡-cong-app : ∀ {A B : Set} {f g : A -> B} {a1 a2} -> f ≋ g -> a1 ≡ a2 -> f a1 ≡ g a2
≡-cong-app H refl = H _

≡-cong2 : ∀ {A B C : Set} (f : A -> B -> C) {a1 a2 b1 b2} -> a1 ≡ a2 -> b1 ≡ b2 -> f a1 b1 ≡ f a2 b2
≡-cong2 f refl refl = refl