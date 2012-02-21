module foo where

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

J : ∀ {A : Set} {x : A} (P : ∀ {y} (q : x ≡ y) -> Set) -> P refl -> ∀ {y} (q : x ≡ y) -> P q
J P p refl = p

foo : ∀ {A} (x y : A) (q : x ≡ y) -> J (λ {y'} q' → y' ≡ y) q q ≡ refl
foo x y q = J (λ {y'} q' → J (λ {y''} q0 → y'' ≡ y') q' q ≡ {!!}) {!!} q

