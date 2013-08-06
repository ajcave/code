-- Free F-algebras and substitution, renaming
module subst-no-binders where
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Function

data Univ : Set where
 I : Univ
 _+_ _⊗_ : (T S : Univ) -> Univ
 var : Univ

⟦_⟧ : Univ -> Set -> Set
⟦ I ⟧ X = Unit
⟦ T + T₁ ⟧ X = ⟦ T ⟧ X ⊎ ⟦ T₁ ⟧ X
⟦ T ⊗ T₁ ⟧ X = ⟦ T ⟧ X × ⟦ T₁ ⟧ X
⟦ var ⟧ X = X

⟦_⟧f  : ∀ T {X Y} -> (X -> Y) -> ⟦ T ⟧ X -> ⟦ T ⟧ Y
⟦_⟧f I g t = unit
⟦_⟧f (T + T₁) g (inj₁ x) = inj₁ (⟦ T ⟧f g x)
⟦_⟧f (T + T₁) g (inj₂ y) = inj₂ (⟦ T₁ ⟧f g y)
⟦_⟧f (T ⊗ T₁) g (x₁ , x₂) = ⟦ T ⟧f g x₁ , ⟦ T₁ ⟧f g x₂
⟦_⟧f var g t = g t

data Free (T : Univ) (X : Set) : Set where
 inj : ⟦ T ⟧ (Free T X) -> Free T X -- Says it's a ⟦ T ⟧-algebra
 var : X -> Free T X

_-alg : Univ -> Set₁
T -alg = Σ Set (λ X -> ⟦ T ⟧ X -> X)

{-[_]_⇒_ : ∀ T -> T -alg -> T -alg -> Set
[ T ] (X , f) ⇒ (Y , g) = {!!} --}

U : ∀ T -> T -alg -> Set
U T (X , f) = X

mutual
 fold : ∀ T X -> (Y : T -alg) -> (X -> U T Y) -> Free T X -> U T Y
 fold T X (Y , h) f (inj x) = h (⟦ T ⟧f (fold T X (Y , h) f) x)
 fold T X (Y , h) f (var x) = f x

{- fold-map : ∀ T X -> (Y : T -alg) -> (X -> U T Y) -> ⟦ T ⟧ (Free T X) -> ⟦ T ⟧ (U T Y)
 fold-map I X (Y , h) f t = unit
 fold-map (T + T₁) X (Y , h) f (inj₁ x) = inj₁ (fold-map T X (Y , h ∘ inj₁) f {!!})
 fold-map (T + T₁) X (Y , h) f (inj₂ y) = {!!}
 fold-map (T ⊗ T₁) X (Y , h) f t = {!!}
 fold-map var X (Y , h) f t = {!!} -}
