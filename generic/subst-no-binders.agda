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
 fold : ∀ T X Y -> (h : ⟦ T ⟧ Y -> Y) -> (X -> Y) -> Free T X -> Y
 fold T X Y h f (inj x) = h (fold-map T T X Y h f x) --(⟦ T ⟧f (fold T X Y h f) x)
 fold T X Y h f (var x) = f x

 fold-map : ∀ T T' X Y -> (⟦ T' ⟧ Y -> Y) -> (X -> Y) -> ⟦ T ⟧ (Free T' X) -> ⟦ T ⟧ Y
 fold-map I T' X Y f g x = unit
 fold-map (T + T₁) T' X Y f g (inj₁ x) = inj₁ (fold-map T T' X Y f g x)
 fold-map (T + T₁) T' X Y f g (inj₂ y) = inj₂ (fold-map T₁ T' X Y f g y)
 fold-map (T ⊗ T₁) T' X Y f g (proj₁ , proj₂) = (fold-map T T' X Y f g proj₁) , (fold-map T₁ T' X Y f g proj₂)
 fold-map var T' X Y f g x = fold T' X Y f g x





