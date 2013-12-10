module subsequentialspaces where
open import Data.Product
open import Data.Nat
open import Data.Unit
open import Data.Sum
open import Function

record SubSeq : Set₁ where
 constructor _,_
 field
  U : Set
  _↝_ : (ℕ -> U) -> U -> Set

1⁺ : SubSeq
1⁺ = Unit , (λ x x₁ → ⊤)

module _ (A B : SubSeq) where
 private
  Underlying : Set
  Underlying = ((SubSeq.U A) ⊎ (SubSeq.U B))
 data _Sum↝_ : (ℕ -> Underlying) -> Underlying -> Set where
  inl : ∀ xs x -> (inj₁ ∘ xs) Sum↝ (inj₁ x)
  inr : ∀ ys y -> (inj₂ ∘ ys) Sum↝ (inj₂ y)

 _⊎⁺_ : SubSeq
 _⊎⁺_ = Underlying , _Sum↝_

_×⁺_ : SubSeq -> SubSeq -> SubSeq
A ×⁺ B = ((SubSeq.U A) × (SubSeq.U B)) , (λ xs x → (SubSeq._↝_ A (proj₁ ∘ xs) (proj₁ x)) × (SubSeq._↝_ B (proj₂ ∘ xs) (proj₂ x)))

record Arr (A B : SubSeq) : Set where
 constructor _,_
 field
  f : SubSeq.U A -> SubSeq.U B
  cont : ∀ {xs x} -> SubSeq._↝_ A xs x -> SubSeq._↝_ B (f ∘ xs) (f x)

_⇒⁺_ : SubSeq -> SubSeq -> SubSeq
A ⇒⁺ B = (Arr A B) , (λ fs f →
         ∀ {xs x} → SubSeq._↝_ A xs x → SubSeq._↝_ B (λ n → Arr.f (fs n) (xs n)) (Arr.f f x))





