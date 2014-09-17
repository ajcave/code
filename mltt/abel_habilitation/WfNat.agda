module WfNat where
open import Data.Nat

≤trans : ∀ {j k n} -> j ≤ k -> k ≤ n -> j ≤ n
≤trans z≤n p2 = z≤n
≤trans (s≤s p1) (s≤s p2) = s≤s (≤trans p1 p2)

data Acc (n : ℕ) : Set where
 inj : (∀ {j} -> j < n -> Acc j) -> Acc n

nat-acc' : (n : ℕ) -> ∀ {j} -> j < n -> Acc j
nat-acc' zero ()
nat-acc' (suc n) (s≤s p) = inj (λ x → nat-acc' n (≤trans x p))

nat-acc : {n : ℕ} -> Acc n
nat-acc = inj (nat-acc' _)