{-# OPTIONS --no-positivity-check --no-termination-check --type-in-type #-}
module iir-single-head-client where
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import iir-single-head

-- natsig : sig
-- natsig = ((⊡ , (κ ⋆)) , (τ (top · unit))) , τ (Π (top · unit) (top · unit))

-- Nat : tp {natsig} ⊡
-- Nat = top · unit

-- Zero : ∀ {Γ : ctx natsig} -> ntm Γ Nat
-- Zero = con (pop top) · refl

-- Suc : ∀ {Γ : ctx natsig} -> ntm Γ Nat -> ntm Γ Nat
-- Suc n = con top · (n , refl)

stlcsig : sig
stlcsig = (((((⊡ ,
          (κ ⋆)) -- otp : type
        , (τ (top · unit))) -- b : otp
        , (τ (Π (top · unit) (Π (top · unit) (top · unit))))) -- arr : tp -> tp -> tp
        , κ (Π (top · unit) ⋆)) -- exp : tp -> type
        , τ (Π (pop top · unit) (Π (pop top · unit) (Π (top · (((con top) , ((v (pop top) , refl) , ((v top , refl) , refl))) , unit)) (Π (top · ((v (pop (pop top)) , refl) , unit)) (top · ((v (pop (pop top)) , refl) , unit)))))))
            -- app : {T:otp}{S:otp} exp (arr T S) -> exp T -> exp S
            -- app : {T:otp}{S:otp} exp (arr T S) -> exp T -> exp ?
        , τ (Π (pop top · unit) (Π (pop top · unit) (Π {!!} (top · (((con (pop top)) , (((v (pop (pop top))) , refl) , (((v (pop top)) , refl) , refl))) , unit)))))
            -- lam : {T:otp}{S:otp} (exp T -> exp S) -> exp (arr T S)
