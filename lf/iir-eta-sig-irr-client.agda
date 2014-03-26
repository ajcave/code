{-# OPTIONS --no-positivity-check --no-termination-check --type-in-type #-}
module iir-eta-sig-irr-client where
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import iir-eta-sig-novsubst

natsig : sig
natsig = ((⊡ , (κ ⋆)) , (τ (top · unit))) , τ (Π (pop top · unit) (pop top · unit))

Nat : ∀ {Γ : ctx natsig} -> tp Γ
Nat = pop (pop top) · unit

Zero : ∀ {Γ : ctx natsig} -> ntm Γ Nat
Zero = con (pop top) · refl

Suc : ∀ {Γ : ctx natsig} -> ntm Γ Nat -> ntm Γ Nat
Suc n = con top · (n , refl)

stlcsig : sig
stlcsig = (((((⊡ ,
          (κ ⋆)) -- otp : type
        , (τ (top · unit))) -- b : otp
        , (τ (Π (pop top · unit) (Π (pop top · unit) (pop top · unit))))) -- arr : tp -> tp -> tp
        , κ (Π (pop (pop top) · unit) ⋆)) -- exp : tp -> type
        , τ (Π (pop (pop (pop top)) · unit) (Π (pop (pop (pop top)) · unit) (Π (top · (((con (pop top)) · ((v (pop top) · refl) , ({!!} , refl))) , unit)) (Π (top · {!!}) (top · {!!}))))))
            -- app : {T:otp}{S:otp} exp (arr T S) -> exp T -> exp S
            -- app : {T:otp}{S:otp} exp (arr T ?) -> exp ? -> exp ?
        , {!!}
            -- lam : {T:otp}{S:otp} (exp T -> exp S) -> exp (arr T S)
