{-# OPTIONS --no-positivity-check --no-termination-check --type-in-type #-}
module iir-eta-sig-irr-client where
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import iir-eta-sig-novsubst

natsig : sig
natsig = ((⊡ , (κ ⋆)) , (τ (a-top · ε))) , τ (Π (a-pop a-top · ε) (a-pop a-top · ε))

Nat : ∀ {Γ : ctx natsig} -> tp Γ
Nat = a-pop (a-pop a-top) · ε

Zero : ∀ {Γ : ctx natsig} -> ntm Γ Nat
Zero = con (a-pop a-top) · refl

Suc : ∀ {Γ : ctx natsig} -> ntm Γ Nat -> ntm Γ Nat
Suc n = con a-top · (n , refl)

stlcsig : sig
stlcsig = (((((⊡ ,
          (κ ⋆)) -- otp : type
        , (τ (a-top · ε))) -- b : otp
        , (τ (Π (a-pop a-top · ε) (Π (a-pop a-top · ε) (a-pop a-top · ε))))) -- arr : tp -> tp -> tp
        , κ (Π (a-pop (a-pop a-top) · ε) ⋆)) -- exp : tp -> type
        , τ (Π (a-pop (a-pop (a-pop a-top)) · ε) (Π (a-pop (a-pop (a-pop a-top)) · ε) (Π (a-top · (((con (a-pop a-top)) · ((v (pop top) · refl) , ({!!} , {!!}))) ,κ ε)) (Π (a-top · {!!}) (a-top · {!!}))))))
            -- app : {T:otp}{S:otp} exp (arr T S) -> exp T -> exp S
            -- app : {T:otp}{S:otp} exp (arr T ?) -> exp ? -> exp ?
        , {!!}
            -- lam : {T:otp}{S:otp} (exp T -> exp S) -> exp (arr T S)
