{-# OPTIONS --no-positivity-check --no-termination-check --type-in-type --no-coverage-check #-}
module iir-single-head6-client where
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import iir-single-head6

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
        , τ (Π (pop top · unit) (Π (pop top · unit) (Π (Π (top · (((v (pop top)) , refl) , unit)) (top · (((v (pop top)) , refl) , unit))) (top · (((con (pop top)) , (((v (pop (pop top))) , refl) , (((v (pop top)) , refl) , refl))) , unit)))))
            -- lam : {T:otp}{S:otp} (exp T -> exp S) -> exp (arr T S)

-- TODO: I wonder if I can somehow use implicits to avoid the need to supply refl and unit

Tp : ∀ {Γ : ctx stlcsig} -> tp Γ
Tp = (pop top) · unit

Exp : ∀ {Γ : ctx stlcsig} -> ntm Γ Tp -> tp Γ
Exp T = top · (T , unit)

pattern lam T1 T2 M = con top , (T1 , T2 , M , refl)
pattern app T1 T2 M N = con (pop top) , (T1 , T2 , M , N , refl)

copy : ∀ {Γ : ctx stlcsig} -> (T : ntm Γ Tp) -> ntm Γ (Exp T) -> ntm Γ (Exp T)
copy T (v x , S) = {!!}
copy ._ (lam T1 T2 M) = {!!}
copy .T2 (app T1 T2 M N) = ?
-- Note that coverage checking is off

-- copy T (con (pop (pop top)) , ()) = ?
-- copy T (con (pop (pop (pop top))) , ()) = ?

-- TODO: Try with telescope type format?
-- TODO: Try with the other sig format?
-- TODO: Figure out "pattern constructor syntax" (i.e. declaring syntax as begin pattern syntax)
 --- These are called "pattern synonyms"