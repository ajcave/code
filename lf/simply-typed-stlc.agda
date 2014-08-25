module simply-typed-stlc where
open import Data.List
open import Data.Empty
open import Data.Unit
open import Data.Product

data ctx (α : Set) : Set where
 ⊡ : ctx α
 _,_ : ctx α -> α -> ctx α

data varOpt {β} (α : β -> Set) (τ : β) : β -> Set where
 top : varOpt α τ τ
 pop : ∀ {τ₁} (x : α τ) -> varOpt α τ τ₁

var : ∀ {α} -> ctx α -> α -> Set
var ⊡ _ = ⊥
var (Γ , τ) τ₁ = varOpt (var Γ) τ τ₁

_<<_ : ∀ {A} -> ctx A -> List A -> ctx A
Γ << [] = Γ
Γ << (x ∷ Δ) = (Γ , x) << Δ

data tpF (sigtp : Set) : Set where
  _⇒_ : List sigtp -> sigtp -> tpF sigtp

module Sig (sigtp : Set) (Con : List (tpF sigtp) -> sigtp -> Set) where
 mutual
  spine' : (Γ : ctx sigtp) (A : List (tpF sigtp)) -> Set
  spine' Γ [] = ⊤
  spine' Γ ((τs ⇒ τ) ∷ []) = tm (Γ << τs) τ
  spine' Γ ((τs ⇒ τ) ∷ Δ) = tm (Γ << τs) τ × spine' Γ Δ

  data tm (Γ : ctx sigtp) : sigtp -> Set where
   _·_ : ∀ {τs τ} (c : Con τs τ) -> spine' Γ τs -> tm Γ τ
   ▹ : ∀ {T} (x : var Γ T) -> tm Γ T

-- We can do basic indexing
data stp : Set where
 i : stp
 _⇒_ : stp -> stp -> stp
data expSigtp : Set  where
 exp : stp -> expSigtp
 a : expSigtp
data expSigCon : List (tpF expSigtp) -> expSigtp -> Set where
 lam : ∀ {T S} -> expSigCon (((exp T ∷ []) ⇒ exp S) ∷ []) (exp (T ⇒ S))
 app : ∀ {T S} -> expSigCon ([] ⇒ exp (T ⇒ S) ∷ [] ⇒ exp T ∷ []) (exp S)
 c : expSigCon [] a

open module SigExp = Sig expSigtp expSigCon

idtm : ∀ {T} -> tm ⊡ (exp (T ⇒ T))
idtm = lam · (▹ top)

-- copy : ∀ {Γ α} -> tm Γ α -> tm Γ α
-- copy (lam · M) = lam · (copy M)
-- copy (app · (M , N)) = app · (copy M , copy N)
-- copy (▹ x) = ▹ x

data tctx : ctx expSigtp -> Set where
 ⊡ : tctx ⊡
 _,exp : ∀ {Γ T} -> tctx Γ -> tctx (Γ , (exp T))

copyv : ∀ {Γ T} -> tctx Γ -> var Γ (exp T) -> var Γ (exp T)
copyv ⊡ ()
copyv (Γ₁ ,exp) top = top
copyv (Γ₁ ,exp) (pop x) = pop (copyv Γ₁ x)

copy' : ∀ {γ T} -> tctx γ -> tm γ (exp T) -> tm γ (exp T)
copy' Γ (lam · M) = lam · (copy' (Γ ,exp) M)
copy' Γ (app · (M , N)) = app · (copy' Γ M , copy' Γ N)
copy' Γ (▹ x) = ▹ (copyv Γ x)

