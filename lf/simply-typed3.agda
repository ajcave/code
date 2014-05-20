module simply-typed3 where
open import Data.List
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality

data ctx (α : Set) : Set where
 ⊡ : ctx α
 _,_ : ctx α -> α -> ctx α

data varOpt (α : Set) : Set where
 top : varOpt α
 pop : (x : α) -> varOpt α

var : ∀ {α} -> ctx α -> Set
var ⊡ = ⊥
var (Γ , τ) = varOpt (var Γ)

lookup : ∀ {α} -> (Γ : ctx α) -> var Γ -> α
lookup ⊡ ()
lookup (Γ , x) top = x
lookup (Γ , x) (pop x₁) = lookup Γ x₁

_<<_ : ∀ {A} -> ctx A -> List A -> ctx A
Γ << [] = Γ
Γ << (x ∷ Δ) = (Γ , x) << Δ

data tpF (sigtp : Set) : Set where
  _⇒_ : List sigtp -> sigtp -> tpF sigtp

sigTm : Set -> Set
sigTm sigtp = List (tpF sigtp) × sigtp

module Sig (sigtp : Set) (Con : Set) (sigtm : Con -> sigTm sigtp) where
 tp1 = tpF sigtp

 mutual
  data tm (Γ : ctx sigtp) : sigtp -> Set where
   _·_ : ∀ (c : Con) -> spine' Γ (proj₁ (sigtm c)) -> tm Γ (proj₂ (sigtm c))
   ▹ : ∀ (x : var Γ) -> tm Γ (lookup Γ x)

  spine' : (Γ : ctx sigtp) (A : List tp1) -> Set
  spine' Γ [] = ⊤
  spine' Γ ((τs ⇒ τ) ∷ []) = tm (Γ << τs) τ
  spine' Γ ((τs ⇒ τ) ∷ Δ) = tm (Γ << τs) τ × spine' Γ Δ

data expSigtp : Set  where exp : expSigtp
data expSigCon : Set where lam app : expSigCon

expSig : expSigCon -> sigTm expSigtp
expSig lam = (((exp ∷ []) ⇒ exp) ∷ []) , exp
expSig app = (([] ⇒ exp ∷ [] ⇒ exp ∷ []) , exp)

open module SigExp = Sig expSigtp expSigCon expSig

idtm : tm ⊡ exp
idtm = lam · (▹ top)

copy : ∀ {Γ α} -> tm Γ α -> tm Γ α
copy (lam · M) = lam · (copy M)
copy (app · (M , N)) = app · (copy M , copy N)
copy (▹ x) = ▹ x


