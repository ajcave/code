module simply-typed where
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
sigTm sigtp = ctx (List (tpF sigtp) × sigtp)

module Sig (sigtp : Set) (sigtm : sigTm sigtp) where
 tp1 = tpF sigtp

 mutual
  data tm (Γ : ctx sigtp) : sigtp -> Set where
   _·_ : ∀ (x : var sigtm) -> spine' Γ (proj₁ (lookup sigtm x)) -> tm Γ (proj₂ (lookup sigtm x))
   ▹ : ∀ (x : var Γ) -> tm Γ (lookup Γ x)

  spine' : (Γ : ctx sigtp) (A : List tp1) -> Set
  spine' Γ [] = ⊤
  spine' Γ ((τs ⇒ τ) ∷ Δ) = tm (Γ << τs) τ × spine' Γ Δ

data expSigtp : Set where exp : expSigtp

expSig : sigTm expSigtp
expSig = (⊡ , (([] ⇒ exp ∷ [] ⇒ exp ∷ []) , exp)) , ((((exp ∷ []) ⇒ exp) ∷ []) , exp)

open module SigExp = Sig expSigtp expSig

idtm : tm ⊡ exp
idtm = top · (▹ top , _)

copy : ∀ {Γ α} -> tm Γ α -> tm Γ α
copy (top · (M , _)) = top · (copy M , _)
copy (pop top · (M , N , _)) = pop top · ((copy M) , ((copy N) , _))
copy (pop (pop ()) · S)
copy (▹ x) = ▹ x