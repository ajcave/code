module simply-typed6 where
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
 
〈_〉 : ∀ {A : Set} -> A -> tpF A
〈 τ 〉 = [] ⇒ τ

data expSigtp : Set  where exp a : expSigtp
data expSigCon : List (tpF expSigtp) -> expSigtp -> Set where
 lam : expSigCon [ [ exp ] ⇒ exp ] exp
 app : expSigCon ( 〈 exp 〉 ∷ 〈 exp 〉 ∷ []) exp
 c : expSigCon [] a

data expSigtp' : Set  where exp a : expSigtp'
data expSigCon' : List (tpF expSigtp') -> expSigtp' -> Set where
 lam : expSigCon' [ [ exp ] ⇒ exp ] exp
 app : expSigCon' ( 〈 exp 〉 ∷ 〈 exp 〉 ∷ []) exp
 c : expSigCon' [] a

open module L = Sig expSigtp expSigCon
module M = Sig expSigtp' expSigCon'

copyctx : ∀ (γ : ctx expSigtp) -> ctx expSigtp'
copyctx ⊡ = ⊡
copyctx (γ , x) = copyctx γ , exp
-- Subtle bit: We will often need to prove that the copied context is of a corresponding schema

data tctx : ctx expSigtp -> Set where
 ⊡ : tctx ⊡
 _,exp : ∀ {Γ} -> tctx Γ -> tctx (Γ , exp)

copyv : ∀ {Γ} -> tctx Γ -> var Γ exp -> var (copyctx Γ) exp
copyv ⊡ ()
copyv (Γ₁ ,exp) top = top
copyv (Γ₁ ,exp) (pop x) = pop (copyv Γ₁ x)

copy' : ∀ {γ} -> tctx γ -> L.tm γ exp -> M.tm (copyctx γ) exp
copy' Γ (lam · M) = lam M.· (copy' (Γ ,exp) M)
copy' Γ (app · (M , N)) = app M.· (copy' Γ M , copy' Γ N)
copy' Γ (▹ x) = M.▹ (copyv Γ x)

-- Different approach using instance arguments
tctx' : ctx expSigtp -> Set
tctx' ⊡ = ⊤
tctx' (Γ , exp) = tctx' Γ
tctx' (Γ , a) = ⊥

copyv' : ∀ {Γ} -> ⦃ p : tctx' Γ ⦄ -> var Γ exp -> var (copyctx Γ) exp
copyv' {⊡} ()
copyv' {Γ , exp} top = top
copyv' {Γ , exp} (pop x₂) = pop (copyv' x₂)
copyv' {Γ , a} ⦃ () ⦄ x

copy'' : ∀ {γ} -> ⦃ p : tctx' γ ⦄ -> L.tm γ exp -> M.tm (copyctx γ) exp
copy'' (lam · M) = lam M.· (copy'' M)
copy'' (app · (M , N)) = app M.· (copy'' M , copy'' N)
copy'' (▹ x) = M.▹ (copyv' x)

