module SyntaxTm where
open import Data.Nat

mutual
 data Exp : Set where
  ƛ : (t : Exp) -> Exp
  Nat zero SetZ : Exp
  suc : (t : Exp) -> Exp
  rec : (tz ts tn : Exp) -> Exp
  idx : (x : ℕ) -> Exp
  _·_ : (r s : Exp) -> Exp
  _[_] : (t : Exp) -> (σ : Subst) -> Exp

 data Subst : Set where
  ↑ id : Subst
  _[_] : (σ τ : Subst) -> Subst
  _,_ : (σ : Subst) -> (t : Exp) -> Subst

data Ctx : Set where
 ⊡ : Ctx
 _,_ : (Γ : Ctx) -> (S : Exp) -> Ctx