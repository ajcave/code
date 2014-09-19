module SyntaxTm where
open import Data.Nat

mutual
 data Exp : Set where
  ƛ : (t : Exp) -> Exp
  Nat zero : Exp
  suc : (t : Exp) -> Exp
  rec : (T tz ts tn : Exp) -> Exp
  idx : (x : ℕ) -> Exp
  _·_ : (r s : Exp) -> Exp
  _[_] : (t : Exp) -> (σ : Subst) -> Exp
  Π : (A F : Exp) -> Exp
  Set* : ℕ -> Exp

 data Subst : Set where
  ⊡ : Subst
  ↑ id : Subst
  _[_] : (σ τ : Subst) -> Subst
  _,_ : (σ : Subst) -> (t : Exp) -> Subst

data Ctx : Set where
 ⊡ : Ctx
 _,_ : (Γ : Ctx) -> (S : Exp) -> Ctx

mutual
 data Nf : Set where
  ƛ : (t : Nf) -> Nf
  Nat zero : Nf
  Set* : ℕ -> Nf
  Π : Nf -> Nf -> Nf
  suc : (t : Nf) -> Nf
  ne : (u : Ne) -> Nf
 data Ne : Set where
  rec : (T tz ts : Exp) (u : Ne) -> Ne
  idx : (x : ℕ) -> Ne
  _·_ : (r : Ne) (s : Nf) -> Ne