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
  Π : (A F : Exp) -> Exp -- This may as well be a regular Π and not a "Fun"
  Set* : ℕ -> Exp
  _⊕_ : Exp -> Exp -> Exp

 data Subst : Set where
  ⊡ : Subst
  ↑ id : Subst
  _[_] : (σ τ : Subst) -> Subst
  _,_ : (σ : Subst) -> (t : Exp) -> Subst

data Ctx : Set where
 ⊡ : Ctx
 _,_ : (Γ : Ctx) -> (S : Exp) -> Ctx

-- mutual
--  data Nf : Set where
--   ƛ : (t : Nf) -> Nf
--   Nat : Nf
--   Set* : ℕ -> Nf
--   Π : Nf -> Nf -> Nf
--   suc : (t : Nf) -> Nf
--   zero : Nf
--   ne : (u : Ne) -> Nf
--   natneu : NatNeu -> Nf
--  data Ne : Set where
--   rec : (T tz ts : Exp) (u : NatNeu) -> Ne
--   idx : (x : ℕ) -> Ne
--   _·_ : (r : Ne) (s : Nf) -> Ne
--  data NatNeu : Set where
--   num : Ne -> NatNeu
--   _⊕_ : NatNeu -> Nf -> NatNeu
  