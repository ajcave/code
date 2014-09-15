module Syntax where
open import Data.Nat

-- Decidability of conversion for MLTT with universes, following Andreas Abel's habilitation thesis
-- (using Bove-Capretta technique -- turns domain semantics into a big step semantics)

-- Parameterized over Tm because I want to experiment with alternate representations:
-- Normal forms, spine forms, etc..
module Syn (Tm : Set) where
 mutual
  data Val : Set where
   ƛ : (t : Tm) -> (ρ : Env) -> Val
   ↑[_]_ : (A : Val) -> (e : Dne) -> Val
   zero : Val
   suc : (a : Val) -> Val
   Π : (A : Val) -> (B : Val) -> Val
   Nat : Val
   Set* : Val

  data Env : Set where
   ⊡ : Env
   _,_ : (ρ : Env) -> (a : Val) -> Env

  data Dne : Set where
   lvl : (x : ℕ) -> Dne
   _·_ : (e : Dne) -> (d : Dnf) -> Dne
   rec : (T : Tm) -> (tz : Tm) -> (ts : Tm) -> (e : Dne) -> Dne

  data Dnf : Set where
   ↓[_] : (A : Val) -> (a : Val) -> Dnf
  