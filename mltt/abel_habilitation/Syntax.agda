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
   ↑[_] : (A : Val) -> (e : Dne) -> Val
   -- zero : Val
   -- suc : (a : Val) -> Val
   Π : (A : Val) -> (B : Val) -> Val
   Nat : Val
   Set* : ℕ -> Val
   _⊕_ : Val -> Val -> Val
   natval : NatVal -> Val

  -- I could just put all of these in the same grammar and just only explain
  -- how to read back the β normal ones?

  data NatVal : Set where
   zero : NatVal
   suc : NatVal -> NatVal
   natneu : NatNeu -> NatVal

  data NatNeu : Set where
   --neu : Dne -> NatNeu
   _⊕_ : Dne -> NatVal -> NatNeu

  data Env : Set where
   ⊡ : Env
   _,_ : (ρ : Env) -> (a : Val) -> Env

  data Dne : Set where
   lvl : (x : ℕ) -> Dne
   _·_ : (e : Dne) -> (d : Dnf) -> Dne
   rec : (T : Tm) -> (tz : Tm) -> (ts : Tm) -> (e : NatNeu) -> Dne

  data Dnf : Set where
   ↓[_] : (A : Val) -> (a : Val) -> Dnf

-- Note that it doesn't really matter that this is inductive.. could be combinators or godel coding,
-- or even an "open" type, as long as we have what we need?
-- doesn't really matter. Could conflate representations. Conflating gets eliminated by type-directed
-- reification?