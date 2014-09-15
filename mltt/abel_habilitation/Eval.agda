module Eval where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Data.Nat

-- Hmm I don't think I can make the others parametric over eval, since
-- it wouldn't be able to see strict positivity...
mutual
 data lookup_,_↘_ : Env -> ℕ -> Val -> Set where
  top : ∀ {ρ a} -> lookup (ρ , a) , zero ↘ a
  pop : ∀ {ρ a b x} -> lookup ρ , x ↘ b -> lookup (ρ , a) , (suc x) ↘ b
 data ⟦_⟧_↘_ : Exp -> Env -> Val -> Set where
  idx : ∀ {x ρ v} -> lookup ρ , x ↘ v -> ⟦ idx x ⟧ ρ ↘ v
  ƛ : ∀ {t ρ} -> ⟦ ƛ t ⟧ ρ ↘ ƛ t ρ
  _·_ : ∀ {r s ρ f a b} -> ⟦ r ⟧ ρ ↘ f -> ⟦ s ⟧ ρ ↘ a -> f · a ↘ b -> ⟦ r · s ⟧ ρ ↘ b
  zero : ∀ {ρ} -> ⟦ zero ⟧ ρ ↘ zero
  suc : ∀ {ρ t d} -> ⟦ t ⟧ ρ ↘ d -> ⟦ suc t ⟧ ρ ↘ (suc d)
  -- Note that this is rec where ts is of arrow type, not expanded.
  -- I guess we could factor out a type of closures and use that, but meh
  rec : ∀ {ρ tz ts tn dz ds dn d} -> ⟦ tz ⟧ ρ ↘ dz -> ⟦ ts ⟧ ρ ↘ ds -> ⟦ tn ⟧ ρ ↘ dn -> rec dz , ds , dn ↘ d
   -> ⟦ rec tz ts tn ⟧ ρ ↘ d
 data _·_↘_ : Val -> Val -> Val -> Set where 
  ƛ : ∀ {t ρ a b} -> ⟦ t ⟧ (ρ , a) ↘ b -> (ƛ t ρ) · a ↘ b
  ↑ : ∀ {A F e a F'}
    -> F · a ↘ F'
    -> (↑[ Π A F ] e) · a ↘ ↑[ F' ] (e · ↓[ A ] a)
 data rec_,_,_↘_ : Val -> Val -> Val -> Val -> Set where
  zero : ∀ {dz ds} -> rec dz , ds , zero ↘ dz
  suc : ∀ {dz ds dn a f b} -> rec dz , ds , dn ↘ a -> ds · dn ↘ f -> f · a ↘ b
    -> rec ds , ds , (suc dn) ↘ b