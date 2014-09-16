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
  rec : ∀ {ρ T tz ts tn dn d} -- -> ⟦ tz ⟧ ρ ↘ dz -> ⟦ ts ⟧ ρ ↘ ds
   -> ⟦ tn ⟧ ρ ↘ dn
   -> rec T , tz , ts , dn ↘ d
   -> ⟦ rec T tz ts tn ⟧ ρ ↘ d
  Set* : ∀ {ρ} -> ⟦ Set* ⟧ ρ ↘ Set*
  Π : ∀ {A A' F ρ} -> ⟦ A ⟧ ρ ↘ A' -> ⟦ Π A F ⟧ ρ ↘ Π A' (ƛ F ρ)
  Nat : ∀ {ρ} -> ⟦ Nat ⟧ ρ ↘ Nat
 data _·_↘_ : Val -> Val -> Val -> Set where 
  ƛ : ∀ {t ρ a b} -> ⟦ t ⟧ (ρ , a) ↘ b -> (ƛ t ρ) · a ↘ b
  ↑ : ∀ {A F e a F'}
    -> F · a ↘ F'
    -> (↑[ Π A F ] e) · a ↘ ↑[ F' ] (e · ↓[ A ] a)
 data rec_,_,_,_↘_ : Exp -> Exp -> Exp -> Val -> Val -> Set where
  zero : ∀ {T tz ts dz} -> ⟦ tz ⟧ ⊡ ↘ dz -> rec T , tz , ts , zero ↘ dz
  suc : ∀ {T tz ts dn a b} -> rec T , tz , ts , dn ↘ a -> ⟦ ts ⟧ ((⊡ , dn) , a) ↘ b
    -> rec T , tz , ts , (suc dn) ↘ b
  ne : ∀ {T T' A tz ts e} 
   -> ⟦ T ⟧ (⊡ , ↑[ A ] e) ↘ T'
   -> rec T , tz , ts , (↑[ A ] e) ↘ (↑[ T' ] (rec T tz ts e))
 -- We diverge from Abel in the treatment of rec.
 -- We treat it "opaquely", like a definition by pattern matching in Agda. No congruence rules, closed body
 -- I think this is like Martin-Lof's "weak" treatment of λ. No congruence rule.
 -- Note that the "usual" rec combinator can still be defined (admissible?) by abstracting over Gamma
 -- I think that the bodies need to be closed in order to keep type soundness? Did Martin-Lof
 -- not have this problem? Why not? No substitution into body of lambda? Kept a closure?
 -- Hmm, actually we may be able to keep *one* closure ρ associated with the normal form of rec
 -- Does this approach also simplify other methods for decidability? e.g. completeness and soundness
 -- of an "efficient algorithm(ic) equality"?

 -- x:N |- T type    |- tz : T[zero/n]  n:N,p:T n |- ts : T[suc n/x]  G |- tn : N
 -- -----------------------------------------------------------------------------
 --                G |- rec (x. T) tz (n,p. ts) tn : T[n/x]

mutual
 data Rnf_,_∶_↘_ : ℕ -> Val -> Val -> Nf -> Set where
  Π : ∀ {n f b A B B' v} -> f · ↑[ A ] (lvl n) ↘ b -> B · ↑[ A ] (lvl n) ↘ B' -> Rnf (suc n) , b ∶ B' ↘ v
     -> Rnf n , f ∶ Π A B ↘ ƛ v
  Nat : ∀ {n} -> Rnf n , Nat ∶ Set* ↘ Nat
  SetZ : ∀ {n} -> Rnf n , Set* ∶ Set* ↘ Set* -- !! Todo: will this work?
  Fun : ∀ {n A A' B B' B''} -> Rnf n , A ∶ Set* ↘ A' -> B · ↑[ A ] (lvl n) ↘ B'
    -> Rnf (suc n) , B ∶ Set* ↘ B''
  Neut : ∀ {n e v B B'} -> Rne n , e ↘ v -> Rnf n , (↑[ B' ] e) ∶ B ↘ (ne v)
  zero : ∀ {n} -> Rnf n , zero ∶ Nat ↘ zero
  suc : ∀ {n a v} -> Rnf n , a ∶ Nat ↘ v -> Rnf n , suc a ∶ Nat ↘ suc v
 data Rne_,_↘_ : ℕ -> Dne -> Ne -> Set where
--  lvl : TODO: arithmetic to turn level into index
  _·_ : ∀ {n e d u v A} -> Rne n , e ↘ u -> Rnf n , d ∶ A ↘ v -> Rne n , (e · (↓[ A ] d)) ↘ (u · v)
  rec : ∀ {n e u T tz ts} -> Rne n , e ↘ u -> Rne n , (rec T tz ts e) ↘ (rec T tz ts u)