module Eval where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])

data Comp : Set where
 ⟦_⟧_ : (term : Exp) -> (env : Env) -> Comp
 _·_ : (f a : Val) -> Comp

mutual
 data lookup_,_↘_ : Env -> ℕ -> Val -> Set where
  top : ∀ {ρ a} -> lookup (ρ , a) , zero ↘ a
  pop : ∀ {ρ a b x} -> lookup ρ , x ↘ b -> lookup (ρ , a) , (suc x) ↘ b
 data _↘_ : Comp -> Val -> Set where
  idx : ∀ {x ρ v} -> lookup ρ , x ↘ v -> ⟦ idx x ⟧ ρ ↘ v
  ƛ : ∀ {t ρ} -> ⟦ ƛ t ⟧ ρ ↘ ƛ t ρ
  _·_ : ∀ {r s ρ f a b} -> ⟦ r ⟧ ρ ↘ f -> ⟦ s ⟧ ρ ↘ a -> (f · a) ↘ b -> ⟦ r · s ⟧ ρ ↘ b
  zero : ∀ {ρ} -> ⟦ zero ⟧ ρ ↘ zero
  suc : ∀ {ρ t d} -> ⟦ t ⟧ ρ ↘ d -> ⟦ suc t ⟧ ρ ↘ (suc d)
  -- Note that this is rec where ts is of arrow type, not expanded.
  -- I guess we could factor out a type of closures and use that, but meh
  rec : ∀ {ρ T tz ts tn dn d} -- -> ⟦ tz ⟧ ρ ↘ dz -> ⟦ ts ⟧ ρ ↘ ds
   -> ⟦ tn ⟧ ρ ↘ dn
   -> rec T , tz , ts , dn ↘ d
   -> ⟦ rec T tz ts tn ⟧ ρ ↘ d
  Set* : ∀ {ρ i} -> ⟦ Set* i ⟧ ρ ↘ Set* i
  Π : ∀ {A A' F ρ} -> ⟦ A ⟧ ρ ↘ A' -> ⟦ Π A F ⟧ ρ ↘ Π A' (ƛ F ρ)
  Nat : ∀ {ρ} -> ⟦ Nat ⟧ ρ ↘ Nat
  _[_] : ∀ {t σ ρ ρ' d} -> ⟦ σ ⟧s ρ ↘ ρ' -> ⟦ t ⟧ ρ' ↘ d -> ⟦ t [ σ ] ⟧ ρ ↘ d
   --data _·_↘_ : Val -> Val -> Val -> Set where 
  ƛ· : ∀ {t ρ a b} -> ⟦ t ⟧ (ρ , a) ↘ b -> ((ƛ t ρ) · a) ↘ b
  ↑ : ∀ {A F e a F'}
    -> (F · a) ↘ F'
    -> (↑[ Π A F ] e · a) ↘ ↑[ F' ] (e · ↓[ A ] a)
 data ⟦_⟧s_↘_ : Subst -> Env -> Env -> Set where
  _[_] : ∀ {σ1 σ2 ρ ρ' ρ''} -> ⟦ σ2 ⟧s ρ ↘ ρ' -> ⟦ σ1 ⟧s ρ' ↘ ρ'' -> ⟦ σ1 [ σ2 ] ⟧s ρ ↘ ρ''
  id : ∀ {ρ} -> ⟦ id ⟧s ρ ↘ ρ
  ↑ : ∀ {ρ a} -> ⟦ ↑ ⟧s (ρ , a) ↘ ρ
  _,_ : ∀ {σ t ρ ρ' a} -> ⟦ σ ⟧s ρ ↘ ρ' -> ⟦ t ⟧ ρ ↘ a -> ⟦ σ , t ⟧s ρ ↘ (ρ' , a)
  ⊡ : ∀ {ρ} -> ⟦ ⊡ ⟧s ρ ↘ ⊡
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

open import Data.Unit
open import Data.Empty

IsBaseType : Val -> Set
IsBaseType Nat = ⊤
IsBaseType (Set* _) = ⊤
IsBaseType (↑[ Set* i ] E) = ⊤
IsBaseType _ = ⊥

mutual
 data Rnf_,_∶_↘_ : ℕ -> Val -> Val -> Nf -> Set where
  Π : ∀ {n f b A B B' v} -> (f · ↑[ A ] (lvl n)) ↘ b -> (B · ↑[ A ] (lvl n)) ↘ B' -> Rnf (suc n) , b ∶ B' ↘ v
     -> Rnf n , f ∶ Π A B ↘ ƛ v
  Nat : ∀ {n i} -> Rnf n , Nat ∶ Set* i ↘ Nat
  SetZ : ∀ {n i j} -> Rnf n , Set* i ∶ Set* j ↘ Set* i -- !! Todo: will this work?
  Fun : ∀ {n A A' F B B' i} -> Rnf n , A ∶ Set* i ↘ A' -> (F · ↑[ A ] (lvl n)) ↘ B
   -> Rnf (suc n) , B ∶ Set* i ↘ B'
   -> Rnf n , (Π A F) ∶ Set* i ↘ (Π A' (ƛ B'))
  Neut : ∀ {B} {_ : IsBaseType B} {n e v B'} -> Rne n , e ↘ v -> Rnf n , (↑[ B' ] e) ∶ B ↘ (ne v)
  zero : ∀ {n} -> Rnf n , zero ∶ Nat ↘ zero
  suc : ∀ {n a v} -> Rnf n , a ∶ Nat ↘ v -> Rnf n , suc a ∶ Nat ↘ suc v
 data Rne_,_↘_ : ℕ -> Dne -> Ne -> Set where
  lvl : ∀ {n} k -> Rne n , (lvl k) ↘ idx (n ∸ suc k)
  _·_ : ∀ {n e d u v A} -> Rne n , e ↘ u -> Rnf n , d ∶ A ↘ v -> Rne n , (e · (↓[ A ] d)) ↘ (u · v)
  rec : ∀ {n e u T tz ts} -> Rne n , e ↘ u -> Rne n , (rec T tz ts e) ↘ (rec T tz ts u)

Singleton : ∀ {A : Set} (P : A -> Set) -> Set
Singleton P = ∀ {x y} -> P x -> P y -> x ≡ y

lookup-deter : ∀ {ρ i} -> Singleton (lookup_,_↘_ ρ i)
lookup-deter top top = refl
lookup-deter (pop p1) (pop p2) = lookup-deter p1 p2

mutual
 eval-deter : ∀ {c} -> Singleton (_↘_ c)
 eval-deter (idx x₂) (idx x₃) = lookup-deter x₂ x₃
 eval-deter ƛ ƛ = refl
 eval-deter (_·_ p1 p2 x₁) (_·_ p3 p4 x₂) with eval-deter p1 p3 | eval-deter p2 p4
 ... | refl | refl = eval-deter x₁ x₂
 eval-deter zero zero = refl
 eval-deter (suc p1) (suc p2) = cong suc (eval-deter p1 p2)
 eval-deter (rec p1 x₁) (rec p2 x₂) with eval-deter p1 p2
 ... | refl = rec-deter x₁ x₂
 eval-deter Set* Set* = refl
 eval-deter (Π p1) (Π p2) = cong₂ Π (eval-deter p1 p2) refl
 eval-deter Nat Nat = refl
 eval-deter (x₁ [ p1 ]) (x₂ [ p2 ]) with evals-deter x₁ x₂
 ... | refl = eval-deter p1 p2
 eval-deter (ƛ· x₁) (ƛ· x₂) = eval-deter x₁ x₂
 eval-deter (↑ p1) (↑ p2) with eval-deter p1 p2
 ... | refl = refl

 evals-deter : ∀ {σ ρ} -> Singleton (⟦_⟧s_↘_ σ ρ)
 evals-deter (p2 [ p1 ]) (p3 [ p4 ]) with evals-deter p2 p3
 ... | refl = evals-deter p1 p4
 evals-deter id id = refl
 evals-deter ↑ ↑ = refl
 evals-deter (p1 , x) (p2 , x₁) = cong₂ _,_ (evals-deter p1 p2) (eval-deter x x₁)
 evals-deter ⊡ ⊡ = refl

 rec-deter : ∀ {T tz ts dn} -> Singleton (rec_,_,_,_↘_ T tz ts dn)
 rec-deter (zero x₁) (zero x₂) = eval-deter x₁ x₂
 rec-deter (suc p1 x₁) (suc p2 x₂) with rec-deter p1 p2
 ... | refl = eval-deter x₁ x₂
 rec-deter (ne x) (ne x₁) with eval-deter x x₁
 ... | refl = refl

mutual
 Rnf-deter : ∀ {n a A} -> Singleton (Rnf_,_∶_↘_ n a A)
 Rnf-deter (Π x x₁ p1) (Π x₂ x₃ p2) with eval-deter x x₂
 Rnf-deter (Π x x₁ p1) (Π x₂ x₃ p2) | refl with eval-deter x₁ x₃
 ... | refl = cong ƛ (Rnf-deter p1 p2)
 Rnf-deter (Π x₂ x p1) (Neut {._} {()} x₃)
 Rnf-deter Nat Nat = refl
 Rnf-deter SetZ SetZ = refl
 Rnf-deter (Fun p1 x p2) (Fun p3 x₁ p4) with eval-deter x x₁
 ... | refl = cong₂ Π (Rnf-deter p1 p3) (cong ƛ (Rnf-deter p2 p4))
 Rnf-deter (Neut {._} {()} x₁) (Π x₂ x₃ p2)
 Rnf-deter (Neut x) (Neut x₃) = cong ne (Rne-deter x x₃)
 Rnf-deter zero zero = refl
 Rnf-deter (suc p1) (suc p2) = cong suc (Rnf-deter p1 p2)

 Rne-deter : ∀ {n a} -> Singleton (Rne_,_↘_ n a)
 Rne-deter (lvl k) (lvl .k) = refl
 Rne-deter (p1 · x) (p2 · x₁) = cong₂ _·_ (Rne-deter p1 p2) (Rnf-deter x x₁)
 Rne-deter (rec p1) (rec p2) = cong (rec _ _ _) (Rne-deter p1 p2)