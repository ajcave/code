module Eval where
open import Syntax 
open import SyntaxTm as T
open Syn Exp
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Data.Empty
open import Data.Unit

-- Comp : Set
-- Comp = 
-- data Comp : Set where
--  ⟦_⟧_ : (term : Exp) -> (env : Env) -> Comp
--  _·_ : (f a : Val) -> Comp

-- data SComp : Set where
--  ⟦_⟧_ : (σ : Subst) -> (ρ : Env) -> SComp

data recComp : Set where
 rec_,_,_,_ : Exp -> Exp -> Exp -> NatVal -> recComp

⟦_⟧_ : ∀ {A B : Set} -> A -> B -> A × B
⟦ t ⟧ ρ = t , ρ

mutual
 data lookup_↘_ : ℕ × Env -> Val -> Set where
  top : ∀ {ρ a} -> lookup zero , (ρ , a)  ↘ a
  pop : ∀ {ρ a b x} -> lookup x , ρ  ↘ b -> lookup (suc x) , (ρ , a) ↘ b
 data _↘_ : Exp × Env -> Val -> Set where
  idx : ∀ {x ρ v} -> lookup x , ρ ↘ v -> ⟦ idx x ⟧ ρ ↘ v
  ƛ : ∀ {t ρ} -> ⟦ ƛ t ⟧ ρ ↘ ƛ t ρ
  ap : ∀ {r s ρ f a b} -> ⟦ r ⟧ ρ ↘ f -> ⟦ s ⟧ ρ ↘ a -> (f , a) ↘a b -> ((r · s) , ρ) ↘ b
  zero : ∀ {ρ} -> ⟦ zero ⟧ ρ ↘ natval zero
  suc : ∀ {ρ t d n} -> ⟦ t ⟧ ρ ↘ d -> UnboxNat d ↘ n -> ⟦ suc t ⟧ ρ ↘ (natval (suc n))
  rec : ∀ {ρ T tz ts tn dn0 dn d} 
   -> ⟦ tn ⟧ ρ ↘ dn0 -> UnboxNat dn0 ↘ dn
   -> (rec T , tz , ts , dn) ↘r d
   -> ⟦ rec T tz ts tn ⟧ ρ ↘ d
  Set* : ∀ {ρ i} -> ⟦ Set* i ⟧ ρ ↘ Set* i
  Π : ∀ {A A' F F' ρ} -> ⟦ A ⟧ ρ ↘ A' -> ⟦ F ⟧ ρ ↘ F' -> ⟦ Π A F ⟧ ρ ↘ Π A' F'
  Nat : ∀ {ρ} -> ⟦ Nat ⟧ ρ ↘ Nat
  _[_] : ∀ {t σ ρ ρ' d} -> ⟦ t ⟧ ρ' ↘ d -> ⟦ σ ⟧ ρ ↘s ρ' -> ⟦ t [ σ ] ⟧ ρ ↘ d
  plus : ∀ {t1 t2 d1 d2 m n ρ} -> ⟦ t1 ⟧ ρ ↘ d1 -> ⟦ t2 ⟧ ρ ↘ d2 
        -> UnboxNat d1 ↘ m -> UnboxNat d2 ↘ n 
        -> ⟦ t1 ⊕ t2 ⟧ ρ ↘ natval (m ⊕̂ n)
 data _↘a_ : Val × Val -> Val -> Set where 
  ƛ· : ∀ {t ρ a b} -> ⟦ t ⟧ (ρ , a) ↘ b -> ((ƛ t ρ) , a) ↘a b
  ↑ : ∀ {A F e a F'}
    -> (F , a) ↘a F'
    -> (↑[ Π A F ] e , a) ↘a ↑[ F' ] (e · ↓[ A ] a)
 data UnboxNat_↘_ : Val -> NatVal -> Set where
  natval : ∀ {n} -> UnboxNat (natval n) ↘ n
  neu : ∀ {e} -> UnboxNat (↑[ Nat ] e) ↘ natneu (e ⊕ zero)
 -- Unbox seems more like a lift? Or an η-expansion/read back that gets done early?
 -- Is our choice between doing expansion earlier or doing recursion later?

 _⊕̂_ : NatVal -> NatVal -> NatVal
 zero ⊕̂ d2 = d2
 suc d1 ⊕̂ d2 = suc (d1 ⊕̂ d2)
 natneu x ⊕̂ d2 = natneu (x ++ d2)

 _++_ : NatNeu -> NatVal -> NatNeu
 --neu x ++ v = x ⊕ v
 (x ⊕ x₁) ++ v = x ⊕ (x₁ ⊕̂ v)
 
 data _↘s_ : Subst × Env -> Env -> Set where
  _[_] : ∀ {σ1 σ2 ρ ρ' ρ''} -> ⟦ σ2 ⟧ ρ ↘s ρ' -> ⟦ σ1 ⟧ ρ' ↘s ρ'' -> ⟦ σ1 [ σ2 ] ⟧ ρ ↘s ρ''
  id : ∀ {ρ} -> ⟦ id ⟧ ρ ↘s ρ
  ↑ : ∀ {ρ a} -> ⟦ ↑ ⟧ (ρ , a) ↘s ρ
  _,_ : ∀ {σ t ρ ρ' a} -> ⟦ σ ⟧ ρ ↘s ρ' -> ⟦ t ⟧ ρ ↘ a -> ⟦ σ , t ⟧ ρ ↘s (ρ' , a)
  ⊡ : ∀ {ρ} -> ⟦ ⊡ ⟧ ρ ↘s ⊡
 data _↘r_ : recComp -> Val -> Set where
  zero : ∀ {T tz ts dz} -> ⟦ tz ⟧ ⊡ ↘ dz -> rec T , tz , ts , zero ↘r dz
  suc : ∀ {T tz ts dn a b} -> rec T , tz , ts , dn ↘r a -> ⟦ ts ⟧ ((⊡ , natval dn) , a) ↘ b
    -> rec T , tz , ts , (suc dn) ↘r b
  ne : ∀ {T T' tz ts e} 
   -> ⟦ T ⟧ (⊡ , (natval (natneu e))) ↘ T'
   -> rec T , tz , ts , (natneu e) ↘r (↑[ T' ] (rec T tz ts e))
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
IsBaseType (Set* _) = ⊤
IsBaseType (↑[ Set* i ] E) = ⊤
IsBaseType _ = ⊥

-- These can give back Nf and Ne instead of Exp, but does it matter?
mutual
 data Rnf_,_↘_ : ℕ -> (Val × Val) -> Exp -> Set where
  Π : ∀ {n f b A B B' v} -> (f , ↑[ A ] (lvl n)) ↘a b -> (B , ↑[ A ] (lvl n)) ↘a B' -> Rnf (suc n) , (b , B') ↘ v
     -> Rnf n , (f , Π A B) ↘ ƛ v
  Nat : ∀ {n i} -> Rnf n , (Nat , Set* i) ↘ Nat
  SetZ : ∀ {n i j} -> Rnf n , (Set* i , Set* j) ↘ Set* i
  Fun : ∀ {n A A' F B B' i} -> Rnf n , (A , Set* i) ↘ A' -> (F , ↑[ A ] (lvl n)) ↘a B
   -> Rnf (suc n) , (B , Set* i) ↘ B'
   -> Rnf n , ((Π A F) , Set* i) ↘ (Π A' (ƛ B'))
  Neut : ∀ {B} {_ : IsBaseType B} {n e v B'} -> Rne n , e ↘ v -> Rnf n , ((↑[ B' ] e) , B) ↘ v
  unbox : ∀ {v m n u} -> UnboxNat v ↘ m -> RnfNat n , m ↘ u -> Rnf n , (v , Nat) ↘ u
  -- This seems kind of essential, because we won't know if something is actually a Nat and needs a zero appended until "late", i.e. after the type is plugged in: A:Set, x:A |- x : A. When we plug Nat/A, we need to expand this to x ⊕ zero ∶ Nat
  -- TODO: Could I even postpone the (re)association and evaluation of ⊕ this far?
  --   (its evaluation could be delayed until now. Then potentially treated lazily?)
 data Rne_,_↘_ : ℕ -> Dne -> Exp -> Set where
  lvl : ∀ {n} k -> Rne n , (lvl k) ↘ idx (n ∸ suc k)
  ap : ∀ {n e d u v A} -> Rne n , e ↘ u -> Rnf n , (d , A) ↘ v -> Rne n , (e · (↓[ A ] d)) ↘ (u · v)
  rec : ∀ {n e u T tz ts} -> RneNat n , e ↘ u -> Rne n , (rec T tz ts e) ↘ (rec T tz ts u)

 data RnfNat_,_↘_ : ℕ -> NatVal -> Exp -> Set where
  zero : ∀ {n} -> RnfNat n , zero ↘ zero
  suc : ∀ {n a v} -> RnfNat n , a ↘ v -> RnfNat n , suc a ↘ suc v
  natneu : ∀ {n x v} -> RneNat n , x ↘ v -> RnfNat n , natneu x ↘ v

 data RneNat_,_↘_ : ℕ -> NatNeu -> Exp -> Set where
  _⊕_ : ∀ {n x v m u} -> Rne n , x ↘ v -> RnfNat n , m ↘ u -> RneNat n , (x ⊕ m) ↘ (v ⊕ u)

Singleton : ∀ {A : Set} (P : A -> Set) -> Set
Singleton P = ∀ {x y} -> P x -> P y -> x ≡ y

Deterministic : ∀ {A B : Set} (R : A -> B -> Set) -> Set
Deterministic R = ∀ {x} -> Singleton (R x)

lookup-deter : Deterministic lookup_↘_
lookup-deter top top = refl
lookup-deter (pop p1) (pop p2) = lookup-deter p1 p2

mutual
 eval-deter : Deterministic _↘_
 eval-deter (idx x₂) (idx x₃) = lookup-deter x₂ x₃
 eval-deter ƛ ƛ = refl
 eval-deter (ap p1 p2 x₁) (ap p3 p4 x₂) with eval-deter p1 p3 | eval-deter p2 p4
 ... | refl | refl = evala-deter x₁ x₂
 eval-deter zero zero = refl
 eval-deter (suc p1 p1') (suc p2 p2') with eval-deter p1 p2
 ... | refl = cong natval (cong suc (unbox-deter p1' p2')) --cong suc (eval-deter p1 p2)
 eval-deter (rec p1 x₁ y1) (rec p2 x₂ y2) with eval-deter p1 p2
 ... | refl with unbox-deter x₁ x₂
 ... | refl = rec-deter y1 y2
 eval-deter Set* Set* = refl
 eval-deter (Π p1 p3) (Π p2 p4) = cong₂ Π (eval-deter p1 p2) (eval-deter p3 p4)
 eval-deter Nat Nat = refl
 eval-deter (x₁ [ p1 ]) (x₂ [ p2 ]) with evals-deter p1 p2
 ... | refl = eval-deter x₁ x₂
 eval-deter (plus d1 d2 d3 d4) (plus d1' d2' d3' d4') with eval-deter d1 d1' | eval-deter d2 d2'
 ... | refl | refl with unbox-deter d3 d3' | unbox-deter d4 d4'
 ... | refl | refl = refl

 unbox-deter : Deterministic UnboxNat_↘_
 unbox-deter natval natval = refl
 unbox-deter neu neu = refl

 evala-deter : Deterministic _↘a_
 evala-deter (ƛ· x₁) (ƛ· x₂) = eval-deter x₁ x₂
 evala-deter (↑ p1) (↑ p2) with evala-deter p1 p2
 ... | refl = refl

 -- evalp-deter : ∀ {u v} -> Singleton (_⊕_↘p_ u v)
 -- evalp-deter zero zero = refl
 -- evalp-deter (suc d1) (suc d2) = cong suc (evalp-deter d1 d2)
 -- evalp-deter (ne x₁) (ne x₂) = evalp'-deter x₁ x₂

 -- evalp'-deter : ∀ {e v} -> Singleton (_+̂_↘p_ e v)
 -- evalp'-deter (plus x₁ d1) (plus x₂ d2) with evalp-deter x₁ x₂
 -- ... | refl = evalp'-deter d1 d2
 -- evalp'-deter (plus x₁ d1) (notplus {._} {()})
 -- evalp'-deter (notplus {._} {()}) (plus x₁ d2)
 -- evalp'-deter notplus notplus = refl

 evals-deter : Deterministic _↘s_
 evals-deter (p2 [ p1 ]) (p3 [ p4 ]) with evals-deter p2 p3
 ... | refl = evals-deter p1 p4
 evals-deter id id = refl
 evals-deter ↑ ↑ = refl
 evals-deter (p1 , x) (p2 , x₁) = cong₂ _,_ (evals-deter p1 p2) (eval-deter x x₁)
 evals-deter ⊡ ⊡ = refl

 rec-deter : Deterministic _↘r_
 rec-deter (zero x₁) (zero x₂) = eval-deter x₁ x₂
 rec-deter (suc p1 x₁) (suc p2 x₂) with rec-deter p1 p2
 ... | refl = eval-deter x₁ x₂
 rec-deter (ne x) (ne x₁) with eval-deter x x₁
 ... | refl = refl

mutual
 Rnf-deter : ∀ {n} -> Deterministic (Rnf_,_↘_ n)
 Rnf-deter (Π x x₁ p1) (Π x₂ x₃ p2) with evala-deter x x₂
 Rnf-deter (Π x x₁ p1) (Π x₂ x₃ p2) | refl with evala-deter x₁ x₃
 ... | refl = cong ƛ (Rnf-deter p1 p2)
 Rnf-deter (Π x₂ x p1) (Neut {._} {()} x₃)
 Rnf-deter Nat Nat = refl
 Rnf-deter SetZ SetZ = refl
 Rnf-deter (Fun p1 x p2) (Fun p3 x₁ p4) with evala-deter x x₁
 ... | refl = cong₂ Π (Rnf-deter p1 p3) (cong ƛ (Rnf-deter p2 p4))
 Rnf-deter (Neut {._} {()} x₁) (Π x₂ x₃ p2)
 Rnf-deter (Neut x) (Neut x₃) = Rne-deter x x₃
 --Rnf-deter (nat p2) (nat q2) = RnfNat-deter p2 q2
 -- Rnf-deter zero zero = refl
 -- Rnf-deter (suc p1) (suc p2) = cong suc (Rnf-deter p1 p2)
 -- Rnf-deter (p1 ⊕ p2) (p3 ⊕ p4) with Rne-deter p1 p3 | Rnf-deter p2 p4
 -- ... | refl | refl = refl
 Rnf-deter (unbox x1 x2) (unbox y1 y2) with unbox-deter x1 y1
 ... | refl = RnfNat-deter x2 y2
 Rnf-deter (Neut {._} {()} _) (unbox _ _)
 Rnf-deter (unbox _ _) (Neut {._} {()} _)

 Rne-deter : ∀ {n a} -> Singleton (Rne_,_↘_ n a)
 Rne-deter (lvl k) (lvl .k) = refl
 Rne-deter (ap p1 x) (ap p2 x₁) = cong₂ _·_ (Rne-deter p1 p2) (Rnf-deter x x₁)
 Rne-deter (rec p1) (rec p2) = cong (rec _ _ _) (RneNat-deter p1 p2) --(Rne-deter p1 p2)

 RnfNat-deter : ∀ {n} -> Deterministic (RnfNat_,_↘_ n)
 RnfNat-deter zero zero = refl
 RnfNat-deter (suc p1) (suc p2) = cong suc (RnfNat-deter p1 p2)
 RnfNat-deter (natneu x₂) (natneu x₃) = RneNat-deter x₂ x₃

 RneNat-deter : ∀ {n} -> Deterministic (RneNat_,_↘_ n)
 --RneNat-deter (neu x₂) (neu x₃) = Rne-deter x₂ x₃
 RneNat-deter (x₂ ⊕ x) (x₃ ⊕ x₄) = cong₂ _⊕_ (Rne-deter x₂ x₃) (RnfNat-deter x x₄)