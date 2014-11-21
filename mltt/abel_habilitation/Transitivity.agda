module Transitivity where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit 
open import Data.Empty
open import Data.Nat
open import WfNat
open import Model
open import Relation.Binary.PropositionalEquality hiding ([_])
open SetF
open import Util
open import Cumulativity
open import Sym

TRANS : ∀ {A} -> PREL A -> Set
TRANS R = ∀ {a b c} -> R a b -> R b c -> R a c

TRANS' : ∀ {A} -> PREL A -> Set
TRANS' R = ∀ {a b b' c} -> R a b -> b ≡ b' -> R b' c -> R a c

SELFL : ∀ {A} -> PREL A -> Set
SELFL R = ∀ {a a'} -> R a a' -> R a a

trans-⊥' : TRANS ⊥'
trans-⊥' h1 h2 n with h1 n | h2 n
... | _ , (p1 , p2) | _ , (p3 , p4) with Rne-deter p2 p3
trans-⊥' h1 h2 n | proj₁ , (p1 , p2) | .proj₁ , (p3 , p4) | refl = , p1 , p4

mutual
 NatR-trans : TRANS NatR
 NatR-trans (natval x) (natval x₁) = natval (NatV-trans x x₁)
 NatR-trans (neu x) (neu x₁) = neu (trans-⊥' x x₁)

 NatV-trans : TRANS NatV
 NatV-trans zero zero = zero
 NatV-trans (suc x) (suc x₁) = suc (NatV-trans x x₁)
 NatV-trans (natneu x) (natneu x₁) = natneu (NatNe-trans x x₁)

 NatNe-trans : TRANS NatNe
 NatNe-trans (x₁ ⊕ x) (x₂ ⊕ x₃) = (trans-⊥' x₁ x₂) ⊕ (NatV-trans x x₃)
 NatNe-trans (neu x) (neu x₁) = neu (trans-⊥' x x₁)

-- NatR-trans (idL p)  = ?
-- NatR-trans (idR p) (idR q) = ?

App-trans : ∀ {C V : Set} {r : C -> V -> Set} {B : PREL V} (d : Deterministic r) -> TRANS B -> TRANS (Clo r B)
App-trans d f (inj red1 (b2 , red2) rel) (inj (b3 , red3) b4 rel₁) with d red2 red3
App-trans d f (inj red1 (b2 , red2) rel) (inj (.b2 , red3) red4 rel₁) | refl = inj red1 red4 (f rel rel₁)

module ΠSYM {α β γ : Set} {red : β × α -> γ -> Set} {A : PREL α}
  {F : ∀ {a a'} -> a ≈ a' ∈ A -> PREL γ}
  (Asym : SYM A) (Atrans : TRANS A)
  (FirrL : ∀ {a a' a''} (p : a ≈ a' ∈ A) (p' : a ≈ a'' ∈ A) -> F p →₂ F p')
  (FirrR : ∀ {a a' a''} (p : a' ≈ a ∈ A) (p' : a'' ≈ a ∈ A) -> F p →₂ F p')
  (Fsym : ∀ {a a'} (p : a ≈ a' ∈ A) -> SYM (F p)) where
 
 Πsym : SYM (Π* red A F)
 Πsym ab a1≈a2 =
  let a2≈a1 = Asym a1≈a2 
      a1≈a1 = Atrans a1≈a2 a2≈a1
      q = App-sym (Fsym a2≈a1) (ab a2≈a1)
      q0 = App→ (FirrR _ _) q
  in  App→ (FirrL a1≈a1 a1≈a2) q0

module ΠPER {α β γ : Set} {red : β × α -> γ -> Set} {A : PREL α}
  {F : ∀ {a a'} -> a ≈ a' ∈ A -> PREL γ}
  (deter : Deterministic red)
  (Aself : SELFL A)
  (FirrL : ∀ {a a' a''} (p : a ≈ a' ∈ A) (p' : a ≈ a'' ∈ A) -> F p →₂ F p')
  (Fsym : ∀ {a a'} (p : a ≈ a' ∈ A) -> SYM (F p))
  (Ftrans : ∀ {a a'} (p : a ≈ a' ∈ A) -> TRANS (F p)) where
 
 Πtrans : TRANS (Π* red A F)
 Πtrans ab bc a1≈a2 =
  let a1≈a1 = Aself a1≈a2 
      q0 = ab a1≈a1
      q1 = bc a1≈a2
      q2 = App→ (FirrL a1≈a1 a1≈a2) q0
  in App-trans deter (Ftrans a1≈a2) q2 q1

module TransF (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j)
      (set<trans : ∀ {j} (p : j < k) -> TRANS (SetU' (akf p)))
  where
 K : Acc k
 K = inj akf
 open Clo
 mutual
  transEl : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> TRANS (ElU' pA)
  transEl (Neu y _) (inj y') (inj y0) = inj (trans-⊥' y' y0)
  transEl Nat ab bc = NatR-trans ab bc
  transEl (Π pA pF) ab bc = ΠPER.Πtrans evala-deter (selfL pA) (irrLF pF)
    (λ p → symEl (rel (pF p))) (λ p → transEl (rel (pF p))) ab bc
  transEl (Set* y) ab bc = set<trans y ab bc

  symEl : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> SYM (ElU' pA)
  symEl (Neu y _) (inj x) = inj (sym-⊥' x)
  symEl Nat ab = NatR-sym ab
  symEl (Π pA pF) ab = ΠSYM.Πsym (symEl pA) (transEl pA) (irrLF pF) (irrRF pF)
     (λ p → symEl (rel (pF p))) ab
  symEl (Set* y) ab = symSetω' (akf y) ab

  selfL : ∀ {A A'} (pA : A ≈ A' ∈ SetU' K) -> SELFL (ElU' pA)
  selfL pA p = transEl pA p (symEl pA p)

 mutual
  transSet' : TRANS' (SetU' K)
  transSet' (Neu x p) refl (Neu x₁ _) = Neu (trans-⊥' x x₁) p
  transSet' Nat refl Nat = Nat
  transSet' (Π pA pF) refl (Π pA₁ pF₁) = Π (transSet pA pA₁) (λ aa'AA'' →
    let aaAA'' = selfL (transSet pA pA₁) aa'AA'' in 
    let aaAA' = irrLω' (transSet pA pA₁) pA aaAA'' in
    let aa'A'A'' = irrRω' (transSet pA pA₁) pA₁ aa'AA'' in
    let q = transSet' (rel (pF aaAA')) (AppDeter1 (pF aaAA') (pF₁ aa'A'A'')) (rel (pF₁ aa'A'A'')) in
    inj (red1 (pF aaAA')) (red2 (pF₁ aa'A'A'')) q
   )
  transSet' (Set* x) refl (Set* x₁) = Set* x

  transSet : TRANS (SetU' K)
  transSet pA pB = transSet' pA refl pB

transSetω' : ∀ {k} (acck : Acc k) -> TRANS (SetU' acck)
transSetω' (inj x) = TransF.transSet _ _ (λ p → transSetω' (x p))

-- transSetω'' : TRANS Type
-- transSetω'' (m , pAB) (n , pBC) with compare' m n
-- transSetω'' (m , pAB) (n , pBC) | lte y = n , transSetω' _ (cumul _ _ y pAB) pBC
-- transSetω'' (m , pAB) (n , pBC) | gte y = m , transSetω' _ pAB (cumul _ _ y pBC)

symω' : ∀ {k} (acck : Acc k) -> ∀ {A A'} (pA : A ≈ A' ∈ SetU' acck) -> SYM (ElU' pA)
symω' (inj x) = TransF.symEl _ _ (λ p → transSetω' (x p))

selfL* : ∀ {k} {acck : Acc k} -> ∀ {A A'} (pA : A ≈ A' ∈ SetU' acck) -> SELFL (ElU' pA)
selfL* {k} {inj x} = TransF.selfL _ _ (λ p → transSetω' (x p))

-- symω : ∀ {A A'} (pA : A ≈ A' ∈ Type) -> SYM ([ pA ])
-- symω (k , pA) = symω' _ pA

transω' : ∀ {k} (K : Acc k) {A A'} (pA : A ≈ A' ∈ SetU' K) -> TRANS (ElU' pA)
transω' (inj x) = TransF.transEl _ _ (λ p → transSetω' (x p))

-- selfSetL : ∀ {k} {K : Acc k} {A B} (pAB : A ≈ B ∈ SetU' K) -> A ≈ A ∈ SetU' K
-- selfSetL pAB = transSetω' _ pAB (symSet _ _ ≤refl pAB)

-- htrans : ∀ {k} {K : Acc k} {A B C}
--      (pAB : A ≈ B ∈ SetU' K) (pBC : B ≈ C ∈ SetU' K) (pAC : A ≈ C ∈ SetU' K) ->
--    ∀ {f g h} -> f ≈ g ∈ ElU' pAB -> g ≈ h ∈ ElU' pBC -> f ≈ h ∈ ElU' pAC
-- htrans pAB pBC pAC f≈g∈AB g≈h∈BC =
--  transω' _ pAC (irrLω' pAB pAC f≈g∈AB) (irrRω' pBC pAC g≈h∈BC)

HTRANS' : ∀ {B A}
 (U1 : PREL A) (El1 : INTERP B U1)
 (U2 : PREL A) (El2 : INTERP B U2)
 (U3 : PREL A) (El3 : INTERP B U3) -> Set
HTRANS' U1 El1 U2 El2 U3 El3 = ∀ {A1 A2 B1 B2 C1 C2}
  (pAB : A1 ≈ B1 ∈ U1) (p1 : A1 ≡ A2)
  (pBC : B2 ≈ C1 ∈ U2) (p2 : B1 ≡ B2)
  (pAC : A2 ≈ C2 ∈ U3) (p3 : C1 ≡ C2)
 -> ∀ {f g h}
 -> f ≈ g ∈ (El1 pAB)
 -> g ≈ h ∈ (El2 pBC)
 -> f ≈ h ∈ (El3 pAC)

HTRANS : ∀ {B A} (U : PREL A) (El : INTERP B U) -> Set
HTRANS U El = HTRANS' U El U El U El

htrans* : ∀ {k n m} -> HTRANS' (SetU k) (ElU k) (SetU n) (ElU n) (SetU m) (ElU m)
htrans* pAB refl pBC refl pAC refl f≈g g≈h =
 transω' _ pAC (irrL _ _ pAB refl pAC f≈g) (irrR _ _ pBC refl pAC g≈h)

-- htransω : HTRANS Type [_]
-- htransω (n , pAB) (m , pBC) (k , pAC) f≈g g≈h =
--  transω' _ pAC (irrL _ _ pAB refl pAC f≈g) (irrR _ _ pBC refl pAC g≈h)

