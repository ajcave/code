module Model where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Nat
open import WfNat
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Util
open import Function

REL = PREL Val

_≈_∈_ : ∀ {α} -> α -> α -> PREL α -> Set
a ≈ b ∈ A = A a b

-- TODO: These can be instances of Clo!!!
⊤' : PREL Dnf
⊤' (↓[ A ] a) (↓[ A₁ ] a₁) = ∀ n → ∃ (λ v → Rnf n , a ∶ A ↘ v × Rnf n , a₁ ∶ A₁ ↘ v)

⊥' : PREL Dne
⊥' e e' = ∀ n → ∃ (λ u → Rne n , e ↘ u × Rne n , e' ↘ u)


record Clo {C V : Set} (Red : C -> V -> Set) (B : PREL V) (c1 c2 : C) : Set where
 constructor inj
 field
  red1 : ∃ (λ v1 -> Red c1 v1)
  red2 : ∃ (λ v2 -> Red c2 v2)
  rel : B (proj₁ red1) (proj₁ red2)

mutual
 NatR : REL
 NatR = Clo UnboxNat_↘_ NatV

 data NatV : PREL NatVal where
  zero : zero ≈ zero ∈ NatV
  suc : ∀ {a a'} -> a ≈ a' ∈ NatV -> suc a ≈ suc a' ∈ NatV
  natneu : ∀ {e1 e2} -> e1 ≈ e2 ∈ NatNe -> natneu e1 ≈ natneu e2 ∈ NatV

 data NatNe : PREL NatNeu where
  _⊕_ : ∀ {e e' v v'} -> e ≈ e' ∈ ⊥' -> v ≈ v' ∈ NatV -> (e ⊕ v) ≈ (e' ⊕ v') ∈ NatNe

EnvREL : Set₁
EnvREL = Env -> Env -> Set

open Clo

rd1 : ∀ {C V : Set} {Red B c1 c2} -> (d : Clo {C} {V} Red B c1 c2) -> Red c1 (proj₁ (red1 d))
rd1 d = proj₂ (red1 d)

rd2 : ∀ {C V B c1 c2} {Red : C -> V -> Set} -> (d : Clo Red B c1 c2) -> Red c2 (proj₁ (red2 d))
rd2 d = proj₂ (red2 d)

inj' : ∀ {C V B c1 c2 v1 v2} {Red : C -> V -> Set} -> Red c1 v1 -> Red c2 v2 -> B v1 v2 -> Clo Red B c1 c2
inj' r1 r2 r3 = inj (, r1) (, r2) r3

App : (B : REL) (c1 c2 : Val × Val) -> Set
App = Clo _↘a_

App→ : ∀ {C V : Set} {red : C -> V -> Set} {B B' : PREL V} -> B →₂ B' -> Clo red B →₂ Clo red B'
App→ f (inj red1 red2 rel) = inj red1 red2 (f rel)

AppDeter1 :  ∀ {c1 c2 c3 B B'} 
    (p : c1 ≈ c2 ∈ App B)
    (q : c2 ≈ c3 ∈ App B')
   -> proj₁ (red2 p) ≡ proj₁ (red1 q)
AppDeter1 (inj red1 (_ , red2) rel)
          (inj (_ , red3) red4 rel') = evala-deter red2 red3

AppDeter2 :  ∀ {c1 c2 c3 B B'} 
    (p : c1 ≈ c2 ∈ App B)
    (q : c2 ≈ c3 ∈ App B')
   -> proj₁ (red1 q) ≡ proj₁ (red2 p) 
AppDeter2 p q = sym (AppDeter1 p q)

AppDeter3 :  ∀ {c1 c2 c3 B B'} 
    (p : c1 ≈ c2 ∈ App B)
    (q : c1 ≈ c3 ∈ App B')
   -> proj₁ (red1 p) ≡ proj₁ (red1 q)
AppDeter3 (inj (_ , red1) red2 rel)
          (inj (_ , red3) red4 rel') = evala-deter red1 red3 

AppDeter4 :  ∀ {c1 c2 c3 B B'} 
    (p : c2 ≈ c1 ∈ App B)
    (q : c3 ≈ c1 ∈ App B')
   -> proj₁ (red2 p) ≡ proj₁ (red2 q)
AppDeter4 (inj red1 (_ , red2) rel)
          (inj red3 (_ , red4) rel') = evala-deter red2 red4

-- record ⟦_⟧s_≈⟦_⟧s_∈_ σ ρ σ' ρ' (B : EnvREL) : Set where
--  field
--   ρ1 : Env
--   ρ2 : Env
--   red1 : ⟦ σ  ⟧s ρ  ↘ ρ1
--   red2 : ⟦ σ' ⟧s ρ' ↘ ρ2
--   rel : B ρ1 ρ2

Π* : ∀ {α β γ : Set} -> (β × α -> γ -> Set)
 -> (A : PREL α) -> (∀ {a a'} -> a ≈ a' ∈ A -> PREL γ) -> PREL β
Π* red A F f1 f2 = ∀ {a1 a2} (pa : a1 ≈ a2 ∈ A) -> (f1 , a1) ≈ (f2 , a2) ∈ (Clo red (F pa))

_⇒[_]_ : ∀ {α β γ : Set} -> (A : PREL α) (r : β × α -> γ -> Set) (B : PREL γ) -> PREL β
A ⇒[ r ] B = Π* r A (λ _ -> B)

ΠR : (A : REL) -> (∀ {a a'} -> A a a' -> REL) -> REL
ΠR A F = Π* _↘a_ A F

_⇒R_ : (A B : REL) -> REL
A ⇒R B = ΠR A (λ _ -> B)

data NeuRel : REL where
 inj : ∀ {e1 E1 e2 E2} -- -> E1 ≈ E ∈⊥ -> E2 ≈ E ∈⊥  -- TODO! ?
     -> e1 ≈ e2 ∈ ⊥' -> NeuRel (↑[ E1 ] e1) (↑[ E2 ] e2)

INTERP : ∀ B {A} -> PREL A -> Set₁
INTERP B U = ∀ {A A'} -> A ≈ A' ∈ U -> PREL B

-- What if we tried something more "unary" in the Pi case?
module SetF (k : ℕ) (SetP : ∀ {j} -> j < k -> REL) where
 mutual
  data SetR : Val -> Val -> Set where
   Neu : ∀ {j E E'} -> E ≈ E' ∈ ⊥' -> j ≤ k -> ↑[ Set* j ] E ≈ ↑[ Set* j ] E' ∈ SetR
   Nat : Nat ≈ Nat ∈ SetR
   Π : ∀ {A A' F F'} (pA : A ≈ A' ∈ SetR)
    -> (pF : F ≈ F' ∈ ((El pA) ⇒R SetR))
    -> (Π A F) ≈ (Π A' F') ∈ SetR
   Set* : ∀ {j} -> j < k -> Set* j ≈ Set* j ∈ SetR

  El : INTERP Val SetR
  El (Neu {E} _ x) = NeuRel
  El Nat = NatR
  El (Π pA pF) = ΠR (El pA) (λ p → El (rel (pF p)))
  El (Set* j<k) = SetP j<k

SetU' : {n : ℕ} -> Acc n -> REL
SetU' {n} (inj f) = SetF.SetR n (λ p → SetU' (f p))

SetU : ℕ -> REL
SetU n = SetU' (nat-acc {n})

Type : REL
Type A B = ∃ (λ n → SetU n A B)

ElU' : {n : ℕ} {p : Acc n} -> ∀ {A A'} -> A ≈ A' ∈ (SetU' p) -> REL
ElU' {n} {inj p} = SetF.El n (SetU' ∘ p)

ElU : (n : ℕ) -> ∀ {A A'} -> A ≈ A' ∈ (SetU n) -> REL
ElU n = ElU' {n} {nat-acc {n}}

-- [_] : ∀ {A A'} -> A ≈ A' ∈ Type -> REL
-- [ n , pA ] = ElU n pA

⟦_⟧tp' : ∀ {α : Set} {red : α -> Val -> Set} {c1 c2} {k} -> c1 ≈ c2 ∈ Clo red (SetU k) -> REL
⟦ vT ⟧tp' = ElU _ (rel vT)

-- ⟦_⟧tp : ∀ {c1 c2} -> c1 ≈ c2 ∈ App Type -> REL
-- ⟦ vT ⟧tp = [ App.rel vT ]

data Comb (R : EnvREL) (S : ∀ {ρ1 ρ2} -> ρ1 ≈ ρ2 ∈ R -> REL) : EnvREL where
 _,_ : ∀ {ρ1 ρ2 a1 a2} (vρ : ρ1 ≈ ρ2 ∈ R) -> a1 ≈ a2 ∈ S vρ -> (ρ1 , a1) ≈ (ρ2 , a2) ∈ Comb R S

data EmpRel : EnvREL where
 tt : EmpRel ⊡ ⊡

open import Function

mutual
 data ⊨_≈_ctx : Ctx -> Ctx -> Set where
  tt : ⊨ ⊡ ≈ ⊡ ctx
  _,_ : ∀ {γ1 γ2 t1 t2 k} -> (Γ : ⊨ γ1 ≈ γ2 ctx) -> [ Γ ]⊨ t1 ≈ t2 type[ k ]
       -> ⊨ (γ1 , t1) ≈ (γ2 , t2) ctx
  
 [_]⊨_≈_type[_] : {γ1 γ2 : Ctx} -> ⊨ γ1 ≈ γ2 ctx -> Exp -> Exp -> ℕ -> Set
 [ Γ ]⊨ T1 ≈ T2 type[ k ] = T1 ≈ T2 ∈ (⟦ Γ ⟧hctx ⇒[ _↘_ ] (SetU k))

 ⟦_⟧hctx : {Γ1 Γ2 : Ctx} -> ⊨ Γ1 ≈ Γ2 ctx -> EnvREL
 ⟦ tt ⟧hctx = EmpRel
 ⟦ Γ , T ⟧hctx = Comb ⟦ Γ ⟧hctx (λ vρ -> ⟦ T vρ ⟧tp')

⊨_ctx : Ctx -> Set
⊨ Γ ctx = ⊨ Γ ≈ Γ ctx

⟦_⟧ctx : {Γ : Ctx} -> ⊨ Γ ctx -> EnvREL
⟦ Γ ⟧ctx = ⟦ Γ ⟧hctx

[_]⊨_type[_] : {Γ : Ctx} -> ⊨ Γ ctx -> Exp -> ℕ -> Set
[ Γ ]⊨ T type[ k ] = [ Γ ]⊨ T ≈ T type[ k ]

[_]⊨_≈_∶h[_] : ∀ {γ1 γ2} (Γ : ⊨ γ1 ≈ γ2 ctx) {k} -> Exp -> Exp -> {T1 T2 : Exp} -> [ Γ ]⊨ T1 ≈ T2 type[ k ] -> Set
[ Γ ]⊨ t ≈ t' ∶h[ T ] = t ≈ t' ∈ Π* _↘_ ⟦ Γ ⟧hctx (⟦_⟧tp' ∘  T)

[_]⊨_≈_∶[_] : ∀ {γ} (Γ : ⊨ γ ctx) {k} -> Exp -> Exp -> {T : Exp} -> [ Γ ]⊨ T type[ k ] -> Set
[ Γ ]⊨ t ≈ t' ∶[ T ] = [ Γ ]⊨ t ≈ t' ∶h[ T ]

[_]⊨s_≈_∶[_] : ∀ {γ1 γ2 δ1 δ2} (Γ : ⊨ γ1 ≈ γ2 ctx)  -> Subst -> Subst -> (Δ : ⊨ δ1 ≈ δ2 ctx) -> Set
[ Γ ]⊨s σ1 ≈ σ2 ∶[ Δ ] =
  ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ ⟧hctx) → ⟦ σ1 ⟧ ρ ≈ ⟦ σ2 ⟧ ρ' ∈ (Clo _↘s_ ⟦ Δ ⟧hctx)
