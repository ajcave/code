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

REL = PREL Val

_≈_∈_ : ∀ {α} -> α -> α -> PREL α -> Set
a ≈ b ∈ A = A a b

⊤' : PREL Dnf
⊤' (↓[ A ] a) (↓[ A₁ ] a₁) = ∀ n → ∃ (λ v → Rnf n , a ∶ A ↘ v × Rnf n , a₁ ∶ A₁ ↘ v)

⊥' : PREL Dne
⊥' e e' = ∀ n → ∃ (λ u → Rne n , e ↘ u × Rne n , e' ↘ u)

data NatR : REL where
 zero : zero ≈ zero ∈ NatR
 suc : ∀ {a a'} -> a ≈ a' ∈ NatR -> suc a ≈ suc a' ∈ NatR
 neu : ∀ {e e'} -> e ≈ e' ∈ ⊥' -> ↑[ Nat ] e ≈ ↑[ Nat ] e' ∈ NatR

EnvREL : Set₁
EnvREL = Env -> Env -> Set

Red : Comp -> Set
Red c = ∃ (λ b -> c ↘ b)

record App (B : REL) (c1 c2 : Comp) : Set where
 constructor inj
 field
  red1 : Red c1
  red2 : Red c2
  rel : B (proj₁ red1) (proj₁ red2)

App→ : ∀ {B B'} -> B →₂ B' -> App B →₂ App B'
App→ f (inj red1 red2 rel) = inj red1 red2 (f rel)

AppDeter1 :  ∀ {c1 c2 c3 B B'} 
    (p : c1 ≈ c2 ∈ App B)
    (q : c2 ≈ c3 ∈ App B')
   -> proj₁ (App.red2 p) ≡ proj₁ (App.red1 q)
AppDeter1 (inj red1 (_ , red2) rel)
          (inj (_ , red3) red4 rel') = eval-deter red2 red3

AppDeter2 :  ∀ {c1 c2 c3 B B'} 
    (p : c1 ≈ c2 ∈ App B)
    (q : c2 ≈ c3 ∈ App B')
   -> proj₁ (App.red1 q) ≡ proj₁ (App.red2 p) 
AppDeter2 p q = sym (AppDeter1 p q)

AppDeter3 :  ∀ {c1 c2 c3 B B'} 
    (p : c1 ≈ c2 ∈ App B)
    (q : c1 ≈ c3 ∈ App B')
   -> proj₁ (App.red1 p) ≡ proj₁ (App.red1 q)
AppDeter3 (inj (_ , red1) red2 rel)
          (inj (_ , red3) red4 rel') = eval-deter red1 red3 

AppDeter4 :  ∀ {c1 c2 c3 B B'} 
    (p : c2 ≈ c1 ∈ App B)
    (q : c3 ≈ c1 ∈ App B')
   -> proj₁ (App.red2 p) ≡ proj₁ (App.red2 q)
AppDeter4 (inj red1 (_ , red2) rel)
          (inj red3 (_ , red4) rel') = eval-deter red2 red4

record ⟦_⟧s_≈⟦_⟧s_∈_ σ ρ σ' ρ' (B : EnvREL) : Set where
 field
  ρ1 : Env
  ρ2 : Env
  red1 : ⟦ σ  ⟧s ρ  ↘ ρ1
  red2 : ⟦ σ' ⟧s ρ' ↘ ρ2
  rel : B ρ1 ρ2

ΠR : (A : REL) -> (∀ {a a'} -> A a a' -> REL) -> REL
ΠR A F f f' = ∀ {a a'} -> (p : A a a') -> (f · a) ≈ (f' · a') ∈ (App (F p))

_⇒R_ : (A B : REL) -> REL
A ⇒R B = ΠR A (λ _ -> B)

data NeuRel : REL where
 inj : ∀ {e1 E1 e2 E2} -- -> E1 ≈ E ∈⊥ -> E2 ≈ E ∈⊥  -- TODO! ?
     -> e1 ≈ e2 ∈ ⊥' -> NeuRel (↑[ E1 ] e1) (↑[ E2 ] e2)

INTERP : ∀ B {A} -> PREL A -> Set₁
INTERP B U = ∀ {A A'} -> A ≈ A' ∈ U -> PREL B

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
  El (Π pA pF) = ΠR (El pA) (λ p → El (App.rel (pF p)))
  El (Set* j<k) = SetP j<k

SetU' : {n : ℕ} -> Acc n -> REL
SetU' {n} (inj f) = SetF.SetR n (λ p → SetU' (f p))

SetU : ℕ -> REL
SetU n = SetU' (nat-acc {n})

Type : REL
Type A B = ∃ (λ n → SetU n A B)

ElU' : {n : ℕ} {p : Acc n} -> ∀ {A A'} -> A ≈ A' ∈ (SetU' p) -> REL
ElU' {n} {inj p} = SetF.El n (λ q → SetU' (p q))

ElU : (n : ℕ) -> ∀ {A A'} -> A ≈ A' ∈ (SetU n) -> REL
ElU n = ElU' {n} {nat-acc {n}}

[_] : ∀ {A A'} -> A ≈ A' ∈ Type -> REL
[ n , pA ] = ElU n pA

⟦_⟧tp' : ∀ {c1 c2} {k} -> c1 ≈ c2 ∈ App (SetU k) -> REL
⟦ vT ⟧tp' = ElU _ (App.rel vT)

⟦_⟧tp : ∀ {c1 c2} -> c1 ≈ c2 ∈ App Type -> REL
⟦ vT ⟧tp = [ App.rel vT ]

data Comb (R : EnvREL) (S : ∀ {ρ1 ρ2} -> ρ1 ≈ ρ2 ∈ R -> REL) : EnvREL where
 _,_ : ∀ {ρ1 ρ2 a1 a2} (vρ : ρ1 ≈ ρ2 ∈ R) -> a1 ≈ a2 ∈ S vρ -> (ρ1 , a1) ≈ (ρ2 , a2) ∈ Comb R S

data EmpRel : EnvREL where
 tt : EmpRel ⊡ ⊡

open import Function

mutual
 data ⊨_ctx : Ctx -> Set where
  tt : ⊨ ⊡ ctx
  _,_ : ∀ {Γ T k} -> (vΓ : ⊨ Γ ctx) -> (∀ {ρ ρ'} → ρ ≈ ρ' ∈ ⟦ vΓ ⟧ctx → ⟦ T ⟧ ρ ≈ ⟦ T ⟧ ρ' ∈ App (SetU k))
       -> ⊨ (Γ , T) ctx

 ⟦_⟧ctx : {Γ : Ctx} -> ⊨ Γ ctx -> EnvREL
 ⟦ tt ⟧ctx = EmpRel
 ⟦ Γ , T ⟧ctx = Comb ⟦ Γ ⟧ctx (⟦_⟧tp' ∘  T)

_⊨'_type[_,_] : (Γ : Ctx) -> Exp -> ⊨ Γ ctx -> ℕ -> Set
Γ ⊨' T type[ vΓ , k ] = ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ vΓ ⟧ctx) → ⟦ T ⟧ ρ ≈ ⟦ T ⟧ ρ' ∈ App (SetU k)

[_]⊨_type[_] : {Γ : Ctx} -> ⊨ Γ ctx -> Exp -> ℕ -> Set
[ Γ ]⊨ T type[ k ] = ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ ⟧ctx) → ⟦ T ⟧ ρ ≈ ⟦ T ⟧ ρ' ∈ App (SetU k)

_⊨_type : Ctx -> Exp -> Set
Γ ⊨ T type = Σ (⊨ Γ ctx) (λ vΓ → ∃ (λ k -> Γ ⊨' T type[ vΓ , k ]))

[_]⊨_≈_∶[_] : ∀ {γ} (Γ : ⊨ γ ctx) {k} -> Exp -> Exp -> {T : Exp} -> [ Γ ]⊨ T type[ k ] -> Set
[ Γ ]⊨ t ≈ t' ∶[ T ] =
  ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ Γ ⟧ctx) → ⟦ t ⟧ ρ ≈ ⟦ t' ⟧ ρ' ∈ App ⟦ T vρ ⟧tp'

_,_⊨''_≈_∶_[_] : ∀ ρ ρ' -> Exp -> Exp -> Exp -> ℕ -> Set
ρ , ρ' ⊨'' t ≈ t' ∶ T [ k ] = Σ (⟦ T ⟧ ρ ≈ ⟦ T ⟧ ρ' ∈ App (SetU k)) (λ p -> ⟦ t ⟧ ρ ≈ ⟦ t' ⟧ ρ' ∈ App ⟦ p ⟧tp')

_⊨_≈_∶_ : Ctx -> Exp -> Exp -> Exp -> Set
Γ ⊨ t ≈ t' ∶ T = Σ (⊨ Γ ctx) (λ vΓ -> ∃ (λ k -> ∀ {ρ ρ'} → ρ ≈ ρ' ∈ ⟦ vΓ ⟧ctx → ρ , ρ' ⊨'' t ≈ t' ∶ T [ k ]))

_⊨_∶_ : Ctx -> Exp -> Exp -> Set
Γ ⊨ t ∶ T    =    Γ ⊨ t ≈ t ∶ T

_⊨s_≈_∶_ : Ctx -> Subst -> Subst -> Ctx -> Set
Γ ⊨s σ ≈ σ' ∶ Δ = Σ (⊨ Γ ctx) (λ vΓ → Σ (⊨ Δ ctx) (λ vΔ →
  ∀ {ρ ρ'} → (vρ : ρ ≈ ρ' ∈ ⟦ vΓ ⟧ctx) → ⟦ σ ⟧s ρ ≈⟦ σ' ⟧s ρ' ∈ ⟦ vΔ ⟧ctx))

_⊨s_∶_ : Ctx -> Subst -> Ctx -> Set
Γ ⊨s σ ∶ Δ    =    Γ ⊨s σ ≈ σ ∶ Δ
