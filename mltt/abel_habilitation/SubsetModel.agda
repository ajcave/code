module SubsetModel where
open import Syntax
open import SyntaxTm
open Syn Exp
open import Eval
open import Data.Product
open import Data.Unit
open import Data.Empty
open import Data.Nat hiding (pred)
open import WfNat
open import Relation.Binary.PropositionalEquality hiding ([_])

{-
 Develops the subset model, which we later use as a termination metric in the proof of transitivity
-}

PRED : Set -> Set₁
PRED α = α -> Set

VPRED = PRED Val

_∈₁_ : ∀ {α} -> α -> PRED α -> Set
a ∈₁ A = A a

⊤' : PRED Dnf
⊤' (↓[ A ] a)  = ∀ n → ∃ (λ v → Rnf n , a ∶ A ↘ v)

⊥' : PRED Dne
⊥' e = ∀ n → ∃ (λ u → Rne n , e ↘ u)

data NatP : VPRED where
 zero : zero ∈₁ NatP
 suc : ∀ {a} -> a ∈₁ NatP -> suc a ∈₁ NatP
 neu : ∀ {e} -> e ∈₁ ⊥' -> ↑[ Nat ] e ∈₁ NatP

EnvREL : Set₁
EnvREL = Env -> Env -> Set

record App₁ (B : VPRED) (c : ValApp) : Set where
 constructor inj
 field
  b : Val
  red : ValApp.f c · ValApp.a c  ↘ b
  pred : B b

AppDeter1 :  ∀ {f a B B'} 
    (p : (f · a) ∈₁ App₁ B)
    (q : (f · a) ∈₁ App₁ B')
   -> App₁.b p ≡ App₁.b q
AppDeter1 (inj b red pred)
          (inj b' red' pred') = app-deter red red'

ΠP : (A : VPRED) -> (∀ {a} -> A a -> VPRED) -> VPRED
ΠP A F f = ∀ {a} -> (p : A a) -> (f · a) ∈₁ (App₁ (F p))

data NeuPred : VPRED where
 inj : ∀ {e E} -> e ∈₁ ⊥' -> NeuPred (↑[ E ] e)

module SetPF (k : ℕ) (SetPrev : ∀ {j} -> j < k -> VPRED) where
 mutual
  data SetP : VPRED where
   Neu : ∀ {E} -> E ∈₁ ⊥' -> ↑[ Set* k ] E ∈₁ SetP
   Nat : Nat ∈₁ SetP
   Π : ∀ {A F} (pA : A ∈₁ SetP)
    -> (pF : F  ∈₁ ΠP (El₁ pA) (λ _ -> SetP))
    -> (Π A F) ∈₁ SetP
   Set* : ∀ {j} -> j < k -> Set* j ∈₁ SetP

  El₁ : ∀ {A} -> A ∈₁ SetP -> VPRED
  El₁ (Neu {E} x) = NeuPred
  El₁ Nat = NatP
  El₁ (Π pA pF) = ΠP (El₁ pA) (λ p → El₁ (App₁.pred (pF p)))
  El₁ (Set* j<k) = SetPrev j<k

SetU₁' : {n : ℕ} -> Acc n -> VPRED
SetU₁' {n} (inj f) = SetPF.SetP n (λ p → SetU₁' (f p))

SetU₁ : ℕ -> VPRED
SetU₁ n = SetU₁' (nat-acc {n})

Type₁ : VPRED
Type₁ A = ∃ (λ n → SetU₁ n A)

ElU₁' : {n : ℕ} (p : Acc n) -> ∀ {A} -> A ∈₁ (SetU₁' p) -> VPRED
ElU₁' {n} (inj p) = SetPF.El₁ n (λ q → SetU₁' (p q))

ElU₁ : (n : ℕ) -> ∀ {A} -> A ∈₁ (SetU₁ n) -> VPRED
ElU₁ n = ElU₁' (nat-acc {n})
