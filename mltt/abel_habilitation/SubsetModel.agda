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

_∈_ : ∀ {α} -> α -> PRED α -> Set
a ∈ A = A a

⊤' : PRED Dnf
⊤' (↓[ A ] a)  = ∀ n → ∃ (λ v → Rnf n , a ∶ A ↘ v)

⊥' : PRED Dne
⊥' e = ∀ n → ∃ (λ u → Rne n , e ↘ u)

data NatP : VPRED where
 zero : zero ∈ NatP
 suc : ∀ {a a'} -> a ∈ NatP -> suc a ∈ NatP
 neu : ∀ {e e'} -> e ∈ ⊥' -> ↑[ Nat ] e ∈ NatP

EnvREL : Set₁
EnvREL = Env -> Env -> Set

record ValApp : Set where
 constructor _·_
 field
  f : Val
  a : Val

record App (B : VPRED) (c : ValApp) : Set where
 constructor inj
 field
  b : Val
  red : ValApp.f c · ValApp.a c  ↘ b
  pred : B b

AppDeter1 :  ∀ {f a B B'} 
    (p : (f · a) ∈ App B)
    (q : (f · a) ∈ App B')
   -> App.b p ≡ App.b q
AppDeter1 (inj b red pred)
          (inj b' red' pred') = app-deter red red'

ΠP : (A : VPRED) -> (∀ {a} -> A a -> VPRED) -> VPRED
ΠP A F f = ∀ {a} -> (p : A a) -> (f · a) ∈ (App (F p))

data NeuPred : VPRED where
 inj : ∀ {e E} -> e ∈ ⊥' -> NeuPred (↑[ E ] e)

module SetF (k : ℕ) (SetPrev : ∀ {j} -> j < k -> VPRED) where
 mutual
  data SetP : VPRED where
   Neu : ∀ {E} -> E ∈ ⊥' -> ↑[ Set* k ] E ∈ SetP
   Nat : Nat ∈ SetP
   Π : ∀ {A F} (pA : A ∈ SetP)
    -> (pF : F  ∈ ΠP (El pA) (λ _ -> SetP))
    -> (Π A F) ∈ SetP
   Set* : ∀ {j} -> j < k -> Set* j ∈ SetP

  El : ∀ {A} -> A ∈ SetP -> VPRED
  El (Neu {E} x) = NeuPred
  El Nat = NatP
  El (Π pA pF) = ΠP (El pA) (λ p → El (App.pred (pF p)))
  El (Set* j<k) = SetPrev j<k

SetU' : {n : ℕ} -> Acc n -> VPRED
SetU' {n} (inj f) = SetF.SetP n (λ p → SetU' (f p))

SetU : ℕ -> VPRED
SetU n = SetU' (nat-acc {n})

Type : VPRED
Type A = ∃ (λ n → SetU n A)

ElU' : {n : ℕ} (p : Acc n) -> ∀ {A} -> A ∈ (SetU' p) -> VPRED
ElU' {n} (inj p) = SetF.El n (λ q → SetU' (p q))

ElU : (n : ℕ) -> ∀ {A} -> A ∈ (SetU n) -> VPRED
ElU n = ElU' (nat-acc {n})
