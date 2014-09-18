module Resp where
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
open import Relation.Binary.PropositionalEquality
open import Sym

open SetF

_↔_ : (A B : Set) -> Set
A ↔ B = (A -> B) × (B -> A)

_⟶₂_ : ∀ {A : Set} (P Q : PREL A) -> Set
P ⟶₂ Q = ∀ a b -> P a b -> Q a b

_↔₂_ : ∀ {A : Set} (P Q : PREL A) -> Set
(P ↔₂ Q) = ∀ a b -> (P a b) ↔ (Q a b)

AppResp : ∀ {f a f' a' B B'} -> B ⟶₂ B' ->
    f · a ≈ f' · a' ∈App B
 -> f · a ≈ f' · a' ∈App B'
AppResp rB x = inj _ _ (_·_≈_·_∈App_.red1 x) (_·_≈_·_∈App_.red2 x) (rB _ _ (_·_≈_·_∈App_.rel x))

AppDeter :  ∀ {f1 a1 f2 a2 f3 a3 B B'} 
    (p : f1 · a1 ≈ f2 · a2 ∈App B)
    (q : f2 · a2 ≈ f3 · a3 ∈App B')
   -> _·_≈_·_∈App_.b2 p ≡ _·_≈_·_∈App_.b1 q
AppDeter p q = {!!}


-- TODO: Just do the twisted recursion scheme..
module Resp (k : ℕ) (akf : ∀ {j} -> j < k -> Acc j) where
 open SymF k akf

 resp : ∀ {A A' B' B}
   (p : A  ≈ A'  ∈ SetU' (inj akf))
   (h : A' ≡ B')
   (q : B'  ≈ B ∈ SetU' (inj akf))
  -> (ElU' _ p) ↔₂ (ElU' _ q)
 resp (Neu y) refl (Neu y') a b = (λ x → x) , (λ x → x)
 resp Nat refl Nat a b = (λ x → x) , (λ x → x)
 resp (Π pA y) refl (Π pA' y') a b with resp pA refl pA'
 ... | rpA = (λ x p →
      let p' = proj₂ (rpA _ _) p in
      -- TODO: Need to use symmetry somehow here..
      let q' = (_·_≈_·_∈App_.rel (y p')) in
      AppResp (λ a' b' x' →  proj₁ (resp q' {!!} (_·_≈_·_∈App_.rel (y' p)) _ _) x') (x p'))
 


    , (λ x p → {!!})
 -- copatterns would really help here...
 resp (Set* y) refl (Set* y') a b with ≤uniq y y'
 resp (Set* .y') refl (Set* y') a b | refl = (λ x → x) , (λ x → x)

 -- Πresp : ∀ {A A' A'' F F' F''} 
 --     (p : A  ≈ A'  ∈ SetU' (inj akf))
 --     (q : A' ≈ A'' ∈ SetU' (inj akf))
 --     (pF  : F ≈ F' ∈ ΠR (ElU' _ p) (λ _ -> (SetU' (inj akf))))
 --     (pF' : F' ≈ F'' ∈ ΠR (ElU' _ q) (λ _ -> (SetU' (inj akf))))
 --   -> (rA : ElU' _ p ↔₂ ElU' _ q)
 --   -> (∀ {a b} (p : ElU' _ p a b) -> ElU' _ (_·_≈_·_∈App_.rel (pF p)) ↔₂ ElU' _ (_·_≈_·_∈App_.rel (pF' (proj₁ (rA _ _) p))))
 --   -> (ΠR (ElU' _ p) (λ p → ElU' _ (_·_≈_·_∈App_.rel (pF p)))) ⟶₂ 
 --      (ΠR (ElU' _ q) (λ p → ElU' _ (_·_≈_·_∈App_.rel (pF' p))))
 -- Πresp pA qA pF pF' rA rF a b x p = {!proj₂ (rF ? _ _)!}