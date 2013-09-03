module comp-in-types where
open import FinMap public
open import Unit public
open import Data.Product public hiding (_×_)
open import Product public hiding (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality public hiding ([_])
open import Data.Empty public

* : Unitz
* = tt

mutual
 data tp (n : ctx Unit) : Set where
  Π : (T₁ : tp n) -> (T₂ : tp (n , *)) -> tp n
  _[_] ♯_[_] : (P : lftp n) -> (Ψ : tm n) -> tp n
  $_[_] $♯_[_] : (Ψ Φ : tm n) -> tp n

 data lftp (n : ctx Unit) : Set where

 data tm (n : ctx Unit) : Set where
  ▹ : (u : var n *) -> tm n
  ƛ : (E : tm (n , *)) -> tm n
  _·_ : (E₁ E₂ : tm n) -> tm n
  _[_] : (E : tm n) (σ : tm n) -> tm n
  ♯_[_] : (p : tm n) (π : tm n) -> tm n
  top : tm n
  ▸ : (p : tm n) -> tm n
--  pop : (x : tm n) -> tm n

data dctx : ctx Unitz -> Set where
 ⊡ : dctx ⊡
 _,_ : ∀ {n} -> (Γ : dctx n) -> tp n -> dctx (n , *)

data _∋_∶_ : ∀ {n} -> dctx n -> var n * -> tp n -> Set where
 top : ∀ {n} {Γ : dctx n} {A} -> (Γ , A) ∋ top ∶ {!!}
 pop : ∀ {n} {Γ : dctx n} {x} {A B} -> Γ ∋ x ∶ B -> (Γ , A) ∋ (pop x) ∶ {!!}

mutual
 data wfctx : ∀ {n} -> dctx n -> Set where
  ⊡ : wfctx ⊡
  _,_ : ∀ {n} {Γ : dctx n} -> wfctx Γ -> ∀ {A} -> Γ ⊢ A type -> wfctx (Γ , A)

 data _⊢_type {n} (Γ : dctx n) : tp n -> Set where
  Π : ∀ {A B} -> Γ ⊢ A type -> (Γ , A) ⊢ B type -> Γ ⊢ (Π A B) type

 data _⊢_∶_ {n} (Γ : dctx n) : tm n -> tp n -> Set where
  ▹ : ∀ {T x} -> Γ ⊢ T type -> Γ ∋ x ∶ T -> Γ ⊢ (▹ x) ∶ T
  ƛ : ∀ {T₁ T₂ E} -> Γ ⊢ T₁ type -> (Γ , T₁) ⊢ E ∶ T₂ -> Γ ⊢ (ƛ E) ∶ (Π T₁ T₂)
  _·_ : ∀ {T₁ T₂ E₁ E₂} -> Γ ⊢ E₁ ∶ (Π T₁ T₂) -> Γ ⊢ E₂ ∶ T₁ -> Γ ⊢ (E₁ · E₂) ∶ {!!} --([ N /x] B)
  _[_] : ∀ {P Ψ Φ E σ} -> Γ ⊢ E ∶ (P [ Ψ ]) -> Γ ⊢ σ ∶ ($ Ψ [ Φ ]) -> Γ ⊢ (E [ σ ]) ∶ ({!!} [ Φ ])
  ▸ : ∀ {p P Ψ} -> Γ ⊢ p ∶ (♯ P [ Ψ ]) -> Γ ⊢ (▸ p) ∶ (P [ Ψ ])
  
--  conv : ∀ {A B} {M} -> Γ ⊢ A type -> B ≈ A -> Γ ⊢ M ∶ B -> Γ ⊢ M ∶ A 
  
  
 
