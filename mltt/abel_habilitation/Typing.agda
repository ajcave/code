module Typing where
open import SyntaxTm
open import Data.Nat

data _∋_∶_ : Ctx -> ℕ -> Exp -> Set where
 top : ∀ {Γ A} -> (Γ , A) ∋ zero ∶ (A [ ↑ ])
 pop : ∀ {Γ A B x} -> Γ ∋ x ∶ A -> (Γ , B) ∋ x ∶ (A [ ↑ ]) 

mutual
 data _⊢ctx : Ctx -> Set where
  ⊡ : ⊡ ⊢ctx
  _,_ : ∀ {Γ A} -> Γ ⊢ A type -> (Γ , A) ⊢ctx

 data _⊢_type (Γ : Ctx) (A : Exp) : Set where
  inj : ∀ {i} -> Γ ⊢ A ≈ A ∶ Set* i -> Γ ⊢ A type

 data _⊢_≈_∶_ (Γ : Ctx) : Exp -> Exp -> Exp -> Set where
  sym : ∀ {t t' A} -> Γ ⊢ t ≈ t' ∶ A -> Γ ⊢ t' ≈ t ∶ A
  trans : ∀ {t t' t'' A} -> Γ ⊢ t ≈ t' ∶ A -> Γ ⊢ t' ≈ t'' ∶ A -> Γ ⊢ t ≈ t'' ∶ A
  Nat : ∀ {i} -> Γ ⊢ctx -> Γ ⊢ Nat ≈ Nat ∶ Set* i
  zero : Γ ⊢ctx -> Γ ⊢ zero ≈ zero ∶ Nat
  suc : ∀ {t t'} -> Γ ⊢ t ≈ t' ∶ Nat -> Γ ⊢ suc t ≈ suc t' ∶ Nat
  Set* : ∀ {i} -> Γ ⊢ Set* i ≈ Set* i ∶ Set* (suc i)
  idx : ∀ {x A} -> Γ ⊢ctx -> Γ ∋ x ∶ A -> Γ ⊢ (idx x) ≈ (idx x) ∶ A
  rec :  ∀ {T ts tz tn tn' i}
       -> (⊡ , Nat) ⊢ T ≈ T ∶ Set* i
       -> ⊡ ⊢ tz ≈ tz ∶ T [ ⊡ , zero ]
       -> ((⊡ , Nat) , T) ⊢ ts ≈ ts ∶ T [ ⊡ , suc (idx 1) ]
       -> Γ ⊢ tn ≈ tn' ∶ Nat
       -> Γ ⊢ rec T tz ts tn ≈ rec T tz ts tn' ∶ T [ ⊡ , tn ]
       -- Note that we don't have congruence under T, tz, and ts.
       -- We treat them like opaque definitions with closed bodies
  _·_ : ∀ {r r' s s' A B} -> Γ ⊢ r ≈ r' ∶ Π A (ƛ B) -> Γ ⊢ s ≈ s' ∶ A
        -> Γ ⊢ r · s ≈ r' · s' ∶ B [ id , s ]
  ƛ : ∀ {t t' A B} -> (Γ , A) ⊢ t ≈ t' ∶ B -> Γ ⊢ (ƛ t) ≈ (ƛ t') ∶ Π A (ƛ B)
  Π : ∀ {A A' B B' i} -> Γ ⊢ A ≈ A' ∶ Set* i -> (Γ , A) ⊢ B ≈ B' ∶ Set* i
      -> Γ ⊢ Π A (ƛ B) ≈ Π A' (ƛ B') ∶ Set* i
  _[_] : ∀ {Δ t t' σ σ' A} -> Δ ⊢ t ≈ t' ∶ A -> Γ ⊢s σ ≈ σ' ∶ Δ
      -> Γ ⊢ t [ σ ] ≈ t' [ σ' ] ∶ A [ σ ]
  conv : ∀ {t t' A A' i} -> Γ ⊢ t ≈ t' ∶ A -> Γ ⊢ A ≈ A' ∶ Set* i -> Γ ⊢ t ≈ t' ∶ A'
  sub : ∀ {A A' i j} -> Γ ⊢ A ≈ A' ∶ Set* i -> i ≤ j -> Γ ⊢ A ≈ A' ∶ Set* j
  funβ : ∀ {A B t t' s s'} ->  (Γ , A) ⊢ t ≈ t' ∶ B -> Γ ⊢ s ≈ s' ∶ A
         -> Γ ⊢ (ƛ t) · s ≈ t' [ id , s' ] ∶ B [ id , s ]
  funη : ∀ {A B t t'} -> Γ ⊢ t ≈ t' ∶ Π A (ƛ B)
         -> Γ ⊢ t ≈ ƛ (t' [ ↑ ] · idx 0) ∶ Π A (ƛ B)
  rec-zero : ∀ {T ts tz tz' i} 
       -> (⊡ , Nat) ⊢ T ≈ T ∶ Set* i
       -> ⊡ ⊢ tz ≈ tz' ∶ T [ ⊡ , zero ]
       -> ((⊡ , Nat) , T) ⊢ ts ≈ ts ∶ T [ ⊡ , suc (idx 1) ]
       -> Γ ⊢ rec T tz ts zero ≈ (tz' [ ⊡ ]) ∶ T [ ⊡ , zero ]
  rec-suc : ∀ {T i tz ts tn tn'} -> (⊡ , Nat) ⊢ T ≈ T ∶ Set* i
       -> ⊡ ⊢ tz ≈ tz ∶ T [ ⊡ , zero ]
       -> ((⊡ , Nat) , T) ⊢ ts ≈ ts ∶ T [ ⊡ , suc (idx 1) ]
       -> Γ ⊢ tn ≈ tn' ∶ Nat
       -> Γ ⊢ rec T tz ts (suc tn) ≈ ts [ (⊡ , tn') , (rec T tz ts tn') ] ∶ T [ ⊡ , suc tn ]
  sub-id : ∀ {t t' A} -> Γ ⊢ t ≈ t' ∶ A -> Γ ⊢ t [ id ] ≈ t' ∶ A
  sub-comp : ∀ {t t' σ σ' τ τ' A Δ Δ'}
       -> Δ' ⊢ t ≈ t' ∶ A -> Δ ⊢s σ ≈ σ' ∶ Δ' -> Γ ⊢s τ ≈ τ' ∶ Δ
       -> Γ ⊢ t [ σ [ τ ] ] ≈ (t' [ σ' ]) [ τ' ] ∶ A [ σ [ τ ] ]
  sub-zero : ∀ {σ σ' Δ} -> Γ ⊢s σ ≈ σ' ∶ Δ -> Γ ⊢ zero [ σ ] ≈ zero ∶ Nat
  sub-suc : ∀ {σ σ' t t' Δ} -> Γ ⊢s σ ≈ σ' ∶ Δ -> Δ ⊢ t ≈ t' ∶ Nat
     -> Γ ⊢ (suc t) [ σ ] ≈ suc (t' [ σ' ]) ∶ Nat
  sub-Nat : ∀ {σ σ' Δ i} -> Γ ⊢s σ ≈ σ' ∶ Δ -> Γ ⊢ Nat [ σ ] ≈ Nat ∶ Set* i
  sub-Set : ∀ {σ σ' Δ i} -> Γ ⊢s σ ≈ σ' ∶ Δ -> Γ ⊢ (Set* i) [ σ ] ≈ Set* i ∶ Set* (suc i)
  sub-ƛ : ∀ {σ σ' Δ t t' A B} -> Γ ⊢s σ ≈ σ' ∶ Δ -> (Δ , A) ⊢ t ≈ t' ∶ B
     -> Γ ⊢ (ƛ t) [ σ ] ≈ ƛ (t' [ σ' [ ↑ ] , idx 0 ]) ∶ (Π A (ƛ B)) [ σ ]
  sub-rec : ∀ {Δ T tz ts tn tn' σ σ' i}
       -> (⊡ , Nat) ⊢ T ≈ T ∶ Set* i
       -> ⊡ ⊢ tz ≈ tz ∶ T [ ⊡ , zero ]
       -> ((⊡ , Nat) , T) ⊢ ts ≈ ts ∶ T [ ⊡ , suc (idx 1) ]
       -> Δ ⊢ tn ≈ tn' ∶ Nat
       -> Γ ⊢s σ ≈ σ' ∶ Δ
       -> Γ ⊢ (rec T tz ts tn) [ σ ] ≈ rec T tz ts (tn' [ σ' ]) ∶ (T [ ⊡ , tn ]) [ σ ]
  sub-idx-top : ∀ {Δ σ σ' t T} -> Γ ⊢s σ ≈ σ' , t ∶ (Δ , T)
    -> Γ ⊢ (idx 0) [ σ ] ≈ t ∶ T [ σ' ] -- Maybe this isn't the most typical way to represent these rules
  sub-idx-pop : ∀ {Δ σ σ' A B x t}
    -> Γ ⊢s σ ≈ σ' , t ∶ (Δ , B)
    -> Δ ∋ x ∶ A
    -> Γ ⊢ (idx (suc x)) [ σ ] ≈ (idx x) [ σ' ] ∶ A [ σ' ]
  sub-· : ∀ {Δ σ σ' r r' s s' A B}
    -> Γ ⊢s σ ≈ σ' ∶ Δ
    -> Δ ⊢ r ≈ r' ∶ Π A (ƛ B)
    -> Δ ⊢ s ≈ s' ∶ A
    -> Γ ⊢ (r · s) [ σ ] ≈ (r' [ σ' ]) · (s' [ σ' ]) ∶ B [ σ , s [ σ ] ]
  sub-Π : ∀ {Δ σ σ' A A' B B' i}
    -> Γ ⊢s σ ≈ σ' ∶ Δ
    -> Δ ⊢ A ≈ A' ∶ Set* i
    -> (Δ , A) ⊢ B ≈ B' ∶ Set* i
    -> Γ ⊢ (Π A (ƛ B)) [ σ ] ≈ Π (A' [ σ' ]) (ƛ (B' [ σ' [ ↑ ] , idx 0 ])) ∶ Set* i
  -- What about context conversion? I guess it's admissible.

 data _⊢s_≈_∶_ : (Γ : Ctx) -> Subst -> Subst -> Ctx -> Set where
  sym : ∀ {Γ σ σ' Δ} -> Γ ⊢s σ ≈ σ' ∶ Δ -> Γ ⊢s σ' ≈ σ ∶ Δ
  trans : ∀ {Γ σ σ' σ'' Δ} -> Γ ⊢s σ ≈ σ' ∶ Δ -> Γ ⊢s σ' ≈ σ'' ∶ Δ -> Γ ⊢s σ ≈ σ'' ∶ Δ
  ⊡ : ∀ {Γ} -> Γ ⊢ctx -> Γ ⊢s ⊡ ≈ ⊡ ∶ ⊡
  id : ∀ {Γ} -> Γ ⊢ctx -> Γ ⊢s id ≈ id ∶ Γ
  ↑ : ∀ {Γ A} -> Γ ⊢ A type -> (Γ , A) ⊢s ↑ ≈ ↑ ∶ Γ
  _[_] : ∀ {Γ Δ Δ' σ σ' τ τ'} -> Δ' ⊢s σ ≈ σ' ∶ Δ -> Γ ⊢s τ ≈ τ' ∶ Δ'
         -> Γ ⊢s σ [ τ ] ≈ σ' [ τ' ] ∶ Δ
  _,_ : ∀ {Γ Δ σ σ' t t' A} -> Δ ⊢ A type -> Γ ⊢s σ ≈ σ' ∶ Δ -> Γ ⊢ t ≈ t' ∶ A [ σ ]
         -> Γ ⊢s σ , t ≈ σ' , t' ∶ (Δ , A)
  idL : ∀ {Γ Δ σ σ'} -> Γ ⊢s σ ≈ σ' ∶ Δ -> Γ ⊢s id [ σ ] ≈ σ' ∶ Δ
  idR : ∀ {Γ Δ σ σ'} -> Γ ⊢s σ ≈ σ' ∶ Δ -> Γ ⊢s σ [ id ] ≈ σ' ∶ Δ
  assoc : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ σ1 σ1' σ2 σ2' σ3 σ3'}
   -> Γ₃ ⊢s σ1 ≈ σ1' ∶ Γ₄ 
   -> Γ₂ ⊢s σ2 ≈ σ2' ∶ Γ₃
   -> Γ₁ ⊢s σ3 ≈ σ3' ∶ Γ₂
   -> Γ₁ ⊢s (σ1 [ σ2 ]) [ σ3 ] ≈ σ1' [ σ2' [ σ3' ] ] ∶ Γ₄
  ⊡η : ∀ {Γ σ σ' τ τ'} -> Γ ⊢s σ ≈ τ ∶ ⊡ -> Γ ⊢s σ' ≈ τ' ∶ ⊡ -> Γ ⊢s σ ≈ σ' ∶ ⊡
  ×η : ∀ {Γ σ σ' Δ A}
   -> Γ ⊢s σ ≈ σ' ∶ (Δ , A)
   -> Γ ⊢s σ ≈ (↑ [ σ' ] , idx 0) ∶ (Δ , A) 
  compβ : ∀ {Γ Δ A σ σ' t}
   -> Γ ⊢s σ ≈ σ' , t ∶ (Δ , A)
   -> Γ ⊢s ↑ [ σ ] ≈ σ' ∶ Δ
  comp-, : ∀ {Γ Δ Δ' A σ σ' t t' τ τ'}
   -> Δ' ⊢s σ ≈ σ' ∶ Δ
   -> Δ' ⊢  t ≈ t' ∶ A [ σ ]
   -> Γ  ⊢s τ ≈ τ' ∶ Δ'
   -> Γ ⊢s (σ , t) [ τ ] ≈ σ' [ τ' ] , t' [ τ' ] ∶ (Δ , A)
  
  
  -- No conversion rule? Does it matter?

  