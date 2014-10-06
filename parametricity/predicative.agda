module predicative where
open import Data.Unit
open import Data.Product
open import Data.Nat

record ⊤₁ : Set₁ where
 constructor tt

data Ctx (A : Set) : Set where
 ⊡ : Ctx A
 _,_ : (Γ : Ctx A) -> (T : A) -> Ctx A

data Var {A : Set} : (Γ : Ctx A) -> (T : A) -> Set where
 top : ∀ {Γ T} -> Var (Γ , T) T
 pop : ∀ {Γ T S} (x : Var Γ T) -> Var (Γ , S) T

data lvl : Set where
 ₀ ₁ : lvl

mutual
 data tp (Δ : Ctx ⊤) : lvl -> Set where
  ▹ : (X : Var Δ _) -> tp Δ ₀
  _⇒_ : ∀ {i} -> (T S : tp Δ i) -> tp Δ i
  _[_] : ∀ {i Δ'} (T : tp Δ' i) -> (η : tpenv Δ Δ') -> tp Δ i
  ∃̂ ∀̂ : (T : tp (Δ , _) ₀) -> tp Δ ₁

 data tpenv : (Δ₁ Δ₂ : Ctx ⊤) -> Set where
  ⊡ : ∀ {Δ₁} -> tpenv Δ₁ ⊡
  _,_ : ∀ {Δ₁ Δ₂} -> tpenv Δ₁ Δ₂ -> tp Δ₁ ₀ -> tpenv Δ₁ (Δ₂ , _)
  ↑ : ∀ {Δ₁} -> tpenv (Δ₁ , _) Δ₁
  id : ∀ {Δ} -> tpenv Δ Δ

data tm : Set where
 ▹ : (x : ℕ) -> tm
 ƛ : (t : tm) -> tm
 _·_ : (t s : tm) -> tm
 letpack : (t s : tm) -> tm

mutual
 data val : Set where
  ƛ_[_]' : (t : tm) -> (ρ : env) -> val
 
 data env : Set where
  ⊡ : env
  _,_ : (ρ : env) -> (v : val) -> env

data comp : Set where
 _[_] : (t : tm) (ρ : env) -> comp
 _·_ : (u v : val) -> comp

data lookup : env -> ℕ -> val -> Set where
 top : ∀ {ρ v} -> lookup (ρ , v) 0 v
 pop : ∀ {ρ n u v} -> lookup ρ n v -> lookup (ρ , u) (suc n) v

data _⇓_ : comp -> val -> Set where
 ▹ : ∀ {ρ x v} -> lookup ρ x v -> (▹ x) [ ρ ] ⇓ v
 ƛ : ∀ {t ρ} -> ((ƛ t) [ ρ ]) ⇓ (ƛ t [ ρ ]')
 _·_ : ∀ {t s u v w ρ} -> t [ ρ ] ⇓ u -> s [ ρ ] ⇓ v -> (u · v) ⇓ w -> (t · s) [ ρ ] ⇓ w
 letpack : ∀ {t s ρ u v} -> t [ ρ ] ⇓ u -> s [ ρ , u ] ⇓ v -> (letpack t s) [ ρ ] ⇓ v
 apλ : ∀ {t ρ u v} -> t [ ρ , u ] ⇓ v -> ((ƛ t [ ρ ]') · u) ⇓ v

data TCtx (Δ : Ctx ⊤) : Set where
 ⊡ : TCtx Δ
 _,_ : ∀ {i} (Γ : TCtx Δ) -> (T : tp Δ i) -> TCtx Δ

data lookupt {Δ} : (Γ : TCtx Δ) -> ℕ -> ∀ {i} -> tp Δ i -> Set where
 top : ∀ {Γ i} {T : tp Δ i} -> lookupt (Γ , T) 0 T
 pop : ∀ {Γ n} {i j} {T : tp Δ i} {S : tp Δ j} -> lookupt Γ n T -> lookupt (Γ , S) (suc n) T

↑c : ∀ {Δ} (Γ : TCtx Δ) -> TCtx (Δ , _)
↑c ⊡ = ⊡
↑c (Γ , T) = (↑c Γ) , (T [ ↑ ])

data _,_⊢_∶_ (Δ : Ctx ⊤) (Γ : TCtx Δ) : ∀ {i} -> tm -> tp Δ i -> Set where
 ▹ : ∀ {i x} {T : tp Δ i} -> lookupt Γ x T -> Δ , Γ ⊢ ▹ x ∶ T
 _·_ : ∀ {t s i} {T S : tp Δ i} -> Δ , Γ ⊢ t ∶ (T ⇒ S) -> Δ , Γ ⊢ s ∶ T -> Δ , Γ ⊢ t · s ∶ S
 ƛ : ∀ {t i} {T S : tp Δ i} -> Δ , (Γ , T) ⊢ t ∶ S -> Δ , Γ ⊢ ƛ t ∶ (T ⇒ S)
 ∀I : ∀ {t T} -> (Δ , _) , (↑c Γ) ⊢ t ∶ T -> Δ , Γ ⊢ t ∶ ∀̂ T
 ∀E : ∀ {t T} -> Δ , Γ ⊢ t ∶ ∀̂ T -> (S : tp Δ ₀) -> Δ , Γ ⊢ t ∶ (T [ id , S ])
 ∃I : ∀ {t T} -> (S : tp Δ ₀) -> Δ , Γ ⊢ t ∶ (T [ id , S ]) -> Δ , Γ ⊢ t ∶ (∃̂ T)
 ∃E : ∀ {t s T i} {C : tp Δ i} -> Δ , Γ ⊢ t ∶ (∃̂ T)
                 -> (Δ , _) , ((↑c Γ) , T) ⊢ s ∶ (C [ ↑ ])
                 -> Δ , Γ ⊢ letpack t s ∶ C

open import Level

REL : ∀ {l} -> (A : Set) -> Set (Level.suc l)
REL {l} A = A -> A -> Set l

VREL : ∀ {l} -> Set (Level.suc l)
VREL = REL val

-- data Lift (R : VREL) : VREL₁ where
--  inj : ∀ {v1 v2} -> R v1 v2 -> Lift R v1 v2

D[_] : Ctx ⊤ -> Set₁
D[ Δ ] = Var Δ _ -> VREL

_,,_ : ∀ {Δ} -> D[ Δ ] -> VREL -> D[ Δ , _ ]
_,,_ η R top = R
_,,_ η R (pop X) = η X

⊡' : D[ ⊡ ]
⊡' ()

open import Function

⟦_⟧ : lvl -> Level
⟦ ₀ ⟧ = Level.zero
⟦ ₁ ⟧ = Level.suc Level.zero

record Clo {l} (R : REL {l} val) (c1 c2 : comp) : Set l where
 field
  red1 : ∃ (λ v1 -> c1 ⇓ v1)
  red2 : ∃ (λ v2 -> c2 ⇓ v2)
  rel : R (proj₁ red1) (proj₁ red2)

mutual
 V[_] : ∀ {Δ i} -> tp Δ i -> D[ Δ ] -> VREL {⟦ i ⟧}
 V[ ▹ X ] η = η X
 V[ T ⇒ T₁ ] η v1 v2 = ∀ {u1 u2} → V[ T ] η u1 u2 → Clo (V[ T₁ ] η) (v1 · u1) (v2 · u2)
 V[ T [ η ] ] η₁ = V[ T ] (VS[ η ] η₁)
 V[ ∃̂ T ] η v1 v2 = ∃ (λ R → V[ T ] (η ,, R) v1 v2)
 V[ ∀̂ T ] η v1 v2 = ∀ R -> V[ T ] (η ,, R) v1 v2

 VS[_] : ∀ {Δ Δ'} -> tpenv Δ Δ' -> D[ Δ ] -> D[ Δ' ]
 VS[ ⊡ ] η' = ⊡'
 VS[ η , T ] η' = (VS[ η ] η') ,, (V[ T ] η')
 VS[ ↑ ] η' = η' ∘ pop
 VS[ id ] η' = η'


 