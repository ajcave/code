module predicative where
open import Data.Unit
open import Data.Product
open import Data.Nat

data Univ : Set where
 ⋆₀ ⋆₁ : Univ

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


 