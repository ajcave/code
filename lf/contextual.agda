module contextual where
open import Level
open import Unit
open import FinMap

schema-ctx = ctx Unitz

* : Unitz
* = tt

data tp : Set where
 i : tp
 _⇒_ : (A B : tp) -> tp

data tctx (Ω : schema-ctx) : Set where
 ⊡ : tctx Ω
 ▹ : (φ : var Ω *) -> tctx Ω
 _,_ : (Ψ : tctx Ω) -> tp -> tctx Ω

data tvar {Ω : schema-ctx} : ∀ (Γ : tctx Ω) (T : tp) -> Set where
 top : ∀ {Γ T} -> tvar (Γ , T) T
 pop : ∀ {Γ T S} -> (x : tvar Γ T) -> tvar (Γ , S) T

data ctp (Ω : schema-ctx) : Set where
 $ : (Ψ : tctx Ω) -> ctp Ω
 ♯ : (A : tp) -> ctp Ω
 % : (A : tp) -> ctp Ω

record mtp (Ω : schema-ctx) : Set where
 constructor _[_]
 field
  dom : ctp Ω
  ran : tctx Ω

mctx : schema-ctx -> Set
mctx Ω = ctx (mtp Ω)

-- POPL'08: Concatenating φ , Ψ is wrong because Ψ can't start with a variable
_<<_ : ∀ {Ω} -> tctx Ω -> ctx tp -> tctx Ω
Ψ₁ << ⊡ = Ψ₁
Ψ₁ << (Ψ₂ , T) = (Ψ₁ << Ψ₂) , T

mutual
 data rtm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ▹ : ∀ {A} (x : tvar Ψ A) -> rtm Δ Ψ A
  _[_] : ∀ {A Φ} (u : var Δ (% A [ Φ ])) (σ : sub Δ Ψ Φ) -> rtm Δ Ψ A
  ♯_[_] : ∀ {A Φ} (p : var Δ (♯ A [ Φ ])) (σ : sub Δ Ψ Φ) -> rtm Δ Ψ A
  _·_ : ∀ {A B} (R : rtm Δ Ψ (A ⇒ B)) (N : rtm Δ Ψ A) -> rtm Δ Ψ B
 data ntm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ƛ : ∀ {A B} (N : ntm Δ (Ψ , A) B) -> ntm Δ Ψ (A ⇒ B)
  ▸ : rtm Δ Ψ i -> ntm Δ Ψ i 
 data sub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  ⊡ : ∀ {Ψ} -> sub Δ Ψ ⊡
  _,_ : ∀ {Ψ Φ A} (σ : sub Δ Ψ Φ) (N : ntm Δ Ψ A) -> sub Δ Ψ (Φ , A)
-- POPL'08: Pretty sure this should allow weakening, s :: (Φ₁ << Φ₁')[Φ₂]
-- produces sub Δ Ψ Φ₁
  _[_] : ∀ {Ψ Φ₁ Φ₂} (s : var Δ ($ Φ₁ [ Φ₂ ])) (ρ : sub Δ Ψ Φ₂) -> sub Δ Ψ Φ₁
  id : ∀ {φ Ψ} -> sub Δ ((▹ φ) << Ψ) (▹ φ)


  

  
 