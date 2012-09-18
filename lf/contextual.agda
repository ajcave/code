module contextual where
open import Level
open import Unit
open import FinMap
open import Relation.Binary.PropositionalEquality hiding ([_])

schema-ctx = ctx Unitz

* : Unitz
* = tt

data tp : Set where
 i : tp
 _⇒_ : (A B : tp) -> tp

data tctx (Ω : schema-ctx) : Set where
 ⊡ : tctx Ω
 ▹ : (φ : var Ω *) -> tctx Ω
 _,_ : (Ψ : tctx Ω) -> (A : tp) -> tctx Ω

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
  _♯[_] : ∀ {A Φ} (p : var Δ (♯ A [ Φ ])) (σ : sub Δ Ψ Φ) -> rtm Δ Ψ A
  _·_ : ∀ {A B} (R : rtm Δ Ψ (A ⇒ B)) (N : ntm Δ Ψ A) -> rtm Δ Ψ B
 data ntm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ƛ : ∀ {A B} (N : ntm Δ (Ψ , A) B) -> ntm Δ Ψ (A ⇒ B)
  ▸ : (R : rtm Δ Ψ i) -> ntm Δ Ψ i 
 data sub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  ⊡ : ∀ {Ψ} -> sub Δ Ψ ⊡
  -- POPL'08: Also we do η-expansions instead of allow both N and R
  _,_ : ∀ {Ψ Φ A} (σ : sub Δ Ψ Φ) (N : ntm Δ Ψ A) -> sub Δ Ψ (Φ , A)
-- POPL'08: Pretty sure this should allow weakening, s :: (Φ₁ << Φ₁')[Φ₂]
-- produces sub Δ Ψ Φ₁
-- POPL'08: Also problem: These need to be normal in that if the range is Ψ , x : A, it needs to be split as a _,_. Maybe this solves the above issue? I guess the analogue is that when we *use* a substitution variable it has to be at "atomic" type? Also we need to identity ⊡ and substitution variables with range ⊡
  _[_] : ∀ {Ψ Φ₁ Φ₂} (s : var Δ ($ Φ₁ [ Φ₂ ])) (ρ : sub Δ Ψ Φ₂) -> sub Δ Ψ Φ₁
  id : ∀ {Ψ φ} -> sub Δ ((▹ φ) << Ψ) (▹ φ)

⟦_⟧tc : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (Φ : tctx Ω₁) -> tctx Ω₂
⟦_⟧tc Ψs ⊡ = ⊡
⟦_⟧tc Ψs (▹ φ) = lookup Ψs φ
⟦_⟧tc Ψs (Φ , A) = ⟦ Ψs ⟧tc Φ , A

⟦⟧tc-<< : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) Φ₁ Φ₂
 -> ⟦ Ψs ⟧tc (Φ₁ << Φ₂) ≡ ((⟦ Ψs ⟧tc Φ₁) << Φ₂)
⟦⟧tc-<< Ψs Φ₁ ⊡ = refl
⟦⟧tc-<< Ψs Φ₁ (ψ , T) = cong (λ α → α , T) (⟦⟧tc-<< Ψs Φ₁ ψ)

⟦_⟧mt : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (U : mtp Ω₁) -> mtp Ω₂
⟦_⟧mt Ψs ($ Ψ [ Φ ]) = $ (⟦ Ψs ⟧tc Ψ) [ ⟦ Ψs ⟧tc Φ ]
⟦_⟧mt Ψs ((♯ A) [ Φ ]) = (♯ A) [ ⟦ Ψs ⟧tc Φ ]
⟦_⟧mt Ψs (% A [ Φ ]) = % A [ ⟦ Ψs ⟧tc Φ ]

⟦_⟧mc : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (Δ : mctx Ω₁) -> mctx Ω₂
⟦_⟧mc Ψs Δ = cmap ⟦ Ψs ⟧mt Δ

⟦_⟧tv : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Φ : tctx Ω₁} {A} -> tvar Φ A -> tvar (⟦ Ψs ⟧tc Φ) A
⟦_⟧tv Ψs top = top
⟦_⟧tv Ψs (pop x) = pop (⟦ Ψs ⟧tv x)

η-expand : ∀ {A} {Ω} {Δ : mctx Ω} {Ψ} -> rtm Δ Ψ A -> ntm Δ Ψ A
η-expand {i} R = ▸ R
η-expand {A ⇒ B} R = ƛ (η-expand ({!!} · η-expand (▹ top)))

id-subst : ∀ {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) -> sub Δ Ψ Ψ
id-subst Δ ⊡ = ⊡
id-subst Δ (▹ φ) = id {Ψ = ⊡}
id-subst Δ (Ψ , A) = {!!} , η-expand (▹ top)

mutual
 ⟦_⟧cr : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Δ : mctx Ω₁} {Ψ} {A}
   -> (R : rtm Δ Ψ A) -> rtm (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) A
 ⟦_⟧cr Ψs (▹ x) = ▹ (⟦ Ψs ⟧tv x)
 ⟦_⟧cr Ψs (u [ σ ]) = cmap-var ⟦ Ψs ⟧mt u [ ⟦ Ψs ⟧cs σ ]
 ⟦_⟧cr Ψs (p ♯[ σ ]) = cmap-var ⟦ Ψs ⟧mt p ♯[ ⟦ Ψs ⟧cs σ ]
 ⟦_⟧cr Ψs (R · N) = (⟦ Ψs ⟧cr R) · ⟦ Ψs ⟧cn N

 ⟦_⟧cn : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Δ : mctx Ω₁} {Ψ} {A}
   -> (N : ntm Δ Ψ A) -> ntm (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) A
 ⟦_⟧cn Ψs (ƛ N) = ƛ (⟦ Ψs ⟧cn N)
 ⟦_⟧cn Ψs (▸ R) = ▸ (⟦ Ψs ⟧cr R)

 ⟦_⟧cs : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Δ : mctx Ω₁} {Ψ} {Φ}
   -> (σ : sub Δ Ψ Φ) -> sub (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) (⟦ Ψs ⟧tc Φ)
 ⟦_⟧cs Ψs ⊡ = ⊡
 ⟦_⟧cs Ψs (σ , N) = (⟦ Ψs ⟧cs σ) , (⟦ Ψs ⟧cn N)
 ⟦_⟧cs Ψs (s [ ρ ]) = cmap-var ⟦ Ψs ⟧mt s [ ⟦ Ψs ⟧cs ρ ]
 ⟦_⟧cs Ψs (id {φ = φ}) with id-subst {!!} (lookup Ψs φ)
 ... | q = {!!}