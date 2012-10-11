module contextual-concat-spine where
open import Level
open import Unit
open import FinMap
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])

schema-ctx = ctx Unitz

* : Unitz
* = tt

data tp : Set where
 i : tp
 _⇒_ : (A B : tp) -> tp

data tctx-elt (Ω : schema-ctx) : Set where
 ▹ : (φ : var Ω *) -> tctx-elt Ω
 ▸ : (A : tp) -> tctx-elt Ω

data tctx (Ω : schema-ctx) : Set where
 ⊡ : tctx Ω
 _,_ : (Ψ : tctx Ω) -> (A : tctx-elt Ω) -> tctx Ω

data tvar {Ω : schema-ctx} : ∀ (Γ : tctx Ω) (T : tp) -> Set where
 top : ∀ {Γ T} -> tvar (Γ , (▸ T)) T
 pop : ∀ {Γ T S} -> (x : tvar Γ T) -> tvar (Γ , S) T

data cvar {Ω : schema-ctx} : ∀ (Γ : tctx Ω) (φ : var Ω *) -> Set where
 top : ∀ {Γ φ} -> cvar (Γ , (▹ φ)) φ
 pop : ∀ {Γ φ S} -> (xs : cvar Γ φ) -> cvar (Γ , S) φ

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

_<<_ : ∀ {Ω} -> tctx Ω -> tctx Ω -> tctx Ω
Ψ₁ << ⊡ = Ψ₁
Ψ₁ << (Ψ , A) = (Ψ₁ << Ψ) , A

infixr 10 _<<_

<<-assoc : ∀ {Ω} (Ψ₁ Ψ₂ Ψ₃ : tctx Ω) -> (Ψ₁ << Ψ₂) << Ψ₃ ≡ Ψ₁ << (Ψ₂ << Ψ₃)
<<-assoc {Ω} Ψ₁ Ψ₂ ⊡ = refl
<<-assoc {Ω} Ψ₁ Ψ₂ (Ψ , A) = cong (λ α → α , A) (<<-assoc Ψ₁ Ψ₂ Ψ)

-- TODO: Give also a non-normal calculus, which is convenient
mutual
 data head {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ▹ : ∀ {A} (x : tvar Ψ A) -> head Δ Ψ A
  _[_] : ∀ {A Φ} (u : var Δ (% A [ Φ ])) (σ : nsub Δ Ψ Φ) -> head Δ Ψ A
  _♯[_] : ∀ {A Φ} (p : var Δ (♯ A [ Φ ])) (σ : nsub Δ Ψ Φ) -> head Δ Ψ A
  -- This is a little out of place. Would normally be included in the spine...
  π : ∀ {Φ A} (x : tvar Φ A) (ρ : rsub Δ Ψ Φ) -> head Δ Ψ A
 data spine {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> tp -> Set where
  ε : ∀ {C} -> spine Δ Ψ C C
  _,_ : ∀ {A B C} (N : ntm Δ Ψ A) (S : spine Δ Ψ B C) -> spine Δ Ψ (A ⇒ B) C
 data rtm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  _·_ : ∀ {A B} (H : head Δ Ψ A) (S : spine Δ Ψ A B) -> rtm Δ Ψ B
 data ntm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ƛ : ∀ {A B} (N : ntm Δ (Ψ , (▸ A)) B) -> ntm Δ Ψ (A ⇒ B)
  ▸ : (R : rtm Δ Ψ i) -> ntm Δ Ψ i 
 data nsub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  ⊡ : ∀ {Ψ} -> nsub Δ Ψ ⊡
  _,_ : ∀ {Ψ Φ A} (σ : nsub Δ Ψ Φ) (N : ntm Δ Ψ A) -> nsub Δ Ψ (Φ , ▸ A)
  _,[_]_ : ∀ {Ψ Φ₁ Φ₂ φ} (σ : nsub Δ Ψ Φ₁) (xs : cvar Φ₂ φ) (ρ : rsub Δ Ψ Φ₂) -> nsub Δ Ψ (Φ₁ , ▹ φ)
 data rsub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  -- I guess this doesn't quite look like a spine. Maybe it's better to make a more direct attempt?
  _[_] : ∀ {Ψ Φ₁ Φ₂} (s : var Δ ($ Φ₁ [ Φ₂ ])) (σ : nsub Δ Ψ Φ₂) -> rsub Δ Ψ Φ₁
  id : ∀ {Ψ φ} (xs : cvar Ψ φ) -> rsub Δ Ψ (⊡ , ▹ φ)

⟦_⟧tc : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (Φ : tctx Ω₁) -> tctx Ω₂
⟦_⟧tc Ψs ⊡ = ⊡
⟦_⟧tc Ψs (Φ , (▹ φ)) = ⟦ Ψs ⟧tc Φ << (lookup Ψs φ)
⟦_⟧tc Ψs (Φ , (▸ A)) = ⟦ Ψs ⟧tc Φ , (▸ A)

⟦⟧tc-<< : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) Φ₁ Φ₂
 -> ⟦ Ψs ⟧tc (Φ₁ << Φ₂) ≡ ((⟦ Ψs ⟧tc Φ₁) << (⟦ Ψs ⟧tc Φ₂))
⟦⟧tc-<< Ψs Φ₁ ⊡ = refl
⟦⟧tc-<< Ψs Φ₁ (ψ , ▹ φ) = trans (cong (λ α → α << lookup Ψs φ) (⟦⟧tc-<< Ψs Φ₁ ψ)) (<<-assoc (⟦ Ψs ⟧tc Φ₁) (⟦ Ψs ⟧tc ψ) (lookup Ψs φ))
⟦⟧tc-<< Ψs Φ₁ (ψ , ▸ A) = cong (λ α → α , ▸ A) (⟦⟧tc-<< Ψs Φ₁ ψ)


⟦_⟧mt : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (U : mtp Ω₁) -> mtp Ω₂
⟦_⟧mt Ψs ($ Ψ [ Φ ]) = $ (⟦ Ψs ⟧tc Ψ) [ ⟦ Ψs ⟧tc Φ ]
⟦_⟧mt Ψs ((♯ A) [ Φ ]) = (♯ A) [ ⟦ Ψs ⟧tc Φ ]
⟦_⟧mt Ψs (% A [ Φ ]) = % A [ ⟦ Ψs ⟧tc Φ ]


⟦_⟧mc : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (Δ : mctx Ω₁) -> mctx Ω₂
⟦_⟧mc Ψs Δ = cmap ⟦ Ψs ⟧mt Δ

<<tv : ∀ {Ω} {Ψ₁ : tctx Ω} {A} -> tvar Ψ₁ A -> ∀ Ψ₂ -> tvar (Ψ₁ << Ψ₂) A
<<tv x ⊡ = x
<<tv x (ψ , T) = pop (<<tv x ψ)

<<cv : ∀ {Ω} {Ψ₁ : tctx Ω} {φ} -> cvar Ψ₁ φ -> ∀ Ψ₂ -> cvar (Ψ₁ << Ψ₂) φ
<<cv xs ⊡ = xs
<<cv xs (Ψ , A) = pop (<<cv xs Ψ)

⟦_⟧tv : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Φ : tctx Ω₁} {A} -> tvar Φ A -> tvar (⟦ Ψs ⟧tc Φ) A
⟦_⟧tv Ψs top = top
⟦_⟧tv Ψs (pop {Γ} {T} {▹ φ} x) = <<tv (⟦ Ψs ⟧tv x) (lookup Ψs φ)
⟦_⟧tv Ψs (pop {Γ} {T} {▸ A} x) = pop (⟦ Ψs ⟧tv x)

tvar-wkn : ∀ {Ω} (Ψ₁ Ψ₂ Ψ₃ : tctx Ω) {A} -> tvar (Ψ₁ << Ψ₃) A -> tvar (Ψ₁ << Ψ₂ << Ψ₃) A
tvar-wkn Ψ₁ Ψ₂ ⊡ x = <<tv x Ψ₂
tvar-wkn Ψ₁ Ψ₂ (Ψ , .(▸ A)) {A} top = top
tvar-wkn Ψ₁ Ψ₂ (Ψ , A) (pop x) = pop (tvar-wkn Ψ₁ Ψ₂ Ψ x)

cvar-wkn : ∀ {Ω} (Ψ₁ Ψ₂ Ψ₃ : tctx Ω) {φ} -> cvar (Ψ₁ << Ψ₃) φ -> cvar (Ψ₁ << Ψ₂ << Ψ₃) φ
cvar-wkn Ψ₁ Ψ₂ ⊡ xs = <<cv xs Ψ₂
cvar-wkn Ψ₁ Ψ₂ (Ψ , .(▹ φ)) {φ} top = top
cvar-wkn Ψ₁ Ψ₂ (Ψ , A) (pop xs) = pop (cvar-wkn Ψ₁ Ψ₂ Ψ xs)

mutual
 h-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A} -> head Δ (Ψ₁ << Ψ₃) A -> head Δ (Ψ₁ << Ψ₂ << Ψ₃) A
 h-wkn Ψ₁ Ψ₂ Ψ₃ (▹ x) = ▹ (tvar-wkn Ψ₁ Ψ₂ Ψ₃ x)
 h-wkn Ψ₁ Ψ₂ Ψ₃ (u [ σ ]) = u [ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]
 h-wkn Ψ₁ Ψ₂ Ψ₃ (p ♯[ σ ]) = p ♯[ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]
 h-wkn Ψ₁ Ψ₂ Ψ₃ (π x ρ) = π x (rs-wkn Ψ₁ Ψ₂ Ψ₃ ρ)

 s-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A B} -> spine Δ (Ψ₁ << Ψ₃) A B -> spine Δ (Ψ₁ << Ψ₂ << Ψ₃) A B
 s-wkn Ψ₁ Ψ₂ Ψ₃ ε = ε
 s-wkn Ψ₁ Ψ₂ Ψ₃ (N , S) = (n-wkn Ψ₁ Ψ₂ Ψ₃ N) , (s-wkn Ψ₁ Ψ₂ Ψ₃ S)

 r-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A} -> rtm Δ (Ψ₁ << Ψ₃) A -> rtm Δ (Ψ₁ << Ψ₂ << Ψ₃) A
 r-wkn Ψ₁ Ψ₂ Ψ₃ (H · S) = (h-wkn Ψ₁ Ψ₂ Ψ₃ H) · (s-wkn Ψ₁ Ψ₂ Ψ₃ S)

 n-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A} -> ntm Δ (Ψ₁ << Ψ₃) A -> ntm Δ (Ψ₁ << Ψ₂ << Ψ₃) A
 n-wkn Ψ₁ Ψ₂ Ψ₃ (ƛ {A} {B} N) = ƛ (n-wkn Ψ₁ Ψ₂ (Ψ₃ , ▸ A) N)
 n-wkn Ψ₁ Ψ₂ Ψ₃ (▸ R) = ▸ (r-wkn Ψ₁ Ψ₂ Ψ₃ R)

 ns-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {Φ} -> nsub Δ (Ψ₁ << Ψ₃) Φ -> nsub Δ (Ψ₁ << Ψ₂ << Ψ₃) Φ
 ns-wkn Ψ₁ Ψ₂ Ψ₃ ⊡ = ⊡
 ns-wkn Ψ₁ Ψ₂ Ψ₃ (σ , N) = (ns-wkn Ψ₁ Ψ₂ Ψ₃ σ) , (n-wkn Ψ₁ Ψ₂ Ψ₃ N)
 ns-wkn Ψ₁ Ψ₂ Ψ₃ (σ ,[ xs ] ρ) = (ns-wkn Ψ₁ Ψ₂ Ψ₃ σ) ,[ xs ] (rs-wkn Ψ₁ Ψ₂ Ψ₃ ρ)

 rs-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {Φ} -> rsub Δ (Ψ₁ << Ψ₃) Φ -> rsub Δ (Ψ₁ << Ψ₂ << Ψ₃) Φ
 rs-wkn Ψ₁ Ψ₂ Ψ₃ (s [ σ ]) = s [ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]
 rs-wkn Ψ₁ Ψ₂ Ψ₃ (id xs) = id (cvar-wkn Ψ₁ Ψ₂ Ψ₃ xs)
 

{-
data vtsubst {Ω} : tctx Ω -> tctx Ω -> Set where
 ⊡ : ∀ {Ψ₂} -> vtsubst ⊡ Ψ₂
 _,_ : ∀ {Ψ₁ Ψ₂ A} (σ : vtsubst Ψ₁ Ψ₂) -> (x : tvar Ψ₂ A) -> vtsubst (Ψ₁ , A) Ψ₂
 id : ∀ {φ} Ψ -> vtsubst (▹ φ) ((▹ φ) << Ψ)


vt-lookup : ∀ {Ω} {Ψ₁ Ψ₂ : tctx Ω} {A} -> vtsubst Ψ₁ Ψ₂ -> tvar Ψ₁ A -> tvar Ψ₂ A
vt-lookup ⊡ ()
vt-lookup (σ , x) top = x
vt-lookup (σ , x) (pop x') = vt-lookup σ x'
vt-lookup (id Ψ) x = <<tv x Ψ

↑vts : ∀ {Ω} {Ψ₁ Ψ₂ : tctx Ω} -> vtsubst Ψ₁ Ψ₂ -> ∀ A -> vtsubst Ψ₁ (Ψ₂ , A)
↑vts ⊡ A = ⊡
↑vts (σ , x) A' = (↑vts σ A') , pop x
↑vts (id Ψ) A = id (Ψ , A)

id-vts : ∀ {Ω} {Ψ : tctx Ω} -> vtsubst Ψ Ψ
id-vts {Ω} {⊡} = ⊡
id-vts {Ω} {▹ φ} = id ⊡
id-vts {Ω} {Ψ , A} = (↑vts id-vts A) , top

wkn-vts : ∀ {Ω} {Ψ : tctx Ω} {A} -> vtsubst Ψ (Ψ , A)
wkn-vts = ↑vts id-vts _

vtsubst-inv-φ : ∀ {Ω} {Ψ₁ : tctx Ω} Ψ₂ {φ} -> vtsubst (▹ φ << Ψ₂) Ψ₁ -> ∃ (λ Ψ₁' -> Ψ₁ ≡ ▹ φ << Ψ₁')
vtsubst-inv-φ ⊡ (id Ψ) = Ψ , refl
vtsubst-inv-φ (ψ , T) (σ , x) with vtsubst-inv-φ ψ σ
vtsubst-inv-φ (ψ , T) (σ , x) | Ψ' , refl = Ψ' , refl

mutual
 [_]vr : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂} (σ : vtsubst Ψ₁ Ψ₂) {A} -> rtm Δ Ψ₁ A -> rtm Δ Ψ₂ A
 [_]vr σ (▹ x) = ▹ (vt-lookup σ x)
 [_]vr σ (u [ ρ ]) = u [ [ σ ]vns ρ ]
 [_]vr σ (p ♯[ ρ ]) = p ♯[ [ σ ]vns ρ ]
 [_]vr σ (R · N) = [ σ ]vr R · [ σ ]vn N
 [_]vr σ (top ρ) = top ([ σ ]vrs ρ)

 [_]vn : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂} (σ : vtsubst Ψ₁ Ψ₂) {A} -> ntm Δ Ψ₁ A -> ntm Δ Ψ₂ A
 [_]vn σ (ƛ N) = ƛ ([ ↑vts σ _ , top ]vn N)
 [_]vn σ (▸ R) = ▸ ([ σ ]vr R)

 [_]vns : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂} (σ : vtsubst Ψ₁ Ψ₂) {Φ} -> nsub Δ Ψ₁ Φ -> nsub Δ Ψ₂ Φ
 [_]vns σ ⊡ = ⊡
 [_]vns σ (σ' , N) = ([ σ ]vns σ') , ([ σ ]vn N)
 [_]vns σ (▸ ρ) = ▸ ([ σ ]vrs ρ)

 [_]vrs : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂} (σ : vtsubst Ψ₁ Ψ₂) {Φ} -> rsub Δ Ψ₁ Φ -> rsub Δ Ψ₂ Φ
 [_]vrs σ (s [ ρ ]) = s [ [ σ ]vns ρ ]
 [_]vrs σ (id Ψ) with vtsubst-inv-φ Ψ σ
 [_]vrs σ (id Ψ) | Φ , refl = id Φ
-- [_]vrs σ (π₁ ρ) = π₁ ([ σ ]vrs ρ)

-}

{-
η-expand : ∀ {A} {Ω} {Δ : mctx Ω} {Ψ} -> rtm Δ Ψ A -> ntm Δ Ψ A
η-expand {i} R = ▸ R
η-expand {A ⇒ B} R = {!!} --ƛ (η-expand (r-wkn _ (⊡ , ▸ A) ⊡ R · η-expand (▹ top)))

-- Maybe this is more of a "join it with an xs" thing?
η-expand-s : ∀ {Ω} {Φ} Φ' {Δ : mctx Ω} {Ψ} -> rsub Δ Ψ (Φ << Φ') -> nsub Δ Ψ Φ
η-expand-s {Ω} {⊡} Φ' ρ = ⊡
η-expand-s {Ω} {Ψ , ▹ φ} Φ' {Δ} {Ψ'} ρ = η-expand-s (⊡ , ▹ φ << Φ') (subst (λ α → rsub Δ Ψ' α) (<<-assoc Ψ (⊡ , ▹ φ) Φ') ρ) ,[ <<cv top Φ' ] ρ
η-expand-s {Ω} {Ψ , ▸ A} Φ' {Δ} {Ψ'} ρ = {!!} --η-expand-s (⊡ , ▸ A << Φ') (subst (λ α → rsub Δ Ψ' α) (<<-assoc Ψ (⊡ , ▸ A) Φ') ρ) , η-expand (π (<<tv top Φ') ρ)

id-subst : ∀ {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) -> nsub Δ Ψ Ψ
id-subst Δ ⊡ = ⊡
id-subst Δ (Ψ , ▹ φ) = (ns-wkn Ψ (⊡ , ▹ φ) ⊡ (id-subst Δ Ψ)) ,[ top ] (id top)
id-subst Δ (Ψ , ▸ A) = {!!} --(ns-wkn Ψ (⊡ , ▸ A) ⊡ (id-subst Δ Ψ)) , η-expand (▹ top)
-}

{-

<<sub : ∀ {Ω} {Δ : mctx Ω} {Ψ Φ : tctx Ω} -> nsub Δ Ψ Φ -> ∀ Ψ' -> nsub Δ (Ψ << Ψ') Φ
<<sub σ ⊡ = σ
<<sub σ (ψ , T) = [ wkn-vts ]vns (<<sub σ ψ)

{-<<subr : ∀ {Ω} {Δ : mctx Ω} {Ψ Φ : tctx Ω} -> rsub Δ Ψ Φ -> ∀ Ψ' -> rsub Δ (Ψ << Ψ') Φ
<<subr (s [ ρ ]) Ψ' = s [ <<sub ρ Ψ' ]
<<subr (id Ψ) Ψ' = {!!}
<<subr (π₁ ρ) Ψ' = π₁ (<<subr ρ Ψ')
-}

mutual
 ⟦_⟧cr : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Δ : mctx Ω₁} {Ψ} {A}
   -> (R : rtm Δ Ψ A) -> rtm (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) A
 ⟦_⟧cr Ψs (▹ x) = ▹ (⟦ Ψs ⟧tv x)
 ⟦_⟧cr Ψs (u [ σ ]) = cmap-var ⟦ Ψs ⟧mt u [ ⟦ Ψs ⟧cns σ ]
 ⟦_⟧cr Ψs (p ♯[ σ ]) = cmap-var ⟦ Ψs ⟧mt p ♯[ ⟦ Ψs ⟧cns σ ]
 ⟦_⟧cr Ψs (R · N) = (⟦ Ψs ⟧cr R) · ⟦ Ψs ⟧cn N
 ⟦_⟧cr Ψs (top ρ) with ⟦ Ψs ⟧crs ρ
 ⟦_⟧cr Ψs (top ρ) | σ , N = {!!}

 ⟦_⟧cn : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Δ : mctx Ω₁} {Ψ} {A}
   -> (N : ntm Δ Ψ A) -> ntm (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) A
 ⟦_⟧cn Ψs (ƛ N) = ƛ (⟦ Ψs ⟧cn N)
 ⟦_⟧cn Ψs (▸ R) = ▸ (⟦ Ψs ⟧cr R)

 ⟦_⟧cns : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Δ : mctx Ω₁} {Ψ} {Φ}
   -> (σ : nsub Δ Ψ Φ) -> nsub (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) (⟦ Ψs ⟧tc Φ)
 ⟦_⟧cns Ψs ⊡ = ⊡
 ⟦_⟧cns Ψs (σ , N) = (⟦ Ψs ⟧cns σ) , (⟦ Ψs ⟧cn N)
 ⟦_⟧cns Ψs (▸ ρ) = ⟦ Ψs ⟧crs ρ

 ⟦_⟧crs : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Δ : mctx Ω₁} {Ψ} {Φ}
   -> (σ : rsub Δ Ψ Φ) -> nsub (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) (⟦ Ψs ⟧tc Φ)
 ⟦_⟧crs Ψs (s [ ρ ]) = η-expand-s ((cmap-var ⟦ Ψs ⟧mt s) [ ⟦ Ψs ⟧cns ρ ])
 ⟦_⟧crs Ψs {Δ} (id {φ} Ψ) = subst (λ α → nsub (⟦ Ψs ⟧mc Δ) α (lookup Ψs φ)) (sym (⟦⟧tc-<< Ψs (▹ φ) Ψ)) (<<sub (id-subst (⟦ Ψs ⟧mc Δ) (lookup Ψs φ)) Ψ)
-- ⟦_⟧crs Ψs (π₁ ρ) with ⟦ Ψs ⟧crs ρ
-- ⟦_⟧crs Ψs (π₁ ρ) | σ , N = σ
-}
{-
slookup : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂ : tctx Ω} {A} -> nsub Δ Ψ₁ Ψ₂ -> tvar Ψ₂ A -> ntm Δ Ψ₁ A
slookup ⊡ ()
slookup (σ , N) top = N
slookup (σ , N) (pop x) = slookup σ x
slookup (σ ,[ xs ] ρ) (pop x) = slookup σ x

clookup : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂ : tctx Ω} {φ} -> nsub Δ Ψ₁ Ψ₂ -> cvar Ψ₂ φ -> nsub Δ Ψ₁ (⊡ , ▹ φ)
clookup σ xs = {!!} -}

{-
sub-inv-φ : ∀ {Ω} {Δ} {Ψ₁ : tctx Ω} Ψ₂ {φ} -> sub Δ Ψ₁ (▹ φ << Ψ₂) -> ∃ (λ Ψ₁' -> Ψ₁ ≡ ▹ φ << Ψ₁')
sub-inv-φ ⊡ (s [ ρ ]) = {!!}
sub-inv-φ ⊡ (id Ψ) = Ψ , refl
sub-inv-φ (ψ , T) (σ , N) with sub-inv-φ ψ σ
sub-inv-φ (ψ , T) (σ , N) | Φ , refl = Φ , refl
sub-inv-φ (ψ , T) (s [ ρ ]) = {!!} -}

cvar-str : ∀ {Ω} {Ψ₁ : tctx Ω} {B} Ψ₂ {φ} -> cvar (Ψ₁ , ▸ B << Ψ₂) φ -> cvar (Ψ₁ << Ψ₂) φ
cvar-str ⊡ (pop xs) = xs
cvar-str (Ψ , ▹ .φ) {φ} top = top
cvar-str (Ψ , ▹ φ) (pop xs) = pop (cvar-str Ψ xs)
cvar-str (Ψ , ▸ A) (pop xs) = pop (cvar-str Ψ xs)

mutual
 n-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {A} -> ntm Δ (Ψ₁ , ▸ B << Ψ₂) A -> ntm Δ (Ψ₁ << Ψ₁) B -> ntm Δ (Ψ₁ << Ψ₂) A
 n-sub Ψ (ƛ {A} {B} N) M = ƛ (n-sub (Ψ , ▸ A) N M)
 n-sub Ψ (▸ (▹ x · S)) M = {!!}
 n-sub Ψ (▸ (u [ σ ] · S)) M = ▸ ((u [ ns-sub Ψ σ M ]) · s-sub Ψ S M)
 n-sub Ψ (▸ (p ♯[ σ ] · S)) M = ▸ ((p ♯[ ns-sub Ψ σ M ]) · s-sub Ψ S M)
 n-sub Ψ (▸ (π x ρ · S)) M = ▸ (π x (rs-sub Ψ ρ M) · s-sub Ψ S M) 

 s-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {A C} -> spine Δ (Ψ₁ , ▸ B << Ψ₂) A C -> ntm Δ (Ψ₁ << Ψ₁) B -> spine Δ (Ψ₁ << Ψ₂) A C
 s-sub Ψ ε N = ε
 s-sub Ψ (N , S) N' = (n-sub Ψ N N') , (s-sub Ψ S N')

 ns-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {Φ} -> nsub Δ (Ψ₁ , ▸ B << Ψ₂) Φ -> ntm Δ (Ψ₁ << Ψ₁) B -> nsub Δ (Ψ₁ << Ψ₂) Φ
 ns-sub Ψ ⊡ M = ⊡
 ns-sub Ψ (σ , N) M = (ns-sub Ψ σ M) , (n-sub Ψ N M)
 ns-sub Ψ (σ ,[ xs ] ρ) M = (ns-sub Ψ σ M) ,[ xs ] (rs-sub Ψ ρ M)

 rs-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {Φ} -> rsub Δ (Ψ₁ , ▸ B << Ψ₂) Φ -> ntm Δ (Ψ₁ << Ψ₁) B -> rsub Δ (Ψ₁ << Ψ₂) Φ
 rs-sub Ψ (s [ σ ]) M = s [ ns-sub Ψ σ M ]
 rs-sub Ψ (id xs) M = id (cvar-str Ψ xs)