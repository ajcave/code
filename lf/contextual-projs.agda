module contextual-projs where
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

-- TODO: Give also a non-normal calculus, which is convenient
mutual
 data rtm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ▹ : ∀ {A} (x : tvar Ψ A) -> rtm Δ Ψ A
  _[_] : ∀ {A Φ} (u : var Δ (% A [ Φ ])) (σ : nsub Δ Ψ Φ) -> rtm Δ Ψ A
  _♯[_] : ∀ {A Φ} (p : var Δ (♯ A [ Φ ])) (σ : nsub Δ Ψ Φ) -> rtm Δ Ψ A
  _·_ : ∀ {A B} (R : rtm Δ Ψ (A ⇒ B)) (N : ntm Δ Ψ A) -> rtm Δ Ψ B
  top : ∀ {Φ A} (ρ : rsub Δ Ψ (Φ , A)) -> rtm Δ Ψ A
 data ntm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ƛ : ∀ {A B} (N : ntm Δ (Ψ , A) B) -> ntm Δ Ψ (A ⇒ B)
  ▸ : (R : rtm Δ Ψ i) -> ntm Δ Ψ i 
 data nsub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  ⊡ : ∀ {Ψ} -> nsub Δ Ψ ⊡
  _,_ : ∀ {Ψ Φ A} (σ : nsub Δ Ψ Φ) (N : ntm Δ Ψ A) -> nsub Δ Ψ (Φ , A)
  ▸ : ∀ {Ψ φ} (ρ : rsub Δ Ψ (▹ φ)) -> nsub Δ Ψ (▹ φ)
 data rsub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  _[_] : ∀ {Ψ Φ₁ Φ₂} (s : var Δ ($ Φ₁ [ Φ₂ ])) (ρ : nsub Δ Ψ Φ₂) -> rsub Δ Ψ Φ₁
  id : ∀ {φ} Ψ -> rsub Δ (▹ φ << Ψ) (▹ φ)
  π₁ : ∀ {Ψ Φ A} (ρ : rsub Δ Ψ (Φ , A)) -> rsub Δ Ψ Φ

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

data vtsubst {Ω} : tctx Ω -> tctx Ω -> Set where
 ⊡ : ∀ {Ψ₂} -> vtsubst ⊡ Ψ₂
 _,_ : ∀ {Ψ₁ Ψ₂ A} (σ : vtsubst Ψ₁ Ψ₂) -> (x : tvar Ψ₂ A) -> vtsubst (Ψ₁ , A) Ψ₂
 id : ∀ {φ} Ψ -> vtsubst (▹ φ) ((▹ φ) << Ψ)

<<tv : ∀ {Ω} {Ψ₁ : tctx Ω} {A} -> tvar Ψ₁ A -> ∀ Ψ₂ -> tvar (Ψ₁ << Ψ₂) A
<<tv x ⊡ = x
<<tv x (ψ , T) = pop (<<tv x ψ) 

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
 [_]vrs σ (π₁ ρ) = π₁ ([ σ ]vrs ρ)

η-expand : ∀ {A} {Ω} {Δ : mctx Ω} {Ψ} -> rtm Δ Ψ A -> ntm Δ Ψ A
η-expand {i} R = ▸ R
η-expand {A ⇒ B} R = ƛ (η-expand ([ wkn-vts ]vr R · η-expand (▹ top)))

η-expand-s : ∀ {Ω} {Φ} {Δ : mctx Ω} {Ψ} -> rsub Δ Ψ Φ -> nsub Δ Ψ Φ
η-expand-s {Ω} {⊡} ρ = ⊡
η-expand-s {Ω} {▹ φ} ρ = ▸ ρ
η-expand-s {Ω} {Ψ , A} ρ = η-expand-s (π₁ ρ) , η-expand (top ρ)

id-subst : ∀ {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) -> nsub Δ Ψ Ψ
id-subst Δ ⊡ = ⊡
id-subst Δ (▹ φ) = ▸ (id ⊡)
id-subst Δ (Ψ , A) = [ wkn-vts ]vns (id-subst Δ Ψ) , η-expand (▹ top)



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
 ⟦_⟧crs Ψs (π₁ ρ) with ⟦ Ψs ⟧crs ρ
 ⟦_⟧crs Ψs (π₁ ρ) | σ , N = σ

slookup : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂ : tctx Ω} {A} -> nsub Δ Ψ₁ Ψ₂ -> tvar Ψ₂ A -> ntm Δ Ψ₁ A
slookup ⊡ ()
slookup (σ , N) top = N
slookup (σ , N) (pop x) = slookup σ x
slookup (▸ ρ) ()

{-sub-inv-φ : ∀ {Ω} {Δ} {Ψ₁ : tctx Ω} Ψ₂ {φ} -> sub Δ Ψ₁ (▹ φ << Ψ₂) -> ∃ (λ Ψ₁' -> Ψ₁ ≡ ▹ φ << Ψ₁')
sub-inv-φ ⊡ (s [ ρ ]) = {!!}
sub-inv-φ ⊡ (id Ψ) = Ψ , refl
sub-inv-φ (ψ , T) (σ , N) with sub-inv-φ ψ σ
sub-inv-φ (ψ , T) (σ , N) | Φ , refl = Φ , refl
sub-inv-φ (ψ , T) (s [ ρ ]) = {!!} -}

mutual
 [_]r :  ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂} (σ : nsub Δ Ψ₂ Ψ₁) {A} -> rtm Δ Ψ₁ A -> ntm Δ Ψ₂ A
 [_]r σ (▹ x) = slookup σ x
 [_]r σ (u [ σ' ]) = η-expand (u [ [ σ ]ns σ' ])
 [_]r σ (p ♯[ σ' ]) = η-expand (p ♯[ [ σ ]ns σ' ])
 [_]r σ (R · N) with [ σ ]r R
 [_]r σ (R · N) | ƛ M = [ (id-subst _ _) , [ σ ]n N ]n M
 [_]r σ (top ρ) with [ σ ]rs ρ
 [_]r σ (top ρ) | σ' , N = N

 [_]n :  ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂} (σ : nsub Δ Ψ₂ Ψ₁) {A} -> ntm Δ Ψ₁ A -> ntm Δ Ψ₂ A
 [_]n σ (ƛ N) = ƛ ([ [ wkn-vts ]vns σ , (η-expand (▹ top)) ]n N)
 [_]n σ (▸ R) = [ σ ]r R

 [_]ns :  ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂} (σ : nsub Δ Ψ₂ Ψ₁) {Φ} -> nsub Δ Ψ₁ Φ -> nsub Δ Ψ₂ Φ
 [_]ns σ ⊡ = ⊡
 [_]ns σ (σ' , N) = ([ σ ]ns σ') , ([ σ ]n N)
 [_]ns σ (▸ ρ) = [ σ ]rs ρ

 [_]rs :  ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Ψ₂} (σ : nsub Δ Ψ₂ Ψ₁) {Φ} -> rsub Δ Ψ₁ Φ -> nsub Δ Ψ₂ Φ
 [_]rs σ (s [ ρ ]) = η-expand-s (s [ [ σ ]ns ρ ])
 [_]rs σ (id Ψ) = {!!}
 [_]rs σ (π₁ ρ) with [ σ ]rs ρ
 [_]rs σ (π₁ ρ) | σ' , N = σ'