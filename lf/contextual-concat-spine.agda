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

infixl 10 _<<_

<<-assoc : ∀ {Ω} (Ψ₁ Ψ₂ Ψ₃ : tctx Ω) -> (Ψ₁ << Ψ₂) << Ψ₃ ≡ Ψ₁ << (Ψ₂ << Ψ₃)
<<-assoc {Ω} Ψ₁ Ψ₂ ⊡ = refl
<<-assoc {Ω} Ψ₁ Ψ₂ (Ψ , A) = cong (λ α → α , A) (<<-assoc Ψ₁ Ψ₂ Ψ)

<<-idl : ∀ {Ω} (Ψ : tctx Ω) -> ⊡ << Ψ ≡ Ψ
<<-idl ⊡ = refl
<<-idl (Ψ , A) = cong (λ α → α , A) (<<-idl Ψ)

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
 data ntm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ƛ : ∀ {A B} (N : ntm Δ (Ψ , (▸ A)) B) -> ntm Δ Ψ (A ⇒ B)
  _·_ : ∀ {A} (H : head Δ Ψ A) (S : spine Δ Ψ A i) -> ntm Δ Ψ i
 data nsub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  ⊡ : ∀ {Ψ} -> nsub Δ Ψ ⊡
  _,_ : ∀ {Ψ Φ A} (σ : nsub Δ Ψ Φ) (N : ntm Δ Ψ A) -> nsub Δ Ψ (Φ , ▸ A)
  _,[_]_ : ∀ {Ψ Φ₁ Φ₂ φ} (σ : nsub Δ Ψ Φ₁) (xs : cvar Φ₂ φ) (ρ : rsub Δ Ψ Φ₂) -> nsub Δ Ψ (Φ₁ , ▹ φ)
 data rsub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  -- I guess this is actually the head, and the cvar is the spine? Why doesn't the code seem to reflect that very well?
  -- TODO: Try directly with a fst and snd approach
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

tvar-wkn1 : ∀ {Ω} {Ψ₁ B} (Ψ₃ : tctx Ω) {A} -> tvar (Ψ₁ << Ψ₃) A -> tvar (Ψ₁ , ▸ B << Ψ₃) A
tvar-wkn1 {Ω} {Ψ₁} {B} Ψ₃ x = tvar-wkn Ψ₁ (⊡ , ▸ B) Ψ₃ x

cvar-wkn : ∀ {Ω} (Ψ₁ Ψ₂ Ψ₃ : tctx Ω) {φ} -> cvar (Ψ₁ << Ψ₃) φ -> cvar (Ψ₁ << Ψ₂ << Ψ₃) φ
cvar-wkn Ψ₁ Ψ₂ ⊡ xs = <<cv xs Ψ₂
cvar-wkn Ψ₁ Ψ₂ (Ψ , .(▹ φ)) {φ} top = top
cvar-wkn Ψ₁ Ψ₂ (Ψ , A) (pop xs) = pop (cvar-wkn Ψ₁ Ψ₂ Ψ xs)

cvar-wkn1 : ∀ {Ω} {Ψ₁ B} (Ψ₃ : tctx Ω) {A} -> cvar (Ψ₁ << Ψ₃) A -> cvar (Ψ₁ , ▹ B << Ψ₃) A
cvar-wkn1 {Ω} {Ψ₁} {B} Ψ₃ x = cvar-wkn Ψ₁ (⊡ , ▹ B) Ψ₃ x

mutual
 h-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A} -> head Δ (Ψ₁ << Ψ₃) A -> head Δ (Ψ₁ << Ψ₂ << Ψ₃) A
 h-wkn Ψ₁ Ψ₂ Ψ₃ (▹ x) = ▹ (tvar-wkn Ψ₁ Ψ₂ Ψ₃ x)
 h-wkn Ψ₁ Ψ₂ Ψ₃ (u [ σ ]) = u [ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]
 h-wkn Ψ₁ Ψ₂ Ψ₃ (p ♯[ σ ]) = p ♯[ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]
 h-wkn Ψ₁ Ψ₂ Ψ₃ (π x ρ) = π x (rs-wkn Ψ₁ Ψ₂ Ψ₃ ρ)

 s-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A B} -> spine Δ (Ψ₁ << Ψ₃) A B -> spine Δ (Ψ₁ << Ψ₂ << Ψ₃) A B
 s-wkn Ψ₁ Ψ₂ Ψ₃ ε = ε
 s-wkn Ψ₁ Ψ₂ Ψ₃ (N , S) = (n-wkn Ψ₁ Ψ₂ Ψ₃ N) , (s-wkn Ψ₁ Ψ₂ Ψ₃ S)

 n-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A} -> ntm Δ (Ψ₁ << Ψ₃) A -> ntm Δ (Ψ₁ << Ψ₂ << Ψ₃) A
 n-wkn Ψ₁ Ψ₂ Ψ₃ (ƛ {A} {B} N) = ƛ (n-wkn Ψ₁ Ψ₂ (Ψ₃ , ▸ A) N)
 n-wkn Ψ₁ Ψ₂ Ψ₃ (H · S) = (h-wkn Ψ₁ Ψ₂ Ψ₃ H) · (s-wkn Ψ₁ Ψ₂ Ψ₃ S)

 ns-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {Φ} -> nsub Δ (Ψ₁ << Ψ₃) Φ -> nsub Δ (Ψ₁ << Ψ₂ << Ψ₃) Φ
 ns-wkn Ψ₁ Ψ₂ Ψ₃ ⊡ = ⊡
 ns-wkn Ψ₁ Ψ₂ Ψ₃ (σ , N) = (ns-wkn Ψ₁ Ψ₂ Ψ₃ σ) , (n-wkn Ψ₁ Ψ₂ Ψ₃ N)
 ns-wkn Ψ₁ Ψ₂ Ψ₃ (σ ,[ xs ] ρ) = (ns-wkn Ψ₁ Ψ₂ Ψ₃ σ) ,[ xs ] (rs-wkn Ψ₁ Ψ₂ Ψ₃ ρ)

 rs-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {Φ} -> rsub Δ (Ψ₁ << Ψ₃) Φ -> rsub Δ (Ψ₁ << Ψ₂ << Ψ₃) Φ
 rs-wkn Ψ₁ Ψ₂ Ψ₃ (s [ σ ]) = s [ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]
 rs-wkn Ψ₁ Ψ₂ Ψ₃ (id xs) = id (cvar-wkn Ψ₁ Ψ₂ Ψ₃ xs)

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

cvar-str : ∀ {Ω} {Ψ₁ : tctx Ω} {B} Ψ₂ {φ} -> cvar (Ψ₁ , ▸ B << Ψ₂) φ -> cvar (Ψ₁ << Ψ₂) φ
cvar-str ⊡ (pop xs) = xs
cvar-str (Ψ , ▹ φ) top = top
cvar-str (Ψ , ▹ φ) (pop xs) = pop (cvar-str Ψ xs)
cvar-str (Ψ , ▸ A) (pop xs) = pop (cvar-str Ψ xs)

thatone : ∀ {Ω} {Ψ : tctx Ω} Φ {A} -> tvar (Ψ , ▸ A << Φ) A
thatone ⊡ = top
thatone (Φ , A) = pop (thatone Φ)

data eqV {Ω} {Ψ : tctx Ω} : ∀ {A} B Φ -> tvar ((Ψ , ▸ B) << Φ) A -> Set where
 same : ∀ {A Φ} -> eqV A Φ (thatone Φ)
 diff : ∀ {A B Φ} (x : tvar (Ψ << Φ) A) -> eqV B Φ (tvar-wkn1 Φ x)

eq? : ∀ {Ω} {Ψ : tctx Ω} Φ {A B} (x : tvar (Ψ , ▸ A << Φ) B) -> eqV A Φ x
eq? ⊡ top = same
eq? ⊡ (pop x) = diff x
eq? (Ψ , .(▸ B)) {A} {B} top = diff top
eq? (Ψ , A) (pop x) with eq? Ψ x
eq? (Ψ , A) (pop .(thatone Ψ)) | same = same
eq? (Ψ , A) (pop .(tvar-wkn1 Ψ x)) | diff x = diff (pop x)

mutual
 n-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {A} -> ntm Δ (Ψ₁ , ▸ B << Ψ₂) A -> ntm Δ Ψ₁ B -> ntm Δ (Ψ₁ << Ψ₂) A
 n-sub Ψ (ƛ {A} {B} N) M = ƛ (n-sub (Ψ , ▸ A) N M)
 n-sub Ψ (▹ x · S) M with eq? Ψ x
 n-sub Ψ (▹ .(thatone Ψ) · S) M | same = (n-wkn _ Ψ ⊡ M) ◇ (s-sub Ψ S M)
 n-sub Ψ (▹ .(tvar-wkn1 Ψ x) · S) M | diff x = (▹ x) · s-sub Ψ S M
 n-sub Ψ (u [ σ ] · S) M = (u [ ns-sub Ψ σ M ]) · s-sub Ψ S M
 n-sub Ψ (p ♯[ σ ] · S) M = (p ♯[ ns-sub Ψ σ M ]) · s-sub Ψ S M
 n-sub Ψ (π x ρ · S) M = π x (rs-sub Ψ ρ M) · s-sub Ψ S M

 s-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {A C} -> spine Δ (Ψ₁ , ▸ B << Ψ₂) A C -> ntm Δ Ψ₁ B -> spine Δ (Ψ₁ << Ψ₂) A C
 s-sub Ψ ε N = ε
 s-sub Ψ (N , S) N' = (n-sub Ψ N N') , (s-sub Ψ S N')

 ns-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {Φ} -> nsub Δ (Ψ₁ , ▸ B << Ψ₂) Φ -> ntm Δ Ψ₁ B -> nsub Δ (Ψ₁ << Ψ₂) Φ
 ns-sub Ψ ⊡ M = ⊡
 ns-sub Ψ (σ , N) M = (ns-sub Ψ σ M) , (n-sub Ψ N M)
 ns-sub Ψ (σ ,[ xs ] ρ) M = (ns-sub Ψ σ M) ,[ xs ] (rs-sub Ψ ρ M)

 rs-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {Φ} -> rsub Δ (Ψ₁ , ▸ B << Ψ₂) Φ -> ntm Δ Ψ₁ B -> rsub Δ (Ψ₁ << Ψ₂) Φ
 rs-sub Ψ (s [ σ ]) M = s [ ns-sub Ψ σ M ]
 rs-sub Ψ (id xs) M = id (cvar-str Ψ xs)

 _◇_ : ∀ {Ω} {Δ : mctx Ω} {Ψ} {A B} -> ntm Δ Ψ A -> spine Δ Ψ A B -> ntm Δ Ψ B
 N ◇ ε = N
 (ƛ N) ◇ (N' , S) = (n-sub ⊡ N N') ◇ S

tvar-str : ∀ {Ω} {Ψ₁ : tctx Ω} {B} Ψ₂ {φ} -> tvar (Ψ₁ , ▹ B << Ψ₂) φ -> tvar (Ψ₁ << Ψ₂) φ
tvar-str ⊡ (pop xs) = xs
tvar-str (Ψ , ▸ A) top = top
tvar-str (Ψ , ▸ A) (pop xs) = pop (tvar-str Ψ xs)
tvar-str (Ψ , ▹ φ) (pop xs) = pop (tvar-str Ψ xs)

cthatone : ∀ {Ω} {Ψ : tctx Ω} Φ {A} -> cvar (Ψ , ▹ A << Φ) A
cthatone ⊡ = top
cthatone (Φ , A) = pop (cthatone Φ)

data ceqV {Ω} {Ψ : tctx Ω} : ∀ {A} B Φ -> cvar ((Ψ , ▹ B) << Φ) A -> Set where
 same : ∀ {A Φ} -> ceqV A Φ (cthatone Φ)
 diff : ∀ {A B Φ} (x : cvar (Ψ << Φ) A) -> ceqV B Φ (cvar-wkn1 Φ x)

ceq? : ∀ {Ω} {Ψ : tctx Ω} Φ {A B} (x : cvar (Ψ , ▹ A << Φ) B) -> ceqV A Φ x
ceq? ⊡ top = same
ceq? ⊡ (pop x) = diff x
ceq? (Ψ , .(▹ B)) {A} {B} top = diff top
ceq? (Ψ , A) (pop x) with ceq? Ψ x
ceq? (Ψ , A) (pop .(cthatone Ψ)) | same = same
ceq? (Ψ , A) (pop .(cvar-wkn1 Ψ x)) | diff x = diff (pop x)

mutual
 nc-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Φ} {φ} Ψ₂ {A} -> ntm Δ (Ψ₁ , ▹ φ << Ψ₂) A -> cvar Φ φ -> rsub Δ Ψ₁ Φ -> ntm Δ (Ψ₁ << Ψ₂) A
 nc-sub Ψ (ƛ {A} {B} N) xs ρ = ƛ (nc-sub (Ψ , ▸ A) N xs ρ)
 nc-sub Ψ (▹ x · S) xs ρ = ▹ (tvar-str Ψ x) · sc-sub Ψ S xs ρ
 nc-sub Ψ (u [ σ ] · S) xs ρ = (u [ nsc-sub Ψ σ xs ρ ]) · sc-sub Ψ S xs ρ
 nc-sub Ψ (p ♯[ σ ] · S) xs ρ = (p ♯[ nsc-sub Ψ σ xs ρ ]) · sc-sub Ψ S xs ρ
 nc-sub Ψ (π x (s [ σ ]) · S) xs ρ = π x (s [ nsc-sub Ψ σ xs ρ ]) · sc-sub Ψ S xs ρ
 nc-sub Ψ (π (pop ()) (id xs) · S) xs' ρ

 sc-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Φ} {φ} Ψ₂ {A B} -> spine Δ (Ψ₁ , ▹ φ << Ψ₂) A B -> cvar Φ φ -> rsub Δ Ψ₁ Φ -> spine Δ (Ψ₁ << Ψ₂) A B
 sc-sub Ψ ε xs ρ = ε
 sc-sub Ψ (N , S) xs ρ = (nc-sub Ψ N xs ρ) , sc-sub Ψ S xs ρ

 nsc-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Φ} {φ} Ψ₂ {χ} -> nsub Δ (Ψ₁ , ▹ φ << Ψ₂) χ -> cvar Φ φ -> rsub Δ Ψ₁ Φ -> nsub Δ (Ψ₁ << Ψ₂) χ
 nsc-sub Ψ ⊡ xs ρ = ⊡
 nsc-sub Ψ (σ , N) xs ρ = (nsc-sub Ψ σ xs ρ) , (nc-sub Ψ N xs ρ)
 nsc-sub Ψ (σ ,[ xs' ] (s [ σ' ])) xs ρ = nsc-sub Ψ σ xs ρ ,[ xs' ] (s [ nsc-sub Ψ σ' xs ρ ])
 nsc-sub Ψ (σ ,[ top ] (id xs')) xs ρ with ceq? Ψ xs'
 nsc-sub Ψ (σ ,[ top ] (id .(cthatone Ψ))) xs ρ | same = nsc-sub Ψ σ xs ρ ,[ xs ] (rs-wkn _ Ψ ⊡ ρ)
 nsc-sub Ψ (σ ,[ top ] (id .(cvar-wkn1 Ψ xs'))) xs ρ | diff xs' = (nsc-sub Ψ σ xs ρ) ,[ top ] (id xs')
 nsc-sub Ψ (σ ,[ pop () ] id xs') xs ρ


mutual
 n-sim-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} Ψ₂ {Φ} {A} -> ntm Δ (Ψ₁ << Ψ₂) A -> nsub Δ Φ Ψ₁ -> ntm Δ (Φ << Ψ₂) A
 n-sim-sub {Ω} {Δ} Ψ {Φ} {A} N ⊡ = subst (λ α → ntm Δ α A) (trans (<<-assoc ⊡ Φ Ψ) (<<-idl (Φ << Ψ))) (n-wkn ⊡ Φ Ψ N)
 n-sim-sub {Ω} {Δ} Ψ {.Φ'} {A} N (_,_ {Φ'} {Φ} {B} σ N') with subst (λ α -> ntm Δ α A) (sym (<<-assoc Φ' (⊡ , ▸ B) Ψ)) (n-sim-sub (⊡ , ▸ B << Ψ) (subst (λ α → ntm Δ α A) (<<-assoc Φ (⊡ , ▸ B) Ψ) N) σ)
 ... | q = n-sub Ψ q N'
 n-sim-sub {Ω} {Δ} Ψ {.Φ'} {A} N (_,[_]_ {Φ'} {Φ} {Φ''} {φ} σ xs ρ) with subst (λ α -> ntm Δ α A) (sym (<<-assoc Φ' (⊡ , ▹ φ) Ψ)) (n-sim-sub (⊡ , ▹ φ << Ψ) (subst (λ α → ntm Δ α A) (<<-assoc Φ (⊡ , ▹ φ) Ψ) N) σ)
 ... | q = nc-sub Ψ q xs ρ 

n-sim-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {Φ} {A} -> ntm Δ Ψ₁ A -> nsub Δ Φ Ψ₁ -> ntm Δ Φ A
n-sim-sub' N σ = n-sim-sub ⊡ N σ

-- Now I need all 3 kinds of meta-substitution...


