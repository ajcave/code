module contextual-substvars-spine where
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

 ▸ : (A : tp) -> tctx-elt Ω

data tctx (Ω : schema-ctx) : Set where
 ⊡ : tctx Ω
 ▹ : (φ : var Ω *) -> tctx Ω
 _,_ : (Ψ : tctx Ω) -> (A : tctx-elt Ω) -> tctx Ω

data tvar {Ω : schema-ctx} : ∀ (Γ : tctx Ω) (T : tp) -> Set where
 top : ∀ {Γ T} -> tvar (Γ , (▸ T)) T
 pop : ∀ {Γ T S} -> (x : tvar Γ T) -> tvar (Γ , S) T

data cvar {Ω : schema-ctx} : ∀ (Γ : tctx Ω) (φ : var Ω *) -> Set where
 top : ∀ {φ} -> cvar (▹ φ) φ
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

_<<_ : ∀ {Ω} -> tctx Ω -> ctx tp -> tctx Ω
Ψ₁ << ⊡ = Ψ₁
Ψ₁ << (Ψ , A) = (Ψ₁ << Ψ) , (▸ A)

_<<'_ : ctx tp -> ctx tp -> ctx tp
Ψ <<' ⊡ = Ψ
Ψ <<' (Φ , T) = (Ψ <<' Φ) , T

infixl 10 _<<_

<<-assoc : ∀ {Ω} (Ψ₁ : tctx Ω) Ψ₂ Ψ₃ -> (Ψ₁ << Ψ₂) << Ψ₃ ≡ Ψ₁ << (Ψ₂ <<' Ψ₃)
<<-assoc {Ω} Ψ₁ Ψ₂ ⊡ = refl
<<-assoc {Ω} Ψ₁ Ψ₂ (Ψ , A) = cong (λ α → α , ▸ A) (<<-assoc Ψ₁ Ψ₂ Ψ)

{-<<-idl : ∀ {Ω} (Ψ : tctx Ω) -> ⊡ << Ψ ≡ Ψ
<<-idl ⊡ = refl
<<-idl (Ψ , A) = cong (λ α → α , A) (<<-idl Ψ) -}

-- TODO: Give also a non-normal calculus, which is convenient
mutual
 data head {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ▹ : ∀ {A} (x : tvar Ψ A) -> head Δ Ψ A
  _[_] : ∀ {A Φ} (u : var Δ (% A [ Φ ])) (σ : nsub Δ Ψ Φ) -> head Δ Ψ A
  _♯[_] : ∀ {A Φ} (p : var Δ (♯ A [ Φ ])) (σ : nsub Δ Ψ Φ) -> head Δ Ψ A
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
  [_]_ : ∀ {Ψ Φ₂ φ} (xs : cvar Φ₂ φ) (ρ : rsub Δ Ψ Φ₂) -> nsub Δ Ψ (▹ φ)
  id : ∀ {Ψ φ} (xs : cvar Ψ φ) -> nsub Δ Ψ (▹ φ)
 data rsub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  _[_] : ∀ {Ψ Φ₁ Φ₂} (s : var Δ ($ Φ₁ [ Φ₂ ])) (σ : nsub Δ Ψ Φ₂) -> rsub Δ Ψ Φ₁

⟦_⟧tc : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (Φ : tctx Ω₁) -> tctx Ω₂
⟦_⟧tc Ψs ⊡ = ⊡
⟦_⟧tc Ψs (▹ φ) = lookup Ψs φ
⟦_⟧tc Ψs (Φ , (▸ A)) = ⟦ Ψs ⟧tc Φ , (▸ A)

⟦⟧tc-<< : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) Φ₁ Φ₂
 -> ⟦ Ψs ⟧tc (Φ₁ << Φ₂) ≡ ((⟦ Ψs ⟧tc Φ₁) << Φ₂)
⟦⟧tc-<< Ψs Φ₁ ⊡ = refl
--⟦⟧tc-<< Ψs Φ₁ (▹ φ) = ? --trans (cong (λ α → α << lookup Ψs φ) (⟦⟧tc-<< Ψs Φ₁ ψ)) (<<-assoc (⟦ Ψs ⟧tc Φ₁) (⟦ Ψs ⟧tc ψ) (lookup Ψs φ))
⟦⟧tc-<< Ψs Φ₁ (ψ , A) = cong (λ α → α , ▸ A) (⟦⟧tc-<< Ψs Φ₁ ψ)


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
⟦_⟧tv Ψs (pop {Γ} {T} {▸ A} x) = pop (⟦ Ψs ⟧tv x)

tvar-wkn : ∀ {Ω} (Ψ₁ : tctx Ω) Ψ₂ Ψ₃ {A} -> tvar (Ψ₁ << Ψ₃) A -> tvar (Ψ₁ << Ψ₂ << Ψ₃) A
tvar-wkn Ψ₁ Ψ₂ ⊡ x = <<tv x Ψ₂
tvar-wkn Ψ₁ Ψ₂ (Ψ , .A) {A} top = top
tvar-wkn Ψ₁ Ψ₂ (Ψ , A) (pop x) = pop (tvar-wkn Ψ₁ Ψ₂ Ψ x)

tvar-wkn' : ∀ {Ω} (Ψ₂ : tctx Ω) Ψ₃ {A} -> tvar {Ω} (⊡ << Ψ₃) A -> tvar (Ψ₂ << Ψ₃) A
tvar-wkn' Ψ₂ ⊡ () 
tvar-wkn' Ψ₂ (Ψ , .A) {A} top = top
tvar-wkn' Ψ₂ (Ψ , A) (pop x) = pop (tvar-wkn' Ψ₂ Ψ x)

tvar-wkn1 : ∀ {Ω} {Ψ₁ : tctx Ω} {B} Ψ₃ {A} -> tvar (Ψ₁ << Ψ₃) A -> tvar (Ψ₁ , ▸ B << Ψ₃) A
tvar-wkn1 {Ω} {Ψ₁} {B} Ψ₃ x = tvar-wkn Ψ₁ (⊡ , B) Ψ₃ x

cvar-wkn : ∀ {Ω} (Ψ₁ : tctx Ω) Ψ₂ Ψ₃ {φ} -> cvar (Ψ₁ << Ψ₃) φ -> cvar (Ψ₁ << Ψ₂ << Ψ₃) φ
cvar-wkn Ψ₁ Ψ₂ ⊡ xs = <<cv xs Ψ₂
cvar-wkn Ψ₁ Ψ₂ (Ψ , A) (pop xs) = pop (cvar-wkn Ψ₁ Ψ₂ Ψ xs)

cvar-wkn' : ∀ {Ω} (Ψ₂ : tctx Ω) Ψ₃ {φ} -> cvar (⊡ << Ψ₃) φ -> cvar (Ψ₂ << Ψ₃) φ
cvar-wkn' Ψ₂ ⊡ ()
cvar-wkn' Ψ₂ (Ψ , A) (pop xs) = pop (cvar-wkn' Ψ₂ Ψ xs)

{-cvar-wkn1 : ∀ {Ω} {Ψ₁ : tctx Ω} {B} Ψ₃ {A} -> cvar (Ψ₁ << Ψ₃) A -> cvar (Ψ₁ , B << Ψ₃) A
cvar-wkn1 {Ω} {Ψ₁} {B} Ψ₃ x = cvar-wkn Ψ₁ (⊡ , ▸ B) Ψ₃ x -}

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
 n-wkn Ψ₁ Ψ₂ Ψ₃ (ƛ {A} {B} N) = ƛ (n-wkn Ψ₁ Ψ₂ (Ψ₃ , A) N)
 n-wkn Ψ₁ Ψ₂ Ψ₃ (H · S) = (h-wkn Ψ₁ Ψ₂ Ψ₃ H) · (s-wkn Ψ₁ Ψ₂ Ψ₃ S)

 ns-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {Φ} -> nsub Δ (Ψ₁ << Ψ₃) Φ -> nsub Δ (Ψ₁ << Ψ₂ << Ψ₃) Φ
 ns-wkn Ψ₁ Ψ₂ Ψ₃ ⊡ = ⊡
 ns-wkn Ψ₁ Ψ₂ Ψ₃ (σ , N) = (ns-wkn Ψ₁ Ψ₂ Ψ₃ σ) , (n-wkn Ψ₁ Ψ₂ Ψ₃ N)
 ns-wkn Ψ₁ Ψ₂ Ψ₃ ([ xs ] ρ) = [ xs ] (rs-wkn Ψ₁ Ψ₂ Ψ₃ ρ)
 ns-wkn Ψ₁ Ψ₂ Ψ₃ (id φ) = id (cvar-wkn Ψ₁ Ψ₂ Ψ₃ φ)

 rs-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {Φ} -> rsub Δ (Ψ₁ << Ψ₃) Φ -> rsub Δ (Ψ₁ << Ψ₂ << Ψ₃) Φ
 rs-wkn Ψ₁ Ψ₂ Ψ₃ (s [ σ ]) = s [ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]

mutual
 h-wkn' : ∀ {Ω} {Δ : mctx Ω} Ψ₂ Ψ₃ {A} -> head Δ (⊡ << Ψ₃) A -> head Δ (Ψ₂ << Ψ₃) A
 h-wkn' Ψ₂ Ψ₃ (▹ x) = ▹ (tvar-wkn' Ψ₂ Ψ₃ x)
 h-wkn' Ψ₂ Ψ₃ (u [ σ ]) = u [ ns-wkn' Ψ₂ Ψ₃ σ ]
 h-wkn' Ψ₂ Ψ₃ (p ♯[ σ ]) = p ♯[ ns-wkn' Ψ₂ Ψ₃ σ ]
 h-wkn' Ψ₂ Ψ₃ (π x ρ) = π x (rs-wkn' Ψ₂ Ψ₃ ρ)

 s-wkn' : ∀ {Ω} {Δ : mctx Ω} Ψ₂ Ψ₃ {A B} -> spine Δ (⊡ << Ψ₃) A B -> spine Δ ( Ψ₂ << Ψ₃) A B
 s-wkn' Ψ₂ Ψ₃ ε = ε
 s-wkn' Ψ₂ Ψ₃ (N , S) = (n-wkn' Ψ₂ Ψ₃ N) , (s-wkn' Ψ₂ Ψ₃ S)

 n-wkn' : ∀ {Ω} {Δ : mctx Ω} Ψ₂ Ψ₃ {A} -> ntm Δ (⊡ << Ψ₃) A -> ntm Δ (Ψ₂ << Ψ₃) A
 n-wkn' Ψ₂ Ψ₃ (ƛ {A} {B} N) = ƛ (n-wkn' Ψ₂ (Ψ₃ , A) N)
 n-wkn' Ψ₂ Ψ₃ (H · S) = (h-wkn' Ψ₂ Ψ₃ H) · (s-wkn' Ψ₂ Ψ₃ S)

 ns-wkn' : ∀ {Ω} {Δ : mctx Ω} Ψ₂ Ψ₃ {Φ} -> nsub Δ (⊡ << Ψ₃) Φ -> nsub Δ (Ψ₂ << Ψ₃) Φ
 ns-wkn' Ψ₂ Ψ₃ ⊡ = ⊡
 ns-wkn' Ψ₂ Ψ₃ (σ , N) = (ns-wkn' Ψ₂ Ψ₃ σ) , (n-wkn' Ψ₂ Ψ₃ N)
 ns-wkn' Ψ₂ Ψ₃ ([ xs ] ρ) = [ xs ] (rs-wkn' Ψ₂ Ψ₃ ρ)
 ns-wkn' Ψ₂ Ψ₃ (id φ) = id (cvar-wkn' Ψ₂ Ψ₃ φ)

 rs-wkn' : ∀ {Ω} {Δ : mctx Ω} Ψ₂ Ψ₃ {Φ} -> rsub Δ (⊡ << Ψ₃) Φ -> rsub Δ (Ψ₂ << Ψ₃) Φ
 rs-wkn' Ψ₂ Ψ₃ (s [ σ ]) = s [ ns-wkn' Ψ₂ Ψ₃ σ ]

cvar-str : ∀ {Ω} {Ψ₁ : tctx Ω} {B} Ψ₂ {φ} -> cvar (Ψ₁ , ▸ B << Ψ₂) φ -> cvar (Ψ₁ << Ψ₂) φ
cvar-str ⊡ (pop xs) = xs
cvar-str (Ψ , A) (pop xs) = pop (cvar-str Ψ xs)

thatone : ∀ {Ω} {Ψ : tctx Ω} Φ {A} -> tvar (Ψ , ▸ A << Φ) A
thatone ⊡ = top
thatone (Φ , A) = pop (thatone Φ)

data eqV {Ω} {Ψ : tctx Ω} : ∀ {A} B Φ -> tvar ((Ψ , ▸ B) << Φ) A -> Set where
 same : ∀ {A Φ} -> eqV A Φ (thatone Φ)
 diff : ∀ {A B Φ} (x : tvar (Ψ << Φ) A) -> eqV B Φ (tvar-wkn1 Φ x)

eq? : ∀ {Ω} {Ψ : tctx Ω} Φ {A B} (x : tvar (Ψ , ▸ A << Φ) B) -> eqV A Φ x
eq? ⊡ top = same
eq? ⊡ (pop x) = diff x
eq? (Ψ , .B) {A} {B} top = diff top
eq? (Ψ , A) (pop x) with eq? Ψ x
eq? (Ψ , A) (pop .(thatone Ψ)) | same = same
eq? (Ψ , A) (pop .(tvar-wkn1 Ψ x)) | diff x = diff (pop x)

mutual
 n-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {A} -> ntm Δ (Ψ₁ , ▸ B << Ψ₂) A -> ntm Δ Ψ₁ B -> ntm Δ (Ψ₁ << Ψ₂) A
 n-sub Ψ (ƛ {A} {B} N) M = ƛ (n-sub (Ψ , A) N M)
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
 ns-sub Ψ ([ xs ] ρ) M = [ xs ] (rs-sub Ψ ρ M)
 ns-sub Ψ (id φ) M = id (cvar-str Ψ φ)

 rs-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {Φ} -> rsub Δ (Ψ₁ , ▸ B << Ψ₂) Φ -> ntm Δ Ψ₁ B -> rsub Δ (Ψ₁ << Ψ₂) Φ
 rs-sub Ψ (s [ σ ]) M = s [ ns-sub Ψ σ M ]

 _◇_ : ∀ {Ω} {Δ : mctx Ω} {Ψ} {A B} -> ntm Δ Ψ A -> spine Δ Ψ A B -> ntm Δ Ψ B
 N ◇ ε = N
 (ƛ N) ◇ (N' , S) = (n-sub ⊡ N N') ◇ S


tvar-str : ∀ {Ω} {B : var Ω *} Ψ₂ {Φ : tctx Ω} {φ} -> tvar (▹ B << Ψ₂) φ -> tvar (Φ << Ψ₂) φ
tvar-str ⊡ ()
tvar-str (Ψ , A) top = top
tvar-str (Ψ , A) (pop xs) = pop (tvar-str Ψ xs)

ceq : ∀ {Ω} Φ {A : var Ω *} {B} (x : cvar (▹ A << Φ) B) -> A ≡ B
ceq ⊡ top = refl
ceq (Φ , T) (pop x) = ceq Φ x


mutual
 nc-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {φ} Ψ₂ {A} -> ntm Δ (▹ φ << Ψ₂) A -> nsub Δ Ψ₁ (▹ φ)  -> ntm Δ (Ψ₁ << Ψ₂) A
 nc-sub' Ψ (ƛ {A} {B} N) ρ = ƛ (nc-sub' (Ψ , A) N ρ)
 nc-sub' Ψ (▹ x · S) ρ = (▹ (tvar-str Ψ x)) · sc-sub' Ψ S ρ
 nc-sub' Ψ (u [ σ ] · S) ρ = (u [ nsc-sub' Ψ σ ρ ]) · sc-sub' Ψ S ρ
 nc-sub' Ψ (p ♯[ σ ] · S) ρ = (p ♯[ nsc-sub' Ψ σ ρ ]) · sc-sub' Ψ S ρ
 nc-sub' Ψ (π x (s [ σ ]) · S) ρ = π x (s [ nsc-sub' Ψ σ ρ ]) · sc-sub' Ψ S ρ

 sc-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {φ} Ψ₂ {A B} -> spine Δ (▹ φ << Ψ₂) A B -> nsub Δ Ψ₁ (▹ φ) -> spine Δ (Ψ₁ << Ψ₂) A B
 sc-sub' Ψ ε ρ = ε
 sc-sub' Ψ (N , S) ρ = (nc-sub' Ψ N ρ) , sc-sub' Ψ S ρ

 nsc-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {φ} Ψ₂ {χ} -> nsub Δ (▹ φ << Ψ₂) χ -> nsub Δ Ψ₁ (▹ φ) -> nsub Δ (Ψ₁ << Ψ₂) χ
 nsc-sub' Ψ ⊡ ρ = ⊡
 nsc-sub' Ψ (σ , N) ρ = (nsc-sub' Ψ σ ρ) , (nc-sub' Ψ N    ρ)
 nsc-sub' Ψ ([ xs' ] (s [ σ' ])) ρ = [ xs' ] (s [ nsc-sub' Ψ σ'    ρ ])
 nsc-sub' Ψ (id φ) ρ with ceq Ψ φ
 ... | refl = ns-wkn _ Ψ ⊡ ρ

mutual
 n-sim-sub : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Φ {A} -> ntm Δ (Ψ₁ << Ψ₂) A -> nsub Δ Φ Ψ₁ -> ntm Δ (Φ << Ψ₂) A
 n-sim-sub .⊡ Ψ₂ Φ N ⊡ = n-wkn' Φ Ψ₂ N
 n-sim-sub {Ω} {Δ} .(Φ₁ , ▸ A₁) Ψ₂ Φ {A} N (_,_ {.Φ} {Φ₁} {A₁} σ N₁) with subst (λ α -> ntm Δ α A) (sym (<<-assoc Φ (⊡ , A₁) Ψ₂)) (n-sim-sub Φ₁ ((⊡ , A₁) <<' Ψ₂) Φ (subst (λ α → ntm Δ α A) (<<-assoc Φ₁ (⊡ , A₁) Ψ₂) N) σ)
 ... | q = n-sub Ψ₂ q N₁
 n-sim-sub .(▹ φ) Ψ₂ Φ N ([_]_ {.Φ} {Φ₂} {φ} xs ρ) = nc-sub' Ψ₂ N ([ xs ] ρ)
 n-sim-sub .(▹ φ) Ψ₂ Φ N (id {.Φ} {φ} xs) = nc-sub' Ψ₂ N (id xs)

 

n-sim-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {Φ} {A} -> ntm Δ Ψ₁ A -> nsub Δ Φ Ψ₁ -> ntm Δ Φ A
n-sim-sub' N σ = n-sim-sub _ ⊡ _ N σ 

{-
mutual
 n-sim-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} Ψ₂ {Φ} {A} -> ntm Δ (Ψ₁ << Ψ₂) A -> nsub Δ Φ Ψ₁ -> ntm Δ (Φ << Ψ₂) A
 n-sim-sub {Ω} {Δ} Ψ {Φ} {A} N ⊡ = subst (λ α → ntm Δ α A) (trans (<<-assoc ⊡ Φ Ψ) ({! <<-idl (Φ << Ψ) !})) (n-wkn ⊡ Φ Ψ N)
 n-sim-sub {Ω} {Δ} Ψ {.Φ'} {A} N (_,_ {Φ'} {Φ} {B} σ N') with subst (λ α -> ntm Δ α A) (sym (<<-assoc Φ' (⊡ , ▸ B) Ψ)) (n-sim-sub (⊡ , ▸ B << Ψ) (subst (λ α → ntm Δ α A) (<<-assoc Φ (⊡ , ▸ B) Ψ) N) σ)
 ... | q = n-sub Ψ q N'
 n-sim-sub {Ω} {Δ} Ψ {.Φ'} {A} N (_,[_]_ {Φ'} {Φ} {Φ''} {φ} σ xs ρ) with subst (λ α -> ntm Δ α A) (sym (<<-assoc Φ' (⊡ , ▹ φ) Ψ)) (n-sim-sub (⊡ , ▹ φ << Ψ) (subst (λ α → ntm Δ α A) (<<-assoc Φ (⊡ , ▹ φ) Ψ) N) σ)
 ... | q = ? --nc-sub Ψ q xs ρ 

n-sim-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {Φ} {A} -> ntm Δ Ψ₁ A -> nsub Δ Φ Ψ₁ -> ntm Δ Φ A
n-sim-sub' N σ = n-sim-sub ⊡ N σ -}

-- Now I need all 3 kinds of meta-substitution...
