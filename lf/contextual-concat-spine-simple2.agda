module contextual-concat-spine-simple2 where
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

data bool : Set where
 type cntx : bool

elt-type : bool -> schema-ctx -> Set
elt-type type Ω = tp
elt-type cntx Ω = var Ω *

record tctx-elt (Ω : schema-ctx) : Set where
 constructor _,,_
 field
  which : bool
  val : elt-type which Ω

con : ∀ {Ω} (b : bool) -> elt-type b Ω -> tctx-elt Ω
con = _,,_

syntax con t B = B ∶ t

data tctx (Ω : schema-ctx) : Set where
 ⊡ : tctx Ω
 _,_ : (Ψ : tctx Ω) -> (A : tctx-elt Ω) -> tctx Ω

data gvar {Ω : schema-ctx} : ∀ (Γ : tctx Ω) (A : tctx-elt Ω) -> Set where
 top : ∀ {Γ T} -> gvar (Γ , T) T
 pop : ∀ {Γ T S} -> (x : gvar Γ T) -> gvar (Γ , S) T

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
  ▹ : ∀ {A} (x : gvar Ψ (A ∶ type)) -> head Δ Ψ A
  _[_] : ∀ {A Φ} (u : var Δ (% A [ Φ ])) (σ : nsub Δ Ψ Φ) -> head Δ Ψ A
  _♯[_] : ∀ {A Φ} (p : var Δ (♯ A [ Φ ])) (σ : nsub Δ Ψ Φ) -> head Δ Ψ A
  π_[_[_]] : ∀ {Φ₁ Φ₂ A} (x : gvar Φ₁ (A ∶ type)) (s : var Δ ($ Φ₁ [ Φ₂ ])) (σ : nsub Δ Ψ Φ₂) -> head Δ Ψ A
 data spine {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> tp -> Set where
  ε : ∀ {C} -> spine Δ Ψ C C
  _,_ : ∀ {A B C} (N : ntm Δ Ψ A) (S : spine Δ Ψ B C) -> spine Δ Ψ (A ⇒ B) C
 data ntm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ƛ : ∀ {A B} (N : ntm Δ (Ψ , (A ∶ type)) B) -> ntm Δ Ψ (A ⇒ B)
  _·_ : ∀ {A} (H : head Δ Ψ A) (S : spine Δ Ψ A i) -> ntm Δ Ψ i
 data nsub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  ⊡ : ∀ {Ψ} -> nsub Δ Ψ ⊡
  _,_ : ∀ {Ψ Φ A} (σ : nsub Δ Ψ Φ) (K : nval Δ Ψ A) -> nsub Δ Ψ (Φ , A)
 data nval {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tctx-elt Ω -> Set where
  ▸ : ∀ {A} (N : ntm Δ Ψ A) -> nval Δ Ψ (A ∶ type)
  _[_[_]] : ∀ {Φ₂ Φ₃ φ} (xs : gvar Φ₂ (φ ∶ cntx)) (s : var Δ ($ Φ₂ [ Φ₃ ])) (σ : nsub Δ Ψ Φ₃) -> nval Δ Ψ (φ ∶ cntx)
  ▹ : ∀ {φ} (xs : gvar Ψ (φ ∶ cntx)) -> nval Δ Ψ (φ ∶ cntx)

⟦_⟧tc : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (Φ : tctx Ω₁) -> tctx Ω₂
⟦_⟧tc Ψs ⊡ = ⊡
⟦_⟧tc Ψs (Φ , (cntx ,, φ)) = ⟦ Ψs ⟧tc Φ << (lookup Ψs φ)
⟦_⟧tc Ψs (Φ , (type ,, A)) = ⟦ Ψs ⟧tc Φ , (A ∶ type)

⟦⟧tc-<< : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) Φ₁ Φ₂
 -> ⟦ Ψs ⟧tc (Φ₁ << Φ₂) ≡ ((⟦ Ψs ⟧tc Φ₁) << (⟦ Ψs ⟧tc Φ₂))
⟦⟧tc-<< Ψs Φ₁ ⊡ = refl
⟦⟧tc-<< Ψs Φ₁ (ψ , (cntx ,, φ)) = trans (cong (λ α → α << lookup Ψs φ) (⟦⟧tc-<< Ψs Φ₁ ψ)) (<<-assoc (⟦ Ψs ⟧tc Φ₁) (⟦ Ψs ⟧tc ψ) (lookup Ψs φ))
⟦⟧tc-<< Ψs Φ₁ (ψ , (type ,, A)) = cong (λ α → α , (A ∶ type)) (⟦⟧tc-<< Ψs Φ₁ ψ)

⟦_⟧mt : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (U : mtp Ω₁) -> mtp Ω₂
⟦_⟧mt Ψs ($ Ψ [ Φ ]) = $ (⟦ Ψs ⟧tc Ψ) [ ⟦ Ψs ⟧tc Φ ]
⟦_⟧mt Ψs ((♯ A) [ Φ ]) = (♯ A) [ ⟦ Ψs ⟧tc Φ ]
⟦_⟧mt Ψs (% A [ Φ ]) = % A [ ⟦ Ψs ⟧tc Φ ]

⟦_⟧mc : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (Δ : mctx Ω₁) -> mctx Ω₂
⟦_⟧mc Ψs Δ = cmap ⟦ Ψs ⟧mt Δ

<<gv : ∀ {Ω} {Ψ₁ : tctx Ω} {A} -> gvar Ψ₁ A -> ∀ Ψ₂ -> gvar (Ψ₁ << Ψ₂) A
<<gv x ⊡ = x
<<gv x (Ψ , A') = pop (<<gv x Ψ)

⟦_⟧tv : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Φ : tctx Ω₁} {A} -> gvar Φ (A ∶ type) -> gvar (⟦ Ψs ⟧tc Φ) (A ∶ type)
⟦_⟧tv Ψs top = top
⟦_⟧tv Ψs {Φ , (cntx ,, φ)} (pop x) = <<gv (⟦ Ψs ⟧tv x) (lookup Ψs φ)
⟦_⟧tv Ψs {Φ , (type ,, A)} (pop x) = pop (⟦ Ψs ⟧tv x)


⟦_⟧te : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (A : tctx-elt Ω₁) -> tctx Ω₂
⟦_⟧te Ψs (type ,, A) = ⊡ , (A ∶ type)
⟦_⟧te Ψs (cntx ,, φ) = lookup Ψs φ


gvar-wkn : ∀ {Ω} (Ψ₁ Ψ₂ Ψ₃ : tctx Ω) {A} -> gvar (Ψ₁ << Ψ₃) A -> gvar (Ψ₁ << Ψ₂ << Ψ₃) A
gvar-wkn Ψ₁ Ψ₂ ⊡ x = <<gv x Ψ₂
gvar-wkn Ψ₁ Ψ₂ (Ψ , .A) {A} top = top
gvar-wkn Ψ₁ Ψ₂ (Ψ , A) (pop x) = pop (gvar-wkn Ψ₁ Ψ₂ Ψ x)

gvar-wkn1 : ∀ {Ω} {Ψ₁ B} (Ψ₃ : tctx Ω) {A} -> gvar (Ψ₁ << Ψ₃) A -> gvar (Ψ₁ , B << Ψ₃) A
gvar-wkn1 {Ω} {Ψ₁} {B} Ψ₃ x = gvar-wkn Ψ₁ (⊡ , B) Ψ₃ x

mutual
 h-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A} -> head Δ (Ψ₁ << Ψ₃) A -> head Δ (Ψ₁ << Ψ₂ << Ψ₃) A
 h-wkn Ψ₁ Ψ₂ Ψ₃ (▹ x) = ▹ (gvar-wkn Ψ₁ Ψ₂ Ψ₃ x)
 h-wkn Ψ₁ Ψ₂ Ψ₃ (u [ σ ]) = u [ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]
 h-wkn Ψ₁ Ψ₂ Ψ₃ (p ♯[ σ ]) = p ♯[ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]
 h-wkn Ψ₁ Ψ₂ Ψ₃ (π x [ s [ σ ]]) = π x [ s [ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]]

 s-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A B} -> spine Δ (Ψ₁ << Ψ₃) A B -> spine Δ (Ψ₁ << Ψ₂ << Ψ₃) A B
 s-wkn Ψ₁ Ψ₂ Ψ₃ ε = ε
 s-wkn Ψ₁ Ψ₂ Ψ₃ (N , S) = (n-wkn Ψ₁ Ψ₂ Ψ₃ N) , (s-wkn Ψ₁ Ψ₂ Ψ₃ S)

 n-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {A} -> ntm Δ (Ψ₁ << Ψ₃) A -> ntm Δ (Ψ₁ << Ψ₂ << Ψ₃) A
 n-wkn Ψ₁ Ψ₂ Ψ₃ (ƛ {A} {B} N) = ƛ (n-wkn Ψ₁ Ψ₂ (Ψ₃ , (A ∶ type)) N)
 n-wkn Ψ₁ Ψ₂ Ψ₃ (H · S) = (h-wkn Ψ₁ Ψ₂ Ψ₃ H) · (s-wkn Ψ₁ Ψ₂ Ψ₃ S)

 ns-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {Φ} -> nsub Δ (Ψ₁ << Ψ₃) Φ -> nsub Δ (Ψ₁ << Ψ₂ << Ψ₃) Φ
 ns-wkn Ψ₁ Ψ₂ Ψ₃ ⊡ = ⊡
 ns-wkn Ψ₁ Ψ₂ Ψ₃ (σ , V) = (ns-wkn Ψ₁ Ψ₂ Ψ₃ σ) , (nv-wkn Ψ₁ Ψ₂ Ψ₃ V)

 nv-wkn : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ {Φ} -> nval Δ (Ψ₁ << Ψ₃) Φ -> nval Δ (Ψ₁ << Ψ₂ << Ψ₃) Φ
 nv-wkn Ψ₁ Ψ₂ Ψ₃ (▸ N) = ▸ (n-wkn Ψ₁ Ψ₂ Ψ₃ N)
 nv-wkn Ψ₁ Ψ₂ Ψ₃ (xs [ s [ σ ]]) = xs [ s [ ns-wkn Ψ₁ Ψ₂ Ψ₃ σ ]]
 nv-wkn Ψ₁ Ψ₂ Ψ₃ (▹ xs) = ▹ (gvar-wkn Ψ₁ Ψ₂ Ψ₃ xs)

thatone : ∀ {Ω} {Ψ : tctx Ω} Φ {A} -> gvar (Ψ , A << Φ) A
thatone ⊡ = top
thatone (Φ , A) = pop (thatone Φ)

data eqV {Ω} {Ψ : tctx Ω} : ∀ {A} B Φ -> gvar ((Ψ , B) << Φ) A -> Set where
 same : ∀ {A Φ} -> eqV A Φ (thatone Φ)
 diff : ∀ {A B Φ} (x : gvar (Ψ << Φ) A) -> eqV B Φ (gvar-wkn1 Φ x)

eq? : ∀ {Ω} {Ψ : tctx Ω} Φ {A B} (x : gvar (Ψ , A << Φ) B) -> eqV A Φ x
eq? ⊡ top = same
eq? ⊡ (pop x) = diff x
eq? (Ψ , A) top = diff top
eq? (Ψ , A) (pop x) with eq? Ψ x
eq? (Ψ , A) (pop .(thatone Ψ)) | same = same
eq? (Ψ , A) (pop .(gvar-wkn1 Ψ x)) | diff x = diff (pop x)

-- We're making clever use of elt-type here to get termination checking.
-- Expressing the sum of var Ω * or tp by dependent pair tagging is better for termination
mutual
 sub-n : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {t} {B} Ψ₂ {A} -> ntm Δ (Ψ₁ , (B ∶ t) << Ψ₂) A -> nval Δ Ψ₁ (B ∶ t) -> ntm Δ (Ψ₁ << Ψ₂) A
 sub-n Ψ (ƛ N) V = ƛ (sub-n (Ψ , _) N V)
 sub-n Ψ (▹ x · S) V with eq? Ψ x
 sub-n Ψ (▹ .(thatone Ψ) · S) (▸ N) | same   = n-wkn _ Ψ ⊡ N ◆ sub-s Ψ S (▸ N)
 sub-n Ψ (▹ .(gvar-wkn1 Ψ x) · S) V | diff x = ▹ x · sub-s Ψ S V
 sub-n Ψ (u [ σ ] · S) V = u [ sub-ns Ψ σ V ] · sub-s Ψ S V
 sub-n Ψ (p ♯[ σ ] · S) V = p ♯[ sub-ns Ψ σ V ] · sub-s Ψ S V
 sub-n Ψ (π x [ s [ σ ]] · S) V = π x [ s [ sub-ns Ψ σ V ]] · sub-s Ψ S V

 sub-s : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {t} {B} Ψ₂ {A C} -> spine Δ (Ψ₁ , (B ∶ t) << Ψ₂) A C -> nval Δ Ψ₁ (B ∶ t) -> spine Δ (Ψ₁ << Ψ₂) A C
 sub-s Ψ ε V = ε
 sub-s Ψ (N , S) V = (sub-n Ψ N V) , (sub-s Ψ S V)

 sub-ns : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {t} {B} Ψ₂ {A} -> nsub Δ (Ψ₁ , (B ∶ t) << Ψ₂) A -> nval Δ Ψ₁ (B ∶ t) -> nsub Δ (Ψ₁ << Ψ₂) A
 sub-ns Ψ ⊡ V = ⊡
 sub-ns Ψ (σ , N) V = (sub-ns Ψ σ V) , sub-nv Ψ N V

 sub-nv : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {t} {B} Ψ₂ {χ} -> nval Δ (Ψ₁ , (B ∶ t) << Ψ₂) χ -> nval Δ Ψ₁ (B ∶ t) -> nval Δ (Ψ₁ << Ψ₂) χ
 sub-nv Ψ (▸ N) V = ▸ (sub-n Ψ N V)
 sub-nv Ψ (xs [ s [ σ ]]) V = xs [ s [ sub-ns Ψ σ V ]]
 sub-nv Ψ (▹ xs) V with eq? Ψ xs
 sub-nv Ψ (▹ .(thatone Ψ)) V      | same    = nv-wkn _ Ψ ⊡ V
 sub-nv Ψ (▹ .(gvar-wkn1 Ψ xs)) V | diff xs = ▹ xs

 _◆_ : ∀ {Ω} {Δ : mctx Ω} {Ψ} {A B} -> ntm Δ Ψ A -> spine Δ Ψ A B -> ntm Δ Ψ B
 N ◆ ε = N
 ƛ N ◆ (N' , S) = sub-n ⊡ N (▸ N') ◆ S

mutual
 helper : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} Ψ₂ Ψ₃ {Φ} {A} -> ntm Δ (Ψ₁ << Ψ₂ << Ψ₃) A -> nsub Δ Φ Ψ₁ -> ntm Δ (Φ << Ψ₂ << Ψ₃) A
 helper {Ω} {Δ} {Ψ₁} Ψ₂ Ψ₃ {Φ} {A} N σ = subst (λ α -> ntm Δ α A) (sym (<<-assoc Φ Ψ₂ Ψ₃)) (n-sim-sub (Ψ₂ << Ψ₃) (subst (λ α -> ntm Δ α A) (<<-assoc Ψ₁ Ψ₂ Ψ₃) N) σ)

 n-sim-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} Ψ₂ {Φ} {A} -> ntm Δ (Ψ₁ << Ψ₂) A -> nsub Δ Φ Ψ₁ -> ntm Δ (Φ << Ψ₂) A
 n-sim-sub {Ω} {Δ} Ψ {Φ} {A} N ⊡ = subst (λ α → ntm Δ α A) (trans (<<-assoc ⊡ Φ Ψ) (<<-idl (Φ << Ψ))) (n-wkn ⊡ Φ Ψ N)
 n-sim-sub Ψ N (σ , V) = sub-n Ψ (helper (⊡ , _) Ψ N σ) V

[_]n : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {Φ} {A} -> nsub Δ Φ Ψ₁ -> ntm Δ Ψ₁ A -> ntm Δ Φ A
[ σ ]n N = n-sim-sub ⊡ N σ

mutual
 helper-ns : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} Ψ₂ Ψ₃ {Φ} {A} -> nsub Δ (Ψ₁ << Ψ₂ << Ψ₃) A -> nsub Δ Φ Ψ₁ -> nsub Δ (Φ << Ψ₂ << Ψ₃) A
 helper-ns {Ω} {Δ} {Ψ₁} Ψ₂ Ψ₃ {Φ} {A} N σ = subst (λ α -> nsub Δ α A) (sym (<<-assoc Φ Ψ₂ Ψ₃)) (ns-sim-sub (Ψ₂ << Ψ₃) (subst (λ α -> nsub Δ α A) (<<-assoc Ψ₁ Ψ₂ Ψ₃) N) σ)

 ns-sim-sub : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} Ψ₂ {Φ} {A} -> nsub Δ (Ψ₁ << Ψ₂) A -> nsub Δ Φ Ψ₁ -> nsub Δ (Φ << Ψ₂) A
 ns-sim-sub {Ω} {Δ} Ψ {Φ} {A} N ⊡ = subst (λ α → nsub Δ α A) (trans (<<-assoc ⊡ Φ Ψ) (<<-idl (Φ << Ψ))) (ns-wkn ⊡ Φ Ψ N)
 ns-sim-sub Ψ N (σ , V) = sub-ns Ψ (helper-ns (⊡ , _) Ψ N σ) V

[_]ns : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {Φ} {A} -> nsub Δ Φ Ψ₁ -> nsub Δ Ψ₁ A -> nsub Δ Φ A
[ σ ]ns N = ns-sim-sub ⊡ N σ

[_]gv : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {Φ} {A} -> nsub Δ Φ Ψ₁ -> gvar Ψ₁ A -> nval Δ Φ A
[ ⊡ ]gv ()
[_]gv (σ , K) top = K
[_]gv (σ , K) (pop x) = [ σ ]gv x

-- TODO: Hmm if instead of a mutual definition, we did a tagged-with-n,r,s,ns definition, then we could have one nice notation, and even infer the n,r,s,ns implicitly

-- All 3 kinds of meta-substitution
foo : ∀ {Ω} Δ -> mtp Ω -> Set
foo Δ ($ Ψ [ Φ ]) = nsub Δ Φ Ψ
foo Δ (♯ A [ Φ ]) = gvar Φ (A ∶ type)
foo Δ (% A [ Φ ]) = ntm Δ Φ A

mutual
 ⟦_⟧mn : ∀ {Ω} {Δ1 Δ2 : mctx Ω} {Ψ} {A} -> gsubst Δ1 (foo Δ2) -> ntm Δ1 Ψ A -> ntm Δ2 Ψ A
 ⟦_⟧mn θ (ƛ N) = ƛ (⟦ θ ⟧mn N)
 ⟦_⟧mn θ (▹ x · S) = ▹ x · ⟦ θ ⟧mr S
 ⟦_⟧mn θ ((u [ σ ]) · S) = ([ ⟦ θ ⟧mns σ ]n (lookup θ u)) ◆ (⟦ θ ⟧mr S)
 ⟦_⟧mn θ ((p ♯[ σ ]) · S) with [ ⟦ θ ⟧mns σ ]gv (lookup θ p)
 ⟦_⟧mn θ ((p ♯[ σ ]) · S) | ▸ N = N ◆ (⟦ θ ⟧mr S)
 ⟦_⟧mn θ (π x [ s [ σ ]] · S) with [ [ ⟦ θ ⟧mns σ ]ns (lookup θ s) ]gv x
 ⟦_⟧mn θ (π x [ s [ σ ]] · S) | ▸ N = N ◆ ⟦ θ ⟧mr S

 ⟦_⟧mr : ∀ {Ω} {Δ1 Δ2 : mctx Ω} {Ψ} {A B} -> gsubst Δ1 (foo Δ2) -> spine Δ1 Ψ A B -> spine Δ2 Ψ A B
 ⟦_⟧mr θ ε = ε
 ⟦_⟧mr θ (N , S) = (⟦ θ ⟧mn N) , (⟦ θ ⟧mr S)

 ⟦_⟧mns : ∀ {Ω} {Δ1 Δ2 : mctx Ω} {Ψ} {A} -> gsubst Δ1 (foo Δ2) -> nsub Δ1 Ψ A -> nsub Δ2 Ψ A
 ⟦_⟧mns θ ⊡ = ⊡
 ⟦_⟧mns θ (σ , K) = (⟦ θ ⟧mns σ) , ⟦ θ ⟧mnv K

 ⟦_⟧mnv : ∀ {Ω} {Δ1 Δ2 : mctx Ω} {Ψ} {A} -> gsubst Δ1 (foo Δ2) -> nval Δ1 Ψ A -> nval Δ2 Ψ A
 ⟦_⟧mnv θ (▸ N) = ▸ (⟦ θ ⟧mn N)
 ⟦_⟧mnv θ (xs [ s [ σ ]]) = [ [ ⟦ θ ⟧mns σ ]ns (lookup θ s) ]gv xs
 ⟦_⟧mnv θ (▹ xs) = ▹ xs

-- Still need context substitution

⟦_⟧cv : ∀ {Ω₁ Ω₂} {Δ : mctx Ω₁} {A} -> (Ψs : gksubst Ω₁ (tctx Ω₂)) -> var Δ A -> var (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧mt A)
⟦_⟧cv Ψs top = top
⟦_⟧cv Ψs (pop y) = pop (⟦ Ψs ⟧cv y)


data blar {Ω} : ∀ (Ψ : tctx Ω) (φ : var Ω *) -> Set where
 con2 : ∀ Ψ₁ φ Ψ₂ -> blar (Ψ₁ , (φ ∶ cntx) << Ψ₂) φ
 
inv : ∀ {Ω} {Ψ : tctx Ω} {φ : var Ω *} -> gvar Ψ (φ ∶ cntx) -> blar Ψ φ
inv top = con2 _ _ ⊡
inv (pop x) with inv x
inv (pop x) | con2 Ψ₁ φ Ψ₂ = con2 Ψ₁ φ (Ψ₂ , _)

ns-id : ∀ {Ω} {Δ : mctx Ω} {Ψ} -> nsub Δ Ψ Ψ
ns-id {Ω} {Δ} {⊡} = ⊡
ns-id {Ω} {Δ} {Ψ , (type ,, A)} = ns-wkn Ψ (⊡ , con type A) ⊡ (ns-id {Ψ = Ψ}) , (▸ {!!})
ns-id {Ω} {Δ} {Ψ , (cntx ,, φ)} = ns-wkn Ψ (⊡ , (φ ∶ cntx)) ⊡ (ns-id {Ψ = Ψ}) , ▹ top

ns-id' : ∀ {Ω} {Δ : mctx Ω} Ψ₁ Ψ₂ Ψ₃ -> nsub Δ ((Ψ₁ << Ψ₂) << Ψ₃) Ψ₂
ns-id' {Ω} {Δ} Ψ₁ Ψ₂ Ψ₃ = ns-wkn (Ψ₁ << Ψ₂) Ψ₃ ⊡ (subst (λ α → nsub Δ α Ψ₂) (trans (<<-assoc ⊡ Ψ₁ Ψ₂) (<<-idl (Ψ₁ << Ψ₂))) (ns-wkn ⊡ Ψ₁ Ψ₂ (subst (λ α → nsub Δ α Ψ₂) (sym (<<-idl Ψ₂)) ns-id))) 

mutual
 ⟦_⟧cn : ∀ {Ω₁ Ω₂} {Δ : mctx Ω₁} {Ψ} {A} -> (Ψs : gksubst Ω₁ (tctx Ω₂)) -> ntm Δ Ψ A -> ntm (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) A
 ⟦_⟧cn Ψs (ƛ N) = ƛ (⟦ Ψs ⟧cn N)
 ⟦_⟧cn Ψs (H · S) = (⟦ Ψs ⟧ch H) · (⟦ Ψs ⟧cs S)

 ⟦_⟧ch : ∀ {Ω₁ Ω₂} {Δ : mctx Ω₁} {Ψ} {A} -> (Ψs : gksubst Ω₁ (tctx Ω₂)) -> head Δ Ψ A -> head (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) A
 ⟦_⟧ch Ψs (▹ x) = ▹ (⟦ Ψs ⟧tv x)
 ⟦_⟧ch Ψs (u [ σ ]) = ⟦ Ψs ⟧cv u [ ⟦ Ψs ⟧cns σ ]
 ⟦_⟧ch Ψs (p ♯[ σ ]) = ⟦ Ψs ⟧cv p ♯[ ⟦ Ψs ⟧cns σ ]
 ⟦_⟧ch Ψs π x [ s [ σ ]] = π ⟦ Ψs ⟧tv x [ ⟦ Ψs ⟧cv s [ ⟦ Ψs ⟧cns σ ]]

 ⟦_⟧cs : ∀ {Ω₁ Ω₂} {Δ : mctx Ω₁} {Ψ} {A B} -> (Ψs : gksubst Ω₁ (tctx Ω₂)) -> spine Δ Ψ A B -> spine (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) A B
 ⟦_⟧cs Ψs ε = ε
 ⟦_⟧cs Ψs (N , S) = (⟦ Ψs ⟧cn N) , (⟦ Ψs ⟧cs S)


 ⟦_⟧cns : ∀ {Ω₁ Ω₂} {Δ : mctx Ω₁} {Ψ} {A} -> (Ψs : gksubst Ω₁ (tctx Ω₂)) -> nsub Δ Ψ A -> nsub (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) (⟦ Ψs ⟧tc A)
 ⟦_⟧cns Ψs ⊡ = ⊡
 ⟦_⟧cns Ψs (σ , ▸ N) = (⟦ Ψs ⟧cns σ) , (▸ (⟦ Ψs ⟧cn N))
 ⟦_⟧cns Ψs (σ , (xs [ s [ σ' ]])) with  ⟦ Ψs ⟧cv s | ⟦ Ψs ⟧cns σ'
 ... | q1 | q2 = {!!}
 ⟦_⟧cns Ψs (σ , ▹ xs) with inv xs
 ⟦_⟧cns Ψs (σ , ▹ xs) | con2 Ψ₁ φ Ψ₂ = {!!}

 

 ⟦_⟧cnv : ∀ {Ω₁ Ω₂} {Δ : mctx Ω₁} {Ψ} {A} -> (Ψs : gksubst Ω₁ (tctx Ω₂)) -> nval Δ Ψ A -> nsub (⟦ Ψs ⟧mc Δ) (⟦ Ψs ⟧tc Ψ) (⟦ Ψs ⟧te A)
 ⟦_⟧cnv Ψs (▸ N) = {!!}
 ⟦_⟧cnv Ψs (xs [ s [ σ ]]) = {!!}
 ⟦_⟧cnv {Ω₁} {Ω₂} {Δ} {Ψ} {cntx ,, φ} Ψs (▹ xs) with inv xs
 ⟦_⟧cnv {Ω₁} {Ω₂} {Δ} {.(Ψ₁ , (cntx ,, φ) << Ψ₂)} {cntx ,, φ} Ψs (▹ xs) | con2 Ψ₁ .φ Ψ₂ = 
  subst (λ α → nsub (⟦ Ψs ⟧mc Δ) α (lookup Ψs φ)) (sym (⟦⟧tc-<< Ψs (Ψ₁ , (φ ∶ cntx)) Ψ₂))
   (ns-id' (⟦ Ψs ⟧tc Ψ₁) (lookup Ψs φ) (⟦ Ψs ⟧tc Ψ₂))

 