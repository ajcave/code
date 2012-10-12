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

blar : bool -> schema-ctx -> Set
blar type Ω = tp
blar cntx Ω = var Ω *

record tctx-elt (Ω : schema-ctx) : Set where
 constructor _,,_
 field
  which : bool
  val : blar which Ω

▸₂ : ∀ {Ω} (A : tp) -> tctx-elt Ω
▸₂ A = type ,, A

▹₂ : ∀ {Ω} (φ : var Ω *) -> tctx-elt Ω
▹₂ φ = cntx ,, φ


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
  ▹ : ∀ {A} (x : gvar Ψ (▸₂ A)) -> head Δ Ψ A
  _[_] : ∀ {A Φ} (u : var Δ (% A [ Φ ])) (σ : nsub Δ Ψ Φ) -> head Δ Ψ A
  _♯[_] : ∀ {A Φ} (p : var Δ (♯ A [ Φ ])) (σ : nsub Δ Ψ Φ) -> head Δ Ψ A
  -- This is a little out of place. Would normally be included in the spine...
  π_[_[_]] : ∀ {Φ₁ Φ₂ A} (x : gvar Φ₁ (▸₂ A)) (s : var Δ ($ Φ₁ [ Φ₂ ])) (σ : nsub Δ Ψ Φ₂) -> head Δ Ψ A
 data spine {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> tp -> Set where
  ε : ∀ {C} -> spine Δ Ψ C C
  _,_ : ∀ {A B C} (N : ntm Δ Ψ A) (S : spine Δ Ψ B C) -> spine Δ Ψ (A ⇒ B) C
 data ntm {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tp -> Set where
  ƛ : ∀ {A B} (N : ntm Δ (Ψ , (▸₂ A)) B) -> ntm Δ Ψ (A ⇒ B)
  _·_ : ∀ {A} (H : head Δ Ψ A) (S : spine Δ Ψ A i) -> ntm Δ Ψ i
 data nsub {Ω} (Δ : mctx Ω) : ∀ (Ψ : tctx Ω) -> tctx Ω -> Set where
  ⊡ : ∀ {Ψ} -> nsub Δ Ψ ⊡
  _,_ : ∀ {Ψ Φ A} (σ : nsub Δ Ψ Φ) (N : nval Δ Ψ A) -> nsub Δ Ψ (Φ , A)
 data nval {Ω} (Δ : mctx Ω) (Ψ : tctx Ω) : tctx-elt Ω -> Set where
  ▸ : ∀ {A} (N : ntm Δ Ψ A) -> nval Δ Ψ (▸₂ A)
  _[_[_]] : ∀ {Φ₂ Φ₃ φ} (xs : gvar Φ₂ (▹₂ φ)) (s : var Δ ($ Φ₂ [ Φ₃ ])) (σ : nsub Δ Ψ Φ₃) -> nval Δ Ψ (▹₂ φ)
  ▹ : ∀ {φ} (xs : gvar Ψ (▹₂ φ)) -> nval Δ Ψ (▹₂ φ)

⟦_⟧tc : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (Φ : tctx Ω₁) -> tctx Ω₂
⟦_⟧tc Ψs ⊡ = ⊡
⟦_⟧tc Ψs (Φ , (cntx ,, φ)) = ⟦ Ψs ⟧tc Φ << (lookup Ψs φ)
⟦_⟧tc Ψs (Φ , (type ,, A)) = ⟦ Ψs ⟧tc Φ , (▸₂ A)

⟦⟧tc-<< : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) Φ₁ Φ₂
 -> ⟦ Ψs ⟧tc (Φ₁ << Φ₂) ≡ ((⟦ Ψs ⟧tc Φ₁) << (⟦ Ψs ⟧tc Φ₂))
⟦⟧tc-<< Ψs Φ₁ ⊡ = refl
⟦⟧tc-<< Ψs Φ₁ (ψ , (cntx ,, φ)) = trans (cong (λ α → α << lookup Ψs φ) (⟦⟧tc-<< Ψs Φ₁ ψ)) (<<-assoc (⟦ Ψs ⟧tc Φ₁) (⟦ Ψs ⟧tc ψ) (lookup Ψs φ))
⟦⟧tc-<< Ψs Φ₁ (ψ , (type ,, A)) = cong (λ α → α , ▸₂ A) (⟦⟧tc-<< Ψs Φ₁ ψ)

⟦_⟧mt : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (U : mtp Ω₁) -> mtp Ω₂
⟦_⟧mt Ψs ($ Ψ [ Φ ]) = $ (⟦ Ψs ⟧tc Ψ) [ ⟦ Ψs ⟧tc Φ ]
⟦_⟧mt Ψs ((♯ A) [ Φ ]) = (♯ A) [ ⟦ Ψs ⟧tc Φ ]
⟦_⟧mt Ψs (% A [ Φ ]) = % A [ ⟦ Ψs ⟧tc Φ ]

⟦_⟧mc : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) (Δ : mctx Ω₁) -> mctx Ω₂
⟦_⟧mc Ψs Δ = cmap ⟦ Ψs ⟧mt Δ

<<gv : ∀ {Ω} {Ψ₁ : tctx Ω} {A} -> gvar Ψ₁ A -> ∀ Ψ₂ -> gvar (Ψ₁ << Ψ₂) A
<<gv x ⊡ = x
<<gv x (Ψ , A') = pop (<<gv x Ψ)

⟦_⟧tv : ∀ {Ω₁ Ω₂} (Ψs : gksubst Ω₁ (tctx Ω₂)) {Φ : tctx Ω₁} {A} -> gvar Φ (▸₂ A) -> gvar (⟦ Ψs ⟧tc Φ) (▸₂ A)
⟦_⟧tv Ψs top = top
⟦_⟧tv Ψs {Φ , (cntx ,, φ)} (pop x) = <<gv (⟦ Ψs ⟧tv x) (lookup Ψs φ)
⟦_⟧tv Ψs {Φ , (type ,, A)} (pop x) = pop (⟦ Ψs ⟧tv x)

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
 n-wkn Ψ₁ Ψ₂ Ψ₃ (ƛ {A} {B} N) = ƛ (n-wkn Ψ₁ Ψ₂ (Ψ₃ , ▸₂ A) N)
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

-- TODO: SHould be able to make this work by passing a selector, and something which computes down to the required type...

mutual
 sub-n : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {b} {B : blar b Ω} Ψ₂ {A} -> ntm Δ (Ψ₁ , (b ,, B) << Ψ₂) A -> nval Δ Ψ₁ (b ,, B) -> ntm Δ (Ψ₁ << Ψ₂) A
 sub-n Ψ (ƛ N) V = ƛ (sub-n (Ψ , _) N V)
 sub-n Ψ (▹ x · S) V with eq? Ψ x
 sub-n Ψ (▹ .(thatone Ψ) · S) (▸ N) | same = n-wkn _ Ψ ⊡ N ◆ sub-s Ψ S (▸ N)
 sub-n Ψ (▹ .(gvar-wkn1 Ψ x) · S) V | diff x = ▹ x · sub-s Ψ S V
 sub-n Ψ ((u [ σ ]) · S) V = (u [ sub-ns Ψ σ V ]) · sub-s Ψ S V
 sub-n Ψ ((p ♯[ σ ]) · S) V = (p ♯[ sub-ns Ψ σ V ]) · sub-s Ψ S V
 sub-n Ψ (π x [ s [ σ ]] · S) V = π x [ s [ sub-ns Ψ σ V ]] · sub-s Ψ S V

 sub-s : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {b} {B : blar b Ω} Ψ₂ {A C} -> spine Δ (Ψ₁ , (b ,, B) << Ψ₂) A C -> nval Δ Ψ₁ (b ,, B) -> spine Δ (Ψ₁ << Ψ₂) A C
 sub-s Ψ ε V = ε
 sub-s Ψ (N , S) V = (sub-n Ψ N V) , (sub-s Ψ S V)

 sub-ns : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {b} {B : blar b Ω} Ψ₂ {A} -> nsub Δ (Ψ₁ , (b ,, B) << Ψ₂) A -> nval Δ Ψ₁ (b ,, B) -> nsub Δ (Ψ₁ << Ψ₂) A
 sub-ns Ψ ⊡ V = ⊡
 sub-ns Ψ (σ , N) V = (sub-ns Ψ σ V) , sub-nv Ψ N V

 sub-nv : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {b} {B : blar b Ω} Ψ₂ {χ} -> nval Δ (Ψ₁ , (b ,, B) << Ψ₂) χ -> nval Δ Ψ₁ (b ,, B) -> nval Δ (Ψ₁ << Ψ₂) χ
 sub-nv Ψ (▸ N) V = ▸ (sub-n Ψ N V)
 sub-nv Ψ (xs [ s [ σ ]]) V = xs [ s [ sub-ns Ψ σ V ]]
 sub-nv Ψ (▹ xs) V with eq? Ψ xs
 sub-nv Ψ (▹ .(thatone Ψ)) V | same = nv-wkn _ Ψ ⊡ V
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

-- Now I need all 3 kinds of meta-substitution...

