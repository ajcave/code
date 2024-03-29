module sums-sequent where
open import Relation.Binary.PropositionalEquality hiding ([_])

record Unit : Set where
 constructor tt

data ctx {a} (A : Set a) : Set a where
 ⊡ : ctx A
 _,_ : (ψ : ctx A) -> (T : A) -> ctx A

data var {a} {A : Set a} : (Γ : ctx A) -> A -> Set a where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

schema-ctx = ctx Unit

* : Unit
* = tt

data tp : Set where
 i : tp
 _⇒_ _⊕_ : (A B : tp) -> tp

data tctx-elt (Ω : schema-ctx) : Set where
 ▸ : (A : tp) -> tctx-elt Ω

tctx : Set
tctx = ctx tp

-- data tvar {Ω : schema-ctx} : ∀ (Γ : tctx Ω) (T : tp) -> Set where
--  top : ∀ {Γ T} -> tvar (Γ , (▸ T)) T
--  pop : ∀ {Γ T S} -> (x : tvar Γ T) -> tvar (Γ , S) T

-- data cvar {Ω : schema-ctx} : ∀ (Γ : tctx Ω) (φ : var Ω *) -> Set where
--  top : ∀ {φ} -> cvar (▹ φ) φ
--  pop : ∀ {Γ φ S} -> (xs : cvar Γ φ) -> cvar (Γ , S) φ

-- -- Tags for substitution variables, parameter variables, and regular metavariables
-- data ctp (Ω : schema-ctx) : Set where
--  $ : (Ψ : tctx Ω) -> ctp Ω
--  ♯ : (A : tp) -> ctp Ω
--  % : (A : tp) -> ctp Ω

-- record mtp (Ω : schema-ctx) : Set where
--  constructor _[_]
--  field
--   dom : ctp Ω
--   ran : tctx Ω

-- mctx : schema-ctx -> Set
-- mctx Ω = ctx (mtp Ω)

_<<_ : tctx -> ctx tp -> tctx
Ψ₁ << ⊡ = Ψ₁
Ψ₁ << (Ψ , A) = (Ψ₁ << Ψ) , A

infixl 10 _<<_

<<-assoc : ∀ (Ψ₁ : tctx) Ψ₂ Ψ₃ -> (Ψ₁ << Ψ₂) << Ψ₃ ≡ Ψ₁ << (Ψ₂ << Ψ₃)
<<-assoc Ψ₁ Ψ₂ ⊡ = refl
<<-assoc Ψ₁ Ψ₂ (Ψ , A) = cong (λ α → α , A) (<<-assoc Ψ₁ Ψ₂ Ψ)

mutual
 data head (Ψ : tctx) : tp -> Set where
  ▹ : ∀ {A} (x : var Ψ A) -> head Ψ A
 data spine (Ψ : tctx) : tp -> tp -> Set where
  ε : ∀ {C} -> spine Ψ C C
  _,_ : ∀ {A B C} (N : ntm Ψ A) (S : spine Ψ B C) -> spine Ψ (A ⇒ B) C
 data ntm : (Ψ : tctx) -> tp -> Set where
  ƛ : ∀ {A B Ψ} (N : ntm (Ψ , A) B) -> ntm Ψ (A ⇒ B)
  _·_ : ∀ {A Ψ} (H : head Ψ A) (S : spine Ψ A i) -> ntm Ψ i
  inl : ∀ {A B Ψ} (N : ntm Ψ A) -> ntm Ψ (A ⊕ B)
  inr : ∀ {A B Ψ} (N : ntm Ψ B) -> ntm Ψ (A ⊕ B)
  case : ∀ {Ψ₁ A B C} Ψ₂
        -> (N₁ : ntm ((Ψ₁ , A) << Ψ₂) C)
        -> (N₂ : ntm ((Ψ₁ , B) << Ψ₂) C)
        -> ntm ((Ψ₁ , (A ⊕ B)) << Ψ₂) C


<<tv : ∀ {Ψ₁ : tctx} {A} -> var Ψ₁ A -> ∀ Ψ₂ -> var (Ψ₁ << Ψ₂) A
<<tv x ⊡ = x
<<tv x (ψ , T) = pop (<<tv x ψ)

{-
<<cv : ∀ {Ω} {Ψ₁ : tctx Ω} {φ} -> cvar Ψ₁ φ -> ∀ Ψ₂ -> cvar (Ψ₁ << Ψ₂) φ
<<cv xs ⊡ = xs
<<cv xs (Ψ , A) = pop (<<cv xs Ψ)

-}
tvar-wkn : ∀ (Ψ₁ : tctx) Ψ₂ Ψ₃ {A} -> var (Ψ₁ << Ψ₃) A -> var (Ψ₁ << Ψ₂ << Ψ₃) A
tvar-wkn Ψ₁ Ψ₂ ⊡ x = <<tv x Ψ₂
tvar-wkn Ψ₁ Ψ₂ (Ψ , .A) {A} top = top
tvar-wkn Ψ₁ Ψ₂ (Ψ , A) (pop x) = pop (tvar-wkn Ψ₁ Ψ₂ Ψ x)

{-
tvar-wkn' : ∀ {Ω} (Ψ₂ : tctx Ω) Ψ₃ {A} -> tvar {Ω} (⊡ << Ψ₃) A -> tvar (Ψ₂ << Ψ₃) A
tvar-wkn' Ψ₂ ⊡ () 
tvar-wkn' Ψ₂ (Ψ , .A) {A} top = top
tvar-wkn' Ψ₂ (Ψ , A) (pop x) = pop (tvar-wkn' Ψ₂ Ψ x)

-}
var-to-tvar : ∀ (Ψ₂ : tctx) {Ψ₃} {A} -> var Ψ₃ A -> var (Ψ₂ << Ψ₃) A
var-to-tvar Ψ₂ (top) = top
var-to-tvar Ψ₂ (pop x) = pop (var-to-tvar Ψ₂ x)


tvar-wkn1 : ∀ {Ψ₁ : tctx} {B} Ψ₃ {A} -> var (Ψ₁ << Ψ₃) A -> var ((Ψ₁ , B) << Ψ₃) A
tvar-wkn1 {Ψ₁} {B} Ψ₃ x = tvar-wkn Ψ₁ (⊡ , B) Ψ₃ x

{-
cvar-wkn : ∀ {Ω} (Ψ₁ : tctx Ω) Ψ₂ Ψ₃ {φ} -> cvar (Ψ₁ << Ψ₃) φ -> cvar (Ψ₁ << Ψ₂ << Ψ₃) φ
cvar-wkn Ψ₁ Ψ₂ ⊡ xs = <<cv xs Ψ₂
cvar-wkn Ψ₁ Ψ₂ (Ψ , A) (pop xs) = pop (cvar-wkn Ψ₁ Ψ₂ Ψ xs)

-}
-- Weakening
mutual
 h-wkn : ∀ Ψ₁ Ψ₂ Ψ₃ {A} -> head (Ψ₁ << Ψ₃) A -> head (Ψ₁ << Ψ₂ << Ψ₃) A
 h-wkn Ψ₁ Ψ₂ Ψ₃ (▹ x) = ▹ (tvar-wkn Ψ₁ Ψ₂ Ψ₃ x)

 s-wkn : ∀ Ψ₁ Ψ₂ Ψ₃ {A B} -> spine (Ψ₁ << Ψ₃) A B -> spine (Ψ₁ << Ψ₂ << Ψ₃) A B
 s-wkn Ψ₁ Ψ₂ Ψ₃ ε = ε
 s-wkn Ψ₁ Ψ₂ Ψ₃ (N , S) = (n-wkn Ψ₁ Ψ₂ Ψ₃ N) , (s-wkn Ψ₁ Ψ₂ Ψ₃ S)

 n-wkn : ∀ Ψ₁ Ψ₂ Ψ₃ {A} -> ntm (Ψ₁ << Ψ₃) A -> ntm (Ψ₁ << Ψ₂ << Ψ₃) A
 n-wkn Ψ₁ Ψ₂ Ψ₃ N = {!!}
 {-n-wkn Ψ₁ Ψ₂ Ψ₃ (ƛ {A} {B} N) = ƛ (n-wkn Ψ₁ Ψ₂ (Ψ₃ , A) N)
 n-wkn Ψ₁ Ψ₂ Ψ₃ (H · S) = (h-wkn Ψ₁ Ψ₂ Ψ₃ H) · (s-wkn Ψ₁ Ψ₂ Ψ₃ S)
 n-wkn Ψ₁ Ψ₂ Ψ₃ (inl N) = {!!}
 n-wkn Ψ₁ Ψ₂ Ψ₃ (inr N) = ?
 n-wkn Ψ₁ Ψ₂ Ψ₃ (case Ψ N₁ N₂) = ? -}


{-
cvar-str : ∀ {Ω} {Ψ₁ : tctx Ω} {B} Ψ₂ {φ} -> cvar ((Ψ₁ , ▸ B) << Ψ₂) φ -> cvar (Ψ₁ << Ψ₂) φ
cvar-str ⊡ (pop xs) = xs
cvar-str (Ψ , A) (pop xs) = pop (cvar-str Ψ xs)

cvar-str2 : ∀ {Ω} {Ψ₁ : tctx Ω} Ψ₂ {φ} -> cvar (Ψ₁ << Ψ₂) φ -> cvar Ψ₁ φ
cvar-str2 ⊡ x = x
cvar-str2 (Ψ , T) (pop x) = cvar-str2 Ψ x

-}
thatone : ∀ {Ψ : tctx} Φ {A} -> var ((Ψ , A) << Φ) A
thatone ⊡ = top
thatone (Φ , A) = pop (thatone Φ)


data eqV {Ψ : tctx} : ∀ {A} B Φ -> var ((Ψ , B) << Φ) A -> Set where
 same : ∀ {A Φ} -> eqV A Φ (thatone Φ)
 diff : ∀ {A B Φ} (x : var (Ψ << Φ) A) -> eqV B Φ (tvar-wkn1 Φ x)


data split {Ψ : tctx} : ∀ {A} Φ -> var (Ψ << Φ) A -> Set where
 left : ∀ {A Φ} (x : var Ψ A) -> split Φ (tvar-wkn _ Φ ⊡ x)
 right : ∀ {A Φ} (x : var Φ A) -> split Φ (var-to-tvar Ψ x)


eq? : ∀ {Ψ : tctx} Φ {A B} (x : var ((Ψ , A) << Φ) B) -> eqV A Φ x
eq? ⊡ top = same
eq? ⊡ (pop x) = diff x
eq? (Ψ , .B) {A} {B} top = diff top
eq? (Ψ , A) (pop x) with eq? Ψ x
eq? (Ψ , A) (pop .(thatone Ψ)) | same = same
eq? (Ψ , A) (pop .(tvar-wkn1 Ψ x)) | diff x = diff (pop x)


decSplit : ∀ {Ψ : tctx} {A} Φ (x : var (Ψ << Φ) A) -> split Φ x
decSplit ⊡ x = left x
decSplit (Φ , T) top = right top
decSplit (Φ , T) (pop x) with decSplit Φ x
decSplit (Φ , T) (pop .(<<tv x Φ)) | left x = left x
decSplit {Ψ} (Φ , T) (pop .(var-to-tvar Ψ x)) | right x = right (pop x)


-- Hereditary substitution
mutual
 n-sub : ∀ {Ψ₁} {B} Ψ₂ {A} -> ntm ((Ψ₁ , B) << Ψ₂) A -> ntm Ψ₁ B -> ntm (Ψ₁ << Ψ₂) A
 n-sub Ψ N M = {!!}
 {- n-sub Ψ (ƛ {A} {B} N) M = ƛ (n-sub (Ψ , A) N M)
 n-sub Ψ (inl N) M = {!!}
 n-sub Ψ (inr N) M = ?
 n-sub Ψ _ = ?
 n-sub Ψ (▹ x · S) M with eq? Ψ x
 n-sub Ψ (▹ .(thatone Ψ) · S) M | same = (n-wkn _ Ψ ⊡ M) ◇ (s-sub Ψ S M)
 n-sub Ψ (▹ .(tvar-wkn1 Ψ x) · S) M | diff x = (▹ x) · s-sub Ψ S M -}

 s-sub : ∀ {Ψ₁} {B} Ψ₂ {A C} -> spine ((Ψ₁ , B) << Ψ₂) A C -> ntm Ψ₁ B -> spine (Ψ₁ << Ψ₂) A C
 s-sub Ψ ε N = ε
 s-sub Ψ (N , S) N' = (n-sub Ψ N N') , (s-sub Ψ S N')

 _◇_ : ∀ {Ψ} {A B} -> ntm Ψ A -> spine Ψ A B -> ntm Ψ B
 N ◇ S = {!!}
{- N ◇ ε = N
 (ƛ N) ◇ (N' , S) = (n-sub ⊡ N N') ◇ S -}

{-

-- Simultaneous substitution under a context
mutual
 v-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ} {B} {A} -> tvar B A -> spine Δ Ψ A i -> nsub Δ Ψ B -> ntm Δ Ψ i
 v-sub' top S (σ , N) = N ◇ S
 v-sub' (pop x) S (σ , N) = v-sub' x S σ

 n-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {Ψ} Ψ₂ {A} -> ntm Δ (Ψ << Ψ₂) A -> nsub Δ Ψ₁ Ψ -> ntm Δ (Ψ₁ << Ψ₂) A
 n-sub' Ψ (ƛ N) σ = ƛ (n-sub' (Ψ , _) N σ)
 n-sub' Ψ (▹ x · S) σ with decSplit Ψ x
 n-sub' Ψ (▹ .(<<tv x Ψ) · S) σ | left x = v-sub' x (s-sub' Ψ S σ) (ns-wkn _ Ψ ⊡ σ)
 n-sub' {Ω} {Δ} {Ψ₁} {Φ} Ψ (▹ .(var-to-tvar Φ x) · S) σ | right x = ▹ (var-to-tvar _ x) · s-sub' Ψ S σ
 n-sub' Ψ ((u [ σ ]) · S) σ₁ = (u [ ns-sub' Ψ σ σ₁ ]) · s-sub' Ψ S σ₁
 n-sub' Ψ ((p ♯[ σ ]) · S) σ₁ = (p ♯[ ns-sub' Ψ σ σ₁ ]) · s-sub' Ψ S σ₁
 n-sub' Ψ (π x ρ · S) σ = π x (rs-sub' Ψ ρ σ) · s-sub' Ψ S σ

 s-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {A C} -> spine Δ (B << Ψ₂) A C -> nsub Δ Ψ₁ B -> spine Δ (Ψ₁ << Ψ₂) A C
 s-sub' Ψ ε σ = ε
 s-sub' Ψ (N , S) σ = (n-sub' Ψ N σ) , (s-sub' Ψ S σ)

 cv-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ φ Φ} -> cvar Ψ φ -> nsub Δ Φ Ψ -> nsub Δ Φ (▹ φ)
 cv-sub' top σ = σ
 cv-sub' (pop xs) (σ , N) = cv-sub' xs σ

 ns-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {Ψ₃} Ψ₂ {Φ} -> nsub Δ (Ψ₃ << Ψ₂) Φ -> nsub Δ Ψ₁ Ψ₃ -> nsub Δ (Ψ₁ << Ψ₂) Φ
 ns-sub' Ψ ⊡ σ' = ⊡
 ns-sub' Ψ (id φ₁) σ = ns-wkn _ Ψ ⊡ (cv-sub' (cvar-str2 Ψ φ₁) σ)
 ns-sub' Ψ (σ , N) σ' = (ns-sub' Ψ σ σ') , (n-sub' Ψ N σ')
 ns-sub' Ψ ([ xs ] ρ) σ' = [ xs ] rs-sub' Ψ ρ σ'

 rs-sub' : ∀ {Ω} {Δ : mctx Ω} {Ψ₁} {B} Ψ₂ {Φ} -> rsub Δ (B << Ψ₂) Φ -> nsub Δ Ψ₁ B -> rsub Δ (Ψ₁ << Ψ₂) Φ
 rs-sub' Ψ (s [ σ ]) σ₁ = s [ ns-sub' Ψ σ σ₁ ]

sp-comp : ∀ {Ω} {Δ : mctx Ω} {Ψ} {A B C} -> spine Δ Ψ A B -> spine Δ Ψ B C -> spine Δ Ψ A C
sp-comp ε S2 = S2
sp-comp (N , S) S2 = N , (sp-comp S S2)

-- Expansion operations
η-expand : ∀ {B T} {Ω} {Δ : mctx Ω} {Ψ} -> head Δ Ψ T -> spine Δ Ψ T B -> ntm Δ Ψ B
η-expand {i} x S = x · S
η-expand {A ⇒ B} x S = ƛ (η-expand (h-wkn _ (⊡ , A) ⊡ x) (sp-comp (s-wkn _ (⊡ , A) ⊡ S) ((η-expand (▹ top) ε) , ε)))

η-expand2 : ∀ {T} {Ω} {Δ : mctx Ω} {Ψ} -> head Δ Ψ T -> ntm Δ Ψ T
η-expand2 x = η-expand x ε

ηs-expand' : ∀ {Ω Φ'} {Δ : mctx Ω} {Ψ} Φ -> rsub Δ Ψ (Φ' << Φ) -> nsub Δ Ψ Φ'
ηs-expand' {Ω} {⊡} Φ σ = ⊡
ηs-expand' {Ω} {▹ φ} {Δ} {Ψ} Φ σ = [ <<cv top Φ ] σ
ηs-expand' {Ω} {Φ' , ▸ A} {Δ} {Ψ} Φ σ = ηs-expand' {Ω} ((⊡ , A) <<' Φ) (subst (rsub Δ Ψ) (<<-assoc Φ' (⊡ , A) Φ) σ) , η-expand2 (π (thatone Φ) σ)

ηs-expand : ∀ {Ω T} {Δ : mctx Ω} {Ψ} -> rsub Δ Ψ T -> nsub Δ Ψ T
ηs-expand ρ = ηs-expand' ⊡ ρ

nsub-ext : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Φ A} -> nsub Δ Φ Ψ₁ -> nsub Δ (Φ , A) (Ψ₁ , A)
nsub-ext {A = ▸ A} σ = (ns-wkn _ (⊡ , _) ⊡ σ) , η-expand2 (▹ top)

id-nsub : ∀ {Ω} {Γ} {Δ : mctx Ω} -> nsub Δ Γ Γ
id-nsub {Ω} {⊡} = ⊡
id-nsub {Ω} {▹ φ} = id top
id-nsub {Ω} {Ψ , A} = nsub-ext id-nsub
-}