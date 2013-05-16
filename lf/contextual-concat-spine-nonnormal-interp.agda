module contextual-concat-spine-nonnormal-interp where
open import Level
open import Unit
open import FinMap
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import contextual-concat-spine

sp-comp : ∀ {Ω} {Δ : mctx Ω} {Ψ} {A B C} -> spine Δ Ψ A B -> spine Δ Ψ B C -> spine Δ Ψ A C
sp-comp ε S2 = S2
sp-comp (N , S) S2 = N , (sp-comp S S2)

η-expand : ∀ {B T} {Ω} {Δ : mctx Ω} {Ψ} -> head Δ Ψ T -> spine Δ Ψ T B -> ntm Δ Ψ B
η-expand {i} x S = x · S
η-expand {A ⇒ B} x S = ƛ (η-expand (h-wkn _ (⊡ , ▸ A) ⊡ x) (sp-comp (s-wkn _ (⊡ , ▸ A) ⊡ S) ((η-expand (▹ top) ε) , ε)))

η-expand2 : ∀ {T} {Ω} {Δ : mctx Ω} {Ψ} -> head Δ Ψ T -> ntm Δ Ψ T
η-expand2 x = η-expand x ε

ηs-expand' : ∀ {Ω T} {Δ : mctx Ω} {Ψ} Φ -> rsub Δ Ψ (T << Φ) -> nsub Δ Ψ T
ηs-expand' {Ω} {⊡} Φ σ = ⊡
ηs-expand' {Ω} {Φ' , ▹ φ} {Δ} {Ψ} Φ σ = ηs-expand' {Ω} ((⊡ , ▹ φ) << Φ) (subst (rsub Δ Ψ) (<<-assoc Φ' (⊡ , ▹ φ) Φ) σ) ,[ cthatone Φ ] σ
ηs-expand' {Ω} {Φ' , ▸ A} {Δ} {Ψ} Φ σ = ηs-expand' {Ω} ((⊡ , ▸ A) << Φ) (subst (rsub Δ Ψ) (<<-assoc Φ' (⊡ , ▸ A) Φ) σ) , η-expand2 (π (thatone Φ) σ)

ηs-expand : ∀ {Ω T} {Δ : mctx Ω} {Ψ} -> rsub Δ Ψ T -> nsub Δ Ψ T
ηs-expand ρ = ηs-expand' ⊡ ρ


mutual
 data tm {Ω} (Δ : mctx Ω) : (Γ : tctx Ω) (T : tp) -> Set where
  v : ∀ {Γ T} -> tvar Γ T -> tm Δ Γ T
  _·_ : ∀ {Γ T S} -> tm Δ Γ (T ⇒ S) -> tm Δ Γ T -> tm Δ Γ S
  ƛ : ∀ {Γ T S} -> tm Δ (Γ , (▸ T)) S -> tm Δ Γ (T ⇒ S)
  mv : ∀ {A Ψ} -> var Δ (% A [ Ψ ]) -> tm Δ Ψ A
  _[_] : ∀ {Ψ Φ A} -> tm Δ Φ A -> sub Δ Ψ Φ -> tm Δ Ψ A
 data sub {Ω} (Δ : mctx Ω) : (Ψ : tctx Ω) (Φ : tctx Ω) -> Set where
  sv : ∀ {Ψ Φ} -> var Δ ($ Φ [ Ψ ]) -> sub Δ Ψ Φ
  _[_] : ∀ {Ψ Φ Φ'} -> sub Δ Ψ Φ -> sub Δ Φ' Ψ -> sub Δ Φ' Φ
  _,₁_ : ∀ {Ψ Φ T} -> sub Δ Ψ Φ -> tm Δ Ψ T -> sub Δ Ψ (Φ , ▸ T)
  _,_ : ∀ {Ψ Φ Φ₂} -> sub Δ Ψ Φ -> sub Δ Ψ Φ₂ -> sub Δ Ψ (Φ << Φ₂)
  id : ∀ {Ψ} -> sub Δ Ψ Ψ
  · : ∀ {Ψ} -> sub Δ Ψ ⊡
  ↑ : ∀ {Ψ A} -> sub Δ (Ψ , A) Ψ

nsub-lookup : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Φ A} -> tvar Ψ₁ A -> nsub Δ Φ Ψ₁ -> ntm Δ Φ A
nsub-lookup top (σ , N) = N
nsub-lookup (pop x) (σ , N) = nsub-lookup x σ
nsub-lookup (pop x) (σ ,[ xs ] ρ) = nsub-lookup x σ

nsub-ext : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Φ A} -> nsub Δ Φ Ψ₁ -> nsub Δ (Φ , A) (Ψ₁ , A)
nsub-ext {A = ▸ A} σ = (ns-wkn _ (⊡ , ▸ _) ⊡ σ) , η-expand2 (▹ top)
nsub-ext {A = ▹ φ} σ = (ns-wkn _ (⊡ , ▹ φ) ⊡ σ) ,[ top ] (id top)

nsub-concat : ∀ {Ω} {Δ : mctx Ω} {Ψ Φ₁ Φ₂} -> nsub Δ Ψ Φ₁ -> nsub Δ Ψ Φ₂ -> nsub Δ Ψ (Φ₁ << Φ₂)
nsub-concat σ₁ ⊡ = σ₁
nsub-concat σ₁ (σ , N) = (nsub-concat σ₁ σ) , N
nsub-concat σ₁ (σ ,[ xs ] ρ) = (nsub-concat σ₁ σ) ,[ xs ] ρ

mutual
 eval : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Φ A} -> tm Δ Ψ₁ A -> nsub Δ Φ Ψ₁ -> ntm Δ Φ A
 eval (v y) σ = nsub-lookup y σ
 eval (y · y') σ with eval y σ
 ... | ƛ N = n-sub ⊡ N (eval y' σ)
 eval (ƛ y) σ = ƛ (eval y (nsub-ext σ))
 eval (mv u) σ = η-expand2 (u [ σ ])
 eval (t [ σ' ]) σ = eval t (evals σ' σ)

 evals : ∀ {Ω} {Δ : mctx Ω} {Ψ₁ Φ A} -> sub Δ Ψ₁ A -> nsub Δ Φ Ψ₁ -> nsub Δ Φ A
 evals (sv s) σ' = ηs-expand (s [ σ' ])
 evals (y [ y' ]) σ' = evals y (evals y' σ')
 evals (σ₁ ,₁ t) σ' = (evals σ₁ σ') , (eval t σ')
 evals (σ₁ , σ₂) σ' = nsub-concat (evals σ₁ σ') (evals σ₂ σ')
 evals id σ' = σ'
 evals · σ' = ⊡
 evals ↑ (σ , N) = σ
 evals ↑ (σ ,[ xs ] ρ) = σ

id-nsub : ∀ {Ω} {Γ} {Δ : mctx Ω} -> nsub Δ Γ Γ
id-nsub {Ω} {⊡} = ⊡
id-nsub {Ω} {Ψ , A} = nsub-ext id-nsub

norm : ∀ {Ω} {Δ : mctx Ω} {Γ T} -> tm Δ Γ T -> ntm Δ Γ T
norm t = eval t id-nsub

{-
 Interesting: It seems we could allow abstractions over entire contexts:
 This is like binders which bind an arbitrary number of things (e.g. patterns)
 Hmm this would be a cool use case for linearity!
 Can we make sense of applying an entire simultaneous substitution in the logical framework?
 "Application" of  Pi (φ : ctx). exp   to a   φ (ctx)...
-}

{- Can probably simplify this (and Beluga's parser, etc) by putting substitutions and terms in one grammar
   They are typed by either a context or a regular type -- disjoint sum, like tctx-elt
   Standard trick for defining mutually recursive families by tagging -}