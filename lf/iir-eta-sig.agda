{-# OPTIONS --no-positivity-check --no-termination-check --type-in-type #-}
-- By Induction-induction-recursion
module iir-eta-sig where
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe

-- What if we didn't use TrustMe and actually proved all of our equations
-- Would Agda actually accept the definition (positivity check and termination check)?
-- No, because the dependency "increases" the size of types. We'd have to use a simply-typed skeleton

-- I guess another approach would be to have constants implementing non-canonical forms LF,
-- but have *only* "fancy" induction principle which breaks things into heads·spines (i.e. normalizes)

-- I guess we can "simplify" the equational theory by only having normal substitution
-- (no var-for-var substitution) and writing the non-well-founded definition
-- Downside: No p[π]? Is this a limitation in practice? Probably...

-- let's write out the theory for this as a "base" MLTT + a big list of constants with their types
-- (then definitional equations for them)
-- Also needs the eliminator.
-- Question: Types appear in terms (although implicitly)
--   Should the eliminator allow (mutual) recursion on them?
--   Not allowing this is.. like using implicit products/intersection types?

-- I guess that perhaps we don't really need a signature Σ if we're willing to use
-- variables in Γ for this purpose...
-- We do need to have "kind" variables then though.
-- How would this work with the induction principle? We want to be able to access variables
-- at the "bottom" of Γ for direct analysis...
--  - Can we "derive" that?
--  Does this also force us to be "higher order"?

-- I guess that for the basic (non-higher order) system, heads only need to be constants
-- variables do not come with a spine (they are always at base type)
--  ...except that this doesn't suffice for intrinsically typed System F

-- What power does adding an implicit product to LF add? Seems to allow us to represent
-- well-typed terms space-efficiently

-- I wonder if we can implement all the variants of substitution simultaneously by
-- tagging them with a flag indicating which family they're from and using large elim
-- If not large elim, then we could do it by combining the mutually recursive types into one
-- and indexing by the flag?

-- It seems that the well-formedness condition for signatures should impose an ordering
-- it just may be that we need to interleave kinding and typing constants in order for the
-- ordering to be possible (e.g. for mutual recursion, and inductive-inductive definitions)

-- What does adding sigma types do? 
-- Can we allow for "arbitrary arity" binders? Have an "n-ary" Π?

-- I guess there is some "opposite spine" representation for types that we can use?
-- i.e. Π Δ. (a · S) where Δ is a "telescope"?
-- constructor:
--    Π_._·_ : tele Γ Γ' -> const K -> tpSpine Γ' K -> tp Γ
-- tele Γ Γ' represents a "context suffix" which, when appended to Γ, yields Γ'
--    think of as a witness that "Γ' is a well-formed extension of Γ"
--    "telescopic extension"?
-- (Obviously there's a "computational" version which explicitly appends, but I expect this
--  version to be better behaved)
--  Will this make it feasible for the coverage checker to disregard useless constants?
-- Explain this as "the part that you need to implement coverage checking is directly available"?
-- Use to give a "direct" explanation/formalization of coverage checking?

-- In general, this looks a lot like an implementation of a datatype mechanismin type theory
-- (it is). Can we make it a little simpler and more general for "general" inductive datatypes?
mutual
 data sig : Set where
  ⊡ : sig
  _,_ : (Σ : sig) -> (α : sigsort Σ) -> sig

 data sigsort (Σ : sig) : Set where
  κ : kind {Σ} ⊡' -> sigsort Σ
  τ : tp {Σ} ⊡' -> sigsort Σ

 _,s_ : (Σ : sig) -> (α : sigsort Σ) -> sig
 _,s_ = _,_

 data ctx (Σ : sig) : Set where
  ⊡ : ctx Σ
  _,'_ : (Γ : ctx Σ) -> (T : tp Γ) -> ctx Σ

 ⊡' : ∀ {Σ} -> ctx Σ
 ⊡' = ⊡
 
 -- Should I actually compute Γ by (induction) recursion on the kind?
 -- Maybe these need to be "in reverse order"?
 data kind {Σ : sig} (Γ : ctx Σ) : Set where
  ⋆ : kind Γ
  Π : (T : tp Γ) -> (K : kind (Γ ,, T)) -> kind Γ

 data tp {Σ : sig} (Γ : ctx Σ) : Set where
  Π : (T : tp Γ) (S : tp (Γ ,' T)) -> tp Γ
  _·_ : ∀ {K : kind ⊡'} -> (c : inSig Σ K) -> tpSpine Γ ([ ⊡s ]kv K) -> tp Γ

 data tpSpine {Σ} (Γ : ctx Σ) : kind Γ -> Set where
  ε : tpSpine Γ ⋆
  _,κ_ : ∀ {T : tp Γ} {K : kind (Γ ,, T)} (N : ntm Γ T) -> tpSpine Γ ([ N /x]kn K)  -> tpSpine Γ (Π T K)

 _,,_ : {Σ : sig} -> (Γ : ctx Σ) -> (T : tp Γ) -> ctx Σ
 Γ ,, T = Γ ,' T
 
 vsubst : ∀ {Σ} (Γ Δ : ctx Σ) -> Set
 ntsubst : ∀ {Σ} (Γ Δ : ctx Σ) -> Set
 id-vsubst : ∀ {Σ} {Γ : ctx Σ} -> vsubst Γ Γ
 do-wkn-vsubst : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Δ} -> vsubst Γ Δ -> vsubst Γ (Δ ,, T)
 
 ntsubst ⊡ Δ = Unit
 ntsubst (Γ ,' T) Δ = Σ (ntsubst Γ Δ) (λ σ -> (ntm Δ ([ σ ]tpn T)))

 -- Do we really need λ to be a constructor?
 -- I guess that we could actually just compute the ntm type by recursion on the tp
 -- arriving eventually at _·_ with Γ appropriately extended (iir-eta-comp)
 -- Can we do the same thing in the formal metatheory of LF?
 data var {Σ} : (Γ : ctx Σ) -> tp Γ -> Set where
  top : ∀ {Γ T} -> var (Γ ,' T) ([ do-wkn-vsubst id-vsubst ]tv T)
  pop : ∀ {Γ T S} (x : var Γ T) -> var (Γ ,' S) ([ do-wkn-vsubst id-vsubst ]tv T)
 data ntm {Σ} (Γ : ctx Σ) : tp Γ -> Set where
  _·_ : ∀ {K} {T} {a : inSig Σ K} {S} -> head Γ T -> spine Γ T (a · S) -> ntm Γ (a · S)
  ƛ : ∀ {T S} -> ntm (Γ ,' T) S -> ntm Γ (Π T S)
 data spine {Σ} (Γ : ctx Σ) : tp Γ -> tp Γ -> Set where
  ε : ∀ {T} -> spine Γ T T
  _&_ : ∀ {T T2 C} -> (N : ntm Γ T) -> (S : spine Γ ([ N /x]tpn T2) C) -> spine Γ (Π T T2) C
 data head {Σ} (Γ : ctx Σ) : tp Γ -> Set where
  v : ∀ {T} -> var Γ T -> head Γ T
  con : ∀ {T : tp ⊡'} -> inSigτ Σ T -> head Γ ([ ⊡s ]tv T)


 vsubst ⊡ Δ = Unit
 vsubst (Γ ,' T) Δ = Σ (vsubst Γ Δ) (λ σ -> (var Δ ([ σ ]tv T)))

 ↑c : ∀ {Σ α} -> ctx Σ -> ctx (Σ ,s α)
 ↑c ⊡ = ⊡
 ↑c (Γ ,' T) = (↑c Γ) ,' (↑t T)

 ↑k : ∀ {Σ} {Γ : ctx Σ} {α : sigsort Σ} -> kind {Σ} Γ -> kind {Σ ,s α} (↑c Γ)
 ↑k ⋆ = ⋆
 ↑k (Π T K) = Π (↑t T) (↑k K)

 -- It seems that using names would be better here, since we don't
 -- have 'freshness' issues (no Σ binders)
 -- TODO: Merge these
 data inSig : ∀ Σ -> kind ⊡' -> Set where
  a-top : ∀ {Σ K} -> inSig (Σ , κ K) (↑k K) 
  a-pop : ∀ {Σ K α} -> inSig Σ K -> inSig (Σ , α) (↑k K)

 data inSigτ : ∀ Σ -> tp ⊡' -> Set where
  a-top : ∀ {Σ T} -> inSigτ (Σ , τ T) (↑t T) -- TODO: Need to do a "shift"
  a-pop : ∀ {Σ T α} -> inSigτ Σ T -> inSigτ (Σ , α) (↑t T)
  -- nat : inSig Σ ⋆
  -- vec : inSig Σ (Π (nat · ε) ⋆)
 
 ↑t : ∀ {Σ Γ α} -> tp {Σ} Γ -> tp {Σ ,s α} (↑c Γ)
 ↑t (Π T T₁) = Π (↑t T) (↑t T₁)
 ↑t (c · x) = a-pop c · subst (λ K → tpSpine _ K) trustMe (↑ts x)

 ↑ts : ∀ {Σ Γ α K} -> tpSpine {Σ} Γ K -> tpSpine {Σ ,s α} (↑c Γ) (↑k K)
 ↑ts ε = ε
 ↑ts (N ,κ S) = ↑n N ,κ (subst (λ K -> tpSpine _ K) trustMe (↑ts S))

 ↑n : ∀ {Σ α Γ T} -> ntm {Σ} Γ T -> ntm {Σ ,s α} (↑c Γ) (↑t T)
 ↑n (c · S) = (↑h c) · (↑s S)
 ↑n (ƛ M) = ƛ (↑n M)

 ↑v : ∀ {Σ α Γ T} -> var {Σ} Γ T -> var {Σ ,s α} (↑c Γ) (↑t T)
 ↑v top = subst (λ T -> var _ T) trustMe top
 ↑v (pop x) = subst (λ T -> var _ T) trustMe (pop (↑v x))

 ↑h : ∀ {Σ α Γ T} -> head {Σ} Γ T -> head {Σ ,s α} (↑c Γ) (↑t T)
 ↑h (v x) = v (↑v x)
 ↑h (con c) = subst (λ T → head _ T) trustMe (con (a-pop c))

 ↑s : ∀ {Σ α Γ A B} -> spine {Σ} Γ A B -> spine {Σ ,s α} (↑c Γ) (↑t A) (↑t B)
 ↑s ε = ε
 ↑s (_&_ {T1} {T2} {T3} N S) = ↑n N & (subst (λ C -> spine _ C (↑t T3)) trustMe (↑s S))
 
 [_]tv : ∀ {Σ} {Γ Δ : ctx Σ} -> vsubst Γ Δ -> tp Γ -> tp Δ

 pop' : ∀ {Σ} {Γ : ctx Σ} {T : tp Γ} {S} (x : var Γ T) -> var (Γ ,, S) ([  do-wkn-vsubst id-vsubst ]tv T)
 pop' = pop

 do-wkn-vsubst {Σ} {⊡} σ = unit
 do-wkn-vsubst {Σ} {Γ ,' T} (σ , x) = do-wkn-vsubst σ , subst (λ S → var _ S) trustMe (pop x)

 wkn-vsubst : ∀ {Σ} {Γ : ctx Σ} {T : tp Γ} -> vsubst Γ (Γ ,, T)
 wkn-vsubst = do-wkn-vsubst id-vsubst

 id-vsubst {Σ} {⊡} = unit
 id-vsubst {Σ} {Γ ,' T} = (do-wkn-vsubst id-vsubst) , top

 vsubst-ext : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ}  (σ : vsubst Γ Δ) -> vsubst (Γ ,, T) (Δ ,, ([ σ ]tv T))
 vsubst-ext σ = do-wkn-vsubst σ , subst (λ S → var _ S) trustMe top
 --vsubst-map : ∀ {Γ Δ} -> vsubst Γ Δ -> 

 [_]kv : ∀ {Σ} {Γ Δ : ctx Σ} (σ : vsubst Γ Δ) -> kind Γ -> kind Δ
 [_]kv σ ⋆ = ⋆
 [_]kv σ (Π T K) = Π ([ σ ]tv T) ([ vsubst-ext σ ]kv K)

 ⊡s : ∀ {Σ} {Γ : ctx Σ} -> vsubst ⊡' Γ
 ⊡s = unit

 _·'_ : ∀ {Σ} {Γ : ctx Σ} {K : kind ⊡'} -> (c : inSig Σ K) -> tpSpine Γ ([ ⊡s ]kv K) -> tp Γ
 c ·' S = c · S

 [_]tsv : ∀ {Σ} {Γ Δ : ctx Σ} {K : kind Γ} -> (σ : vsubst Γ Δ) -> tpSpine Γ K -> tpSpine Δ ([ σ ]kv K)
 [_]tsv σ ε = ε
 [_]tsv σ (N ,κ S) = ([ σ ]vn N) ,κ (subst (λ K -> tpSpine _ K) trustMe ([ σ ]tsv S))

-- [_]isv : ∀ {Σ} {Γ Δ : ctx Σ} {K : kind Γ} -> (σ : vsubst Γ Δ) -> inSig Σ K -> inSig Σ ([ σ ]kv K)
 [_]tv σ (Π T S) = Π ([ σ ]tv T) ([ vsubst-ext σ ]tv S)
 [ σ ]tv (c · S) = c ·  subst (λ K → tpSpine _ K) trustMe ([ σ ]tsv S)

 -- [_]isv σ nat = nat
 -- [_]isv σ vec = vec

 [_]vv : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> var Γ T -> var Δ ([ σ ]tv T)
 [_]vv (σ , y) top = subst (λ S → var _ S) trustMe y
 [_]vv (σ , y) (pop x) = subst (λ S → var _ S) trustMe ([ σ ]vv x)

 [_]vh : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> head Γ T -> head Δ ([ σ ]tv T)
 [_]vh σ (v x) = v ([ σ ]vv x)
 [ σ ]vh (con c) = subst (λ T → head _ T) trustMe (con c)

 [_]vs : ∀ {Σ} {Γ Δ : ctx Σ} {T C : tp Γ} -> (σ : vsubst Γ Δ) -> spine Γ T C -> spine Δ ([ σ ]tv T) ([ σ ]tv C)
 [_]vs σ ε = ε
 [_]vs σ (_&_ {T} {T2} {C} N S) = ([ σ ]vn N) & subst (λ S₁ → spine _ S₁ ([ σ ]tv C)) trustMe ([ σ ]vs S)

 [_]vn : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> ntm Γ T -> ntm Δ ([ σ ]tv T)
 [_]vn σ (H · S) = [ σ ]vh H · [ σ ]vs S
 [_]vn σ (ƛ M) = ƛ ([ vsubst-ext σ ]vn M)

 do-wkn-ntsubst : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Δ} -> ntsubst Γ Δ -> ntsubst Γ (Δ ,, T)
 do-wkn-ntsubst {Σ} {⊡} σ = unit
 do-wkn-ntsubst {Σ} {Γ ,' T} (σ , N) = do-wkn-ntsubst σ , subst (λ S → ntm _ S) trustMe ([ wkn-vsubst ]vn N)

 _◇_ : ∀ {Σ} {Γ : ctx Σ} {A B} -> head Γ A -> spine Γ A B -> ntm Γ B
 _◇_ {Σ} {Γ} {A} {Π B B₁} H S = ƛ (([ wkn-vsubst ]vh H) ◇ ([ wkn-vsubst ]vs S ++ ((v top ◇ ε) & subst (λ C → spine _ C B₁) trustMe ε)))
 _◇_ {Σ} {Γ} {A} {c · x} H S = H · S

 id-ntsubst : ∀ {Σ} {Γ : ctx Σ} -> ntsubst Γ Γ
 id-ntsubst {Σ} {⊡} = unit
 id-ntsubst {Σ} {Γ ,' T} = do-wkn-ntsubst id-ntsubst , (subst (λ S -> ntm _ S) trustMe (v top ◇ ε))

 [_]tpn : ∀ {Σ} {Γ Δ : ctx Σ} -> ntsubst Γ Δ -> tp Γ -> tp Δ
 ntsubst-ext : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ}  (σ : ntsubst Γ Δ) -> ntsubst (Γ ,, T) (Δ ,, ([ σ ]tpn T))
 ntsubst-ext σ = (do-wkn-ntsubst σ) , (subst (λ S → ntm _ S) trustMe (v top ◇ ε))

 [_]kn : ∀ {Σ} {Γ Δ : ctx Σ} (σ : ntsubst Γ Δ) -> kind Γ -> kind Δ
 [_]kn σ ⋆ = ⋆
 [_]kn σ (Π T K) = Π ([ σ ]tpn T) ([ ntsubst-ext σ ]kn K)

 [_/x]kn : ∀ {Σ} {Γ : ctx Σ} {T} -> ntm Γ T -> kind (Γ ,, T) -> kind Γ
 [ N /x]kn K = [ single-tsubst N ]kn K

 [_]ts : ∀ {Σ} {Γ Δ : ctx Σ} {K : kind Γ} -> (σ : ntsubst Γ Δ) -> tpSpine Γ K -> tpSpine Δ ([ σ ]kn K)
 [_]ts σ ε = ε
 [_]ts σ (N ,κ S) = ([ σ ]nn N) ,κ (subst (λ K → tpSpine _ K) trustMe ([ σ ]ts S))

 --[_]isn : ∀ {Σ} {Γ Δ : ctx Σ} {K : kind Γ} -> (σ : ntsubst Γ Δ) -> inSig Σ K -> inSig Σ ([ σ ]kn K)

 [ σ ]tpn (Π T T₁) = Π ([ σ ]tpn T) ([ ntsubst-ext σ ]tpn T₁)
 [ σ ]tpn (c · S) = c · subst (λ K → tpSpine _ K) trustMe ([ σ ]ts S)

 -- [ σ ]isn nat = nat
 -- [ σ ]isn vec = vec

 [_]nv : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ} -> (σ : ntsubst Γ Δ) -> var Γ T -> ntm Δ ([ σ ]tpn T)
 [_]nv (σ , N) top = subst (λ S → ntm _ S) trustMe N
 [_]nv (σ , N) (pop x) = subst (λ S → ntm _ S) trustMe ([ σ ]nv x)

 _++_ : ∀ {Σ} {Γ : ctx Σ} {A B C : tp Γ} -> spine Γ A B -> spine Γ B C -> spine Γ A C
 ε ++ S2 = S2
 (N & S1) ++ S2 = N & (S1 ++ S2)

 _◆'_ : ∀ {Σ} {Γ : ctx Σ} {K} {a : inSig Σ K} {T : tp Γ} {S} -> ntm Γ T -> spine Γ T (a ·' S) -> ntm Γ (a ·' S)
 (H · S) ◆' S₁ = H · (S ++ S₁)
 ƛ N ◆' (N₁ & S₁) = ([ N₁ /x]nn N) ◆' S₁

 [_]ns : ∀ {Σ} {Γ Δ : ctx Σ} {T C : tp Γ} -> (σ : ntsubst Γ Δ) -> spine Γ T C -> spine Δ ([ σ ]tpn T) ([ σ ]tpn C)
 [_]ns σ ε = ε
 [_]ns σ (_&_ {T} {T2} {C} N S) = [ σ ]nn N & subst (λ R → spine _ R ([ σ ]tpn C)) trustMe ([ σ ]ns S)

 [_]nn : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ} -> (σ : ntsubst Γ Δ) -> ntm Γ T -> ntm Δ ([ σ ]tpn T)
 [_]nn σ (v x · S) = ([ σ ]nv x) ◆' ([ σ ]ns S)
 [ σ ]nn (con c · S) = subst (λ T → head _ T) trustMe (con c) · ([ σ ]ns S)
 [_]nn σ (ƛ M) = ƛ ([ ntsubst-ext σ ]nn M)

 single-tsubst : ∀ {Σ} {Γ : ctx Σ} {T} -> ntm Γ T -> ntsubst (Γ ,, T) Γ
 single-tsubst N = id-ntsubst , (subst (λ S → ntm _ S) trustMe N)

 [_/x]tpn : ∀ {Σ} {Γ : ctx Σ} {T} -> ntm Γ T -> tp (Γ ,, T) -> tp Γ
 [ N /x]tpn T = [ single-tsubst N ]tpn T

 [_/x]nn : ∀ {Σ} {Γ : ctx Σ} {T} {C} -> (N : ntm Γ T) -> ntm (Γ ,, T) C -> ntm Γ ([ N /x]tpn C)
 [ N /x]nn M = [ single-tsubst N ]nn M

-- Important things still to do:
-- 1) Add term constants
-- 3) Define "weak" induction principle which disallows recursion on embedded types?
-- 4) Try examples
--    e.g. do plain stlc terms + typing derivations. Prove substitution lemma
--    (even though we do get it for free)
--    because this reveals where nasty equations show up.
-- 5) Do the metatheory involving 

-- Another possible way to save memory? Use irrelevant quantification for types in constructors
 