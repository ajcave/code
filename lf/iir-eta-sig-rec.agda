{-# OPTIONS --no-positivity-check --no-termination-check #-}
-- By Induction-induction-recursion
module iir-eta-sig-rec where
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
  data ctx : Set where
   ⊡ : ctx 
   _,'_ : (Γ : ctx ) -> (T : tp Γ) -> ctx 

  ⊡' : ctx 
  ⊡' = ⊡
 
  -- Should I actually compute Γ by (induction) recursion on the kind?
  -- Maybe these need to be "in reverse order"?
  data kind (Γ : ctx) : Set where
   ⋆ : kind Γ
   Π : (T : tp Γ) -> (K : kind (Γ ,, T)) -> kind Γ

  data inSig : kind ⊡' -> Set

  data tp (Γ : ctx) : Set where
   Π : (T : tp Γ) (S : tp (Γ ,' T)) -> tp Γ
   _·_ : ∀ {K : kind ⊡'} -> (c : inSig K) -> tpSpine Γ ([ ⊡s ]kv K) -> tp Γ
  
  data inSigτ : tp ⊡' -> Set

  data tpSpine (Γ : ctx) : kind Γ -> Set where
   ε : tpSpine Γ ⋆
   _,κ_ : ∀ {T : tp Γ} {K : kind (Γ ,, T)} (N : ntm Γ T) -> tpSpine Γ ([ N /x]kn K)  -> tpSpine Γ (Π T K)


  _,,_ : (Γ : ctx) -> (T : tp Γ) -> ctx
  Γ ,, T = Γ ,' T
 
  vsubst : ∀ (Γ Δ : ctx) -> Set
  ntsubst : ∀ (Γ Δ : ctx) -> Set
  id-vsubst : ∀ {Γ : ctx} -> vsubst Γ Γ
  do-wkn-vsubst : ∀ {Γ Δ : ctx} {T : tp Δ} -> vsubst Γ Δ -> vsubst Γ (Δ ,, T)
 
  ntsubst ⊡ Δ = Unit
  ntsubst (Γ ,' T) Δ = Σ (ntsubst Γ Δ) (λ σ -> (ntm Δ ([ σ ]tpn T)))

  -- Do we really need λ to be a constructor?
  -- I guess that we could actually just compute the ntm type by recursion on the tp
  -- arriving eventually at _·_ with Γ appropriately extended (iir-eta-comp)
  -- Can we do the same thing in the formal metatheory of LF?
  data var : (Γ : ctx) -> tp Γ -> Set where
   top : ∀ {Γ T} -> var (Γ ,' T) ([ do-wkn-vsubst id-vsubst ]tv T)
   pop : ∀ {Γ T S} (x : var Γ T) -> var (Γ ,' S) ([ do-wkn-vsubst id-vsubst ]tv T)
  data ntm (Γ : ctx) : tp Γ -> Set where
   _·_ : ∀ {K} {T} {a : inSig K} {S} -> head Γ T -> spine Γ T (a · S) -> ntm Γ (a · S)
   ƛ : ∀ {T S} -> ntm (Γ ,' T) S -> ntm Γ (Π T S)
  data spine (Γ : ctx) : tp Γ -> tp Γ -> Set where
   ε : ∀ {T} -> spine Γ T T
   _&_ : ∀ {T T2 C} -> (N : ntm Γ T) -> (S : spine Γ ([ N /x]tpn T2) C) -> spine Γ (Π T T2) C
  data head (Γ : ctx) : tp Γ -> Set where
   v : ∀ {T} -> var Γ T -> head Γ T
   con : ∀ {T : tp ⊡'} -> inSigτ T -> head Γ ([ ⊡s ]tv T)

  vsubst ⊡ Δ = Unit
  vsubst (Γ ,' T) Δ = Σ (vsubst Γ Δ) (λ σ -> (var Δ ([ σ ]tv T)))

  [_]tv : ∀ {Γ Δ : ctx} -> vsubst Γ Δ -> tp Γ -> tp Δ

  pop' : ∀ {Γ : ctx} {T : tp Γ} {S} (x : var Γ T) -> var (Γ ,, S) ([  do-wkn-vsubst id-vsubst ]tv T)
  pop' = pop

  do-wkn-vsubst {⊡} σ = unit
  do-wkn-vsubst {Γ ,' T} (σ , x) = do-wkn-vsubst σ , subst (λ S → var _ S) trustMe (pop x)

  wkn-vsubst : ∀ {Γ : ctx} {T : tp Γ} -> vsubst Γ (Γ ,, T)
  wkn-vsubst = do-wkn-vsubst id-vsubst

  id-vsubst {⊡} = unit
  id-vsubst {Γ ,' T} = (do-wkn-vsubst id-vsubst) , top

  vsubst-ext : ∀ {Γ Δ : ctx} {T : tp Γ}  (σ : vsubst Γ Δ) -> vsubst (Γ ,, T) (Δ ,, ([ σ ]tv T))
  vsubst-ext σ = do-wkn-vsubst σ , subst (λ S → var _ S) trustMe top

  [_]kv : ∀ {Γ Δ : ctx} (σ : vsubst Γ Δ) -> kind Γ -> kind Δ
  [_]kv σ ⋆ = ⋆
  [_]kv σ (Π T K) = Π ([ σ ]tv T) ([ vsubst-ext σ ]kv K)

  ⊡s : ∀ {Γ : ctx} -> vsubst ⊡' Γ
  ⊡s = unit

  _·'_ : ∀ {Γ : ctx} {K : kind ⊡'} -> (c : inSig K) -> tpSpine Γ ([ ⊡s ]kv K) -> tp Γ
  c ·' S = c · S

  [_]tsv : ∀ {Γ Δ : ctx} {K : kind Γ} -> (σ : vsubst Γ Δ) -> tpSpine Γ K -> tpSpine Δ ([ σ ]kv K)
  [_]tsv σ ε = ε
  [_]tsv σ (N ,κ S) = ([ σ ]vn N) ,κ (subst (λ K -> tpSpine _ K) trustMe ([ σ ]tsv S))

  [_]tv σ (Π T S) = Π ([ σ ]tv T) ([ vsubst-ext σ ]tv S)
  [ σ ]tv (c · S) = c ·  subst (λ K → tpSpine _ K) trustMe ([ σ ]tsv S)

  [_]vv : ∀ {Γ Δ : ctx} {T : tp Γ} -> (σ : vsubst Γ Δ) -> var Γ T -> var Δ ([ σ ]tv T)
  [_]vv (σ , y) top = subst (λ S → var _ S) trustMe y
  [_]vv (σ , y) (pop x) = subst (λ S → var _ S) trustMe ([ σ ]vv x)

  [_]vh : ∀ {Γ Δ : ctx} {T : tp Γ} -> (σ : vsubst Γ Δ) -> head Γ T -> head Δ ([ σ ]tv T)
  [_]vh σ (v x) = v ([ σ ]vv x)
  [ σ ]vh (con c) = subst (λ T → head _ T) trustMe (con c)

  [_]vs : ∀ {Γ Δ : ctx} {T C : tp Γ} -> (σ : vsubst Γ Δ) -> spine Γ T C -> spine Δ ([ σ ]tv T) ([ σ ]tv C)
  [_]vs σ ε = ε
  [_]vs σ (_&_ {T} {T2} {C} N S) = ([ σ ]vn N) & subst (λ S₁ → spine _ S₁ ([ σ ]tv C)) trustMe ([ σ ]vs S)

  [_]vn : ∀ {Γ Δ : ctx} {T : tp Γ} -> (σ : vsubst Γ Δ) -> ntm Γ T -> ntm Δ ([ σ ]tv T)
  [_]vn σ (H · S) = [ σ ]vh H · [ σ ]vs S
  [_]vn σ (ƛ M) = ƛ ([ vsubst-ext σ ]vn M)

  do-wkn-ntsubst : ∀ {Γ Δ : ctx} {T : tp Δ} -> ntsubst Γ Δ -> ntsubst Γ (Δ ,, T)
  do-wkn-ntsubst {⊡} σ = unit
  do-wkn-ntsubst {Γ ,' T} (σ , N) = do-wkn-ntsubst σ , subst (λ S → ntm _ S) trustMe ([ wkn-vsubst ]vn N)

  _◇_ : ∀ {Γ : ctx} {A B} -> head Γ A -> spine Γ A B -> ntm Γ B
  _◇_ {Γ} {A} {Π B B₁} H S = ƛ (([ wkn-vsubst ]vh H) ◇ ([ wkn-vsubst ]vs S ++ ((v top ◇ ε) & subst (λ C → spine  _ C B₁) trustMe ε)))
  _◇_ {Γ} {A} {c · x} H S = H · S

  id-ntsubst : ∀ {Γ : ctx} -> ntsubst Γ Γ
  id-ntsubst {⊡} = unit
  id-ntsubst {Γ ,' T} = do-wkn-ntsubst id-ntsubst , (subst (λ S -> ntm _ S) trustMe (v top ◇ ε))

  [_]tpn : ∀ {Γ Δ : ctx} -> ntsubst Γ Δ -> tp Γ -> tp Δ
  ntsubst-ext : ∀ {Γ Δ : ctx} {T : tp Γ}  (σ : ntsubst Γ Δ) -> ntsubst (Γ ,, T) (Δ ,, ([ σ ]tpn T))
  ntsubst-ext σ = (do-wkn-ntsubst σ) , (subst (λ S → ntm _ S) trustMe (v top ◇ ε))

  [_]kn : ∀ {Γ Δ : ctx} (σ : ntsubst Γ Δ) -> kind Γ -> kind Δ
  [_]kn σ ⋆ = ⋆
  [_]kn σ (Π T K) = Π ([ σ ]tpn T) ([ ntsubst-ext σ ]kn K)

  [_/x]kn : ∀ {Γ : ctx} {T} -> ntm Γ T -> kind (Γ ,, T) -> kind Γ
  [ N /x]kn K = [ single-tsubst N ]kn K

  [_]ts : ∀ {Γ Δ : ctx} {K : kind Γ} -> (σ : ntsubst Γ Δ) -> tpSpine Γ K -> tpSpine Δ ([ σ ]kn K)
  [_]ts σ ε = ε
  [_]ts σ (N ,κ S) = ([ σ ]nn N) ,κ (subst (λ K → tpSpine _ K) trustMe ([ σ ]ts S))

  [ σ ]tpn (Π T T₁) = Π ([ σ ]tpn T) ([ ntsubst-ext σ ]tpn T₁)
  [ σ ]tpn (c · S) = c · subst (λ K → tpSpine _ K) trustMe ([ σ ]ts S)

  [_]nv : ∀ {Γ Δ : ctx} {T : tp Γ} -> (σ : ntsubst Γ Δ) -> var Γ T -> ntm Δ ([ σ ]tpn T)
  [_]nv (σ , N) top = subst (λ S → ntm _ S) trustMe N
  [_]nv (σ , N) (pop x) = subst (λ S → ntm _ S) trustMe ([ σ ]nv x)

  _++_ : ∀ {Γ : ctx} {A B C : tp Γ} -> spine Γ A B -> spine Γ B C -> spine Γ A C
  ε ++ S2 = S2
  (N & S1) ++ S2 = N & (S1 ++ S2)

  _◆'_ : ∀ {Γ : ctx} {K} {a : inSig K} {T : tp Γ} {S} -> ntm Γ T -> spine Γ T (a ·' S) -> ntm Γ (a ·' S)
  (H · S) ◆' S₁ = H · (S ++ S₁)
  ƛ N ◆' (N₁ & S₁) = ([ N₁ /x]nn N) ◆' S₁

  [_]ns : ∀ {Γ Δ : ctx} {T C : tp Γ} -> (σ : ntsubst Γ Δ) -> spine Γ T C -> spine Δ ([ σ ]tpn T) ([ σ ]tpn C)
  [_]ns σ ε = ε
  [_]ns σ (_&_ {T} {T2} {C} N S) = [ σ ]nn N & subst (λ R → spine _ R ([ σ ]tpn C)) trustMe ([ σ ]ns S)

  [_]nn : ∀ {Γ Δ : ctx} {T : tp Γ} -> (σ : ntsubst Γ Δ) -> ntm Γ T -> ntm Δ ([ σ ]tpn T)
  [_]nn σ (v x · S) = ([ σ ]nv x) ◆' ([ σ ]ns S)
  [ σ ]nn (con c · S) = subst (λ T → head _ T) trustMe (con c) · ([ σ ]ns S)
  [_]nn σ (ƛ M) = ƛ ([ ntsubst-ext σ ]nn M)

  single-tsubst : ∀ {Γ : ctx} {T} -> ntm Γ T -> ntsubst (Γ ,, T) Γ
  single-tsubst N = id-ntsubst , (subst (λ S → ntm _ S) trustMe N)

  [_/x]tpn : ∀ {Γ : ctx} {T} -> ntm Γ T -> tp (Γ ,, T) -> tp Γ
  [ N /x]tpn T = [ single-tsubst N ]tpn T

  [_/x]nn : ∀ {Γ : ctx} {T} {C} -> (N : ntm Γ T) -> ntm (Γ ,, T) C -> ntm Γ ([ N /x]tpn C)
  [ N /x]nn M = [ single-tsubst N ]nn M

  data inSig where
   nat : inSig ⋆
   vec : inSig (Π (nat · ε) ⋆)

  data inSigτ where
   zero : inSigτ (nat · ε)
   suc : inSigτ (Π (nat · ε) (nat · ε))
   nil : inSigτ (vec · ((con zero · ε) ,κ ε))
   cons : inSigτ (Π (nat · ε) (Π (vec · ((v top · ε) ,κ ε)) (vec · ((con suc · ((v (pop top) · ε) & ε)) ,κ ε))))

-- Important things still to do:
-- 3) Define "weak" induction principle which disallows recursion on embedded types?
-- 4) Try examples
--    e.g. do plain stlc terms + typing derivations. Prove substitution lemma
--    (even though we do get it for free)
--    because this reveals where nasty equations show up.
-- 5) Do the metatheory involving 
 