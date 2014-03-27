{-# OPTIONS --no-positivity-check --no-termination-check --type-in-type #-}
-- By Induction-induction-recursion
module iir-single where
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import Data.Empty

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

 -- Maybe I should use a relational approach so that there's no so much "green goo" in the indices
 data ctxext {Σ} (Γ : ctx Σ) : Set where
  ⊡ : ctxext Γ
  _,_ : (Δ : ctxext Γ) -> (T : tp (Γ << Δ)) -> ctxext Γ

 _<<_ : ∀ {Σ} -> (Γ : ctx Σ) -> ctxext Γ -> ctx Σ
 Γ << ⊡ = Γ
 Γ << (Δ , T) = (Γ << Δ) ,' T
 
 -- Should I actually compute Γ by (induction) recursion on the kind?
 -- Maybe these need to be "in reverse order"?
 data kind {Σ : sig} (Γ : ctx Σ) : Set where
  ⋆ : kind Γ
  Π : (T : tp Γ) -> (K : kind (Γ ,, T)) -> kind Γ

 κ' : ∀ {Σ} -> kind {Σ} ⊡' -> sigsort Σ
 κ' = κ

 data tp {Σ : sig} (Γ : ctx Σ) : Set where
  Π : (T : tp Γ) (S : tp (Γ ,' T)) -> tp Γ
  _·_ : (x : inSig1κ Σ) -> tpSpine Γ (⇑k0 (lookups Σ x)) -> tp Γ

 tpSpine : ∀ {Σ} (Γ : ctx Σ) -> kind Γ -> Set
 tpSpine Γ ⋆ = Unit
 tpSpine Γ (Π T K) = Σ (ntm Γ T) (λ N → tpSpine Γ ([ N /x]kn K))

 _,,_ : {Σ : sig} -> (Γ : ctx Σ) -> (T : tp Γ) -> ctx Σ
 Γ ,, T = Γ ,' T
 
 -- Do we really need λ to be a constructor?
 -- I guess that we could actually just compute the ntm type by recursion on the tp
 -- arriving eventually at _·_ with Γ appropriately extended (iir-eta-comp)
 -- Can we do the same thing in the formal metatheory of LF?

 data varOpt (A : Set) : Set where
  top : varOpt A
  pop : A -> varOpt A

 var1 : ∀ {Σ} (Γ : ctx Σ) -> Set
 var1 ⊡ = ⊥
 var1 (Γ ,' T) = varOpt (var1 Γ)

 lookup : ∀ {Σ} (Γ : ctx Σ) -> var1 Γ -> tp Γ
 lookup ⊡ ()
 lookup (Γ ,' T) top = ⇑t1 T
 lookup (Γ ,' T) (pop x) = ⇑t1 (lookup Γ x)

 data ntm {Σ} (Γ : ctx Σ) : tp Γ -> Set where
  _·_ : ∀ {T} {a S} -> head Γ T -> spine Γ T (a · S) -> ntm Γ (a · S)
  ƛ : ∀ {T S} -> ntm (Γ ,' T) S -> ntm Γ (Π T S)
 spine : ∀ {Σ} (Γ : ctx Σ) -> tp Γ -> tp Γ -> Set
 spine Γ (Π A A₁) B = Σ (ntm Γ A) (λ N -> spine Γ ([ N /x]tpn A₁) B)
 spine Γ (c · x) B = (c · x) ≡ B
 data head {Σ} (Γ : ctx Σ) : tp Γ -> Set where
  v : (x : var1 Γ) -> head Γ (lookup Γ x)
  con : (x : inSig1τ Σ) -> head Γ (⇑t0 (lookupsτ Σ x))

 ↑c : ∀ {Σ α} -> ctx Σ -> ctx (Σ ,s α)
 ↑c ⊡ = ⊡
 ↑c (Γ ,' T) = (↑c Γ) ,' (↑t T)

 ↑k : ∀ {Σ} {Γ : ctx Σ} {α : sigsort Σ} -> kind {Σ} Γ -> kind {Σ ,s α} (↑c Γ)
 ↑k ⋆ = ⋆
 ↑k (Π T K) = Π (↑t T) (↑k K)

 ↑ss : ∀ {Σ α} -> sigsort Σ -> sigsort (Σ ,s α)
 ↑ss (κ K) = κ (↑k K)
 ↑ss (τ T) = τ (↑t T)

 inSig1κ : ∀ Σ -> Set
 inSig1κ ⊡ = ⊥
 inSig1κ (Σ , τ T) = inSig1κ Σ
 inSig1κ (Σ , κ K) = varOpt (inSig1κ Σ)

 inSig1τ : ∀ Σ -> Set
 inSig1τ ⊡ = ⊥
 inSig1τ (Σ , κ T) = inSig1τ Σ
 inSig1τ (Σ , τ K) = varOpt (inSig1τ Σ)

 lookups : ∀ Σ -> inSig1κ Σ -> kind {Σ} ⊡'
 lookups ⊡ ()
 lookups (Σ , τ T) x = ↑k (lookups Σ x)
 lookups (Σ , κ K) top = ↑k K
 lookups (Σ , κ K) (pop x) = ↑k (lookups Σ x)

 lookupsτ : ∀ Σ -> inSig1τ Σ -> tp {Σ} ⊡'
 lookupsτ ⊡ ()
 lookupsτ (Σ , κ T) x = ↑t (lookupsτ Σ x)
 lookupsτ (Σ , τ K) top = ↑t K
 lookupsτ (Σ , τ K) (pop x) = ↑t (lookupsτ Σ x)
 
 ↑t : ∀ {Σ Γ α} -> tp {Σ} Γ -> tp {Σ ,s α} (↑c Γ)
 ↑t (Π T T₁) = Π (↑t T) (↑t T₁)
 ↑t {α = κ K} (c · x) = pop c · subst (λ K → tpSpine _ K) trustMe (↑ts x)
 ↑t {α = τ T} (c · x) = c · subst (λ K → tpSpine _ K) trustMe (↑ts x)

 ↑ts : ∀ {Σ Γ α K} -> tpSpine {Σ} Γ K -> tpSpine {Σ ,s α} (↑c Γ) (↑k K)
 ↑ts {Σ} {Γ} {α} {⋆} S = unit
 ↑ts {Σ} {Γ} {α} {Π T K} (N , S) = (↑n N) , (subst (tpSpine _) trustMe (↑ts S))

 ↑n : ∀ {Σ α Γ T} -> ntm {Σ} Γ T -> ntm {Σ ,s α} (↑c Γ) (↑t T)
 ↑n {α = τ T} (c · S) = (↑h c) · (↑s S)
 ↑n {α = κ K} (c · S) = (↑h c) · (↑s S) 
 ↑n (ƛ M) = ƛ (↑n M)

 ↑v : ∀ {Σ α Γ} -> var1 {Σ} Γ -> var1 {Σ ,s α} (↑c Γ)
 ↑v {Σ} {α} {⊡} ()
 ↑v {Σ} {α} {Γ ,' S} top = top
 ↑v {Σ} {α} {Γ ,' S} (pop x) = (pop (↑v x))

 ↑h : ∀ {Σ α Γ T} -> head {Σ} Γ T -> head {Σ ,s α} (↑c Γ) (↑t T)
 ↑h (v x) = subst (head _) trustMe (v (↑v x))
 ↑h {α = τ T} (con c) = subst (λ T → head _ T) trustMe (con (pop c))
 ↑h {α = κ T} (con c) = subst (head _) trustMe (con c)

 ↑s : ∀ {Σ α Γ A B} -> spine {Σ} Γ A B -> spine {Σ ,s α} (↑c Γ) (↑t A) (↑t B)
 ↑s {Σ} {α} {Γ} {Π A A₁} {B} (N , S) = (↑n N) , subst (λ C → spine _ C (↑t B)) trustMe (↑s S)
 ↑s {Σ} {κ K} {Γ} {c · x} S = trustMe
 ↑s {Σ} {τ T} {Γ} {c · x} S = trustMe

 ⌜_⌝ : ∀ {Σ} -> ctx Σ -> ctxext {Σ} ⊡'
 ⌜ ⊡ ⌝ = ⊡
 ⌜ Γ ,' T ⌝ = ⌜ Γ ⌝ , (subst tp trustMe T)

 ⇑ce : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) -> ctxext Γ -> ctxext (Γ << Δ)
 ⇑ce Γ Δ ⊡ = ⊡
 ⇑ce Γ Δ (Δ' , T) = (⇑ce Γ Δ Δ') , ⇑t Γ Δ Δ' T

 ⇑k : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) -> kind (Γ << Δ') -> kind ((Γ << Δ) << (⇑ce Γ Δ Δ'))
 ⇑k Γ Δ Δ' ⋆ = ⋆
 ⇑k Γ Δ Δ' (Π T K) = Π (⇑t Γ Δ Δ' T) (⇑k Γ Δ (Δ' , T) K)

 ⇑k0 : ∀ {Σ} {Γ : ctx Σ} -> kind {Σ} ⊡' -> kind Γ
 ⇑k0 {Σ} {Γ} K = subst kind trustMe (⇑k ⊡ ⌜ Γ ⌝ ⊡ K)

 ⇑t : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) -> tp (Γ << Δ') -> tp ((Γ << Δ) << (⇑ce Γ Δ Δ'))
 ⇑t Γ Δ Δ' (Π T T₁) = Π (⇑t Γ Δ Δ' T) (⇑t Γ Δ (Δ' , T) T₁)
 ⇑t Γ Δ Δ' (a · is) = a · subst (tpSpine _) trustMe (⇑ts Γ Δ Δ' is)

 ⇑t0 : ∀ {Σ} {Γ : ctx Σ} -> tp {Σ} ⊡' -> tp Γ
 ⇑t0 {Σ} {Γ} T = subst tp trustMe (⇑t ⊡ ⌜ Γ ⌝ ⊡ T)

 ⇑ts : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) {K} -> tpSpine (Γ << Δ') K -> tpSpine ((Γ << Δ) << (⇑ce Γ Δ Δ')) (⇑k Γ Δ Δ' K)
 ⇑ts Γ Δ Δ' {⋆} S = unit
 ⇑ts Γ Δ Δ' {Π T K} (N , S) = ⇑n Γ Δ Δ' N , subst (tpSpine _) trustMe (⇑ts Γ Δ Δ' S) 

 ⇑n : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) {T} -> ntm (Γ << Δ') T -> ntm ((Γ << Δ) << (⇑ce Γ Δ Δ')) (⇑t Γ Δ Δ' T)
 ⇑n Γ Δ Δ' (c · S) = (⇑h Γ Δ Δ' c) · ⇑s Γ Δ Δ' S
 ⇑n Γ Δ Δ' (ƛ N) = ƛ (⇑n Γ Δ (Δ' , _) N)

 ⇑s : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) {A B} -> spine (Γ << Δ') A B -> spine ((Γ << Δ) << (⇑ce Γ Δ Δ')) (⇑t Γ Δ Δ' A) (⇑t Γ Δ Δ' B)
 ⇑s Γ Δ Δ' {Π A A₁} {B} (N , S) = (⇑n Γ Δ Δ' N) , (subst (λ C → spine _ C (⇑t Γ Δ Δ' B)) trustMe (⇑s Γ Δ Δ' S))
 ⇑s Γ Δ Δ' {x · x₁} S = trustMe

 ⇑v : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) -> var1 (Γ << Δ') -> var1 ((Γ << Δ) << (⇑ce Γ Δ Δ'))
 ⇑v Γ ⊡ ⊡ x = x
 ⇑v Γ (Δ , T) ⊡ x = pop (⇑v Γ Δ ⊡ x)
 ⇑v Γ Δ (Δ' , T) top = top
 ⇑v Γ Δ (Δ' , T) (pop x) = pop (⇑v Γ Δ Δ' x)

 ⇑h : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) {T} -> head (Γ << Δ') T -> head ((Γ << Δ) << (⇑ce Γ Δ Δ')) (⇑t Γ Δ Δ' T)
 ⇑h Γ Δ Δ' (v x) = subst (head _) trustMe (v (⇑v Γ Δ Δ' x))
 ⇑h Γ Δ Δ' (con x) = subst (head _) trustMe (con x)

 ⇑t1 : ∀ {Σ} {Γ : ctx Σ} {S} -> tp Γ -> tp (Γ ,, S)
 ⇑t1 T = ⇑t _ (⊡ , _) ⊡ T
 
 [_/x]kn : ∀ {Σ} {Γ : ctx Σ} {T} -> ntm Γ T -> kind (Γ ,, T) -> kind Γ
 [ N /x]kn K = {!!} --[ single-tsubst N ]kn K

 -- _++_ : ∀ {Σ} {Γ : ctx Σ} {A B C : tp Γ} -> spine Γ A B -> spine Γ B C -> spine Γ A C
 -- _++_ {Σ} {Γ} {c · xs} refl S2 = S2
 -- _++_ {Σ} {Γ} {Π A B} (N , S1) S2 = N , (S1 ++ S2)

 _◆'_ : ∀ {Σ} {Γ : ctx Σ} {C} {T : tp Γ} -> ntm Γ T -> spine Γ T C -> ntm Γ C
 _◆'_ {Σ} {Γ} {C} {Π T T₁} (ƛ M) (N , S) = [ N /x]nn M ◆' S
 _◆'_ {Σ} {Γ} {.(x · x₁)} {x · x₁} N refl = N

 [_/x]tpn : ∀ {Σ} {Γ : ctx Σ} {T} -> ntm Γ T -> tp (Γ ,, T) -> tp Γ
 [ N /x]tpn T = {!!} --[ single-tsubst N ]tpn T

 [_/x]nn : ∀ {Σ} {Γ : ctx Σ} {T} {C} -> (N : ntm Γ T) -> ntm (Γ ,, T) C -> ntm Γ ([ N /x]tpn C)
 [ N /x]nn M = {!!} --[ single-tsubst N ]nn M

-- Important things still to do:
-- 3) Define "weak" induction principle which disallows recursion on embedded types?
-- 4) Try examples
--    e.g. do plain stlc terms + typing derivations. Prove substitution lemma
--    (even though we do get it for free)
--    because this reveals where nasty equations show up.
-- 5) Do the metatheory involving 

-- Another possible way to save memory? Use irrelevant quantification for types in constructors
 