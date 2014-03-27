{-# OPTIONS --no-positivity-check --no-termination-check --type-in-type #-}
-- By Induction-induction-recursion
module iir-single-head4 where
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

 var : ∀ {Σ} (Γ : ctx Σ) -> Set
 var ⊡ = ⊥
 var (Γ ,' T) = varOpt (var Γ)

 lookup : ∀ {Σ} (Γ : ctx Σ) -> var Γ -> tp Γ
 lookup ⊡ ()
 lookup (Γ ,' T) top = ⇑t1 T
 lookup (Γ ,' T) (pop x) = ⇑t1 (lookup Γ x)

 ntm : ∀ {Σ} (Γ : ctx Σ) -> tp Γ -> Set
 -- TODO : I could even prevent this from storing the type by having "untyped" heads that compute (synthesize) types
 ntm Γ (a · S) = Σ (head Γ) (λ H -> spine Γ (hlookup Γ H) (a · S))
 ntm Γ (Π T S) = ntm (Γ ,' T) S
 -- TODO: Index spine by a "c" and "x" instead of a B
 spine : ∀ {Σ} (Γ : ctx Σ) -> tp Γ -> tp Γ -> Set
 spine Γ (Π A A₁) B = Σ (ntm Γ A) (λ N -> spine Γ ([ N /x]tpn A₁) B)
 spine Γ (c · x) B = (c · x) ≡ B
 data head {Σ} (Γ : ctx Σ) : Set where
  v : (x : var Γ) -> head Γ
  con : (x : inSig1τ Σ) -> head Γ 

 hlookup : ∀ {Σ} (Γ : ctx Σ) -> head Γ -> tp Γ
 hlookup Γ (v x) = lookup Γ x
 hlookup {Σ} Γ (con c) = ⇑t0 (lookupsτ Σ c)

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

 ↑inSig1κ : ∀ {Σ} α -> inSig1κ Σ -> inSig1κ (Σ ,s α)
 ↑inSig1κ (κ K) = pop
 ↑inSig1κ (τ T) = id
 
 ↑t : ∀ {Σ Γ α} -> tp {Σ} Γ -> tp {Σ ,s α} (↑c Γ)
 ↑t (Π T T₁) = Π (↑t T) (↑t T₁)
 ↑t {α = α} (c · x) = ↑inSig1κ α c · subst (λ K → tpSpine _ K) trustMe (↑ts x)

 ↑ts : ∀ {Σ Γ α K} -> tpSpine {Σ} Γ K -> tpSpine {Σ ,s α} (↑c Γ) (↑k K)
 ↑ts {Σ} {Γ} {α} {⋆} S = unit
 ↑ts {Σ} {Γ} {α} {Π T K} (N , S) = (↑n {T = T} N) , (subst (tpSpine _) trustMe (↑ts S))

 ↑n : ∀ {Σ α Γ T} -> ntm {Σ} Γ T -> ntm {Σ ,s α} (↑c Γ) (↑t T)
 ↑n {T = c · St} (H , S) = ↑h H , subst (λ C -> spine _ C (↑t (c · St))) trustMe (↑s S)
 ↑n {T = Π T B} N = ↑n {T = B} N

 ↑v : ∀ {Σ α Γ} -> var {Σ} Γ -> var {Σ ,s α} (↑c Γ)
 ↑v {Σ} {α} {⊡} ()
 ↑v {Σ} {α} {Γ ,' S} top = top
 ↑v {Σ} {α} {Γ ,' S} (pop x) = (pop (↑v x))

 ↑h : ∀ {Σ α Γ} -> head {Σ} Γ -> head {Σ ,s α} (↑c Γ)
 ↑h (v x) = v (↑v x)
 ↑h {α = τ T} (con c) = con (pop c)
 ↑h {α = κ T} (con c) = con c

 ↑s : ∀ {Σ α Γ A B} -> spine {Σ} Γ A B -> spine {Σ ,s α} (↑c Γ) (↑t A) (↑t B)
 ↑s {Σ} {α} {Γ} {Π A A₁} {B} (N , S) = (↑n {T = A} N) , subst (λ C → spine _ C (↑t B)) trustMe (↑s S)
 ↑s {Σ} {κ K} {Γ} {c · x} S = trustMe
 ↑s {Σ} {τ T} {Γ} {c · x} S = trustMe

 tvar : ∀ {Σ} (Γ : ctx Σ) (T : tp Γ) -> Set
 tvar Γ T = Σ (var Γ) (λ x -> lookup Γ x ≡ T)

 vsubst : ∀ {Σ} (Γ Δ : ctx Σ) -> Set
 vsubst ⊡ Δ = Unit
 vsubst (Γ ,' T) Δ = Σ (vsubst Γ Δ) (λ σ -> tvar Δ ([ σ ]tv T))
 id-vsubst : ∀ {Σ} {Γ : ctx Σ} -> vsubst Γ Γ
 do-wkn-vsubst : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Δ} -> vsubst Γ Δ -> vsubst Γ (Δ ,, T)

-- pop-tvar : ∀ {Σ} {Γ : ctx Σ} {S : tp Γ} {T : 

 do-wkn-vsubst {Σ} {⊡} σ = unit
 do-wkn-vsubst {Σ} {Γ ,' T} (σ , x) = (do-wkn-vsubst σ) , ((pop (proj₁ x)) , trustMe) --(subst (varOpt_) trustMe (pop x)) 

 wkn-vsubst : ∀ {Σ} {Γ : ctx Σ} {T : tp Γ} -> vsubst Γ (Γ ,, T)
 wkn-vsubst = do-wkn-vsubst id-vsubst

 id-vsubst {Σ} {⊡} = unit
 id-vsubst {Σ} {Γ ,' T} = (do-wkn-vsubst id-vsubst) , (top , trustMe)

 [_]tv : ∀ {Σ} {Γ Δ : ctx Σ} -> vsubst Γ Δ -> tp Γ -> tp Δ

 vsubst-ext : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ}  (σ : vsubst Γ Δ) -> vsubst (Γ ,, T) (Δ ,, ([ σ ]tv T))
 vsubst-ext σ = do-wkn-vsubst σ , (top , trustMe) --subst (λ S → var _ S) trustMe top

 [_]kv : ∀ {Σ} {Γ Δ : ctx Σ} (σ : vsubst Γ Δ) -> kind Γ -> kind Δ
 [_]kv σ ⋆ = ⋆
 [_]kv σ (Π T K) = Π ([ σ ]tv T) ([ vsubst-ext σ ]kv K)


 [_]tsv : ∀ {Σ} {Γ Δ : ctx Σ} {K : kind Γ} -> (σ : vsubst Γ Δ) -> tpSpine Γ K -> tpSpine Δ ([ σ ]kv K)
 [_]tsv {K = ⋆} σ S = unit -- ε = ε
 [_]tsv {K = Π A K} σ (N , S) = ([ σ ]vn N) , (subst (tpSpine _) trustMe ([ σ ]tsv S))
 -- [_]tsv σ (N , S) = ([ σ ]vn N) , (subst (λ K -> tpSpine _ K) trustMe ([ σ ]tsv S))

-- [_]isv : ∀ {Σ} {Γ Δ : ctx Σ} {K : kind Γ} -> (σ : vsubst Γ Δ) -> inSig Σ K -> inSig Σ ([ σ ]kv K)
 [_]tv σ (Π T S) = Π ([ σ ]tv T) ([ vsubst-ext σ ]tv S)
 [ σ ]tv (c · S) = c ·  subst (λ K → tpSpine _ K) trustMe ([ σ ]tsv S)

 -- [_]isv σ nat = nat
 -- [_]isv σ vec = vec

 [_]v1 : ∀ {Σ} {Γ Δ : ctx Σ} -> (σ : vsubst Γ Δ) -> var Γ -> var Δ
 [_]v1 {Σ} {⊡} unit ()
 [_]v1 {Σ} {Γ ,' T} (σ , (y , _)) top = y
 [_]v1 {Σ} {Γ ,' T} (σ , (y , _)) (pop x) = [_]v1 σ x

 -- [_]vv : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> tvar Γ -> tvar Δ ([ σ ]tv T)
 -- [_]vv {Σ} {⊡} σ ()
 -- [_]vv {Σ} {Γ ,' S} (σ , y) top = y
 -- [_]vv {Σ} {Γ ,' S} (σ , y) (pop x) = [ σ ]vv x -- top = subst (λ S → var _ S) trustMe y
 -- [_]vv (σ , y) (pop x) = subst (λ S → var _ S) trustMe ([ σ ]vv x)

 [_]vh : ∀ {Σ} {Γ Δ : ctx Σ} -> (σ : vsubst Γ Δ) -> head Γ -> head Δ
 [_]vh σ (v x) = v ([ σ ]v1 x) --([ σ ]vv x)
 [ σ ]vh (con c) = con c

 [_]vs : ∀ {Σ} {Γ Δ : ctx Σ} {T C : tp Γ} -> (σ : vsubst Γ Δ) -> spine Γ T C -> spine Δ ([ σ ]tv T) ([ σ ]tv C)
 [_]vs {Σ} {Γ} {Δ} {Π T T₁} {C} σ (N , S) = [_]vn {T = T} σ N , subst (λ A → spine _ A ([ σ ]tv C)) trustMe ([ σ ]vs S)
 [_]vs {Σ} {Γ} {Δ} {c · x} σ S = trustMe --  ε = ε
 -- [_]vs σ (_&_ {T} {T2} {C} N S) = ([ σ ]vn N) & subst (λ S₁ → spine _ S₁ ([ σ ]tv C)) trustMe ([ σ ]vs S)

 [_]vn : ∀ {Σ} {Γ Δ : ctx Σ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> ntm Γ T -> ntm Δ ([ σ ]tv T)
 [_]vn {T = a · St} σ (H , S) = ([ σ ]vh H) , (subst (λ C → spine _ C ([ σ ]tv (a · St))) trustMe ([ σ ]vs S)) --  (H · S) = [ σ ]vh H · [ σ ]vs S
 [_]vn {T = Π A B} σ H = [_]vn {T = B} (vsubst-ext σ) H
 -- [_]vn σ (ƛ M) = ƛ ([ vsubst-ext σ ]vn M)

 -- ⌜_⌝ : ∀ {Σ} -> ctx Σ -> ctxext {Σ} ⊡'
 -- ⌜ ⊡ ⌝ = ⊡
 -- ⌜ Γ ,' T ⌝ = ⌜ Γ ⌝ , (subst tp trustMe T)

 ⇑ce : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) -> ctxext Γ -> ctxext (Γ << Δ)
 ⇑ce Γ Δ ⊡ = ⊡
 ⇑ce Γ Δ (Δ' , T) = (⇑ce Γ Δ Δ') , ⇑t Γ Δ Δ' T

 -- ⇑k : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) -> kind (Γ << Δ') -> kind ((Γ << Δ) << (⇑ce Γ Δ Δ'))
 -- ⇑k Γ Δ Δ' ⋆ = ⋆
 -- ⇑k Γ Δ Δ' (Π T K) = Π (⇑t Γ Δ Δ' T) (⇑k Γ Δ (Δ' , T) K)

 ⇑k0 : ∀ {Σ} {Γ : ctx Σ} -> kind {Σ} ⊡' -> kind Γ
 ⇑k0 {Σ} {Γ} K = [ unit ]kv K

 build-sub : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) -> vsubst (Γ << Δ') ((Γ << Δ) << (⇑ce Γ Δ Δ'))

 ⇑t : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) -> tp (Γ << Δ') -> tp ((Γ << Δ) << (⇑ce Γ Δ Δ'))
 ⇑t Γ Δ Δ' T = [ build-sub Γ Δ Δ' ]tv T

 build-sub Γ ⊡ ⊡ = id-vsubst
 build-sub Γ (Δ , T) ⊡ = do-wkn-vsubst (build-sub Γ Δ ⊡)
 build-sub Γ Δ (Δ' , T) = vsubst-ext (build-sub Γ Δ Δ')

 -- ⇑t Γ Δ Δ' (Π T T₁) = Π (⇑t Γ Δ Δ' T) (⇑t Γ Δ (Δ' , T) T₁)
 -- ⇑t Γ Δ Δ' (a · is) = a · subst (tpSpine _) trustMe (⇑ts Γ Δ Δ' is)

 ⇑t0 : ∀ {Σ} {Γ : ctx Σ} -> tp {Σ} ⊡' -> tp Γ
 ⇑t0 {Σ} {Γ} T = [ unit ]tv T

 -- ⇑ts : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) {K} -> tpSpine (Γ << Δ') K -> tpSpine ((Γ << Δ) << (⇑ce Γ Δ Δ')) (⇑k Γ Δ Δ' K)
 -- ⇑ts Γ Δ Δ' {⋆} S = unit
 -- ⇑ts Γ Δ Δ' {Π T K} (N , S) = ⇑n Γ Δ Δ' {T} N , subst (tpSpine _) trustMe (⇑ts Γ Δ Δ' S) 

 ⇑n : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) {T} -> ntm (Γ << Δ') T -> ntm ((Γ << Δ) << (⇑ce Γ Δ Δ')) (⇑t Γ Δ Δ' T)
 ⇑n Γ Δ Δ' {T} N = [_]vn {T = T} (build-sub Γ Δ Δ') N
 -- ⇑n Γ Δ Δ' {a · St} (H , S) = ⇑h Γ Δ Δ' H , subst (λ C -> spine _ C (⇑t Γ Δ Δ' (a · St))) trustMe (⇑s Γ Δ Δ' S)
 -- ⇑n Γ Δ Δ' {Π T B} N = ⇑n Γ Δ (Δ' , T) {B} N

 -- ⇑s : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) {A B} -> spine (Γ << Δ') A B -> spine ((Γ << Δ) << (⇑ce Γ Δ Δ')) (⇑t Γ Δ Δ' A) (⇑t Γ Δ Δ' B)
 -- ⇑s Γ Δ Δ' {Π A A₁} {B} (N , S) = (⇑n Γ Δ Δ' {A} N) , (subst (λ C → spine _ C (⇑t Γ Δ Δ' B)) trustMe (⇑s Γ Δ Δ' S))
 -- ⇑s Γ Δ Δ' {x · x₁} S = trustMe

 ⇑v : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) -> var (Γ << Δ') -> var ((Γ << Δ) << (⇑ce Γ Δ Δ'))
 ⇑v Γ Δ Δ' x = [ build-sub Γ Δ Δ' ]v1 x
 -- ⇑v Γ ⊡ ⊡ x = x
 -- ⇑v Γ (Δ , T) ⊡ x = pop (⇑v Γ Δ ⊡ x)
 -- ⇑v Γ Δ (Δ' , T) top = top
 -- ⇑v Γ Δ (Δ' , T) (pop x) = pop (⇑v Γ Δ Δ' x)

 -- ⇑h : ∀ {Σ} (Γ : ctx Σ) (Δ : ctxext Γ) (Δ' : ctxext Γ) -> head (Γ << Δ') -> head ((Γ << Δ) << (⇑ce Γ Δ Δ'))
 -- ⇑h Γ Δ Δ' (v x) = v (⇑v Γ Δ Δ' x)
 -- ⇑h Γ Δ Δ' (con x) = con x

 ⇑t1 : ∀ {Σ} {Γ : ctx Σ} {S} -> tp Γ -> tp (Γ ,, S)
 ⇑t1 T = ⇑t _ (⊡ , _) ⊡ T

 -- _◆_ : ∀ {Σ} {Γ : ctx Σ} {C} {T : tp Γ} -> ntm Γ T -> spine Γ T C -> ntm Γ C
 -- _◆_ {Σ} {Γ} {._} {a · St} M refl = M
 -- _◆_ {Σ} {Γ} {T} {Π A B} M (N , S) = ([ N /x]nn M) ◆ S

 -- n-cesub : ∀ {Σ} {Γ : ctx Σ} {B} -> ntm Γ B -> (Δ : ctxext (Γ ,, B)) -> ctxext Γ
 -- n-cesub N ⊡ = ⊡
 -- n-cesub N (Δ , T) = (n-cesub N Δ) , n-tsub N Δ T

 -- n-ksub : ∀ {Σ} {Γ : ctx Σ} {B} (N : ntm Γ B) (Δ : ctxext (Γ ,, B)) -> kind ((Γ ,, B) << Δ) -> kind (Γ << n-cesub N Δ)
 -- n-ksub N Δ ⋆ = ⋆
 -- n-ksub N Δ (Π T K) = Π (n-tsub N Δ T) (n-ksub N (Δ , T) K)

 [_/x]kn : ∀ {Σ} {Γ : ctx Σ} {T} -> ntm Γ T -> kind (Γ ,, T) -> kind Γ
 [ N /x]kn K = {!!} --n-ksub N ⊡ K 

 -- n-tssub : ∀ {Σ} {Γ : ctx Σ} {B} (N : ntm Γ B) (Δ : ctxext (Γ ,, B)) {K} -> tpSpine ((Γ ,, B) << Δ) K -> tpSpine (Γ << (n-cesub N Δ)) (n-ksub N Δ K)
 -- n-tssub N Δ {⋆} S = unit
 -- n-tssub {Σ} {Γ} N Δ {Π T K} (N₁ , S) = (n-sub N Δ N₁) , (subst (tpSpine _) trustMe (n-tssub N Δ S))
 
 -- n-tsub : ∀ {Σ} {Γ : ctx Σ} {B} (N : ntm Γ B) (Δ : ctxext (Γ ,, B)) -> tp ((Γ ,, B) << Δ) -> tp (Γ << n-cesub N Δ)
 -- n-tsub N Δ (Π T T₁) = Π (n-tsub N Δ T) (n-tsub N (Δ , T) T₁)
 -- n-tsub N Δ (x · x₁) = x · (subst (tpSpine _) trustMe (n-tssub N Δ x₁))
 
 -- vare : ∀ {Σ} {Γ : ctx Σ} (Δ : ctxext Γ) -> Set
 -- vare ⊡ = ⊥
 -- vare (Δ , T) = varOpt (vare Δ)

 -- emb : ∀ {Σ} {Γ : ctx Σ} (Δ : ctxext Γ) -> vare Δ -> var (Γ << Δ)
 -- emb ⊡ ()
 -- emb (Δ , T) top = top
 -- emb (Δ , T) (pop y) = pop (emb Δ y)

 -- emb1 : ∀ {Σ} {Γ : ctx Σ} {B} (N : ntm Γ B) (Δ : ctxext (Γ ,, B)) -> vare Δ -> vare (n-cesub N Δ)
 -- emb1 N ⊡ ()
 -- emb1 N (Δ , T) top = top
 -- emb1 N (Δ , T) (pop y) = pop (emb1 N Δ y)

 -- data eqDec {Σ} {Γ : ctx Σ} (Δ : ctxext Γ) : var (Γ << Δ) -> Set where
 --  before : (y : var Γ) -> eqDec Δ (⇑v Γ Δ ⊡ y)
 --  after : ∀ (y : vare Δ) -> eqDec Δ (emb Δ y)

 -- var-eq : ∀ {Σ} {Γ : ctx Σ} (Δ : ctxext Γ) (x : var (Γ << Δ)) -> eqDec Δ x
 -- var-eq ⊡ x = before x
 -- var-eq (Δ , T) top = after top
 -- var-eq (Δ , T) (pop x) with var-eq Δ x
 -- var-eq {Σ} {Γ} (Δ , T) (pop .(⇑v Γ Δ ⊡ y)) | before y = before y
 -- var-eq (Δ , T) (pop .(emb Δ y)) | after y = after (pop y)

 -- -- TODO: Try this again. Has to be "under another context" though
 -- -- nv-sub : ∀ {Σ} {Γ : ctx Σ} {B} (N : ntm Γ B) (Δ : ctxext (Γ ,, B)) (x : var1 ((Γ ,, B) << Δ)) {a St} -> spine (Γ << (n-cesub N Δ)) (n-tsub N Δ (lookup ((Γ ,, B) << Δ) x)) (a ·' St) -> ntm (Γ << (n-cesub N Δ)) (a ·' St)
 -- -- nv-sub N ⊡ top S = N ◆ subst (λ C → spine _ C _) trustMe S
 -- -- nv-sub N ⊡ (pop x) {a} {St} S = v x · subst (λ C → spine _ C (a · St)) trustMe S
 -- -- nv-sub N (Δ , T) top {a} {St} S = v top · subst (λ C -> spine _ C (a · St)) trustMe S
 -- -- nv-sub N (Δ , T) (pop x) S = {!!}

 -- n-sub : ∀ {Σ} {Γ : ctx Σ} {B} (N : ntm Γ B) (Δ : ctxext (Γ ,, B)) {T} -> ntm ((Γ ,, B) << Δ) T -> ntm (Γ << (n-cesub N Δ)) (n-tsub N Δ T)
 -- n-sub N Δ {a · St} (v x , S) with var-eq Δ x
 -- n-sub {Σ} {Γ} {B} N Δ {a · St} (v .(⇑v (Γ ,' B) Δ ⊡ top) , S) | before top = _◆_ {T = ⇑t Γ (n-cesub N Δ) ⊡ B} (⇑n Γ (n-cesub N Δ) ⊡ {B} N) (subst (λ α → spine _ α (n-tsub N Δ (a · St))) trustMe (s-sub N Δ S))
 -- n-sub {Σ} {Γ} {B} N Δ {a · St} (v .(⇑v (Γ ,' B) Δ ⊡ (pop x)) , S) | before (pop x) = (v (⇑v Γ (n-cesub N Δ) ⊡ x) , subst (λ α -> spine _ α (n-tsub N Δ (a · St))) trustMe (s-sub N Δ S))
 -- n-sub {Σ} {Γ} {B} N Δ {a · St} (v .(emb Δ y) , S) | after y = (v (emb (n-cesub N Δ) (emb1 N Δ y)) , subst (λ α -> spine _ α (n-tsub N Δ (a · St))) trustMe (s-sub N Δ S))
 -- n-sub N Δ {a · St} (con c , S) = (con c , subst (λ α → spine _ α (n-tsub N Δ (a · St))) trustMe (s-sub N Δ S))
 -- n-sub N Δ {Π A B} M = n-sub N (Δ , A) {B} M

 -- s-sub : ∀ {Σ} {Γ : ctx Σ} {B} (N : ntm Γ B) (Δ : ctxext (Γ ,, B)) {T C} -> spine ((Γ ,, B) << Δ) T C -> spine (Γ << (n-cesub N Δ)) (n-tsub N Δ T) (n-tsub N Δ C)
 -- s-sub N Δ {a · is} S = trustMe
 -- s-sub N Δ {Π T1 T2} {C} (N₁ , S) = (n-sub N Δ {T1} N₁) , (subst (λ α → spine _ α (n-tsub N Δ C)) trustMe (s-sub N Δ S))


 [_/x]tpn : ∀ {Σ} {Γ : ctx Σ} {T} -> ntm Γ T -> tp (Γ ,, T) -> tp Γ
 [ N /x]tpn T = {!!} -- n-tsub N ⊡ T -- TODO: we could just give these operations better syntax and forget about this definition

 [_/x]nn : ∀ {Σ} {Γ : ctx Σ} {T} {C} -> (N : ntm Γ T) -> ntm (Γ ,, T) C -> ntm Γ ([ N /x]tpn C)
 [_/x]nn {C = C} N M = {!!} --n-sub N ⊡ {C} M --[ single-tsubst N ]nn M

-- Important things still to do:
-- 3) Define "weak" induction principle which disallows recursion on embedded types?
-- 4) Try examples
--    e.g. do plain stlc terms + typing derivations. Prove substitution lemma
--    (even though we do get it for free)
--    because this reveals where nasty equations show up.
-- 5) Do the metatheory involving 

-- Another possible way to save memory? Use irrelevant quantification for types in constructors
 