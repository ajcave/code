{-# OPTIONS --no-positivity-check --no-termination-check #-}
-- By Induction-induction-recursion
module iir-kinding where
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
-- This file treats constants for kinds slightly differently: they must be "closed"
-- and they are weakened at their use-point
-- How does this scale to also allowing term constants? Not sure...

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
mutual
 data ctx : Set where
  ⊡ : ctx
  _,'_ : (Γ : ctx) -> (T : tp Γ) -> ctx

 ⊡' : ctx
 ⊡' = ⊡
 
 -- Should I actually compute Γ by (induction) recursion on the kind?
 -- Maybe these need to be "in reverse order"?
 data kind (Γ : ctx) : Set where
  ⋆ : kind Γ
  Π : (T : tp Γ) -> (K : kind (Γ ,, T)) -> kind Γ

 data tp (Γ : ctx) : Set where
  Π : (T : tp Γ) (S : tp (Γ ,' T)) -> tp Γ
  _·_ : ∀ {K : kind ⊡'} -> (c : inSig K) -> tpSpine Γ ([ ⊡s ]kv K) -> tp Γ

 data tpSpine Γ : kind Γ -> Set where
  ε : tpSpine Γ ⋆
  _,κ_ : ∀ {T : tp Γ} {K : kind (Γ ,, T)} (N : ntm Γ T) -> tpSpine Γ ([ N /x]kn K) -> tpSpine Γ (Π T K)

 

 _,,_ : (Γ : ctx) -> (T : tp Γ) -> ctx
 Γ ,, T = Γ ,' T
 
 vsubst : (Γ Δ : ctx) -> Set
 ntsubst : (Γ Δ : ctx) -> Set
 id-vsubst : ∀ {Γ} -> vsubst Γ Γ
 do-wkn-vsubst : ∀ {Γ Δ : ctx} {T : tp Δ} -> vsubst Γ Δ -> vsubst Γ (Δ ,, T)
 
 ntsubst ⊡ Δ = Unit
 ntsubst (Γ ,' T) Δ = Σ (ntsubst Γ Δ) (λ σ -> (ntm Δ ([ σ ]tpn T)))

 -- TODO: We need to enforce η-longness?
 -- Do we really need λ to be a constructor?
 -- I guess that we could actually just compute the ntm type by recursion on the tp
 -- arriving eventually at _·_ with Γ appropriately extended
 -- Can we do the same thing in the formal metatheory of LF?
 data var : (Γ : ctx) -> tp Γ -> Set where
  top : ∀ {Γ T} -> var (Γ ,' T) ([ do-wkn-vsubst id-vsubst ]tv T)
  pop : ∀ {Γ T S} (x : var Γ T) -> var (Γ ,' S) ([ do-wkn-vsubst id-vsubst ]tv T)
 data ntm (Γ : ctx) : tp Γ -> Set where
  _·_ : ∀ {T S} -> head Γ T -> spine Γ T S -> ntm Γ S
  ƛ : ∀ {T S} -> ntm (Γ ,' T) S -> ntm Γ (Π T S)
 data spine (Γ : ctx) : tp Γ -> tp Γ -> Set where
  ε : ∀ {T} -> spine Γ T T
  _&_ : ∀ {T T2 C} -> (N : ntm Γ T) -> (S : spine Γ ([ N /x]tpn T2) C) -> spine Γ (Π T T2) C
 data head (Γ : ctx) : tp Γ -> Set where
  v : ∀ {T} -> var Γ T -> head Γ T

 vsubst ⊡ Δ = Unit
 vsubst (Γ ,' T) Δ = Σ (vsubst Γ Δ) (λ σ -> (var Δ ([ σ ]tv T)))

 [_]tv : ∀ {Γ Δ} -> vsubst Γ Δ -> tp Γ -> tp Δ

 pop' : ∀ {Γ} {T : tp Γ} {S} (x : var Γ T) -> var (Γ ,, S) ([  do-wkn-vsubst id-vsubst ]tv T)
 pop' = pop

 do-wkn-vsubst {⊡} σ = unit
 do-wkn-vsubst {Γ ,' T} (σ , x) = do-wkn-vsubst σ , subst (λ S → var _ S) trustMe (pop x)

 wkn-vsubst : ∀ {Γ : ctx} {T : tp Γ} -> vsubst Γ (Γ ,, T)
 wkn-vsubst = do-wkn-vsubst id-vsubst

 id-vsubst {⊡} = unit
 id-vsubst {Γ ,' T} = (do-wkn-vsubst id-vsubst) , top

 vsubst-ext : ∀ {Γ Δ : ctx} {T : tp Γ}  (σ : vsubst Γ Δ) -> vsubst (Γ ,, T) (Δ ,, ([ σ ]tv T))
 vsubst-ext σ = do-wkn-vsubst σ , subst (λ S → var _ S) trustMe top
 --vsubst-map : ∀ {Γ Δ} -> vsubst Γ Δ -> 

 [_]kv : ∀ {Γ Δ} (σ : vsubst Γ Δ) -> kind Γ -> kind Δ
 [_]kv σ ⋆ = ⋆
 [_]kv σ (Π T K) = Π ([ σ ]tv T) ([ vsubst-ext σ ]kv K)

 -- Hmm what is the scope for these? Γ seems weird...
 -- Especially since we intend to parameterize by them... I guess it needs to be some
 -- family that supports weakening?
 data inSig : kind ⊡' -> Set where
  nat : inSig ⋆
  vec : inSig (Π (nat · ε) ⋆)

 ⊡s : ∀ {Γ} -> vsubst ⊡' Γ
 ⊡s = unit

 [_]tsv : ∀ {Γ Δ} {K : kind Γ} -> (σ : vsubst Γ Δ) -> tpSpine Γ K -> tpSpine Δ ([ σ ]kv K)
 [_]tsv σ ε = ε
 [_]tsv σ (N ,κ S) = ([ σ ]vn N) ,κ (subst (λ K -> tpSpine _ K) trustMe ([ σ ]tsv S))

 --[_]isv : ∀ {Γ Δ} {K : kind Γ} -> (σ : vsubst Γ Δ) -> inSig K -> inSig ([ σ ]kv K)
 [_]tv σ (Π T S) = Π ([ σ ]tv T) ([ vsubst-ext σ ]tv S)
 -- [_]tv σ nat = nat
 -- [_]tv σ (vec n) = vec ([ σ ]vn n)
 [ σ ]tv (c · S) = c · subst (λ K → tpSpine _ K) trustMe ([ σ ]tsv S)

 -- [_]isv σ nat = nat
 -- [_]isv σ vec = vec

 [_]vv : ∀ {Γ Δ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> var Γ T -> var Δ ([ σ ]tv T)
 [_]vv (σ , y) top = subst (λ S → var _ S) trustMe y
 [_]vv (σ , y) (pop x) = subst (λ S → var _ S) trustMe ([ σ ]vv x)

 [_]vh : ∀ {Γ Δ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> head Γ T -> head Δ ([ σ ]tv T)
 [_]vh σ (v x) = v ([ σ ]vv x)

 [_]vs : ∀ {Γ Δ} {T C : tp Γ} -> (σ : vsubst Γ Δ) -> spine Γ T C -> spine Δ ([ σ ]tv T) ([ σ ]tv C)
 [_]vs σ ε = ε
 [_]vs σ (_&_ {T} {T2} {C} N S) = ([ σ ]vn N) & subst (λ S₁ → spine _ S₁ ([ σ ]tv C)) trustMe ([ σ ]vs S)

 [_]vn : ∀ {Γ Δ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> ntm Γ T -> ntm Δ ([ σ ]tv T)
 [_]vn σ (H · S) = [ σ ]vh H · [ σ ]vs S
 [_]vn σ (ƛ M) = ƛ ([ vsubst-ext σ ]vn M)

 do-wkn-ntsubst : ∀ {Γ Δ : ctx} {T : tp Δ} -> ntsubst Γ Δ -> ntsubst Γ (Δ ,, T)
 do-wkn-ntsubst {⊡} σ = unit
 do-wkn-ntsubst {Γ ,' T} (σ , N) = do-wkn-ntsubst σ , subst (λ S → ntm _ S) trustMe ([ wkn-vsubst ]vn N)

 id-ntsubst : ∀ {Γ} -> ntsubst Γ Γ
 id-ntsubst {⊡} = unit
 id-ntsubst {Γ ,' T} = do-wkn-ntsubst id-ntsubst , (subst (λ S -> ntm _ S) trustMe ((v top) · ε))

 [_]tpn : ∀ {Γ Δ} -> ntsubst Γ Δ -> tp Γ -> tp Δ
 ntsubst-ext : ∀ {Γ Δ : ctx} {T : tp Γ}  (σ : ntsubst Γ Δ) -> ntsubst (Γ ,, T) (Δ ,, ([ σ ]tpn T))
 ntsubst-ext σ = (do-wkn-ntsubst σ) , (subst (λ S → ntm _ S) trustMe (v top · ε))

 [_]kn : ∀ {Γ Δ} (σ : ntsubst Γ Δ) -> kind Γ -> kind Δ
 [_]kn σ ⋆ = ⋆
 [_]kn σ (Π T K) = Π ([ σ ]tpn T) ([ ntsubst-ext σ ]kn K)

 [_/x]kn : ∀ {Γ} {T} -> ntm Γ T -> kind (Γ ,, T) -> kind Γ
 [ N /x]kn K = [ single-tsubst N ]kn K

 [_]ts : ∀ {Γ Δ} {K : kind Γ} -> (σ : ntsubst Γ Δ) -> tpSpine Γ K -> tpSpine Δ ([ σ ]kn K)
 [_]ts σ ε = ε
 [_]ts σ (N ,κ S) = ([ σ ]nn N) ,κ ( subst (λ K → tpSpine _ K) trustMe ([ σ ]ts S))

 -- [_]ts' : ∀ {Γ Δ} {K : kind ⊡'} -> (σ : ntsubst Γ Δ) -> tpSpine Γ ([ ⊡s ]kv K) -> tpSpine Δ ([ ⊡s ]kv K)
 -- [_]ts' {Γ} {Δ} {⋆} σ ε = ε
 -- [_]ts' {Γ} {Δ} {Π T K} σ (N ,κ S) = (subst (λ T₁ → ntm Δ T₁) trustMe ([ σ ]nn N)) ,κ subst (λ K₁ → tpSpine _ K₁) trustMe {![ σ ]ts'!}

 --[_]isn : ∀ {Γ Δ} {K : kind Γ} -> (σ : ntsubst Γ Δ) -> inSig K -> inSig ([ σ ]kn K)

 [_]tpn σ (Π T T₁) = Π ([ σ ]tpn T) ([ ntsubst-ext σ ]tpn T₁)
 [ σ ]tpn (c · S) = c · subst (λ K → tpSpine _ K) trustMe ([ σ ]ts S) 

 -- [ σ ]isn nat = nat
 -- [ σ ]isn vec = vec

 [_]nv : ∀ {Γ Δ} {T : tp Γ} -> (σ : ntsubst Γ Δ) -> var Γ T -> ntm Δ ([ σ ]tpn T)
 [_]nv (σ , N) top = subst (λ S → ntm _ S) trustMe N
 [_]nv (σ , N) (pop x) = subst (λ S → ntm _ S) trustMe ([ σ ]nv x)

 _++_ : ∀ {Γ} {A B C : tp Γ} -> spine Γ A B -> spine Γ B C -> spine Γ A C
 ε ++ S2 = S2
 (N & S1) ++ S2 = N & (S1 ++ S2)

 -- TODO: Again, η-longness is crucial but we're not doing it here
 _◆_ : ∀ {Γ} {T C : tp Γ} -> ntm Γ T -> spine Γ T C -> ntm Γ C
 (H · S) ◆ S₁ = H · (S ++ S₁)
 ƛ N ◆ ε = ƛ N
 ƛ N ◆ (N₁ & S₁) = ([ N₁ /x]nn N) ◆ S₁

 [_]ns : ∀ {Γ Δ} {T C : tp Γ} -> (σ : ntsubst Γ Δ) -> spine Γ T C -> spine Δ ([ σ ]tpn T) ([ σ ]tpn C)
 [_]ns σ ε = ε
 [_]ns σ (_&_ {T} {T2} {C} N S) = [ σ ]nn N & subst (λ R → spine _ R ([ σ ]tpn C)) trustMe ([ σ ]ns S)

 [_]nn : ∀ {Γ Δ} {T : tp Γ} -> (σ : ntsubst Γ Δ) -> ntm Γ T -> ntm Δ ([ σ ]tpn T)
 [_]nn σ (v x · S) = ([ σ ]nv x) ◆ ([ σ ]ns S)
 [_]nn σ (ƛ M) = ƛ ([ ntsubst-ext σ ]nn M)

 single-tsubst : ∀ {Γ} {T} -> ntm Γ T -> ntsubst (Γ ,, T) Γ
 single-tsubst N = id-ntsubst , (subst (λ S → ntm _ S) trustMe N)

 [_/x]tpn : ∀ {Γ} {T} -> ntm Γ T -> tp (Γ ,, T) -> tp Γ
 [ N /x]tpn T = [ single-tsubst N ]tpn T

 [_/x]nn : ∀ {Γ} {T} {C} -> (N : ntm Γ T) -> ntm (Γ ,, T) C -> ntm Γ ([ N /x]tpn C)
 [ N /x]nn M = [ single-tsubst N ]nn M





 {-data vsubst (Δ : ctx) : ctx -> Set where
  ⊡ : vsubst Δ ⊡
  _,_ : ∀ {Γ T} -> (σ : vsubst Δ Γ) -> var Δ {!!} -> vsubst Δ (Γ , T) -}

 