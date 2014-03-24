{-# OPTIONS --no-positivity-check --no-termination-check #-}
-- By Induction-induction-recursion
module iir where
open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe

-- What if we didn't use TrustMe and actually proved all of our equations
-- Would Agda actually accept the definition (positivity check and termination check)?
mutual
 data ctx : Set where
  ⊡ : ctx
  _,'_ : (Γ : ctx) -> (T : tp Γ) -> ctx
 
 data tp (Γ : ctx) : Set where
  Π : (T : tp Γ) (S : tp (Γ ,' T)) -> tp Γ
  nat : tp Γ
  vec : (n : ntm Γ nat) -> tp Γ

 _,,_ : (Γ : ctx) -> (T : tp Γ) -> ctx
 Γ ,, T = Γ ,' T
 
 vsubst : (Γ Δ : ctx) -> Set
 ntsubst : (Γ Δ : ctx) -> Set
 id-vsubst : ∀ {Γ} -> vsubst Γ Γ
 do-wkn-vsubst : ∀ {Γ Δ : ctx} {T : tp Δ} -> vsubst Γ Δ -> vsubst Γ (Δ ,, T)
 
 ntsubst ⊡ Δ = Unit
 ntsubst (Γ ,' T) Δ = Σ (ntsubst Γ Δ) (λ σ -> (ntm Δ ([ σ ]tpn T)))

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

 [_]tv σ (Π T S) = Π ([ σ ]tv T) ([ vsubst-ext σ ]tv S)
 [_]tv σ nat = nat
 [_]tv σ (vec n) = vec ([ σ ]vn n)

 [_]vv : ∀ {Γ Δ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> var Γ T -> var Δ ([ σ ]tv T)
 [_]vv (σ , y) top = subst (λ S → var _ S) trustMe y
 [_]vv (σ , y) (pop x) = subst (λ S → var _ S) trustMe ([ σ ]vv x)

 [_]vh : ∀ {Γ Δ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> head Γ T -> head Δ ([ σ ]tv T)
 [_]vh σ (v x) = v ([ σ ]vv x)

 [_]vs : ∀ {Γ Δ} {T C : tp Γ} -> (σ : vsubst Γ Δ) -> spine Γ T C -> spine Δ ([ σ ]tv T) ([ σ ]tv C)
 [_]vs σ ε = ε
 [_]vs σ (N & S) = ([ σ ]vn N) & {!!}

 [_]vn : ∀ {Γ Δ} {T : tp Γ} -> (σ : vsubst Γ Δ) -> ntm Γ T -> ntm Δ ([ σ ]tv T)
 [_]vn σ (H · S) = [ σ ]vh H · {!!}
 [_]vn σ (ƛ M) = ƛ ([ vsubst-ext σ ]vn M)

 do-wkn-ntsubst : ∀ {Γ Δ : ctx} {T : tp Δ} -> ntsubst Γ Δ -> ntsubst Γ (Δ ,, T)
 do-wkn-ntsubst {⊡} σ = {!!}
 do-wkn-ntsubst {Γ ,' T} σ = {!!}

 id-ntsubst : ∀ {Γ} -> ntsubst Γ Γ
 id-ntsubst {⊡} = unit
 id-ntsubst {Γ ,' T} = do-wkn-ntsubst id-ntsubst , (subst (λ S -> ntm _ S) trustMe ((v top) · ε))

 [_]tpn : ∀ {Γ Δ} -> ntsubst Γ Δ -> tp Γ -> tp Δ
 [ σ ]tpn T = {!T!}

 [_]nn : ∀ {Γ Δ} {T : tp Γ} -> (σ : ntsubst Γ Δ) -> ntm Γ T -> ntm Δ ([ σ ]tpn T)
 [ σ ]nn T = {!!}

 single-tsubst : ∀ {Γ} {T} -> ntm Γ T -> ntsubst (Γ ,, T) Γ
 single-tsubst N = id-ntsubst , (subst (λ S → ntm _ S) trustMe N)

 [_/x]tpn : ∀ {Γ} {T} -> ntm Γ T -> tp (Γ ,, T) -> tp Γ
 [ N /x]tpn T = [ single-tsubst N ]tpn T




 {-data vsubst (Δ : ctx) : ctx -> Set where
  ⊡ : vsubst Δ ⊡
  _,_ : ∀ {Γ T} -> (σ : vsubst Δ Γ) -> var Δ {!!} -> vsubst Δ (Γ , T) -}

 