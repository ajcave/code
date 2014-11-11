module bigstep-cbv-mu where
open import Data.Nat
open import Data.Fin

record Unit : Set where
 constructor tt

mutual
 data tp' (Δ : ℕ) : Set where
  unit : tp' Δ
  _⇝_ : (T : tp' zero) -> (S : tp' Δ) -> tp' Δ
  var : Fin Δ -> tp' Δ
  μ : tp' (suc Δ) -> tp' Δ
  _⊕_ _⊗_ : tp' Δ -> tp' Δ -> tp' Δ
  _[_] : ∀ {Δ'} -> tp' Δ' -> tpenv Δ Δ' -> tp' Δ

 data tpenv : (Δ₁ Δ₂ : ℕ) -> Set where
  ⊡ : ∀ {Δ₁} -> tpenv Δ₁ zero
  _,_ : ∀ {Δ₁ Δ₂} -> tpenv Δ₁ Δ₂ -> tp' Δ₁ -> tpenv Δ₁ (suc Δ₂)
  _[_] : ∀ {Δ1 Δ2 Δ3} -> tpenv Δ2 Δ3 -> tpenv Δ1 Δ2 -> tpenv Δ1 Δ3
  ↑ : ∀ {Δ₁} -> tpenv (suc Δ₁) Δ₁
  id : ∀ {Δ} -> tpenv Δ Δ

tp = tp' zero

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data tm : Set where
 var : ℕ -> tm -- de Bruijn index
 _·_ : tm -> tm -> tm -- application
 ƛ : tm -> tm -- lambda
 inj : tm -> tm
 inl inr : tm -> tm
 pair : tm -> tm -> tm

data _∶_∈_ : (x : ℕ) -> (T : tp) -> (Γ : ctx) -> Set where
 z : ∀ {Γ T} -> zero ∶ T ∈ (Γ , T)
 s : ∀ {Γ x T S} -> x ∶ T ∈ Γ -> (suc x) ∶ T ∈ (Γ , S)

data _⊢_∶_ (Γ : ctx) : (M : tm) -> (T : tp) -> Set where
 var : ∀ {T x} -> x ∶ T ∈ Γ -> Γ ⊢ (var x) ∶ T
 _·_ : ∀ {T S M N} -> Γ ⊢ M ∶ (T ⇝ S) -> Γ ⊢ N ∶ T -> Γ ⊢ (M · N) ∶ S
 ƛ : ∀ {T S M} -> (Γ , T) ⊢ M ∶  S -> Γ ⊢ (ƛ M) ∶ (T ⇝ S)
 inj : ∀ {F M} -> Γ ⊢ M ∶ (F [ id , μ F ]) -> Γ ⊢ (inj M) ∶ μ F

mutual
 data val : Set where
  ƛ_[_]' : tm -> env -> val
  inl inr inj : val -> val
  pair : val -> val -> val

 data env :  Set where
  ⊡ : env
  _,_ : env -> val -> env

data comp : Set where 
 _[_] : tm -> env -> comp
 _·_ : val -> val -> comp -- This is not exactly what we did on the board

data lookup : env -> ℕ -> val -> Set where
 top : ∀ {σ v} -> lookup (σ , v) zero v
 pop : ∀ {σ x v u} -> lookup σ x v -> lookup (σ , u) (suc x) v

data _⇓_ : comp -> val -> Set where
 app : ∀ {M N M' σ u σ' v}
       -> M [ σ ] ⇓ (ƛ M' [ σ' ]')
       -> N [ σ ] ⇓ u
       -> M' [ σ' , u ] ⇓ v
       -> (M · N) [ σ ] ⇓ v
 var : ∀ {x σ v} -> lookup σ x v -> (var x) [ σ ] ⇓ v
 ƛ : ∀ {M σ} -> (ƛ M) [ σ ] ⇓ (ƛ M [ σ ]')
 apƛ : ∀ {M σ v u} -> M [ σ , v ] ⇓ u -> ((ƛ M [ σ ]') · v) ⇓ u -- This is not exactly what we did on the board

-- Just some notation
_∈_ : ∀ {A : Set} -> A -> (P : A -> Set) -> Set
x ∈ P = P x

record Clo (R : val -> Set) (c : comp) : Set where
 constructor inj
 field
  v : val
  ev : c ⇓ v
  red : v ∈ R

open import Data.Sum
open import Data.Product
open import Data.Empty

data Sum (P Q : val -> Set) : val -> Set where
 inl : ∀ {v} -> P v -> Sum P Q (inl v)
 inr : ∀ {v} -> Q v -> Sum P Q (inr v)

data Pair (P Q : val -> Set) : val -> Set where
 pair : ∀ {u v} -> P u -> Q v -> Pair P Q (pair u v)

data VarU {n} (x : Fin n) (u : val) : Fin n -> val -> Set where
 con : VarU x u x u

data FunU (P : val -> Set) (Ut : val -> val -> Set) (t : val) (u : val) : Set where
 con : ∀ {t' v} -> P t' -> (t · t') ⇓ v -> Ut v u -> FunU P Ut t u

data μ̂ (Vf : val -> Set) (Uf : val -> val -> Set) : val -> Set where
 inj : ∀ {v} -> Vf v -> (∀ u -> Uf v u -> μ̂ Vf Uf u) -> μ̂ Vf Uf (inj v)

data SumU (P Q : val -> val -> Set) : val -> val -> Set where
 inl : ∀ {u t} -> P t u -> SumU P Q (inl t) u
 inr : ∀ {u t} -> Q t u -> SumU P Q (inr t) u

-- This is different from the definition in the paper, but currently I suspect it's
-- a mistake in the paper...
data PairU (P Q : val -> val -> Set) : val -> val -> Set where 
 pair1 : ∀ {u t1 t2} -> P t1 u -> PairU P Q (pair t1 t2) u
 pair2 : ∀ {u t1 t2} -> Q t2 u -> PairU P Q (pair t1 t2) u

data μU (Un : val -> val -> Set) (Ur : val -> val -> Set) : val -> val -> Set where
 nonrec : ∀ {u t} -> Un t u -> μU Un Ur (inj t) u
 rec : ∀ {u t t'} -> μU Un Ur t' u -> Ur t t' -> μU Un Ur (inj t) u

mutual
 V[_] : ∀ {Δ} (T : tp' Δ) -> val -> Set
 V[_] unit v = Unit
 V[_] (T ⇝ S) v =  ∀ {u} -> u ∈ V[ T ] -> (v · u) ∈ Clo V[ S ]
 V[_] (var x) v = Unit
 V[_] (μ T) v = μ̂ V[ T ] (U[ T ] zero) v
 V[_] (T ⊕ T₁) v = Sum V[ T ] V[ T₁ ] v
 V[_] (T ⊗ T₁) v = Pair V[ T ] V[ T₁ ] v
 V[_] (T [ σ ]) v = V[ T ]' (λ i → {!!}) v

 -- Vs[_] : ∀ {Δ Δ'} (σ : tpenv Δ Δ') -> Fin Δ' -> env -> Set
 -- Vs[_] ⊡ () ρ
 -- Vs[_] (σ , x) zero (ρ , v) = V[ x ] v
 -- Vs[_] (σ , x) (suc i) (ρ , v) = Vs[ σ ] i ρ
 -- Vs[_] (σ [ σ₁ ]) i ρ = {!!}
 -- Vs[_] ↑ i (ρ , = {!!}
 -- Vs[_] id i ρ = {!!}
 -- Vs[_] _ _ _ = ⊥

 -- Could write this as a tuple instead of as a function on i...?
 U[_] : ∀ {Δ} (T : tp' Δ) (i : Fin Δ) (t : val) -> val -> Set
 U[_] unit i t u = ⊥
 U[_] (T ⇝ T₁) i t u = FunU V[ T ] (U[ T₁ ] i) t u
 U[_] (var x) i t u = VarU x t i u
 U[_] (μ T) i t u = μU (U[ T ] (suc i)) (U[ T ] zero) t u
 U[_] (T ⊕ T₁) i t u = SumU (U[ T ] i) (U[ T₁ ] i) t u
 U[_] (T ⊗ T₁) i t u = PairU (U[ T ] i) (U[ T₁ ] i) t u
 U[_] (T [ x ]) i t u = {!!}

 V[_]' : ∀ {Δ} (T : tp' Δ) -> (Fin Δ -> (val -> Set)) -> val -> Set
 V[ T ]' ρ v = (V[ T ] v) × (∀ i u → U[ T ] i v u → ρ i u)


-- E[_] : ∀ T -> comp -> Set
-- E[ T ] = Clo V[ T ]

-- data G[_] : ctx -> env -> Set where
--  ⊡ : ⊡ ∈ G[ ⊡ ]
--  _,_ : ∀ {Γ T σ v} -> σ ∈ G[ Γ ] -> v ∈ V[ T ] -> (σ , v) ∈ G[ Γ , T ]

-- thmv : ∀ {Γ x T} -> x ∶ T ∈ Γ -> ∀ {σ} -> σ ∈ G[ Γ ] -> (var x) [ σ ] ∈ E[ T ]
-- thmv z (gΓ , x) = inj _ (var top) x
-- thmv (s d) (gΓ , x₁) with thmv d gΓ
-- thmv (s d) (gΓ , x₁) | inj v (var d') red = inj _ (var (pop d')) red

-- thm : ∀ {Γ t T} -> Γ ⊢ t ∶ T -> ∀ {σ} -> σ ∈ G[ Γ ] -> t [ σ ] ∈ E[ T ]
-- thm (var x₁) gΓ = thmv x₁ gΓ
-- thm (d · d₁) gΓ with thm d gΓ | thm d₁ gΓ
-- thm (d · d₁) gΓ | inj v ev red | inj v₁ ev₁ red₁ with red red₁
-- thm (d · d₁) gΓ | inj .(ƛ M [ σ ]') ev₁ red | inj v₁ ev₂ red₁ | inj v₂ (apƛ {M} {σ} ev) red₂ = inj v₂ (app ev₁ ev₂ ev) red₂
-- thm (ƛ {T} {S} {M}  d) {σ} gΓ = inj _ ƛ helper
--  where helper : ∀ {u} -> u ∈ V[ T ] -> (ƛ M [ σ ]' · u) ∈ E[ S ]
--        helper x with thm d (gΓ , x)
--        helper x | inj v ev red = inj v (apƛ ev) red

-- record normalizes (t : tm) : Set where
--  field
--   v : val
--   ev : t [ ⊡ ] ⇓ v

-- norm : ∀ {t T} -> ⊡ ⊢ t ∶ T -> normalizes t
-- norm d with thm d ⊡
-- norm d | inj v ev red = record { v = v; ev = ev }
