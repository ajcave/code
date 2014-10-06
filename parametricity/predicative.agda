module predicative where
open import Data.Unit
open import Data.Product
open import Data.Nat

data Ctx (A : Set) : Set where
 ⊡ : Ctx A
 _,_ : (Γ : Ctx A) -> (T : A) -> Ctx A

data Var {A : Set} : (Γ : Ctx A) -> (T : A) -> Set where
 top : ∀ {Γ T} -> Var (Γ , T) T
 pop : ∀ {Γ T S} (x : Var Γ T) -> Var (Γ , S) T

data lvl : Set where
 ₀ ₁ : lvl

mutual
 data tp (Δ : Ctx ⊤) : lvl -> Set where
  ▹ : (X : Var Δ _) -> tp Δ ₀
  _⇒_ : ∀ {i} -> (T S : tp Δ i) -> tp Δ i
  _[_] : ∀ {i Δ'} (T : tp Δ' i) -> (η : tpenv Δ Δ') -> tp Δ i
  ∃̂ ∀̂ : (T : tp (Δ , _) ₀) -> tp Δ ₁

 data tpenv : (Δ₁ Δ₂ : Ctx ⊤) -> Set where
  ⊡ : ∀ {Δ₁} -> tpenv Δ₁ ⊡
  _,_ : ∀ {Δ₁ Δ₂} -> tpenv Δ₁ Δ₂ -> tp Δ₁ ₀ -> tpenv Δ₁ (Δ₂ , _)
  ↑ : ∀ {Δ₁} -> tpenv (Δ₁ , _) Δ₁
  id : ∀ {Δ} -> tpenv Δ Δ

data tm : Set where
 ▹ : (x : ℕ) -> tm
 ƛ : (t : tm) -> tm
 _·_ : (t s : tm) -> tm
 letpack : (t s : tm) -> tm

mutual
 data val : Set where
  ƛ_[_]' : (t : tm) -> (ρ : env) -> val
 
 data env : Set where
  ⊡ : env
  _,_ : (ρ : env) -> (v : val) -> env

data comp : Set where
 _[_] : (t : tm) (ρ : env) -> comp
 _·_ : (u v : val) -> comp

data lookup : env -> ℕ -> val -> Set where
 top : ∀ {ρ v} -> lookup (ρ , v) 0 v
 pop : ∀ {ρ n u v} -> lookup ρ n v -> lookup (ρ , u) (suc n) v

data _⇓_ : comp -> val -> Set where
 ▹ : ∀ {ρ x v} -> lookup ρ x v -> (▹ x) [ ρ ] ⇓ v
 ƛ : ∀ {t ρ} -> ((ƛ t) [ ρ ]) ⇓ (ƛ t [ ρ ]')
 _·_ : ∀ {t s u v w ρ} -> t [ ρ ] ⇓ u -> s [ ρ ] ⇓ v -> (u · v) ⇓ w -> (t · s) [ ρ ] ⇓ w
 letpack : ∀ {t s ρ u v} -> t [ ρ ] ⇓ u -> s [ ρ , u ] ⇓ v -> (letpack t s) [ ρ ] ⇓ v
 apλ : ∀ {t ρ u v} -> t [ ρ , u ] ⇓ v -> ((ƛ t [ ρ ]') · u) ⇓ v

open import Relation.Binary.PropositionalEquality hiding ([_])

lookupdeter : ∀ {ρ x v1 v2} -> lookup ρ x v1 -> lookup ρ x v2 -> v1 ≡ v2
lookupdeter top top = refl
lookupdeter (pop d1) (pop d2) = lookupdeter d1 d2

⇓deter : ∀ {c1 v1 v2} -> c1 ⇓ v1 -> c1 ⇓ v2 -> v1 ≡ v2
⇓deter (▹ x₁) (▹ x₂) = lookupdeter x₁ x₂
⇓deter ƛ ƛ = refl
⇓deter (_·_ d1 d3 d2) (_·_ d4 d5 d6) with ⇓deter d1 d4 | ⇓deter d3 d5
... | refl | refl = ⇓deter d2 d6
⇓deter (letpack d1 d2) (letpack d3 d4) with ⇓deter d1 d3
... | refl = ⇓deter d2 d4
⇓deter (apλ d1) (apλ d2) = ⇓deter d1 d2

data TCtx (Δ : Ctx ⊤) : Set where
 ⊡ : TCtx Δ
 _,_ : ∀ {i} (Γ : TCtx Δ) -> (T : tp Δ i) -> TCtx Δ

data lookupt {Δ} : (Γ : TCtx Δ) -> ℕ -> ∀ {i} -> tp Δ i -> Set where
 top : ∀ {Γ i} {T : tp Δ i} -> lookupt (Γ , T) 0 T
 pop : ∀ {Γ n} {i j} {T : tp Δ i} {S : tp Δ j} -> lookupt Γ n T -> lookupt (Γ , S) (suc n) T

↑c : ∀ {Δ} (Γ : TCtx Δ) -> TCtx (Δ , _)
↑c ⊡ = ⊡
↑c (Γ , T) = (↑c Γ) , (T [ ↑ ])

data _,_⊢_∶_ (Δ : Ctx ⊤) (Γ : TCtx Δ) : ∀ {i} -> tm -> tp Δ i -> Set where
 ▹ : ∀ {i x} {T : tp Δ i} -> lookupt Γ x T -> Δ , Γ ⊢ ▹ x ∶ T
 _·_ : ∀ {t s i} {T S : tp Δ i} -> Δ , Γ ⊢ t ∶ (T ⇒ S) -> Δ , Γ ⊢ s ∶ T -> Δ , Γ ⊢ t · s ∶ S
 ƛ : ∀ {t i} {T S : tp Δ i} -> Δ , (Γ , T) ⊢ t ∶ S -> Δ , Γ ⊢ ƛ t ∶ (T ⇒ S)
 ∀I : ∀ {T t} -> (Δ , _) , (↑c Γ) ⊢ t ∶ T -> Δ , Γ ⊢ t ∶ ∀̂ T
 ∀E : ∀ {t T} -> Δ , Γ ⊢ t ∶ ∀̂ T -> (S : tp Δ ₀) -> Δ , Γ ⊢ t ∶ (T [ id , S ])
 ∃I : ∀ {t T} -> (S : tp Δ ₀) -> Δ , Γ ⊢ t ∶ (T [ id , S ]) -> Δ , Γ ⊢ t ∶ (∃̂ T)
 ∃E : ∀ {T i} {C : tp Δ i} {t s} -> Δ , Γ ⊢ t ∶ (∃̂ T)
                 -> (Δ , _) , ((↑c Γ) , T) ⊢ s ∶ (C [ ↑ ])
                 -> Δ , Γ ⊢ letpack t s ∶ C

open import Level

record ⊤' {l} : Set l where
 constructor tt

REL : ∀ {l} -> (A : Set) -> Set (Level.suc l)
REL {l} A = A -> A -> Set l

VREL : ∀ {l} -> Set (Level.suc l)
VREL = REL val

⊤R : ∀ {l} {A : Set} -> REL {l} A
⊤R x y = ⊤'

-- data Lift (R : VREL) : VREL₁ where
--  inj : ∀ {v1 v2} -> R v1 v2 -> Lift R v1 v2

D[_] : Ctx ⊤ -> Set₁
D[ Δ ] = Var Δ _ -> VREL

_,,_ : ∀ {Δ} -> D[ Δ ] -> VREL -> D[ Δ , _ ]
_,,_ η R top = R
_,,_ η R (pop X) = η X

⊡' : D[ ⊡ ]
⊡' ()

open import Function

⟦_⟧ : lvl -> Level
⟦ ₀ ⟧ = Level.zero
⟦ ₁ ⟧ = Level.suc Level.zero

record Clo {l} (R : REL {l} val) (c1 c2 : comp) : Set l where
 constructor clo
 field
  red1 : ∃ (λ v1 -> c1 ⇓ v1)
  red2 : ∃ (λ v2 -> c2 ⇓ v2)
  rel : R (proj₁ red1) (proj₁ red2)

mutual
 V[_] : ∀ {Δ i} -> tp Δ i -> D[ Δ ] -> VREL {⟦ i ⟧}
 V[ ▹ X ] η = η X
 V[ T ⇒ T₁ ] η v1 v2 = ∀ {u1 u2} → V[ T ] η u1 u2 → Clo (V[ T₁ ] η) (v1 · u1) (v2 · u2)
 V[ T [ η ] ] η₁ = V[ T ] (VS[ η ] η₁)
 V[ ∃̂ T ] η v1 v2 = ∃ (λ R → V[ T ] (η ,, R) v1 v2)
 V[ ∀̂ T ] η v1 v2 = ∀ R -> V[ T ] (η ,, R) v1 v2

 VS[_] : ∀ {Δ Δ'} -> tpenv Δ Δ' -> D[ Δ ] -> D[ Δ' ]
 VS[ ⊡ ] η' = ⊡'
 VS[ η , T ] η' = (VS[ η ] η') ,, (V[ T ] η')
 VS[ ↑ ] η' = η' ∘ pop
 VS[ id ] η' = η'

data G_[_] {Δ} (η : D[ Δ ]) : TCtx Δ -> REL {⟦ ₁ ⟧} env where
 ⊡ : G η [ ⊡ ] ⊡ ⊡
 _,_ : ∀ {Γ ρ1 ρ2 v1 v2 i} {T : tp Δ i} -> G η [ Γ ] ρ1 ρ2 -> V[ T ] η v1 v2
   -> G η [ Γ , T ] (ρ1 , v1) (ρ2 , v2)

_,_⊨_∶_ : ∀ Δ Γ t {i} (T : tp Δ i) -> Set (Level.suc Level.zero Level.⊔ ⟦ i ⟧)
Δ , Γ ⊨ t ∶ T = ∀ (η : D[ Δ ]) {ρ1 ρ2} -> G η [ Γ ] ρ1 ρ2 -> Clo (V[ T ] η) (t [ ρ1 ]) (t [ ρ2 ])

_⇒₂_ : ∀ {l} {A : Set} -> REL {l} A -> REL {l} A -> Set l
R ⇒₂ S = ∀ {x y} -> R x y -> S x y

≡R : ∀ {l} {A : Set} (R : REL {l} A) -> ∀ {x1 x2 y1 y2} -> x1 ≡ x2 -> y1 ≡ y2 -> R x1 y1 -> R x2 y2
≡R R refl refl x = x

G↑ : ∀ {Δ} {η : D[ Δ ]} (Γ : TCtx Δ) R -> (G η [ Γ ]) ⇒₂ (G (η ,, R) [ ↑c Γ ])
G↑ ⊡ R ⊡ = ⊡
G↑ (Γ , T) R (p , x) = (G↑ Γ R p) , x

fundv : ∀ {Δ Γ x i} {T : tp Δ i} -> lookupt Γ x T -> ∀ (η : D[ Δ ]) {ρ1 ρ2} -> G η [ Γ ] ρ1 ρ2 -> ∃₂ (λ v1 v2 -> lookup ρ1 x v1 × lookup ρ2 x v2 × V[ T ] η v1 v2)
fundv top η (ρr , x) = , (, (top , (top , x)))
fundv (pop x) η (ρr , x₁) with fundv x η ρr
fundv (pop x) η (ρr , x₁) | _ , (_ , (x1 , (x2 , y))) = , (, ((pop x1) , ((pop x2) , y)))

fund : ∀ {Δ Γ t i} {T : tp Δ i} -> Δ , Γ ⊢ t ∶ T -> Δ , Γ ⊨ t ∶ T
fund (▹ x₁) η ρr with fundv x₁ η ρr
... | _ , (_ , (x1 , (x2 , y))) = clo (, ▹ x1) (, ▹ x2) y
fund (d · d₁) η ρr with fund d η ρr | fund d₁ η ρr
fund (d · d₁) η ρr | clo (v1 , red1) (v2 , red2) rel | clo (v3 , red3) (v4 , red4) rel₁ with rel rel₁
fund (d · d₁) η ρr | clo (v1 , red1) (v2 , red2) rel | clo (v3 , red3) (v4 , red4) rel₁ | clo (u1 , red5) (u2 , red6) rel₂ = clo (u1 , (red1 · red3) red5) (u2 , (red2 · red4) red6) rel₂
fund (ƛ d) η ρr = clo (, ƛ) (, ƛ) (λ x →
  let q = fund d η (ρr , x) in
  clo (, apλ (proj₂ (Clo.red1 q))) (, apλ (proj₂ (Clo.red2 q))) (Clo.rel q))
fund (∀I d) η ρr with fund d (η ,, ⊤R) (G↑ _ ⊤R ρr)
fund (∀I {T} d) η ρr | clo (v1 , red1) (v2 , red2) rel = clo (v1 , red1) (v2 , red2) (λ R →
  let q = fund d (η ,, R) (G↑ _ R ρr) in
  ≡R (V[ T ] (η ,, R)) (⇓deter (proj₂ (Clo.red1 q)) red1) (⇓deter (proj₂ (Clo.red2 q)) red2) (Clo.rel q))
fund (∀E d S) η ρr with fund d η ρr
fund (∀E d S) η ρr | clo red1 red2 rel = clo red1 red2 (rel (V[ S ] η))
fund (∃I S d) η ρr with fund d η ρr
fund (∃I S d) η ρr | clo red1 red2 rel = clo red1 red2 (V[ S ] η , rel)
fund (∃E {T} {._} {C} d d₁) η ρr with fund d η ρr
fund (∃E {T} {._} {C} d d₁) η ρr | clo red1 red2 (R , rel) with fund d₁ (η ,, R) ((G↑ _ R ρr) , rel)
fund (∃E {T} {._} {C} d d₁) η ρr | clo (v1 , red1) (v2 , red2) (R , rel) | clo (u1 , red3) (u2 , red4) rel₁ = clo (, letpack red1 red3) (, letpack red2 red4) rel₁

-- TODO!!! Need type equivalence!!