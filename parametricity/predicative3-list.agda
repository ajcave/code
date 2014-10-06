module predicative3-list where
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
  ▹ : ∀ {i} (X : Var Δ _) -> tp Δ i
  _⇒_ : ∀ {i} -> (T S : tp Δ i) -> tp Δ i
  _[_] : ∀ {i Δ'} (T : tp Δ' i) -> (η : tpenv Δ Δ') -> tp Δ i
  Lst : ∀ {i} (T : tp Δ i) -> tp Δ i
  ∃̂ ∀̂ : (T : tp (Δ , _) ₁) -> tp Δ ₁ 

 data tpenv : (Δ₁ Δ₂ : Ctx ⊤) -> Set where
  ⊡ : ∀ {Δ₁} -> tpenv Δ₁ ⊡
  _,_ : ∀ {Δ₁ Δ₂} -> tpenv Δ₁ Δ₂ -> tp Δ₁ ₀ -> tpenv Δ₁ (Δ₂ , _)
  _[_] : ∀ {Δ1 Δ2 Δ3} -> tpenv Δ2 Δ3 -> tpenv Δ1 Δ2 -> tpenv Δ1 Δ3
  ↑ : ∀ {Δ₁} -> tpenv (Δ₁ , _) Δ₁
  id : ∀ {Δ} -> tpenv Δ Δ

data lookupT : ∀ {Δ1 Δ2} -> tpenv Δ1 Δ2 -> Var Δ2 _ -> tp Δ1 ₀ -> Set where
 top : ∀ {Δ1 Δ2} {ρ : tpenv Δ1 Δ2} {v} -> lookupT (ρ , v) top v
 pop : ∀ {Δ1 Δ2} {ρ : tpenv Δ1 Δ2} {n u v} -> lookupT ρ n v -> lookupT (ρ , u) (pop n) v

data _⇢_ {Δ : Ctx ⊤} : ∀ {i} -> tp Δ i -> tp Δ i -> Set where
 ▹[] : ∀ {Δ'} {η : tpenv Δ Δ'} {X T} -> lookupT η X T -> (▹ X) [ η ] ⇢ T
 ⇒[] : ∀ {Δ'} {η : tpenv Δ Δ'} {i} (T S : tp Δ' i) -> (T ⇒ S) [ η ] ⇢ (T [ η ] ⇒ S [ η ])
 ∀[] : ∀ {Δ'} {η : tpenv Δ Δ'} (T : tp (Δ' , _) ₁) -> (∀̂ T) [ η ] ⇢ ∀̂ (T [ η [ ↑ ] , (▹ top) ])
 ∃[] : ∀ {Δ'} {η : tpenv Δ Δ'} (T : tp (Δ' , _) ₁) -> (∃̂ T) [ η ] ⇢ ∃̂ (T [ η [ ↑ ] , (▹ top) ])
 [][] : ∀ {Δ'} {η : tpenv Δ Δ'} {i Δ''} (T : tp Δ'' i) (η' : tpenv Δ' Δ'') -> (T [ η' ]) [ η ] ⇢ T [ η' [ η ] ]
  
 -- Hmm I think I only need a "reduction" which pushes under one constructor
 -- Would need to handle T[η][η'] carefully.. a couple choices...
 -- (It's the only "computation")
 -- Would also need reduction in either direction...
 -- Prove that type system sound and complete for the "usual" one?

data tm : Set where
 ▹ : (x : ℕ) -> tm
 ƛ : (t : tm) -> tm
 _·_ : (t s : tm) -> tm
 letpack : (t s : tm) -> tm
 [] : tm
 _∷_ : (t ts : tm) -> tm
 fold' : (tnil tsuc tl : tm) -> tm

mutual
 data val : Set where
  ƛ_[_]' : (t : tm) -> (ρ : env) -> val
  [] : val
  _∷_ : (v vs : val) -> val
 
 data env : Set where
  ⊡ : env
  _,_ : (ρ : env) -> (v : val) -> env

data comp : Set where
 _[_] : (t : tm) (ρ : env) -> comp
 _·_ : (u v : val) -> comp
 fold' : (tnil ts : tm) (ρ : env) (v : val) -> comp

data lookup : env -> ℕ -> val -> Set where
 top : ∀ {ρ v} -> lookup (ρ , v) 0 v
 pop : ∀ {ρ n u v} -> lookup ρ n v -> lookup (ρ , u) (suc n) v

data _⇓_ : comp -> val -> Set where
 ▹ : ∀ {ρ x v} -> lookup ρ x v -> (▹ x) [ ρ ] ⇓ v
 ƛ : ∀ {t ρ} -> ((ƛ t) [ ρ ]) ⇓ (ƛ t [ ρ ]')
 [] : ∀ {ρ} -> [] [ ρ ] ⇓ []
 _∷_ : ∀ {t ts v vs ρ} -> t [ ρ ] ⇓ v -> ts [ ρ ] ⇓ vs -> (t ∷ ts) [ ρ ] ⇓ (v ∷ vs)
 _·_ : ∀ {t s u v w ρ} -> t [ ρ ] ⇓ u -> s [ ρ ] ⇓ v -> (u · v) ⇓ w -> (t · s) [ ρ ] ⇓ w
 letpack : ∀ {t s ρ u v} -> t [ ρ ] ⇓ u -> s [ ρ , u ] ⇓ v -> (letpack t s) [ ρ ] ⇓ v
 apλ : ∀ {t ρ u v} -> t [ ρ , u ] ⇓ v -> ((ƛ t [ ρ ]') · u) ⇓ v
 fold[] : ∀ {tnil tcons v ρ} -> tnil [ ρ ] ⇓ v -> fold' tnil tcons ρ [] ⇓ v
 fold∷ : ∀ {tnil tcons v vs u w ρ} -> fold' tnil tcons ρ vs ⇓ u -> tcons [ (ρ , v) , u ] ⇓ w
         -> fold' tnil tcons ρ (v ∷ vs) ⇓ w
 fold' : ∀ {tnil tcons ts u v ρ} -> ts [ ρ ] ⇓ u -> fold' tnil tcons ρ u ⇓ v -> fold' tnil tcons ts [ ρ ] ⇓ v

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
⇓deter [] [] = refl
⇓deter (d ∷ ds) (d1 ∷ ds1) = cong₂ _∷_ (⇓deter d d1) (⇓deter ds ds1)
⇓deter (fold' d1 d2) (fold' d1' d2') with ⇓deter d1 d1'
⇓deter (fold' d1 d2) (fold' d1' d2') | refl = ⇓deter d2 d2'
⇓deter (fold[] d) (fold[] d') = ⇓deter d d'
⇓deter (fold∷ d1 d2) (fold∷ d1' d2') with ⇓deter d1 d1'
... | refl = ⇓deter d2 d2'

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
 ∃E : ∀ {i} {C : tp Δ i} {T} {t s} -> Δ , Γ ⊢ t ∶ (∃̂ T)
                 -> (Δ , _) , ((↑c Γ) , T) ⊢ s ∶ (C [ ↑ ])
                 -> Δ , Γ ⊢ letpack t s ∶ C
 [] : ∀ {i} {T : tp Δ i} -> Δ , Γ ⊢ [] ∶ Lst T
 _∷_ : ∀ {i} {T : tp Δ i} {t ts} -> Δ , Γ ⊢ t ∶ T -> Δ , Γ ⊢ ts ∶ Lst T -> Δ , Γ ⊢ (t ∷ ts) ∶ Lst T
 fold' : ∀ {i j} {T : tp Δ i} {C : tp Δ j} {tnil tcons ts}
        -> Δ , Γ ⊢ tnil ∶ C -> Δ , ((Γ , T) , C) ⊢ tcons ∶ C -> Δ , Γ ⊢ ts ∶ Lst T
        -> Δ , Γ ⊢ fold' tnil tcons ts ∶ C
 convfwd : ∀ {i} {T T' : tp Δ i} {t} -> Δ , Γ ⊢ t ∶ T -> T ⇢ T' -> Δ , Γ ⊢ t ∶ T'
 convbwd : ∀ {i} {T T' : tp Δ i} {t} -> Δ , Γ ⊢ t ∶ T -> T' ⇢ T -> Δ , Γ ⊢ t ∶ T'


open import Level

record ⊤' {l} : Set l where
 constructor tt

REL : ∀ {l} -> (A : Set) -> Set (Level.suc l)
REL {l} A = A -> A -> Set l

⊤R : ∀ {l} {A : Set} -> REL {l} A
⊤R x y = ⊤'

data D[_] : Ctx ⊤ -> Set₁ where
 ⊡ : D[ ⊡ ]
 _,_ : ∀ {Δ} -> D[ Δ ] -> REL {Level.zero} val -> D[ Δ , _ ]

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

lookupE : ∀ {Δ} -> D[ Δ ] -> Var Δ _ -> REL {Level.zero} val
lookupE ⊡ ()
lookupE (η , R) top = R
lookupE (η , R) (pop X) = lookupE η X

data All {l} (R : REL {l} val) : REL {l} val where
 [] : All R [] []
 _∷_ : ∀ {u v us vs} -> R u v -> All R us vs -> All R (u ∷ us) (v ∷ vs)

mutual
 V[_] : ∀ {Δ i} -> tp Δ i -> D[ Δ ] -> REL {⟦ i ⟧} val
 V[ ▹ {₀} X ] η = lookupE η X
 V[ ▹ {₁} X ] η v1 v2 = Lift (lookupE η X v1 v2)
 V[ T ⇒ T₁ ] η v1 v2 = ∀ {u1 u2} → V[ T ] η u1 u2 → Clo (V[ T₁ ] η) (v1 · u1) (v2 · u2)
 V[ T [ η ] ] η₁ = V[ T ] (VS[ η ] η₁)
 V[ ∃̂ T ] η v1 v2 = ∃ (λ R → V[ T ] (η , R) v1 v2)
 V[ ∀̂ T ] η v1 v2 = ∀ R -> V[ T ] (η , R) v1 v2
 V[ Lst T ] η v1 v2 = All (V[ T ] η) v1 v2

 VS[_] : ∀ {Δ Δ'} -> tpenv Δ Δ' -> D[ Δ ] -> D[ Δ' ]
 VS[ ⊡ ] η' = ⊡
 VS[ η , T ] η' = (VS[ η ] η') , (V[ T ] η')
 VS[ ↑ ] (η' , R) = η'
 VS[ id ] η' = η'
 VS[ η [ η' ] ] η'' = VS[ η ] (VS[ η' ] η'')

data G_[_] {Δ} (η : D[ Δ ]) : TCtx Δ -> REL {⟦ ₁ ⟧} env where
 ⊡ : G η [ ⊡ ] ⊡ ⊡
 _,_ : ∀ {Γ ρ1 ρ2 v1 v2 i} {T : tp Δ i} -> G η [ Γ ] ρ1 ρ2 -> V[ T ] η v1 v2
   -> G η [ Γ , T ] (ρ1 , v1) (ρ2 , v2)

_,_⊨_∶_ : ∀ Δ Γ t {i} (T : tp Δ i) -> Set (Level.suc Level.zero Level.⊔ ⟦ i ⟧)
Δ , Γ ⊨ t ∶ T = ∀ (η : D[ Δ ]) {ρ1 ρ2} -> G η [ Γ ] ρ1 ρ2 -> Clo (V[ T ] η) (t [ ρ1 ]) (t [ ρ2 ])

_⇒₂_ : ∀ {l} {A : Set} -> REL {l} A -> REL {l} A -> Set l
R ⇒₂ S = ∀ {x y} -> R x y -> S x y

Clo≡ : ∀ {l} {R S : REL {l} val} -> R ≡ S -> Clo R ⇒₂ Clo S
Clo≡ refl (clo red1 red2 rel) = clo red1 red2 rel

≡R : ∀ {l} {A : Set} (R : REL {l} A) -> ∀ {x1 x2 y1 y2} -> x1 ≡ x2 -> y1 ≡ y2 -> R x1 y1 -> R x2 y2
≡R R refl refl x = x

G↑ : ∀ {Δ} {η : D[ Δ ]} (Γ : TCtx Δ) R -> (G η [ Γ ]) ⇒₂ (G (η , R) [ ↑c Γ ])
G↑ ⊡ R ⊡ = ⊡
G↑ (Γ , T) R (p , x) = (G↑ Γ R p) , x

feqv : ∀ {Δ : Ctx ⊤} {T' : tp Δ ₀} {Δ' : Ctx ⊤} {η : tpenv Δ Δ'} {X : Var Δ' tt} ->
        lookupT η X T' -> {η₁ : D[ Δ ]} -> lookupE (VS[ η ] η₁) X ≡ V[ T' ] η₁
feqv top = refl
feqv (pop x) = feqv x

feq : ∀ {Δ i} {T T' : tp Δ i} -> T ⇢ T' -> {η : D[ Δ ]} -> V[ T ] η ≡ V[ T' ] η 
feq (▹[] x) = feqv x
feq (⇒[] T S) = refl
feq (∀[] T) = refl
feq (∃[] T) = refl
feq ([][] T η') = refl

fundv : ∀ {Δ Γ x i} {T : tp Δ i} -> lookupt Γ x T -> ∀ (η : D[ Δ ]) {ρ1 ρ2} -> G η [ Γ ] ρ1 ρ2 -> ∃₂ (λ v1 v2 -> lookup ρ1 x v1 × lookup ρ2 x v2 × V[ T ] η v1 v2)
fundv top η (ρr , x) = , (, (top , (top , x)))
fundv (pop x) η (ρr , x₁) with fundv x η ρr
fundv (pop x) η (ρr , x₁) | _ , (_ , (x1 , (x2 , y))) = , (, ((pop x1) , ((pop x2) , y)))

-- TODO: Pretty sure this can be cleaned up
foldH : ∀ {Δ} {i} (T : tp Δ i) {η : D[ Δ ]}
           {ρ1 ρ2 u} {v} {i₁} (T₁ : tp Δ i₁) {tnil tcons} →
         Clo (V[ T₁ ] η) (tnil [ ρ1 ]) (tnil [ ρ2 ]) →
         (∀ {w1 w2 wn wm} -> V[ T ] η w1 w2 -> V[ T₁ ] η wn wm ->
          Clo (V[ T₁ ] η) (tcons [ (ρ1 , w1) , wn ]) (tcons [ (ρ2 , w2) , wm ])) →
         All (V[ T ] η) u v →
         Clo (V[ T₁ ] η) (fold' tnil tcons ρ1 u)
         (fold' tnil tcons ρ2 v)
foldH T T₁ (clo (_ , r1) (_ , r2) n1) d2 [] = clo (, fold[] r1) (, fold[] r2) n1
foldH T T₁ d1 d2 (x ∷ r₁) with foldH T T₁ d1 d2 r₁
foldH T T₁ d1 d2 (x ∷ r₁) | clo (_ , r1) (_ , r2) rel with d2 x rel
foldH T T₁ d1 d2 (x ∷ r₁) | clo (proj₁ , r1) (proj₂ , r2) rel | clo (_ , r3) (_ , r4) rel₁ = clo (, fold∷ r1 r3) (, fold∷ r2 r4) rel₁

fund : ∀ {Δ Γ t i} {T : tp Δ i} -> Δ , Γ ⊢ t ∶ T -> Δ , Γ ⊨ t ∶ T
fund (▹ x₁) η ρr with fundv x₁ η ρr
... | _ , (_ , (x1 , (x2 , y))) = clo (, ▹ x1) (, ▹ x2) y
fund (d · d₁) η ρr with fund d η ρr | fund d₁ η ρr
fund (d · d₁) η ρr | clo (v1 , red1) (v2 , red2) rel | clo (v3 , red3) (v4 , red4) rel₁ with rel rel₁
fund (d · d₁) η ρr | clo (v1 , red1) (v2 , red2) rel | clo (v3 , red3) (v4 , red4) rel₁ | clo (u1 , red5) (u2 , red6) rel₂ = clo (u1 , (red1 · red3) red5) (u2 , (red2 · red4) red6) rel₂
fund (ƛ d) η ρr = clo (, ƛ) (, ƛ) (λ x →
  let q = fund d η (ρr , x) in
  clo (, apλ (proj₂ (Clo.red1 q))) (, apλ (proj₂ (Clo.red2 q))) (Clo.rel q))
fund (∀I d) η ρr with fund d (η , ⊤R) (G↑ _ ⊤R ρr)
fund (∀I {T} d) η ρr | clo (v1 , red1) (v2 , red2) rel = clo (v1 , red1) (v2 , red2) (λ R →
  let q = fund d (η , R) (G↑ _ R ρr) in
  ≡R (V[ T ] (η , R)) (⇓deter (proj₂ (Clo.red1 q)) red1) (⇓deter (proj₂ (Clo.red2 q)) red2) (Clo.rel q))
fund (∀E d S) η ρr with fund d η ρr
fund (∀E d S) η ρr | clo red1 red2 rel = clo red1 red2 (rel (V[ S ] η))
fund (∃I S d) η ρr with fund d η ρr
fund (∃I S d) η ρr | clo red1 red2 rel = clo red1 red2 (V[ S ] η , rel)
fund (∃E {._} {C} d d₁) η ρr with fund d η ρr
fund (∃E {._} {C} d d₁) η ρr | clo red1 red2 (R , rel) with fund d₁ (η , R) ((G↑ _ R ρr) , rel)
fund (∃E {._} {C} d d₁) η ρr | clo (v1 , red1) (v2 , red2) (R , rel) | clo (u1 , red3) (u2 , red4) rel₁ = clo (, letpack red1 red3) (, letpack red2 red4) rel₁
fund (convfwd d eq) η ρr = Clo≡ (feq eq) (fund d η ρr)
fund (convbwd d eq) η ρr = Clo≡ (sym (feq eq)) (fund d η ρr)
fund [] η ρr = clo ([] , []) ([] , []) []
fund (d ∷ ds) η ρr with fund d η ρr | fund ds η ρr
fund (d ∷ ds) η ρr | clo (u , red1) (v , red2) rel | clo (us , red3) (vs , red4) rel₁ =
  clo (_ , (red1 ∷ red3)) (, red2 ∷ red4) (rel ∷ rel₁)
fund (fold' {_} {_} {T} {C} dnil dcons ds) η ρr with fund ds η ρr
... | clo (u , r1) (v , r2) r with foldH T C (fund dnil η ρr) (λ x x₁ → fund dcons η ((ρr , x) , x₁)) r
fund (fold' dnil dcons ds) η ρr | clo (u , r1) (v , r2) r | clo (w , r3) (z , r4) rel = clo (, fold' r1 r3) (, fold' r2 r4) rel

_≈_ : tm -> tm -> Set
t ≈ s = ∃ (λ v -> t [ ⊡ ] ⇓ v × s [ ⊡ ] ⇓ v)

idFree : ∀ {t s} {T : tp ⊡ ₀} -> ⊡ , ⊡ ⊢ t ∶ ∀̂ (▹ top ⇒ ▹ top) -> ⊡ , ⊡ ⊢ s ∶ T -> (t · s) ≈ s
idFree d1 d2 with fund d1 ⊡ ⊡ | fund d2 ⊡ ⊡
idFree d1 d2 | clo red1 red2 rel | clo (u , red3) red4 rel₁ with rel (λ v1 v2 -> v1 ≡ u) {u} {u} (lift refl)
idFree d1 d2 | clo red1 red2 rel | clo (u , red5) red6 rel₂ | clo red3 red4 (lift q) = u , ((((proj₂ red1) · red5) (subst (_⇓_ (proj₁ red1 · u)) q (proj₂ red3))) , red5)

open import Data.Empty

emp : ∀ {t} -> ⊡ , ⊡ ⊢ t ∶ ∀̂ (▹ top) -> ⊥
emp d with fund d ⊡ ⊡
emp d | clo (v , red1) (u , red2) rel = Lift.lower (rel (λ _ _ → ⊥))

-- TODO: Can we implement theorems for free "generically"?

map' : tm
map' = ƛ (ƛ (fold' [] (((▹ 3) · (▹ 1)) ∷ (▹ 0)) (▹ 0)))

mapc : val -> val -> val -> comp
mapc fv ws us = fold' [] (((▹ 3) · (▹ 1)) ∷ (▹ 0)) ((⊡ , fv) , ws) us

maptp' : ∀ {Δ} {i} (S T : tp Δ i) -> Δ , ⊡ ⊢ map' ∶ ((S ⇒ T) ⇒ (Lst S ⇒ Lst T))
maptp' S T = ƛ (ƛ (fold' [] (((▹ (pop (pop (pop top)))) · ▹ (pop top)) ∷ ▹ top) (▹ top)))

maptp :  ⊡ , ⊡ ⊢ map' ∶ ∀̂ (∀̂ ((▹ (pop top) ⇒ ▹ top) ⇒ (Lst (▹ (pop top)) ⇒ Lst (▹ top))))
maptp = ∀I (∀I (maptp' _ _))

maplem' : ∀ {i} {S S' : tp ⊡ i} {fv fv' us us' ws ws'} -> V[ S ⇒ S' ] ⊡ fv fv' -> V[ Lst S ] ⊡ ws ws' -> V[ Lst S ] ⊡ us us' -> Clo (V[ Lst S' ] ⊡) (mapc fv ws us) (mapc fv' ws us')
maplem' df dw [] = clo (, fold[] []) (, fold[] []) []
maplem' {i} {S} {S'} df dw (x ∷ du) with df x | maplem' {i} {S} {S'} df dw du
maplem' df dw (x ∷ du) | clo (proj₁ , proj₂) (proj₃ , proj₄) rel | clo (proj₅ , proj₆) (proj₇ , proj₈) rel₁ = clo (, fold∷ proj₆ ((((▹ (pop (pop (pop top)))) · (▹ (pop top))) proj₂) ∷ (▹ top))) (, fold∷ proj₈ ((((▹ (pop (pop (pop top)))) · (▹ (pop top))) proj₄) ∷ (▹ top))) (rel ∷ rel₁)

-- TODO: Would a CBPV style type system clean this up?

maplem2 : ∀ {fv us vs ws} -> mapc fv ws us  ⇓ vs -> All {Level.suc Level.zero} (λ x y -> Lift ((fv · x) ⇓ y)) us vs
maplem2 (fold[] []) = []
maplem2 (fold∷ m (_·_ (▹ (pop (pop (pop top)))) (▹ (pop top)) m₃ ∷ (▹ top))) = (lift m₃) ∷ maplem2 m

maplem3 : ∀ {fv us vs ws} -> All {Level.suc Level.zero} (λ x y -> Lift ((fv · x) ⇓ y)) us vs -> mapc fv ws us  ⇓ vs
maplem3 [] = fold[] []
maplem3 (x ∷ d) = fold∷ (maplem3 d) ((((▹ (pop (pop (pop top)))) · (▹ (pop top))) (lower x)) ∷ (▹ top))

record Clo' {i} (P : val -> Set i) (c : comp) : Set i where
 constructor clo
 field
  v : val
  red : c ⇓ v
  rel : P v

clo1 : ∀ {i} {T : tp ⊡ i} {c} -> Clo (V[ T ] ⊡) c c -> Clo' (λ v -> V[ T ] ⊡ v v) c
clo1 (clo (v , red1) (u , red2) rel) with ⇓deter red1 red2
clo1 (clo (v , red1) (.v , red2) rel) | refl = clo v red2 rel

fund' : ∀ {i t} {T : tp ⊡ i} -> ⊡ , ⊡ ⊢ t ∶ T -> Clo' (λ v -> V[ T ] ⊡ v v) (t [ ⊡ ])
fund' d with fund d ⊡ ⊡
... | clo (v , r1) (u , r2) rel with ⇓deter r1 r2
fund' d | clo (v , r1) (.v , r2) rel | refl = clo v r1 rel

permFree : ∀ {f t s} {S S' : tp ⊡ ₀}
  -> ⊡ , ⊡ ⊢ t ∶ ∀̂ (Lst (▹ top) ⇒ Lst (▹ top))
  -> ⊡ , ⊡ ⊢ s ∶ Lst S
  -> ⊡ , ⊡ ⊢ f ∶ (S ⇒ S')
  -> ((map' · f) · (t · s)) ≈ (t · ((map' · f) · s))
permFree {f} d1 d2 d3 with fund' d1 | fund' d2 | fund' d3
permFree {f} {t} {s} {S} {S'} d1 d2 d3 | clo ut r1 rel | clo us r3 rel₁ | clo uf r5 rel₂ with clo1 {₀} {Lst S'} (maplem' {₀} {S} {S'} rel₂ rel₁ rel₁)
permFree d1 d2 d3 | clo ut r1 rel₃ | clo us r3 rel₁ | clo uf r5 rel₂ | clo um rm rel with rel₃ (λ x -> _⇓_ (uf · x)) (maplem2 rm)
permFree d1 d2 d3 | clo ut r1 rel₃ | clo us r3 rel₁ | clo uf r5 rel₂ | clo um rm rel₄ | clo (vm , r0) (vm' , r0') rel with maplem3 {ws = vm} rel
... | q = _ , (((((ƛ · r5) (apλ ƛ)) · ((r1 · r3) r0)) (apλ (fold' (▹ top) q))) , (r1 · ((((ƛ · r5) (apλ ƛ)) · r3) (apλ (fold' (▹ top) rm)))) r0')
