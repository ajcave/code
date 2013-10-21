module rec-types-cbpv where
open import FinMap
open import Unit
open import Product

{- We want this if we want both computational rec types and value rec types
data sort : Set where
 comp : sort
 val : sort
-}

* : Unitz
* = tt

mutual
 data ctpf (Δ : ctx Unitz) : Set where
  _⇒_ : (A : vtpf Δ) (B : ctpf Δ) -> ctpf Δ
  F : (A : vtpf Δ) -> ctpf Δ  -- embedding/producer type
 data vtpf (Δ : ctx Unitz) : Set where
  μ : (T : vtpf (Δ , *)) -> vtpf Δ
  ▹ : (X : var Δ *) -> vtpf Δ
  U : (B : ctpf Δ) -> vtpf Δ -- thunk

mutual
 [_]ctr : ∀ {Δ1 Δ2} -> vsubst Δ1 Δ2 -> ctpf Δ1 -> ctpf Δ2
 [_]ctr σ (T ⇒ T₁) = ([ σ ]vtr T) ⇒ ([ σ ]ctr T₁)
 [_]ctr σ (F A) = F ([ σ ]vtr A)

 [_]vtr : ∀ {Δ1 Δ2} -> vsubst Δ1 Δ2 -> vtpf Δ1 -> vtpf Δ2
 [_]vtr σ (▹ X) = ▹ ([ σ ]v X)
 [_]vtr σ (μ T) = μ ([ vsub-ext σ ]vtr T)
 [_]vtr σ (U B) = U ([ σ ]ctr B)

fsubst : ∀ (Δ1 Δ2 : ctx Unitz) -> Set
fsubst Δ1 Δ2 = gksubst Δ1 (vtpf Δ2)

fsubst-ext : ∀ {Δ1 Δ2} -> fsubst Δ1 Δ2 -> fsubst (Δ1 , *) (Δ2 , *)
fsubst-ext σ = (gmap [ wkn-vsub ]vtr σ) , (▹ top)

mutual
 [_]ct : ∀ {Δ1 Δ2} -> fsubst Δ1 Δ2 -> ctpf Δ1 -> ctpf Δ2
 [_]ct σ (T ⇒ T₁) = ([ σ ]vt T) ⇒ ([ σ ]ct T₁)
 [_]ct σ (F A) = F ([ σ ]vt A)

 [_]vt : ∀ {Δ1 Δ2} -> fsubst Δ1 Δ2 -> vtpf Δ1 -> vtpf Δ2
 [_]vt σ (▹ X) = [ σ ]v X
 [_]vt σ (μ T) = μ ([ fsubst-ext σ ]vt T)
 [_]vt σ (U B) = U ([ σ ]ct B)

id-fsub : ∀ {Δ : ctx Unitz} -> fsubst Δ Δ
id-fsub {⊡} = tt
id-fsub {Δ , T} = fsubst-ext id-fsub

[_/X]c : ∀ {Δ} -> vtpf Δ -> ctpf (Δ , *) -> ctpf Δ
[ A /X]c B = [ id-fsub , A ]ct B

[_/X]v : ∀ {Δ} -> vtpf Δ -> vtpf (Δ , *) -> vtpf Δ
[ A /X]v A₁ = [ id-fsub , A ]vt A₁

vtp : Set
vtp = vtpf ⊡

ctp : Set
ctp = ctpf ⊡

mutual
 data val (Γ : ctx Unitz) : Set where
  ▹ : (x : var Γ *) -> val Γ
  roll : (v : val Γ) -> val Γ
  thunk : (e : tm Γ) -> val Γ
 data tm (Γ : ctx Unitz) : Set where
  ƛ : (e : tm (Γ , *)) -> tm Γ
  _·_ : (e1 : tm Γ) (v : val Γ) -> tm Γ
  pm : ∀ (v : val Γ) (e : tm (Γ , *)) -> tm Γ
--  letbe : ∀ (v : val Γ) (e : tm (Γ , *)) -> tm Γ
  produce : (v : val Γ) -> tm Γ 
  _to_ : (e1 : tm Γ) (e2 : tm (Γ , *)) -> tm Γ
  force : (v : val Γ) -> tm Γ
  

{-
data tm (Γ : ctx tp) : tp -> Set where
 ▹ : ∀ {T} (x : var Γ T) -> tm Γ T
 ƛ : ∀ {T S} (e : tm (Γ , T) S) -> tm Γ (T ⇒ S)
 _·_ : ∀ {T S} (e1 : tm Γ (T ⇒ S)) (e2 : tm Γ T) -> tm Γ S
 roll : ∀ (T : func (⊡ , *)) (e : tm Γ ([ μ T /X] T)) -> tm Γ (μ T)
 unroll : ∀ {T : func (⊡ , *)} (e : tm Γ (μ T)) -> tm Γ ([ μ T /X] T)

[_]r : ∀ {Γ1 Γ2 T} -> vsubst Γ1 Γ2 -> tm Γ1 T -> tm Γ2 T
[_]r w (▹ x) = ▹ ([ w ]v x)
[_]r w (ƛ e) = ƛ ([ vsub-ext w ]r e)
[_]r w (e · e₁) = ([ w ]r e) · ([ w ]r e₁)
[_]r w (roll T e) = roll T ([ w ]r e)
[_]r w (unroll e) = unroll ([ w ]r e)

tsubst : ∀ (Δ1 Δ2 : ctx tp) -> Set
tsubst Δ1 Δ2 = gsubst Δ1 (tm Δ2)

tsubst-ext : ∀ {Δ1 Δ2 T} -> tsubst Δ1 Δ2 -> tsubst (Δ1 , T) (Δ2 , T)
tsubst-ext σ = (gmap [ wkn-vsub ]r σ) , (▹ top)

[_]t : ∀ {Γ1 Γ2 T} -> tsubst Γ1 Γ2 -> tm Γ1 T -> tm Γ2 T
[_]t σ (▹ x) = [ σ ]v x
[_]t σ (ƛ e) = ƛ ([ tsubst-ext σ ]t e)
[_]t σ (e · e₁) = [ σ ]t e · [ σ ]t e₁
[_]t σ (roll T e) = roll T ([ σ ]t e)
[_]t σ (unroll e) = unroll ([ σ ]t e)

id-tsub : ∀ {Δ : ctx tp} -> tsubst Δ Δ
id-tsub {⊡} = tt
id-tsub {Δ , T} = tsubst-ext id-tsub

[_/x] : ∀ {Δ T S} -> tm Δ T -> tm (Δ , T) S -> tm Δ S
[ e2 /x] e1 = [ id-tsub , e2 ]t e1

data _⟶_ : ∀ {T} -> tm ⊡ T -> tm ⊡ T -> Set where
 β : ∀ {T S} {e1 : tm (⊡ , T) S} {e2 : tm ⊡ T} -> (ƛ e1 · e2) ⟶ [ e2 /x] e1
 βμ : ∀ {T : func (⊡ , *)} {e : tm ⊡ ([ μ T /X] T)} -> (unroll (roll T e)) ⟶ e
 -}
