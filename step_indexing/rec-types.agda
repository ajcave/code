module rec-types where
open import FinMap
open import Unit
open import Product

* : Unitz
* = tt

data func (Δ : ctx Unitz) : Set where
 _⇒_ : (T S : func Δ) -> func Δ
 ▹ : (X : var Δ *) -> func Δ
 μ : (T : func (Δ , *)) -> func Δ

[_]fv : ∀ {Δ1 Δ2} -> vsubst Δ1 Δ2 -> func Δ1 -> func Δ2
[_]fv σ (T ⇒ T₁) = ([ σ ]fv T) ⇒ ([ σ ]fv T₁)
[_]fv σ (▹ X) = ▹ ([ σ ]v X)
[_]fv σ (μ T) = μ ([ vsub-ext σ ]fv T)

fsubst : ∀ (Δ1 Δ2 : ctx Unitz) -> Set
fsubst Δ1 Δ2 = gksubst Δ1 (func Δ2)

fsubst-ext : ∀ {Δ1 Δ2} -> fsubst Δ1 Δ2 -> fsubst (Δ1 , *) (Δ2 , *)
fsubst-ext σ = (gmap [ wkn-vsub ]fv σ) , (▹ top)

[_]ff : ∀ {Δ1 Δ2} -> fsubst Δ1 Δ2 -> func Δ1 -> func Δ2
[_]ff σ (T ⇒ T₁) = ([ σ ]ff T) ⇒ ([ σ ]ff T₁)
[_]ff σ (▹ X) = [ σ ]v X
[_]ff σ (μ T) = μ ([ fsubst-ext σ ]ff T)

id-fsub : ∀ {Δ : ctx Unitz} -> fsubst Δ Δ
id-fsub {⊡} = tt
id-fsub {Δ , T} = fsubst-ext id-fsub

[_/X] : ∀ {Δ} -> func Δ -> func (Δ , *) -> func Δ
[ T /X] S = [ id-fsub , T ]ff S

tp : Set
tp = func ⊡

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
