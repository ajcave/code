module lambda where
open import FinMap
open import Unit

* : Unitz
* = tt

data tm (Γ : ctx Unitz) : Set where
 ▹ : (x : var Γ *) -> tm Γ
 ƛ : (M : tm (Γ , *)) -> tm Γ
 _·_ : (M : tm Γ) -> (N : tm Γ) -> tm Γ

