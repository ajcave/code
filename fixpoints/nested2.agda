module nested2 where
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Empty

data SPF (I : Set) : Set₁ where
 one : SPF I
 _⊗_ _⊕_ : (F G : SPF I) -> SPF I
 _⇒_ : (A : Set) -> (F : SPF I) -> SPF I
 κ : (A : Set) -> SPF I
 var : I -> SPF I

-- Can also define the bind... SPF I -> (I -> SPF J) -> SPF J ....

⟦_⟧ : ∀ {I} -> SPF I -> (I -> Set) -> Set
⟦_⟧ one ρ = Unit
⟦_⟧ (F ⊗ F₁) ρ = ⟦ F ⟧ ρ × ⟦ F₁ ⟧ ρ
⟦_⟧ (F ⊕ F₁) ρ = ⟦ F ⟧ ρ ⊎ ⟦ F₁ ⟧ ρ
⟦_⟧ (A ⇒ F) ρ = A → ⟦ F ⟧ ρ
⟦_⟧ (κ A) ρ = A
⟦_⟧ (var x) ρ = ρ x

data μ̂ {I} (F : SPF I) (i : I) : Set where
 con : ⟦ F ⟧ (μ̂ F) -> μ̂ F i 

-- TODO: Try to give directly a ML-like syntax and the logical relation interpreting it
-- Show that it's actually quite direct

-- TODO: Am I not just happy with this? In practice we only write mutually recursive things,
-- which are easily interpreted here instead of the nested mu thing...
-- Oh. Not quite; We do things like embed "list" in an inductive type definition, so we do want
-- them to be compositional or something...

μ* : ∀ {I} -> SPF (I ⊎ Unit) -> SPF I
μ* F = {!!}

open import Data.Nat
open import Data.Fin
open import Function

Suc : Set -> Set
Suc A = A ⊎ Unit

data tp (Δ : Set) : Set where
 unit : tp Δ
 _⇝_ : (T : tp ⊥) -> (S : tp Δ) -> tp Δ
 var : Δ -> tp Δ
 μ : tp (Suc Δ) -> tp Δ
 _⊕_ _⊗_ : tp Δ -> tp Δ -> tp Δ

cnt : ∀ {Δ} -> tp Δ -> Set
cnt unit = ⊥
cnt (F ⇝ F₁) = cnt F₁
cnt (var x) = ⊥
cnt (μ F) = Suc (cnt F)
cnt (F ⊕ F₁) = cnt F ⊎ cnt F₁
cnt (F ⊗ F₁) = cnt F ⊎ cnt F₁

wkn : ∀ {I J} -> (I -> J) -> SPF I -> SPF J
wkn f one = one
wkn f (F ⊗ F₁) = (wkn f F) ⊗ (wkn f F₁)
wkn f (F ⊕ F₁) = (wkn f F) ⊕ (wkn f F₁)
wkn f (A ⇒ F) = A ⇒ (wkn f F)
wkn f (κ A) = κ A
wkn f (var x) = var (f x)

_⊎̂_ : ∀ {A B C D : Set} -> (A -> B) -> (C -> D) -> A ⊎ C -> B ⊎ D
_⊎̂_ f g (inj₁ x) = inj₁ (f x)
_⊎̂_ f g (inj₂ y) = inj₂ (g y)

⊎assoc : ∀ {A B C : Set} -> A ⊎ (B ⊎ C) -> (A ⊎ B) ⊎ C
⊎assoc (inj₁ x) = inj₁ (inj₁ x)
⊎assoc (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
⊎assoc (inj₂ (inj₂ y)) = inj₂ y

⊎assoc' : ∀ {A B C : Set} -> (A ⊎ B) ⊎ C -> A ⊎ (B ⊎ C)
⊎assoc' (inj₁ (inj₁ x)) = inj₁ x
⊎assoc' (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
⊎assoc' (inj₂ y) = inj₂ (inj₂ y)

⊎comm : ∀ {A B : Set} -> A ⊎ B -> B ⊎ A
⊎comm (inj₁ x) = inj₂ x
⊎comm (inj₂ y) = inj₁ y

fancy : ∀ {A B C : Set} -> (A ⊎ B) ⊎ C -> A ⊎ (C ⊎ B)
fancy = (λ { (inj₁ (inj₁ x)) → inj₁ x ; (inj₁ (inj₂ y)) → inj₂ (inj₂ y) ; (inj₂ y) → inj₂ (inj₁ y) })

mutual
 -- This interprets the "main one", "entry point"
 -- I guess this should be Suc (Δ ⊎ cnf F) for the distinguished entry point?
 interp : ∀ {Δ} -> (F : tp Δ) -> SPF (Δ ⊎ cnt F)
 interp unit = one
 interp (F ⇝ F₁) with μ̂ (interp F) {!!}
 ... | q = {!!} ⇒ interp F₁
 interp (var x) = var (inj₁ x)
 interp (μ F) = var (inj₂ (inj₂ unit))
 interp (F ⊕ F₁) = wkn (id ⊎̂ inj₁) (interp F) ⊕ wkn (id ⊎̂ inj₂) (interp F₁)
 interp (F ⊗ F₁) = wkn (id ⊎̂ inj₁) (interp F) ⊗ wkn (id ⊎̂ inj₂) (interp F₁)

 -- This finds and interprets the "auxiliary ones"
 interp' : ∀ {Δ} -> (F : tp Δ) -> cnt F -> SPF (Δ ⊎ cnt F)
 interp' unit ()
 interp' (F ⇝ F₁) p = {!!}
 interp' (var x) ()
 interp' (μ F) p = wkn fancy (interp F)
 interp' (F ⊕ F₁) (inj₁ x) = wkn (id ⊎̂ inj₁) (interp' F x)
 interp' (F ⊕ F₁) (inj₂ y) = wkn (id ⊎̂ inj₂) (interp' F₁ y)
 interp' (F ⊗ F₁) p = {!!}
 -- Is this prettier with indexed containers?
open import Data.Container

-- Does the Agda Containers library already implement this?
 
 