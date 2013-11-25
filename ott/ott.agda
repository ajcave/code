module ott where

open import Data.Empty

open import Data.Unit

open import Data.Bool

open import Data.Product
open import Data.Nat


-- The universe of types

-- The types of terms(set) and proofs(prop)

mutual 
  data set : Set where
    `0 : set
    `1 : set
    `2 : set

    `Π : (S : set) -> (⟦ S ⟧ -> set) -> set
    `Σ : (S : set) -> (⟦ S ⟧ -> set) -> set
    `ℕ : set

  ⟦_⟧ : set -> Set
  ⟦ `0 ⟧ = ⊥
  ⟦ `1 ⟧ = Unit
  ⟦ `2 ⟧ = Bool
  ⟦ `Π S T ⟧ = (x : ⟦ S ⟧) → ⟦ T x ⟧
  ⟦ `Σ S T ⟧ = Σ ⟦ S ⟧ (λ x → ⟦ T x ⟧)
  ⟦ `ℕ ⟧ = ℕ

infix 60 _`∧_

_↝_ : set -> set -> set
T ↝ S = `Π T (λ _ -> S)

mutual 
  data prop : Set where
    `⊥ : prop
    `⊤ : prop
    _`∧_ : prop -> prop -> prop
    `∀ : (S : set) -> (⟦ S ⟧ -> prop) -> prop

  ⌈_⌉ : prop -> set
  ⌈ `⊥ ⌉ = `0
  ⌈ `⊤ ⌉ = `1
  ⌈ P `∧ P₁ ⌉ = `Σ ⌈ P ⌉ (λ _ → ⌈ P₁ ⌉) 
  ⌈ `∀ S P ⌉ = `Π S (λ P₁ → ⌈ (P P₁) ⌉)


⟨_⟩ : prop -> Set
⟨ P ⟩  = ⟦ ⌈ P ⌉ ⟧

_⇒_ : prop -> prop -> prop
P ⇒ Q = `∀ ⌈ P ⌉ λ _ -> Q



-- Type and value equality

mutual
  _⋍_ : set -> set -> prop 
  `0 ⋍ `0 = `⊤
  `1 ⋍ `1 = `⊤
  `2 ⋍ `2 = `⊤
  `Σ S₀ T₀ ⋍ `Σ S₁ T₁ = (S₀ ⋍ S₁) `∧ 
    `∀ S₀ (λ s₀ → `∀ S₁ (λ s₁ → (S₀ > s₀ ⋍ S₁ > s₁) ⇒ (T₀ s₀ ⋍ T₁ s₁)))
  `Π S₀ T₀ ⋍ `Π S₁ T₁ = (S₁ ⋍ S₀) `∧ -- notice the other order for the proofs (inside de function we get an s₁)
    `∀ S₁ (λ s₁ → `∀ S₀ (λ s₀ → (S₁ > s₁ ⋍ S₀ > s₀) ⇒ ((T₀ s₀) ⋍ T₁ s₁)))
  `ℕ ⋍ `ℕ = `⊤
  _ ⋍ _ = `⊥
  
  _>_⋍_>_ : (S : set) -> ⟦ S ⟧ -> (T : set) -> ⟦ T ⟧ -> prop
  `0 > _ ⋍ `0 > _ = `⊤
  `1 > _ ⋍ `1 > _ = `⊤
  `2 > true ⋍ `2 > true = `⊤
  `2 > false ⋍ `2 > false = `⊤
  `Π S₀ T₀ > f₀  ⋍ `Π S₁ T₁ > f₁ = -- extensionlity!
    `∀ S₀ (λ x₀ → `∀ S₁ (λ x₁ → (S₀ > x₀ ⋍ S₁ > x₁) ⇒ (T₀ x₀ > f₀ x₀ ⋍ T₁ x₁ > f₁ x₁)))
  `Σ S₀ T₀ > p₀ ⋍ `Σ S₁ T₁ > p₁ = (S₀ > proj₁ p₀ ⋍ S₁ > proj₁ p₁) `∧ 
    ((T₀ (proj₁ p₀)) > proj₂ p₀ ⋍ T₁ (proj₁ p₁) > proj₂ p₁)
  `ℕ > zero ⋍ `ℕ > zero = `⊤
  `ℕ > suc t ⋍ `ℕ > suc s = `ℕ > t ⋍ `ℕ > s
  _ > _ ⋍ _ > _ = `⊥


-- Coercions and coherence

mutual
  -- if a proof that twp types are equal and a value of the first, we
  -- can coerce the value to the other type. (This one is in set).
  coe : (S : set) (T : set) -> ⟨ S ⋍ T ⟩ -> ⟦ S ⟧ -> ⟦ T ⟧
  coe `1 `1 Q unit = unit
  coe `2 `2 Q v = v
  coe (`Π S₀ T₀) (`Π S₁ T₁) (S₁≃S₀ , T₀≃T₁) v = 
    λ s₁ -> let s₀ : ⟦ S₀ ⟧
                s₀ = coe S₁ S₀ S₁≃S₀ s₁
                s₁s₀ : ⟨ S₁ > s₁ ⋍ S₀ > s₀ ⟩
                s₁s₀ = coh S₁ S₀ S₁≃S₀ s₁
           in
             coe (T₀ s₀) (T₁ s₁) (T₀≃T₁ s₁ s₀ s₁s₀) (v s₀)
  coe (`Σ S₀ T₀) (`Σ S₁ T₁) (S₀⋍S₁ , T₀⋍T₁) (s₀ , t₀) =  s₁ , t₁
    where
      s₁ = (coe S₀ S₁ S₀⋍S₁ s₀)
      t₁ = coe (T₀ s₀) (T₁ s₁) (T₀⋍T₁ s₀ s₁ (coh S₀ S₁ S₀⋍S₁ s₀)) t₀
  coe `ℕ `ℕ Q v = v

  coe `0 `0 Q () -- there is no possible value to coerce
  coe `0 `1 () v -- from this case on, there is no possbile proof of equality
  coe `0 `2 () v
  coe `0 (`Π T x) () v
  coe `0 (`Σ T x) () v
  
  coe `1 `0 () v
  coe `1 `2 () v
  coe `1 (`Π T x) () v
  coe `1 (`Σ T x) () v

  coe `2 `0 () v
  coe `2 `1 () v
  coe `2 (`Π T x) () v
  coe `2 (`Σ T x) () v

  coe (`Π S x) `0 () v
  coe (`Π S x) `1 () v
  coe (`Π S x) `2 () v
  coe (`Π S x) (`Σ T x₁) () v

  coe (`Σ S x) `0 () v
  coe (`Σ S x) `1 () v
  coe (`Σ S x) `2 () v
  coe (`Σ S x) (`Π T x₁) () v

  coe `ℕ `0 () v
  coe `ℕ `1 () v
  coe `ℕ `2 () v
  coe `ℕ (`Π T x) () v
  coe `ℕ (`Σ T x) () v
  coe `0 `ℕ () v
  coe `1 `ℕ () v
  coe `2 `ℕ () v
  coe (`Π T x) `ℕ () v
  coe (`Σ T x) `ℕ () v
  
  -- if we have a proof that two types are equivalent, a value of the
  -- first we can constructu a proof that the value and the coerced
  -- value are equal. (This one is in prop as it is a proof).
  coh : (S : set) (T : set) (Q : ⟨ S ⋍ T ⟩) (s : ⟦ S ⟧) -> ⟨ (S > s ⋍ T > (coe S T Q s)) ⟩
  coh S T Q s = {!!}

postulate
 Resp : (S : set)(P : ⟦ S ⟧ -> set)
       {s0 s1 : ⟦ S ⟧} -> ⟨ ((S > s0 ⋍ S > s1) ⇒ (P s0 ⋍ P s1)) ⟩
 [|_>_|] : (S : set)(s : ⟦ S ⟧) -> ⟨ (S > s ⋍ S > s) ⟩
 Sym : (S0 S1 : set) -> ⟨ ((S0 ⋍ S1) ⇒ (S1 ⋍ S0)) ⟩
 sym : (S0 : set)(s0 : ⟦ S0 ⟧)(S1 : set)(s1 : ⟦ S1 ⟧) ->
      ⟨ ((S0 > s0 ⋍ S1 > s1) ⇒ (S1 > s1 ⋍ S0 > s0)) ⟩


_∘_ : ∀ {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘ g) = λ x -> f (g x)

subst0 : ∀ {A} (P : ⟦ A ⟧ -> set) -> ⟦ `Π A (λ x₀ → `Π A (λ x₁ ->
      ⌈ A > x₀ ⋍ A > x₁ ⌉ ↝ ((P x₀) ↝ (P x₁)))) ⟧
subst0 P = λ x y x⋍y px → coe (P x) (P y) (Resp _ P x⋍y) px

cong0 : ∀ {A B} (f : ⟦ A ↝ B ⟧) -> ⟦ `Π A (λ x₀ → `Π A (λ x₁ ->
      ⌈ A > x₀ ⋍ A > x₁ ⌉ ↝ ⌈ B > (f x₀) ⋍ B > (f x₁) ⌉)) ⟧
cong0 {A} {B} f = λ x y x⋍y → subst0 (λ b → ⌈ B > f x ⋍ B > f b ⌉) x y x⋍y [| B > f x |]

test0 : ∀ {A B C} (P : ⟦ A ↝ C ⟧ -> set) -> ⟦ `Π (A ↝ B) (λ f₀ → `Π (A ↝ B) (λ f₁ → `Π (B ↝ C) (λ g ->
      ⌈ (A ↝ B) > f₀ ⋍ A ↝ B > f₁ ⌉ 
   ↝ (P (g ∘ f₀) ↝ P (g ∘ f₁))))) ⟧
test0 P = λ f0 f1 g f0⋍f1 p0 → subst0 P (g ∘ f0) (g ∘ f1) (cong0 (λ f → g ∘ f) f0 f1 f0⋍f1) p0

test : ∀ {A B C} -> ⟨ `∀ (A ↝ B) (λ f₀ → `∀ (A ↝ B) (λ f₁ → `∀ (B ↝ C) (λ g ->
      ((A ↝ B) > f₀ ⋍ A ↝ B > f₁)
   ⇒ ((A ↝ C) > (g ∘ f₀) ⋍ (A ↝ C) > (g ∘ f₁))))) ⟩
test = λ f0 f1 g f0⋍f1 → cong0 (λ f → g ∘ f) f0 f1 f0⋍f1


open import Relation.Binary.PropositionalEquality

lem : ∀ x -> x ≡ x + 0
lem zero = refl
lem (suc x) = cong suc (lem x)


t0 : ℕ
t0 = subst0 {`ℕ ↝ `ℕ} (λ _ -> `ℕ) (λ x → x) (λ x → x + 0) (λ x y x⋍y → {!!}) 8

postulate
 ext : ∀ {A B : Set} (f g : A -> B) -> (∀ x -> f x ≡ g x) -> f ≡ g

t1 : ℕ
t1 = subst (λ _ → ℕ) {x = λ x → x} {y = λ x → x + 0} (ext _ _ (λ x → lem x)) 8 
























