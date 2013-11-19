module ott where

open import Data.Empty

open import Data.Unit

open import Data.Bool

open import Data.Product



-- The universe of types

-- The types of terms(set) and proofs(prop)

mutual 
  data set : Set where
    `0 : set
    `1 : set
    `2 : set

    `Π : (S : set) -> (⟦ S ⟧ -> set) -> set
    `Σ : (S : set) -> (⟦ S ⟧ -> set) -> set

  ⟦_⟧ : set -> Set
  ⟦ `0 ⟧ = ⊥
  ⟦ `1 ⟧ = Unit
  ⟦ `2 ⟧ = Bool
  ⟦ `Π S T ⟧ = (x : ⟦ S ⟧) → ⟦ T x ⟧
  ⟦ `Σ S T ⟧ = Σ ⟦ S ⟧ (λ x → ⟦ T x ⟧)

infix 60 _`∧_

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
  
  -- if we have a proof that two types are equivalent, a value of the
  -- first we can constructu a proof that the value and the coerced
  -- value are equal. (This one is in prop as it is a proof).
  coh : (S : set) (T : set) (Q : ⟨ S ⋍ T ⟩) (s : ⟦ S ⟧) -> ⟨ (S > s ⋍ T > (coe S T Q s)) ⟩
  coh `1 `1 Q unit = unit
  coh `2 `2 Q true = unit
  coh `2 `2 Q false = unit
  coh (`Π S₀ T₀) (`Π S₁ T₁) (S₁≃S₀ , T₀≃T₁) f = λ s₀ s₁ s₀≃s₁  → {!!} -- we don't need to fill this! you cheater!
  coh (`Σ S₀ T₀) (`Σ S₁ T₁) (S₀⋍S₁ , T₀⋍T₁) (s₀ , t₀) =  q , coh (T₀ s₀) (T₁ s₁) (T₀⋍T₁ s₀ s₁ q) t₀
    where
      s₁ = (coe S₀ S₁ S₀⋍S₁ s₀)
      q = (coh S₀ S₁ S₀⋍S₁ s₀)

  coh `0 `0 Q ()
  coh `0 `1 () v
  coh `0 `2 () v
  coh `0 (`Π T x) () v
  coh `0 (`Σ T x) () v
  coh `1 `0 () v
  coh `1 `2 () v
  coh `1 (`Π T x) () v
  coh `1 (`Σ T x) () v
  coh `2 `0 () v 
  coh `2 `1 () v 
  coh `2 (`Π T x) () v
  coh `2 (`Σ T x) () v
  coh (`Π S x) `0 () v
  coh (`Π S x) `1 () v
  coh (`Π S x) `2 () v
  coh (`Π S x) (`Σ T x₁) () v
  coh (`Σ S x) `0 () v
  coh (`Σ S x) `1 () v
  coh (`Σ S x) `2 () v
  coh (`Σ S x) (`Π T x₁) () v
























