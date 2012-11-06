{-# OPTIONS --no-positivity-check #-}
module semantics where
open import mu-ltl
open import Data.Sum
open import Data.Nat
open import FinMap
open import Coinduction
open import Product
open import Unit
open import Data.Empty
open import Function
open import Relation.Binary.PropositionalEquality

open ≤-Reasoning

data ω+1 : Set where
 ▹ : (n : ℕ) -> ω+1
 ω : ω+1

data _≤ω_ : ω+1 -> ω+1 -> Set where
 inj₁ : ∀ {n m} -> (n≤m : n ≤ m) -> (▹ n) ≤ω (▹ m)
 inj₂ : ∀ {α} -> α ≤ω ω

≤ω-refl : ∀ {α} -> α ≤ω α
≤ω-refl {▹ n} = inj₁ (begin n ∎)
≤ω-refl {ω} = inj₂

_∘ω_ : ∀ {α β γ} (β≤ωγ : β ≤ω γ) (α≤ωβ : α ≤ω β) -> α ≤ω γ
inj₁ n≤m ∘ω inj₁ n≤m' = inj₁ (begin _ ≤⟨ n≤m' ⟩ _ ≤⟨ n≤m ⟩ (_ ∎))
inj₂ ∘ω _ = inj₂

≤-unique : ∀ {n m} (p1 p2 : n ≤ m) -> p1 ≡ p2
≤-unique z≤n z≤n = refl
≤-unique (s≤s m≤n) (s≤s m≤n') = cong s≤s (≤-unique m≤n m≤n')

≤ω-unique : ∀ {α β} (p1 p2 : α ≤ω β) -> p1 ≡ p2
≤ω-unique (inj₁ n≤m) (inj₁ n≤m') = cong inj₁ (≤-unique n≤m n≤m')
≤ω-unique inj₂ inj₂ = refl

∘ω-assoc : ∀ {α β γ ε} {γ≤ωε : γ ≤ω ε} {β≤ωγ : β ≤ω γ} {α≤ωβ : α ≤ω β} -> ((γ≤ωε ∘ω β≤ωγ) ∘ω α≤ωβ) ≡ (γ≤ωε ∘ω (β≤ωγ ∘ω α≤ωβ))
∘ω-assoc = ≤ω-unique _ _

obj₁ : Set₁
obj₁ = ω+1 -> Set

obj₂ : obj₁ -> Set
obj₂ A = ∀ {β α} -> (β≤ωα : β ≤ω α) -> A α -> A β

record obj : Set₁ where
 field
  A : obj₁
  ωmap : obj₂ A
  .fcomp : ∀ {α β γ} (β≤ωγ : β ≤ω γ) (α≤ωβ : α ≤ω β)  -> (ωmap (β≤ωγ ∘ω α≤ωβ)) ≈ ((ωmap α≤ωβ) ∘ (ωmap β≤ωγ))
  .fid : ∀ {α} -> ωmap (≤ω-refl {α}) ≈ id

_₁ : obj -> obj₁
A ₁ = obj.A A

_₂ : ∀ (A : obj) -> obj₂ (A ₁)
A ₂ = obj.ωmap A

○₁ : obj₁ -> obj₁
(○₁ A) (▹ zero) = Unit
(○₁ A) (▹ (suc n)) = A (▹ n)
(○₁ A) ω = A ω

○₂ : ∀ {A} -> obj₂ A -> obj₂ (○₁ A)
○₂ A' {▹ zero} {▹ n'} (inj₁ n≤m) = λ x → tt
○₂ A' {▹ (suc n)} {▹ zero} (inj₁ ())
○₂ A' {▹ (suc n)} {▹ (suc n')} (inj₁ (s≤s m≤n)) = A' (inj₁ m≤n)
○₂ A' {▹ zero} {ω} α≤ωβ = λ x → tt
○₂ A' {▹ (suc n)} {ω} α≤ωβ = A' inj₂
○₂ A' {ω} {▹ n} ()
○₂ A' {ω} {ω} α≤ωβ = A' α≤ωβ

○⁺ : obj -> obj
○⁺ A = record {
        A = ○₁ (A ₁);
        ωmap = ○₂ (A ₂);
        fcomp = λ β≤ωγ α≤ωβ x → {!!};
        fid = λ x → {!!}
       }

record _⊃₁_ (A B : obj) (α : ω+1) : Set where
 constructor _,_
 field
  f : ∀ β → (β≤ωα : β ≤ω α) → (A ₁) β → (B ₁) β
  .natural : ∀ {β γ} (β≤ωα : β ≤ω α) (γ≤ωβ : γ ≤ω β) -> ∀ x -> (B ₂) γ≤ωβ (f β β≤ωα x) ≡ f γ (β≤ωα ∘ω γ≤ωβ) ((A ₂) γ≤ωβ x)

⊃₁≡ : ∀ {A B : obj} {α : ω+1} {P Q : (A ⊃₁ B) α} ->  _⊃₁_.f P ≡ _⊃₁_.f Q -> P ≡ Q
⊃₁≡ {A} {B} {α} {.f' , natural} {f' , natural'} refl = refl

_⊃⁺_ : obj -> obj -> obj
(A ⊃⁺ B) = record {
            -- TODO: Crap, this needs a naturality condition
            A = A ⊃₁ B;
            ωmap = λ β≤ωα F → record {
                               f = λ γ γ≤ωβ x → _⊃₁_.f F γ (β≤ωα ∘ω γ≤ωβ) x;
                               natural = λ β≤ωα' γ≤ωβ x → trans (_⊃₁_.natural F (β≤ωα ∘ω β≤ωα') γ≤ωβ x)
                                                                (cong (λ ρ → _⊃₁_.f F _ ρ (obj.ωmap A γ≤ωβ x)) ∘ω-assoc) 
                              };
            fcomp = λ β≤ωγ α≤ωβ x → ⊃₁≡ {!!};
            fid = λ x → ⊃₁≡ {!!}
           }


_∧⁺_ : obj -> obj -> obj
(A ∧⁺ B) = record {
             A = λ α -> (A ₁) α × (B ₁) α;
             ωmap = λ α≤ωβ x → (A ₂) α≤ωβ (proj₁ x) , (B ₂) α≤ωβ (proj₂ x);
             fcomp = λ β≤ωγ α≤ωβ x → cong₂ _,_ (obj.fcomp A β≤ωγ α≤ωβ (proj₁ x)) (obj.fcomp B β≤ωγ α≤ωβ (proj₂ x));
             fid = λ x → cong₂ _,_ (obj.fid A (proj₁ x)) (obj.fid B (proj₂ x))
           }

_∨⁺_ : obj -> obj -> obj
(A ∨⁺ B) = record {
             A = λ α -> (A ₁) α ⊎ (B ₁) α;
             ωmap = λ α≤ωβ → [ (λ x -> inj₁ ((A ₂) α≤ωβ x)) , (λ x → inj₂ ((B ₂) α≤ωβ x)) ]′;
             fcomp = λ β≤ωγ α≤ωβ → λ {(inj₁ x) → cong inj₁ (obj.fcomp A β≤ωγ α≤ωβ x); (inj₂ y) → cong inj₂ (obj.fcomp B β≤ωγ α≤ωβ y)};
             fid = λ { (inj₁ x) → cong inj₁ (obj.fid A x) ; (inj₂ y) -> cong inj₂ (obj.fid B y) }
           }

⊤⁺ : obj
⊤⁺ = record {
       A = λ x → Unit;
       ωmap = λ α≤ωβ x → tt;
       fcomp = λ β≤ωγ α≤ωβ x → refl;
       fid = λ x → refl
     }

{-
mutual
 data ν⁺ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) (α : ωnat) : Set where
  ⟨_⟩ : ∞ (⟦ F ⟧f (ρ , (ν⁺ F ρ)) α) -> ν⁺ F ρ α

 data μ⁺ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) (α : ωnat) : Set where
  ⟨_⟩ : ⟦ F ⟧f (ρ , (μ⁺ F ρ)) α -> μ⁺ F ρ α

 ⟦_⟧f : ∀ {Δ} -> functor Δ -> (ρ : gksubst Δ obj) -> obj
 ⟦_⟧f (▹ A) ρ = lookup ρ A
 ⟦_⟧f (μ F) ρ = μ⁺ F ρ
 ⟦_⟧f (ν F) ρ = ν⁺ F ρ
 ⟦_⟧f (○ A) ρ = ○⁺ (⟦ A ⟧f ρ)
 ⟦_⟧f (A ⊃ B) ρ = ⟦ A ⟧f tt ⊃⁺ ⟦ B ⟧f ρ
 ⟦_⟧f (A ∧ B) ρ = ⟦ A ⟧f ρ ∧⁺ ⟦ B ⟧f ρ
 ⟦_⟧f (A ∨ B) ρ = ⟦ A ⟧f ρ ∨⁺ ⟦ B ⟧f ρ
 ⟦_⟧f ⊤ ρ = ⊤⁺

⟦_⟧t : prop -> obj
⟦ A ⟧t = ⟦ A ⟧f tt

⟦_⟧c : ctx prop -> obj
⟦ ⊡ ⟧c = ⊤⁺
⟦ Γ , T ⟧c = ⟦ Γ ⟧c ∧⁺ ⟦ T ⟧t

Functorial : obj -> Set
Functorial A = ∀ {α β} -> β ≤ω α -> A α -> A β



mutual
 ⟦_⟧mf : ∀ {Δ} (F : functor Δ) {ρ : gksubst Δ obj} (P : gsubst-pred Functorial ρ) -> Functorial (⟦ F ⟧f ρ)
 ⟦_⟧mf (▹ A) ρ = lookup-pred ρ A
 ⟦_⟧mf (μ F) ρ = {!!}
 ⟦_⟧mf (ν F) ρ = {!!}
 ⟦_⟧mf (○ A) ρ = ○⁺f (⟦ A ⟧mf ρ)
 ⟦_⟧mf (A ⊃ B) ρ = {!!}
 ⟦_⟧mf (A ∧ B) ρ = {!!}
 ⟦_⟧mf (A ∨ B) ρ = {!!}
 ⟦_⟧mf ⊤ ρ = {!!}

_⇒_ : obj -> obj -> Set
A ⇒ B = ∀ α → A α → B α

_∘⁺_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C
f ∘⁺ g = λ α x → f α (g α x)

id⁺ : ∀ A -> A ⇒ A
id⁺ A α x = x

π₁⁺ : ∀ {A B} -> (A ∧⁺ B) ⇒ A
π₁⁺ α t = proj₁ t

π₂⁺ : ∀ {A B} -> (A ∧⁺ B) ⇒ B
π₂⁺ α t = proj₂ t

<_,_>⁺ : ∀ {A B C} -> A ⇒ B -> A ⇒ C -> A ⇒ (B ∧⁺ C)
< t , u >⁺ α x = (t α x) , (u α x)

-- TODO: Build up proofs of naturality at the same time by only using nice combinators
∧⁺-assoc' : ∀ A B C -> ((A ∧⁺ B) ∧⁺ C) ⇒ (A ∧⁺ (B ∧⁺ C))
∧⁺-assoc' A B C = < π₁⁺ ∘⁺ π₁⁺ , < (π₂⁺ ∘⁺ π₁⁺) , π₂⁺ >⁺ >⁺

∧⁺-assoc : ∀ {A B C} -> ((A ∧⁺ B) ∧⁺ C) ⇒ (A ∧⁺ (B ∧⁺ C))
∧⁺-assoc {A} {B} {C} = ∧⁺-assoc' A B C

λ⁺ : ∀ {Γ B C} -> (Γ ∧⁺ B) ⇒ C -> Γ ⇒ (B ⊃⁺ C)
λ⁺ t α γ β β≤α b = t β ({!!} , b)

_·⁺_ : ∀ {Γ B C} -> Γ ⇒ (B ⊃⁺ C) -> Γ ⇒ B -> Γ ⇒ C
(M ·⁺ N) α γ = M α γ α (≤ω-refl {α}) (N α γ)

⟦_⟧e : ∀ {θ Γ T} -> θ , Γ ⊢ T - true -> ((○⁺ (⟦ θ ⟧c)) ∧⁺ ⟦ Γ ⟧c) ⇒ ⟦ T ⟧t
⟦ ▹ x ⟧e = {!!}
⟦ ƛ M ⟧e = λ⁺ (⟦ M ⟧e ∘⁺ ∧⁺-assoc)
⟦ M · N ⟧e = ⟦ M ⟧e ·⁺ ⟦ N ⟧e
⟦ let-◦ M N ⟧e = {!!}
⟦ ◦ M ⟧e = {!!}
⟦ inj M ⟧e = {!!}
⟦ rec F M N ⟧e = {!!}
⟦ out M ⟧e = {!!}
⟦ mu-ltl.unfold F M N ⟧e = {!!}
⟦ < M , N > ⟧e = {!!}
⟦ fst M ⟧e = π₁⁺ ∘⁺ ⟦ M ⟧e
⟦ snd M ⟧e = π₂⁺ ∘⁺ ⟦ M ⟧e
⟦ inl M ⟧e = {!!}
⟦ inr M ⟧e = {!!}
⟦ case M N1 N2 ⟧e = {!!}
⟦ unit ⟧e = {!!}
-}