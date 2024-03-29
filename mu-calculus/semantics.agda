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

∘ω-idl : ∀ {α β} (α≤ωβ : α ≤ω β) -> ≤ω-refl ∘ω α≤ωβ ≡ α≤ωβ
∘ω-idl α≤ωβ = ≤ω-unique _ _

∘ω-idr : ∀ {α β} (α≤ωβ : α ≤ω β) -> α≤ωβ ∘ω ≤ω-refl ≡ α≤ωβ
∘ω-idr α≤ωβ = ≤ω-unique _ _

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
⊃₁≡ {A} {B} {α} {.f , natural} {f , natural'} refl = refl

postulate
 funext : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g

_⊃⁺_ : obj -> obj -> obj
(A ⊃⁺ B) = record {
            -- TODO: Crap, this needs a naturality condition
            A = A ⊃₁ B;
            ωmap = λ β≤ωα F → record {
                               f = λ γ γ≤ωβ x → _⊃₁_.f F γ (β≤ωα ∘ω γ≤ωβ) x;
                               natural = λ β≤ωα' γ≤ωβ x → trans (_⊃₁_.natural F (β≤ωα ∘ω β≤ωα') γ≤ωβ x)
                                                                (cong (λ ρ → _⊃₁_.f F _ ρ (obj.ωmap A γ≤ωβ x)) ∘ω-assoc) 
                              };
            fcomp = λ β≤ωγ α≤ωβ x → ⊃₁≡ (funext (λ ε → funext (λ ε≤ωα → funext (λ x1 → cong (λ ρ → _⊃₁_.f x ε ρ x1) ∘ω-assoc))));
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


mutual
 data ν₁ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) (α : ω+1) : Set where
  ⟨_⟩ : ∞ ((⟦ F ⟧f (ρ , (ν⁺ F ρ)) ₁) α) -> ν₁ F ρ α

 ν⁺ : ∀ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) -> obj
 ν⁺ F ρ = record { A = ν₁ F ρ; ωmap = νωmap; fcomp = {!!}; fid = {!!} }
  where νωmap : {β α : ω+1} → β ≤ω α → ν₁ F ρ α → ν₁ F ρ β
        νωmap β≤ωα ⟨ y ⟩ = ⟨ (♯ (⟦ F ⟧f (ρ , ν⁺ F ρ) ₂) β≤ωα (♭ y)) ⟩

 data μ₁ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) (α : ω+1) : Set where
  ⟨_⟩ : (⟦ F ⟧f (ρ , (μ⁺ F ρ)) ₁) α -> μ₁ F ρ α


 μ⁺ : ∀ {Δ} (F : functor (Δ , #prop)) (ρ : gksubst Δ obj) -> obj
 μ⁺ F ρ = record { A = μ₁ F ρ; ωmap = μωmap; fcomp = {!!}; fid = {!!} }
  where μωmap : {β α : ω+1} → β ≤ω α → μ₁ F ρ α → μ₁ F ρ β
        μωmap β≤ωα ⟨ y ⟩ = ⟨ ((⟦ F ⟧f (ρ , (μ⁺ F ρ))) ₂) β≤ωα y ⟩

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

record _⇒_ (A B : obj) : Set where
 constructor _,_
 field
  η : ∀ α → (A ₁) α → (B ₁) α
  .natural : ∀ {α β} (β≤ωα : β ≤ω α) -> ∀ x -> η β ((A ₂) β≤ωα x) ≡ (B ₂) β≤ωα (η α x) 

_∘⁺_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C
(η , natural) ∘⁺ (ε , natural') = (λ α x → η α (ε α x)) , (λ β≤ωα x → trans (cong (η _) (natural' β≤ωα x)) (natural β≤ωα (ε _ x)))

id⁺ : ∀ A -> A ⇒ A
id⁺ A = (λ α x → x) , (λ β≤ωα x → refl)

π₁⁺ : ∀ {B A} -> (A ∧⁺ B) ⇒ A
π₁⁺ = (λ α x → proj₁ x) , (λ β≤ωα x → refl)

π₂⁺ : ∀ {A B} -> (A ∧⁺ B) ⇒ B
π₂⁺ = (λ α t -> proj₂ t) , (λ β≤ωα x → refl)

<_,_>⁺ : ∀ {A B C} -> A ⇒ B -> A ⇒ C -> A ⇒ (B ∧⁺ C)
< (t , nt) , (u , nu) >⁺ = (λ α x → t α x , u α x) , (λ β≤ωα x → cong₂ _,_ (nt β≤ωα x) (nu β≤ωα x))

∧⁺-assoc' : ∀ A B C -> ((A ∧⁺ B) ∧⁺ C) ⇒ (A ∧⁺ (B ∧⁺ C))
∧⁺-assoc' A B C = < (π₁⁺ {B} {A} ∘⁺ π₁⁺ {C}) , (< (π₂⁺ {A} {B} ∘⁺ π₁⁺ {C}) , (π₂⁺ {A ∧⁺ B} {C}) >⁺) >⁺

∧⁺-assoc : ∀ {A B C} -> ((A ∧⁺ B) ∧⁺ C) ⇒ (A ∧⁺ (B ∧⁺ C))
∧⁺-assoc {A} {B} {C} = ∧⁺-assoc' A B C


λ⁺ : ∀ {Γ B C} -> (Γ ∧⁺ B) ⇒ C -> Γ ⇒ (B ⊃⁺ C)
λ⁺ {Γ} {B} {C} (t , nt) = record {
        η = λ α γ -> record {
              f = λ β β≤ωα b → t β ((Γ ₂) β≤ωα γ , b);
              natural = (λ β≤ωα γ≤ωβ x → trans (sym (nt γ≤ωβ (obj.ωmap Γ β≤ωα γ , x))) (cong (t _) (cong₂ _,_ (sym (obj.fcomp Γ β≤ωα γ≤ωβ γ)) refl)))
            };
        natural = (λ β≤ωα x → ⊃₁≡ {!!})
     }

_·⁺_ : ∀ {Γ B C} -> Γ ⇒ (B ⊃⁺ C) -> Γ ⇒ B -> Γ ⇒ C
_·⁺_ {Γ} (t , mt) (u , mu) = record {
    η = λ α γ → _⊃₁_.f (t α γ) α ≤ω-refl (u α γ);
    natural = λ {α} {β} β≤ωα x → trans
       (trans
           (cong (λ ρ → _⊃₁_.f ρ β ≤ω-refl (u β (obj.ωmap Γ β≤ωα x))) (mt β≤ωα x))
           (cong₂ (λ a b → _⊃₁_.f (t α x) β a b) (trans (∘ω-idr β≤ωα)
                                                            (sym (∘ω-idl β≤ωα)))
                                                     (mu β≤ωα x)))
       (sym (_⊃₁_.natural (t α x) ≤ω-refl β≤ωα (u α x)))
  }


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
