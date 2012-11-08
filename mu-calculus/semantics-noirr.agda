{-# OPTIONS --no-positivity-check #-}
module semantics-noirr where
open import mu-ltl
open import Data.Sum
open import Data.Nat
open import FinMap
open import Coinduction hiding (unfold)
open import Product
open import Unit
open import Data.Empty
open import Function
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

data ω+1 : Set where
 ▹ : (n : ℕ) -> ω+1
 ω : ω+1

data _≤ω_ : ω+1 -> ω+1 -> Set where
 inj₁ : ∀ {n m} -> (n≤m : n ≤ m) -> (▹ n) ≤ω (▹ m)
 inj₂ : ∀ {α} -> α ≤ω ω

≤ω-refl : ∀ {α} -> α ≤ω α
≤ω-refl {▹ n} = inj₁ {!!} --(begin n ∎)
≤ω-refl {ω} = inj₂

_∘ω_ : ∀ {α β γ} (β≤ωγ : β ≤ω γ) (α≤ωβ : α ≤ω β) -> α ≤ω γ
inj₁ n≤m ∘ω inj₁ n≤m' = inj₁ {!!} --(begin _ ≤⟨ n≤m' ⟩ _ ≤⟨ n≤m ⟩ (_ ∎))
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
  fcomp : ∀ {α β γ} (β≤ωγ : β ≤ω γ) (α≤ωβ : α ≤ω β)  -> (ωmap (β≤ωγ ∘ω α≤ωβ)) ≈ ((ωmap α≤ωβ) ∘ (ωmap β≤ωγ))
  fid : ∀ {α} -> ωmap (≤ω-refl {α}) ≈ id

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
  natural : ∀ {β γ} (β≤ωα : β ≤ω α) (γ≤ωβ : γ ≤ω β) -> ∀ x -> (B ₂) γ≤ωβ (f β β≤ωα x) ≡ f γ (β≤ωα ∘ω γ≤ωβ) ((A ₂) γ≤ωβ x)

K : ∀ {A : Set} {x y : A} -> (p q : x ≡ y) -> p ≡ q
K refl refl = refl

postulate
 funext : ∀ {a b} {A : Set a} {B : A -> Set b} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g
 funext-imp : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> _≡_ {_} { {x : A} -> B x} (λ {x} -> f x) (λ {x} -> g x)

⊃₁≡ : ∀ {A B : obj} {α : ω+1} {P Q : (A ⊃₁ B) α} ->  _⊃₁_.f P ≡ _⊃₁_.f Q -> P ≡ Q
⊃₁≡ {A} {B} {α} {.f , natural} {f , natural'} refl = cong (_,_ f) (funext-imp (λ x → funext-imp (λ x' → funext (λ x0 → funext (λ x1 → funext (λ x2 → K _ _))))))

_⊃⁺_ : obj -> obj -> obj
(A ⊃⁺ B) = record {
            A = A ⊃₁ B;
            ωmap = λ β≤ωα F → record {
                               f = λ γ γ≤ωβ x → _⊃₁_.f F γ (β≤ωα ∘ω γ≤ωβ) x;
                               natural = λ β≤ωα' γ≤ωβ x → trans (_⊃₁_.natural F (β≤ωα ∘ω β≤ωα') γ≤ωβ x)
                                                                (cong (λ ρ → _⊃₁_.f F _ ρ (obj.ωmap A γ≤ωβ x)) ∘ω-assoc) 
                              };
            fcomp = λ β≤ωγ α≤ωβ x → ⊃₁≡ (funext (λ ε → funext (λ ε≤ωα → funext (λ x1 → cong (λ ρ → _⊃₁_.f x ε ρ x1) ∘ω-assoc))));
            fid = λ x → ⊃₁≡ (funext (λ γ → funext (λ γ≤ωα → funext (λ x1 → cong (λ ρ → _⊃₁_.f x γ ρ x1) (∘ω-idl γ≤ωα)))))
           }

_∧₁_ : obj₁ -> obj₁ -> obj₁
(A ∧₁ B) α = A α × B α

_∧⁺_ : obj -> obj -> obj
(A ∧⁺ B) = record {
             A = (A ₁) ∧₁ (B ₁);
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

⊤₁ : obj₁
⊤₁ = λ x → Unit

⊤⁺ : obj
⊤⁺ = record {
       A = ⊤₁;
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

 data μ₁ (F : obj -> obj) (α : ω+1) : Set where
  ⟨_⟩ : ((F (μ⁺ F)) ₁) α -> μ₁ F α

 μ⁺ : ∀ (F : obj -> obj) -> obj
 μ⁺ F = record { A = μ₁ F; ωmap = μωmap; fcomp = {!!}; fid = {!!} }
  where μωmap : {β α : ω+1} → β ≤ω α → μ₁ F α → μ₁ F β
        μωmap β≤ωα ⟨ y ⟩ = ⟨ ((F (μ⁺ F) ₂) β≤ωα y) ⟩

 ⟦_⟧f : ∀ {Δ} -> functor Δ -> (ρ : gksubst Δ obj) -> obj
 ⟦_⟧f (▹ A) ρ = lookup ρ A
 ⟦_⟧f (μ F) ρ = μ⁺ (λ X -> ⟦ F ⟧f (ρ , X))
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

_⇒₁_ : obj₁ -> obj₁ -> Set
(A ⇒₁ B) = ∀ α -> A α -> B α

⇒₂ : ∀ A B -> (η : (A ₁) ⇒₁ (B ₁)) -> Set
⇒₂ A B η = ∀ {α β} (β≤ωα : β ≤ω α) -> ∀ x -> η β ((A ₂) β≤ωα x) ≡ (B ₂) β≤ωα (η α x)

record _⇒_ (A B : obj) : Set where
 constructor _,_
 field
  η : (A ₁) ⇒₁ (B ₁)
  natural : ⇒₂ A B η

_∘⁺_ : ∀ {A B C} -> B ⇒ C -> A ⇒ B -> A ⇒ C
(η , natural) ∘⁺ (ε , natural') = (λ α x → η α (ε α x)) , (λ β≤ωα x → trans (cong (η _) (natural' β≤ωα x)) (natural β≤ωα (ε _ x)))

id⁺ : ∀ A -> A ⇒ A
id⁺ A = (λ α x → x) , (λ β≤ωα x → refl)

id⁺≡ : ∀ {A B} -> A ≡ B -> A ⇒ B
id⁺≡ {A} refl = id⁺ A

π₁⁺ : ∀ {B A} -> (A ∧⁺ B) ⇒ A
π₁⁺ = (λ α x → proj₁ x) , (λ β≤ωα x → refl)

π₂⁺ : ∀ {A B} -> (A ∧⁺ B) ⇒ B
π₂⁺ = (λ α t -> proj₂ t) , (λ β≤ωα x → refl)

<_,_>⁺ : ∀ {A B C} -> A ⇒ B -> A ⇒ C -> A ⇒ (B ∧⁺ C)
< (t , nt) , (u , nu) >⁺ = (λ α x → t α x , u α x) , (λ β≤ωα x → cong₂ _,_ (nt β≤ωα x) (nu β≤ωα x))

tt⁺ : ∀ {Γ} -> Γ ⇒ ⊤⁺
tt⁺ {Γ} = record {
            η = λ α x → tt;
            natural = λ β≤ωα x → refl
          }

∧⁺-assoc' : ∀ A B C -> ((A ∧⁺ B) ∧⁺ C) ⇒ (A ∧⁺ (B ∧⁺ C))
∧⁺-assoc' A B C = < (π₁⁺ {B} {A} ∘⁺ π₁⁺ {C}) , (< (π₂⁺ {A} {B} ∘⁺ π₁⁺ {C}) , (π₂⁺ {A ∧⁺ B} {C}) >⁺) >⁺

∧⁺-assoc : ∀ {A B C} -> ((A ∧⁺ B) ∧⁺ C) ⇒ (A ∧⁺ (B ∧⁺ C))
∧⁺-assoc {A} {B} {C} = ∧⁺-assoc' A B C


λ⁺ : ∀ {B Γ C} -> (Γ ∧⁺ B) ⇒ C -> Γ ⇒ (B ⊃⁺ C)
λ⁺ {B} {Γ} {C} (t , nt) = record {
        η = λ α γ -> record {
              f = λ β β≤ωα b → t β ((Γ ₂) β≤ωα γ , b);
              natural = (λ β≤ωα γ≤ωβ x → trans (sym (nt γ≤ωβ (obj.ωmap Γ β≤ωα γ , x))) (cong (t _) (cong₂ _,_ (sym (obj.fcomp Γ β≤ωα γ≤ωβ γ)) refl)))
            };
        natural = (λ β≤ωα x → ⊃₁≡ (funext (λ γ → funext (λ γ≤ωβ → funext (λ b →
                     cong (λ ρ → t γ (ρ , b)) (sym (obj.fcomp Γ β≤ωα γ≤ωβ x)))))))
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

dist₁ : ∀ {A B} -> (○₁ (A ∧₁ B)) ⇒₁ ((○₁ A) ∧₁ (○₁ B))
dist₁ (▹ zero) = λ x → tt , tt
dist₁ (▹ (suc n)) = id
dist₁ ω = id

dist₂ : ∀ {A B} -> ⇒₂ (○⁺ (A ∧⁺ B)) ((○⁺ A) ∧⁺ (○⁺ B)) dist₁
dist₂ {A} {B} {▹ zero} {▹ zero} β≤ωα x = refl
dist₂ {A} {B} {▹ zero} {▹ (suc n)} (inj₁ ()) x
dist₂ {A} {B} {▹ (suc n)} {▹ zero} β≤ωα x = refl
dist₂ {A} {B} {▹ (suc n)} {▹ (suc n')} (inj₁ (s≤s m≤n)) x = refl
dist₂ {A} {B} {▹ n} {ω} () x
dist₂ {A} {B} {ω} {▹ zero} β≤ωα x = refl
dist₂ {A} {B} {ω} {▹ (suc n)} β≤ωα x = refl
dist₂ {A} {B} {ω} {ω} β≤ωα x = refl

dist : ∀ {A B} -> (○⁺ (A ∧⁺ B)) ⇒ ((○⁺ A) ∧⁺ (○⁺ B))
dist {A} {B} = record {
    η = dist₁;
    natural = dist₂ {A} {B}
  }

dist₁⁻¹ : ∀ {A B} -> ((○₁ A) ∧₁ (○₁ B)) ⇒₁ (○₁ (A ∧₁ B))
dist₁⁻¹ (▹ zero) = λ x → tt
dist₁⁻¹ (▹ (suc n)) = id
dist₁⁻¹ ω = id

dist₂⁻¹ : ∀ {A B} -> ⇒₂ ((○⁺ A) ∧⁺ (○⁺ B)) (○⁺ (A ∧⁺ B)) dist₁⁻¹
dist₂⁻¹ {A} {B} {▹ zero} {▹ zero} β≤ωα x = refl
dist₂⁻¹ {A} {B} {▹ zero} {▹ (suc n)} (inj₁ ()) x
dist₂⁻¹ {A} {B} {▹ (suc n)} {▹ zero} β≤ωα x = refl
dist₂⁻¹ {A} {B} {▹ (suc n)} {▹ (suc n')} (inj₁ (s≤s m≤n)) x = refl
dist₂⁻¹ {A} {B} {▹ n} {ω} () x
dist₂⁻¹ {A} {B} {ω} {▹ zero} β≤ωα x = refl
dist₂⁻¹ {A} {B} {ω} {▹ (suc n)} β≤ωα x = refl
dist₂⁻¹ {A} {B} {ω} {ω} β≤ωα x = refl

dist⁻¹ : ∀ {A B} -> ((○⁺ A) ∧⁺ (○⁺ B)) ⇒ (○⁺ (A ∧⁺ B))
dist⁻¹ {A} {B} = record {
    η = dist₁⁻¹;
    natural = dist₂⁻¹ {A} {B}
  }

⊤dist₁⁻¹ : ⊤₁ ⇒₁ (○₁ ⊤₁)
⊤dist₁⁻¹ (▹ zero) x = tt
⊤dist₁⁻¹ (▹ (suc n)) x = tt
⊤dist₁⁻¹ ω x = tt

⊤dist₂⁻¹ : ⇒₂ ⊤⁺ (○⁺ ⊤⁺) ⊤dist₁⁻¹
⊤dist₂⁻¹ {▹ zero} {▹ zero} (inj₁ z≤n) x = refl
⊤dist₂⁻¹ {▹ zero} {▹ (suc n)} (inj₁ ()) x
⊤dist₂⁻¹ {▹ (suc n)} {▹ zero} (inj₁ z≤n) x = refl
⊤dist₂⁻¹ {▹ (suc n)} {▹ (suc n')} (inj₁ (s≤s m≤n)) x = refl
⊤dist₂⁻¹ {▹ n} {ω} () x
⊤dist₂⁻¹ {ω} {▹ zero} β≤ωα x = refl
⊤dist₂⁻¹ {ω} {▹ (suc n)} β≤ωα x = refl
⊤dist₂⁻¹ {ω} {ω} β≤ωα x = refl

⊤dist⁻¹ : ⊤⁺ ⇒ (○⁺ ⊤⁺)
⊤dist⁻¹  = record {
    η = ⊤dist₁⁻¹;
    natural = ⊤dist₂⁻¹
  }

let-◦⁺ : ∀ θ Γ T S -> ((○⁺ θ) ∧⁺ Γ) ⇒ (○⁺ S) -> ((○⁺ (θ ∧⁺ S)) ∧⁺ Γ) ⇒ T -> ((○⁺ θ) ∧⁺ Γ) ⇒ T
let-◦⁺ θ Γ T S m n = n ∘⁺ < dist⁻¹ {θ} {S} ∘⁺ < π₁⁺ {Γ} {○⁺ θ} , m >⁺ , π₂⁺ {○⁺ θ} {Γ} >⁺

◦₁ : ∀ {A B} -> A ⇒₁ B -> ○₁ A ⇒₁ ○₁ B
◦₁ t (▹ zero) = id
◦₁ t (▹ (suc n)) = t (▹ n)
◦₁ t ω = t ω

◦₂ : ∀ A B f -> ⇒₂ A B f -> ⇒₂ (○⁺ A) (○⁺ B) (◦₁ f)
◦₂ A B f t {▹ zero} {▹ zero} β≤ωα x = refl
◦₂ A B f t {▹ zero} {▹ (suc n)} (inj₁ ()) x
◦₂ A B f t {▹ (suc n)} {▹ zero} (inj₁ z≤n) x = refl
◦₂ A B f t {▹ (suc n)} {▹ (suc n')} (inj₁ (s≤s m≤n)) x = t (inj₁ m≤n) x
◦₂ A B f t {▹ n} {ω} () x
◦₂ A B f t {ω} {▹ zero} β≤ωα x = refl
◦₂ A B f t {ω} {▹ (suc n)} β≤ωα x = t inj₂ x
◦₂ A B f t {ω} {ω} β≤ωα x = t β≤ωα x

◦⁺ : ∀ A B -> A ⇒ B -> ○⁺ A ⇒ ○⁺ B
◦⁺ A B (t , nt) = record {
             η = ◦₁ t;
             natural = ◦₂ A B t nt
           }

inj₁⁺ : ∀ B {A} -> A ⇒ (A ∨⁺ B)
inj₁⁺ B = record {
            η = λ α x → inj₁ x;
            natural = λ β≤ωα x → refl
          }

inj₂⁺ : ∀ B {A} -> A ⇒ (B ∨⁺ A)
inj₂⁺ B = record {
            η = λ α x → inj₂ x;
            natural = λ β≤ωα x → refl
          }

[_,_]⁺ : ∀ {A B C} -> B ⇒ A -> C ⇒ A -> (B ∨⁺ C) ⇒ A
[ (f , nf) , (g , ng) ]⁺ = record {
     η = λ α → λ {(inj₁ x) → f α x; (inj₂ y) → g α y};
     natural = λ β≤ωα → λ {(inj₁ x) → nf β≤ωα x; (inj₂ y) → ng β≤ωα y}
   }

swap⁺ : ∀ A B -> (A ∧⁺ B) ⇒ (B ∧⁺ A)
swap⁺ A B = < π₂⁺ {A} {B} , π₁⁺ {B} {A} >⁺

case⁺ : ∀ {Γ A B C} -> Γ ⇒ (A ∨⁺ B) -> (Γ ∧⁺ A) ⇒ C -> (Γ ∧⁺ B) ⇒ C -> Γ ⇒ C
case⁺ {Γ} {A} {B} {C} M N1 N2 = ([ (λ⁺ (N1 ∘⁺ swap⁺ A Γ)) , (λ⁺ (N2 ∘⁺ swap⁺ B Γ)) ]⁺ ∘⁺ M) ·⁺ (id⁺ Γ)

data arrow1 : ∀ {Δ} -> (ρ1 : gksubst Δ obj) -> (ρ2 : gksubst Δ obj) -> Set₁ where
 ⊡ : arrow1 tt tt
 _,_ : ∀ {Δ} {ρ1 ρ2 : gksubst Δ obj} (σ : arrow1 ρ1 ρ2) {A B} (N : A ⇒ B) -> arrow1 {Δ , #prop} (ρ1 , A) (ρ2 , B)

fmap : ∀ {Δ} (F : functor Δ) ρ1 ρ2 -> (σ : arrow1 ρ1 ρ2) -> (⟦ F ⟧f ρ1) ⇒ (⟦ F ⟧f ρ2)
fmap (▹ A) ρ1 ρ2 σ = {!!}
fmap (μ F) ρ1 ρ2 σ = {!!}
fmap (ν F) ρ1 ρ2 σ = {!!}
fmap (○ A) ρ1 ρ2 σ = ◦⁺ (⟦ A ⟧f ρ1) (⟦ A ⟧f ρ2) (fmap A ρ1 ρ2 σ)
fmap (A ⊃ B) ρ1 ρ2 σ = {!!}
fmap (A ∧ B) ρ1 ρ2 σ = {!!}
fmap (A ∨ B) ρ1 ρ2 σ = {!!}
fmap ⊤ ρ1 ρ2 σ = tt⁺

inj⁺ : ∀ F -> ⟦ F ⟧f (tt , ⟦ μ F ⟧t) ⇒ ⟦ μ F ⟧t
inj⁺ F = record {
     η = λ α x → ⟨ x ⟩;
     natural = λ β≤ωα x → refl
   }


fold⁺ : ∀ F C -> ⟦ F ⟧f (tt , C) ⇒ C -> ⟦ μ F ⟧t ⇒ C
fold⁺ F C (f , nf) = record {
     η = fold₁;
     natural = fold₁nat
  }
  where fold₁ : (⟦ μ F ⟧t ₁) ⇒₁ (C ₁)
        fold₁ α ⟨ y ⟩ = f α (_⇒_.η (fmap F (tt , ⟦ μ F ⟧t) (tt , C) (⊡ , (fold⁺ F C (f , nf)))) α y)
        fold₁nat : {α β : ω+1} (β≤ωα : β ≤ω α) (x : ((⟦ μ F ⟧t) ₁) α) → fold₁ β (((⟦ μ F ⟧t) ₂) β≤ωα x) ≡ ((C ₂) β≤ωα (fold₁ α x))
        fold₁nat β≤ωα ⟨ y ⟩ = trans
              (cong (f _) (_⇒_.natural (fmap F (tt , ⟦ μ F ⟧t) (tt , C) (⊡ , (fold⁺ F C (f , nf)))) β≤ωα y))
              (nf β≤ωα (_⇒_.η (fmap F (tt , ⟦ μ F ⟧t) (tt , C) (⊡ , fold⁺ F C (f , nf))) _ y))

out⁺ : ∀ F -> ν⁺ F tt ⇒ ⟦ F ⟧f (tt , ν⁺ F tt)
out⁺ F = record {
     η = λ α -> (λ {⟨ y ⟩ → ♭ y });
     natural = λ β≤ωα → λ {⟨ y ⟩ → refl}
   }

unfold⁺ : ∀ F C -> C ⇒ ⟦ F ⟧f (tt , C) -> C ⇒ ν⁺ F tt
unfold⁺ F C (f , nf) = record {
     η = unfold₁;
     natural = unfold₁nat
  }
  where unfold₁ : (C ₁) ⇒₁ ν₁ F tt
        unfold₁ α c = ⟨ ♯ _⇒_.η (fmap F (tt , C) (tt , ν⁺ F tt) (⊡ , unfold⁺ F C (f , nf))) α (f α c) ⟩
        unfold₁nat : {α β : ω+1} (β≤ωα : β ≤ω α) (x : (C ₁) α) → unfold₁ β ((C ₂) β≤ωα x) ≡ (ν⁺ F tt ₂) β≤ωα (unfold₁ α x)
        unfold₁nat β≤ωα x = cong ⟨_⟩ {!!}

_⋆v_ : ∀ {A} {Δ1 Δ2} (σ : vsub {A} Δ1 Δ2) (ρ : gksubst Δ1 obj) -> gksubst Δ2 obj
σ ⋆v ρ = gmap (λ Y -> lookup ρ Y) σ

⟦⟧f-compv : ∀ {Δ1 Δ2} (σ : vsub Δ1 Δ2) F ρ -> ⟦ [ σ ]pv F ⟧f ρ ≡ ⟦ F ⟧f (σ ⋆v ρ)
⟦⟧f-compv σ F ρ = {!!}

_⋆_ : ∀ {Δ1 Δ2} (σ : psub Δ1 Δ2) (ρ : gksubst Δ1 obj) -> gksubst Δ2 obj
σ ⋆ ρ = gmap (λ C -> ⟦ C ⟧f ρ) σ

lem3 : ∀ {Δ1 Δ2} (σ : psub Δ1 Δ2) (ρ : gksubst Δ1 obj) X -> (psub-ext σ) ⋆ (ρ , X) ≡ (σ ⋆ ρ) , X
lem3 σ ρ X = cong (λ α -> α , X)
              (begin
                ((gmap [ wkn-vsub ]pv σ) ⋆ (ρ , X))               ≡⟨ (gmap-funct σ) ⟩
                ((gmap (λ C → ⟦ [ wkn-vsub ]pv C ⟧f (ρ , X)) σ)   ≡⟨ gmap-cong (λ C → ⟦⟧f-compv wkn-vsub C (ρ , X)) ⟩
                (gmap (λ C → ⟦ C ⟧f (wkn-vsub ⋆v (ρ , X))) σ)     ≡⟨ gmap-cong (λ C → cong ⟦ C ⟧f (gmap-funct id-vsub)) ⟩
                (gmap (λ C → ⟦ C ⟧f (ρ ⁌ id-vsub)) σ)             ≡⟨ gmap-cong (λ C → cong ⟦ C ⟧f (id-v-right ρ)) ⟩
                (gmap (λ C → ⟦ C ⟧f ρ) σ
              ∎)))

⟦⟧f-comp : ∀ {Δ1 Δ2} (σ : psub Δ1 Δ2) F ρ -> ⟦ [ σ ]p F ⟧f ρ ≡ ⟦ F ⟧f (σ ⋆ ρ)
⟦⟧f-comp σ (▹ A) ρ = sym (lookup-gmap (λ x → ⟦ x ⟧f ρ) σ A)
⟦⟧f-comp σ (μ F) ρ = cong μ⁺ (funext (λ X →
         begin
           ⟦ [ psub-ext σ ]p F ⟧f (ρ , X)     ≡⟨ ⟦⟧f-comp (psub-ext σ) F (ρ , X) ⟩
           ⟦ F ⟧f ((psub-ext σ) ⋆ (ρ , X))    ≡⟨ cong ⟦ F ⟧f (lem3 σ ρ X) ⟩
           ⟦ F ⟧f ((σ ⋆ ρ) , X)
         ∎))
⟦⟧f-comp σ (ν F) ρ = {!!}
⟦⟧f-comp σ (○ A) ρ rewrite ⟦⟧f-comp σ A ρ = refl
⟦⟧f-comp σ (A ⊃ B) ρ rewrite ⟦⟧f-comp σ B ρ = refl
⟦⟧f-comp σ (A ∧ B) ρ rewrite ⟦⟧f-comp σ A ρ | ⟦⟧f-comp σ B ρ = refl
⟦⟧f-comp σ (A ∨ B) ρ = cong₂ _∨⁺_ {!!} {!!}
⟦⟧f-comp σ ⊤ ρ = refl

eval-var : ∀ Γ T -> var Γ T -> ⟦ Γ ⟧c ⇒ ⟦ T ⟧t
eval-var .(Γ , T) T (top {Γ}) = π₂⁺ {⟦ Γ ⟧c}
eval-var .(Γ , S) T (pop {Γ} {.T} {S} y) = eval-var Γ T y ∘⁺ π₁⁺ {⟦ S ⟧t}

eval : ∀ θ Γ T -> θ , Γ ⊢ T - true -> ((○⁺ (⟦ θ ⟧c)) ∧⁺ ⟦ Γ ⟧c) ⇒ ⟦ T ⟧t
eval θ Γ T (▹ x) = eval-var Γ T x ∘⁺ π₂⁺ {○⁺ ⟦ θ ⟧c}
eval θ Γ .(A ⊃ B) (ƛ {A} {B} M) = λ⁺ {⟦ A ⟧t} (eval θ (Γ , A) B M ∘⁺ (∧⁺-assoc' (○⁺ ⟦ θ ⟧c) ⟦ Γ ⟧c ⟦ A ⟧t))
eval θ Γ T (M · N) = (eval θ Γ (_ ⊃ T) M) ·⁺ (eval θ Γ _ N)
eval θ Γ T (let-◦ {S} M N) = let-◦⁺ ⟦ θ ⟧c ⟦ Γ ⟧c ⟦ T ⟧t ⟦ S ⟧t (eval θ Γ (○ S) M) (eval (θ , S) Γ T N)
eval θ Γ .(○ A) (◦ {A} M) = ◦⁺ ⟦ θ ⟧c ⟦ A ⟧t ((eval ⊡ θ A M) ∘⁺ < ⊤dist⁻¹ ∘⁺ tt⁺ , (id⁺ ⟦ θ ⟧c) >⁺) ∘⁺ (π₁⁺ {⟦ Γ ⟧c} {○⁺ ⟦ θ ⟧c} )
eval θ Γ .(μ F) (inj {F} M) = (inj⁺ F) ∘⁺ (id⁺≡ (⟦⟧f-comp (tt , μ F) F tt) ∘⁺ eval θ Γ ([ tt , μ F ]p F) M)
eval θ Γ T (rec F M N) = (fold⁺ F ⟦ T ⟧t ((eval ⊡ (⊡ , [ tt , T ]p F) T N) ∘⁺ < (⊤dist⁻¹ ∘⁺ tt⁺) , < tt⁺ , id⁺≡ (sym (⟦⟧f-comp (tt , T) F tt)) >⁺ >⁺)) ∘⁺ (eval θ Γ (μ F) M)
eval θ Γ .([ tt , ν F ]p F) (out {F} M) = ((id⁺≡ (sym (⟦⟧f-comp (tt , ν F) F tt))) ∘⁺ (out⁺ F)) ∘⁺ (eval θ Γ (ν F) M)
eval θ Γ .(ν F) (unfold F {T} M N) = unfold⁺ F ⟦ T ⟧t (((id⁺≡ (⟦⟧f-comp (tt , T) F tt)) ∘⁺ (eval ⊡ (⊡ , T) ([ tt , T ]p F) N)) ∘⁺ < (⊤dist⁻¹ ∘⁺ tt⁺) , < tt⁺ , (id⁺ ⟦ T ⟧t) >⁺ >⁺) ∘⁺ eval θ Γ T M
eval θ Γ .(A ∧ B) (<_,_> {A} {B} M N) = < (eval θ Γ A M) , (eval θ Γ B N) >⁺
eval θ Γ .T (fst {T} {B} M) = π₁⁺ {⟦ B ⟧t} ∘⁺ eval θ Γ (T ∧ B) M
eval θ Γ .T (snd {B} {T} M) = π₂⁺ {⟦ B ⟧t} ∘⁺ eval θ Γ (B ∧ T) M
eval θ Γ .(A ∨ B) (inl {B} {A} M) = inj₁⁺ ⟦ B ⟧t ∘⁺ (eval θ Γ A M)
eval θ Γ .(A ∨ B) (inr {A} {B} M) = inj₂⁺ ⟦ A ⟧t ∘⁺ eval θ Γ B M
eval θ Γ T (case {A} {B} M N1 N2) =
    case⁺ (eval θ Γ (A ∨ B) M)
          (eval θ (Γ , A) T N1 ∘⁺ ∧⁺-assoc' (○⁺ ⟦ θ ⟧c) ⟦ Γ ⟧c ⟦ A ⟧t)
          (eval θ (Γ , B) T N2 ∘⁺ ∧⁺-assoc' (○⁺ ⟦ θ ⟧c) ⟦ Γ ⟧c ⟦ B ⟧t)
eval θ Γ .⊤ unit = tt⁺
