{-# OPTIONS --no-positivity-check --no-termination-check #-}
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

≤-refl : ∀ {n} -> n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {n m q} -> m ≤ q -> n ≤ m -> n ≤ q
≤-trans z≤n z≤n = z≤n
≤-trans (s≤s m≤n) z≤n = z≤n
≤-trans (s≤s m≤n) (s≤s m≤n') = s≤s (≤-trans m≤n m≤n')

data _≤ω_ : ω+1 -> ω+1 -> Set where
 inj₁ : ∀ {n m} -> (n≤m : n ≤ m) -> (▹ n) ≤ω (▹ m)
 inj₂ : ∀ {α} -> α ≤ω ω

≤ω-refl : ∀ {α} -> α ≤ω α
≤ω-refl {▹ n} = inj₁ ≤-refl
≤ω-refl {ω} = inj₂

_∘ω_ : ∀ {α β γ} (β≤ωγ : β ≤ω γ) (α≤ωβ : α ≤ω β) -> α ≤ω γ
inj₁ n≤m ∘ω inj₁ n≤m' = inj₁ (≤-trans n≤m n≤m') 
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

○₂-comp : ∀ (A : obj) {α β γ : ω+1} (β≤ωγ : β ≤ω γ) (α≤ωβ : α ≤ω β) x →
      ○₂ (A ₂) (β≤ωγ ∘ω α≤ωβ) x ≡ ○₂ (A ₂) α≤ωβ (○₂ (A ₂) β≤ωγ x)
○₂-comp A {▹ zero} {▹ zero} {▹ zero} (inj₁ n≤m) (inj₁ n≤m') x = refl
○₂-comp A {▹ zero} {▹ zero} {▹ (suc n)} (inj₁ n≤m) (inj₁ n≤m') x = refl
○₂-comp A {▹ zero} {▹ (suc n)} {▹ n0} (inj₁ n≤m) (inj₁ n≤m') x = refl
○₂-comp A {▹ (suc n)} {▹ zero} {▹ zero} (inj₁ n≤m) (inj₁ ()) x
○₂-comp A {▹ (suc n)} {▹ zero} {▹ (suc n')} (inj₁ n≤m) (inj₁ ()) x 
○₂-comp A {▹ (suc n)} {▹ (suc n')} {▹ zero} (inj₁ ()) (inj₁ (s≤s m≤n)) x
○₂-comp A {▹ (suc n)} {▹ (suc n')} {▹ (suc n0)} (inj₁ (s≤s m≤n)) (inj₁ (s≤s m≤n')) x = obj.fcomp A (inj₁ m≤n) (inj₁ m≤n') x
○₂-comp A {▹ n} {ω} {▹ n'} () α≤ωβ x
○₂-comp A {ω} {▹ n} {▹ n'} β≤ωγ () x
○₂-comp A {ω} {ω} {▹ n} () α≤ωβ x
○₂-comp A {▹ zero} {▹ zero} {ω} inj₂ (inj₁ n≤m) x = refl
○₂-comp A {▹ zero} {▹ (suc n)} {ω} inj₂ (inj₁ n≤m) x = refl
○₂-comp A {▹ (suc n)} {▹ zero} {ω} inj₂ (inj₁ ()) x
○₂-comp A {▹ (suc n)} {▹ (suc n')} {ω} inj₂ (inj₁ (s≤s m≤n)) x = obj.fcomp A inj₂ (inj₁ m≤n) x
○₂-comp A {ω} {▹ n} {ω} inj₂ () x
○₂-comp A {▹ zero} {ω} {ω} inj₂ inj₂ x = refl
○₂-comp A {▹ (suc n)} {ω} {ω} inj₂ inj₂ x = obj.fcomp A inj₂ inj₂ x
○₂-comp A {ω} {ω} {ω} inj₂ inj₂ x = obj.fcomp A inj₂ inj₂ x

○₂-id : ∀ (A : obj) {α : ω+1} x -> ○₂ (A ₂) (≤ω-refl {α}) x ≡ x
○₂-id A {▹ zero} x = refl
○₂-id A {▹ (suc n)} x = obj.fid A x
○₂-id A {ω} x = obj.fid A x

○⁺ : obj -> obj
○⁺ A = record {
        A = ○₁ (A ₁);
        ωmap = ○₂ (A ₂);
        fcomp = ○₂-comp A;
        fid = λ {α} x -> ○₂-id A {α} x
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

postulate
 yay : ∀ {a} {A : Set a} -> A

mutual
 data ν₁ (F : obj -> obj) (α : ω+1) : Set where
  ⟨_⟩ : ∞ (((F (ν⁺ F)) ₁) α) -> ν₁ F α
 
-- data bisim (F : obj -> obj) (α : ω+1) : ν₁ F α -> ν₁ F α -> Set where
--  in : ∞ 

 ν⁺ : ∀ (F : obj -> obj) -> obj
 ν⁺ F = record { A = ν₁ F; ωmap = νωmap; fcomp = yay; fid = yay }
  where νωmap : {β α : ω+1} → β ≤ω α → ν₁ F α → ν₁ F β
        νωmap β≤ωα ⟨ y ⟩ = ⟨ (♯ (F (ν⁺ F) ₂) β≤ωα (♭ y)) ⟩

 -- TODO: ugly bisimilation and stuff
--postulate
-- νcomp : {α β γ : ω+1} (β≤ωγ : β ≤ω γ) (α≤ωβ : α ≤ω β) (x : ν₁ F γ) → νωmap (β≤ωγ ∘ω α≤ωβ) x ≡ νωmap α≤ωβ (νωmap β≤ωγ x)

mutual
 data μ₁ (F : obj -> obj) (α : ω+1) : Set where
  ⟨_⟩ : ((F (μ⁺ F)) ₁) α -> μ₁ F α

 μ⁺ : ∀ (F : obj -> obj) -> obj
 μ⁺ F = record { A = μ₁ F; ωmap = μωmap; fcomp = μcomp; fid = μid }
  where μωmap : {β α : ω+1} → β ≤ω α → μ₁ F α → μ₁ F β
        μωmap β≤ωα ⟨ y ⟩ = ⟨ ((F (μ⁺ F) ₂) β≤ωα y) ⟩
        μcomp : {α β γ : ω+1} (β≤ωγ : β ≤ω γ) (α≤ωβ : α ≤ω β) (x : μ₁ F γ) → μωmap (β≤ωγ ∘ω α≤ωβ) x ≡ μωmap α≤ωβ (μωmap β≤ωγ x)
        μcomp β≤ωγ α≤ωβ ⟨ y ⟩ = cong ⟨_⟩ (obj.fcomp (F (μ⁺ F)) β≤ωγ α≤ωβ y)
        μid : {α : ω+1} (x : μ₁ F α) → μωmap ≤ω-refl x ≡ x
        μid ⟨ y ⟩ = cong ⟨_⟩ (obj.fid (F (μ⁺ F)) y)

mutual
 ⟦_⟧f : ∀ {Δ} -> functor Δ -> (ρ : gksubst Δ obj) -> obj
 ⟦_⟧f (▹ A) ρ = lookup ρ A
 ⟦_⟧f (μ F) ρ = μ⁺ (λ X -> ⟦ F ⟧f (ρ , X))
 ⟦_⟧f (ν F) ρ = ν⁺ (λ X -> ⟦ F ⟧f (ρ , X))
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

-- Could generalize this with arrow in mu-ltl
data arrow1 : ∀ {Δ} -> (ρ1 : gksubst Δ obj) -> (ρ2 : gksubst Δ obj) -> Set₁ where
 ⊡ : arrow1 tt tt
 _,_ : ∀ {Δ} {ρ1 ρ2 : gksubst Δ obj} (σ : arrow1 ρ1 ρ2) {A B} (N : A ⇒ B) -> arrow1 {Δ , #prop} (ρ1 , A) (ρ2 , B)

arrow-lookup1 : ∀ {ζ} {σ1 σ2 : gksubst ζ obj} (θ : arrow1 σ1 σ2) (A : var ζ #prop) -> ([ σ1 ]v A) ⇒ ([ σ2 ]v A)
arrow-lookup1 ⊡ ()
arrow-lookup1 (σ , N) top = N
arrow-lookup1 (σ , N) (pop y) = arrow-lookup1 σ y

id-arrow : ∀ {Δ} (ρ : gksubst Δ obj) -> arrow1 ρ ρ
id-arrow {⊡} tt = ⊡
id-arrow {ψ , T} (ρ , C) = (id-arrow ρ) , (id⁺ C)

_∧̂⁺_ : ∀ {A1 A2 B1 B2} -> A1 ⇒ A2 -> B1 ⇒ B2 -> (A1 ∧⁺ B1) ⇒ (A2 ∧⁺ B2)
_∧̂⁺_ {A1} {A2} {B1} {B2} f g = < (f ∘⁺ π₁⁺ {B1}) , (g ∘⁺ π₂⁺ {A1}) >⁺

_∨̂⁺_ : ∀ {A1 A2 B1 B2} -> A1 ⇒ A2 -> B1 ⇒ B2 -> (A1 ∨⁺ B1) ⇒ (A2 ∨⁺ B2)
_∨̂⁺_ {A1} {A2} {B1} {B2} f g = [ ((inj₁⁺ B2) ∘⁺ f) , ((inj₂⁺ A2) ∘⁺ g) ]⁺

_⊃̂⁺_ : ∀ A {B1 B2} -> B1 ⇒ B2 -> (A ⊃⁺ B1) ⇒ (A ⊃⁺ B2)
_⊃̂⁺_ A {B1} {B2} f = λ⁺ (f ∘⁺ (π₁⁺ {A} ·⁺ π₂⁺ {A ⊃⁺ B1}))

inj⁺' : ∀ {Δ} (F : functor (Δ , #prop)) ρ -> ⟦ F ⟧f (ρ , ⟦ μ F ⟧f ρ) ⇒ ⟦ μ F ⟧f ρ
inj⁺' F ρ = record {
     η = λ α x → ⟨ x ⟩;
     natural = λ β≤ωα x → refl
   }

inj⁺ : ∀ F -> ⟦ F ⟧f (tt , ⟦ μ F ⟧t) ⇒ ⟦ μ F ⟧t
inj⁺ F = inj⁺' F tt

out⁺' : ∀ {Δ} (F : functor (Δ , #prop)) ρ -> ⟦ ν F ⟧f ρ ⇒ ⟦ F ⟧f (ρ , ⟦ ν F ⟧f ρ)
out⁺' F ρ = record {
     η = λ α -> (λ {⟨ y ⟩ → ♭ y });
     natural = λ β≤ωα → λ {⟨ y ⟩ → refl}
   }

out⁺ : ∀ F -> ⟦ ν F ⟧t ⇒ ⟦ F ⟧f (tt , ⟦ ν F ⟧t)
out⁺ F = out⁺' F tt

mutual
 fmap : ∀ {Δ} (F : functor Δ) ρ1 ρ2 -> (σ : arrow1 ρ1 ρ2) -> (⟦ F ⟧f ρ1) ⇒ (⟦ F ⟧f ρ2)
 fmap (▹ A) ρ1 ρ2 σ = arrow-lookup1 σ A
 fmap (μ F) ρ1 ρ2 σ = fold⁺' F (⟦ μ F ⟧f ρ2) ρ1 ((inj⁺' F ρ2) ∘⁺ (fmap F (ρ1 , ⟦ μ F ⟧f ρ2) (ρ2 , ⟦ μ F ⟧f ρ2) (σ , (id⁺ (⟦ μ F ⟧f ρ2)))))
 fmap (ν F) ρ1 ρ2 σ = unfold⁺' F (⟦ ν F ⟧f ρ1) ρ2 ((fmap F (ρ1 , ⟦ ν F ⟧f ρ1) (ρ2 , ⟦ ν F ⟧f ρ1) (σ , id⁺ (⟦ ν F ⟧f ρ1))) ∘⁺ (out⁺' F ρ1))
 fmap (○ A) ρ1 ρ2 σ = ◦⁺ (⟦ A ⟧f ρ1) (⟦ A ⟧f ρ2) (fmap A ρ1 ρ2 σ)
 fmap (A ⊃ B) ρ1 ρ2 σ = ⟦ A ⟧t ⊃̂⁺ fmap B ρ1 ρ2 σ
 fmap (A ∧ B) ρ1 ρ2 σ = (fmap A ρ1 ρ2 σ) ∧̂⁺ (fmap B ρ1 ρ2 σ)
 fmap (A ∨ B) ρ1 ρ2 σ = (fmap A ρ1 ρ2 σ) ∨̂⁺ (fmap B ρ1 ρ2 σ)
 fmap ⊤ ρ1 ρ2 σ = tt⁺

 fold⁺' : ∀ {Δ} (F : functor (Δ , #prop)) C ρ -> ⟦ F ⟧f (ρ , C) ⇒ C -> ⟦ μ F ⟧f ρ ⇒ C
 fold⁺' F C ρ (f , nf) = record {
     η = fold₁';
     natural = fold₁nat'
  }
  where fold₁' : ((⟦ μ F ⟧f ρ) ₁) ⇒₁ (C ₁)
        fold₁' α ⟨ y ⟩ = f α (_⇒_.η (fmap F (ρ , ⟦ μ F ⟧f ρ) (ρ , C) (id-arrow ρ , fold⁺' F C ρ (f , nf))) α y)
        fold₁nat' : {α β : ω+1} (β≤ωα : β ≤ω α) (x : ((⟦ μ F ⟧f ρ) ₁) α) → fold₁' β (((⟦ μ F ⟧f ρ) ₂) β≤ωα x) ≡ ((C ₂) β≤ωα (fold₁' α x))
        fold₁nat' β≤α ⟨ y ⟩ = trans
              (cong (f _) (_⇒_.natural (fmap F (ρ , ⟦ μ F ⟧f ρ) (ρ , C) (id-arrow ρ , fold⁺' F C ρ (f , nf))) β≤α y))
              (nf β≤α (_⇒_.η (fmap F (ρ , ⟦ μ F ⟧f ρ) (ρ , C) ((id-arrow ρ) , (fold⁺' F C ρ (f , nf)))) _ y))

 fold⁺ : ∀ F C -> ⟦ F ⟧f (tt , C) ⇒ C -> ⟦ μ F ⟧t ⇒ C
 fold⁺ F C f = fold⁺' F C tt f

 unfold⁺' : ∀ {Δ} (F : functor (Δ , #prop)) C ρ -> C ⇒ ⟦ F ⟧f (ρ , C) -> C ⇒ ⟦ ν F ⟧f ρ
 unfold⁺' F C ρ (f , nf) = record {
     η = unfold₁';
     natural = yay --unfold₁nat'
  }
  where unfold₁' : (C ₁) ⇒₁ ((⟦ ν F ⟧f ρ) ₁)
        unfold₁' α c = ⟨ ♯ _⇒_.η (fmap F (ρ , C) (ρ , ⟦ ν F ⟧f ρ) (id-arrow ρ , unfold⁺' F C ρ (f , nf))) α (f α c) ⟩

 unfold⁺ : ∀ F C -> C ⇒ ⟦ F ⟧f (tt , C) -> C ⇒ ⟦ ν F ⟧t
 unfold⁺ F C f = unfold⁺' F C tt f

-- TODO: Move into FinMap

lem3v : ∀ {a b} {A : Set a} {F : A -> Set b} {Δ1 Δ2} (σ : vsubst {a} {A} Δ2 Δ1) (ρ : gsubst Δ1 F) {T} (X : F T) -> (ρ , X) ⁌ (vsub-ext σ) ≡ (ρ ⁌ σ) , X
lem3v σ ρ X = cong (λ α → α , X)
    (begin
      ((ρ , X) ⁌ (wkn σ)) ≡⟨ (gmap-funct σ) ⟩
      ((ρ ⁌ σ)
    ∎))

-- Perhaps a simpler lemma:
--lem3v' : ∀ {a b} {A : Set a} {F : A -> Set b} {Δ1 Δ2} (σ : vsubst {a} {A} Δ2 Δ1) (ρ : gsubst Δ1 F) {T} (X : F T) -> (wkn-vsub ◆ σ) ⁌ (ρ , X) ≡ (ρ ⁌ σ)
--lem3v' σ ρ X = ?

mutual
 lem4 : ∀ {Δ1 Δ2} (σ : vsub Δ1 Δ2) F ρ X -> ⟦ [ vsub-ext σ ]pv F ⟧f (ρ , X) ≡ ⟦ F ⟧f ((ρ ⁌ σ) , X)
 lem4 σ F ρ X = begin (
          ⟦ [ vsub-ext σ ]pv F ⟧f (ρ , X)) ≡⟨ (⟦⟧f-compv (vsub-ext σ) F (ρ , X)) ⟩
          ⟦ F ⟧f ((ρ , X) ⁌ vsub-ext σ)    ≡⟨ (cong ⟦ F ⟧f (lem3v σ ρ X)) ⟩
          ⟦ F ⟧f ((ρ ⁌ σ) , X)
        ∎

 ⟦⟧f-compv : ∀ {Δ1 Δ2} (σ : vsub Δ1 Δ2) F ρ -> ⟦ [ σ ]pv F ⟧f ρ ≡ ⟦ F ⟧f (ρ ⁌ σ)
 ⟦⟧f-compv σ (▹ A) ρ = sym (lookup-gmap (lookup ρ) σ A)
 ⟦⟧f-compv σ (μ F) ρ = cong μ⁺ (funext (lem4 σ F ρ))
 ⟦⟧f-compv σ (ν F) ρ = cong ν⁺ (funext (lem4 σ F ρ))
 ⟦⟧f-compv σ (○ A) ρ = cong ○⁺ (⟦⟧f-compv σ A ρ)
 ⟦⟧f-compv σ (A ⊃ B) ρ = cong (_⊃⁺_ ⟦ A ⟧t) (⟦⟧f-compv σ B ρ)
 ⟦⟧f-compv σ (A ∧ B) ρ = cong₂ _∧⁺_ (⟦⟧f-compv σ A ρ) (⟦⟧f-compv σ B ρ)
 ⟦⟧f-compv σ (A ∨ B) ρ = cong₂ _∨⁺_ (⟦⟧f-compv σ A ρ) (⟦⟧f-compv σ B ρ)
 ⟦⟧f-compv σ ⊤ ρ = refl

_⋆_ : ∀ {Δ1 Δ2} (σ : psub Δ1 Δ2) (ρ : gksubst Δ1 obj) -> gksubst Δ2 obj
σ ⋆ ρ = gmap (λ C -> ⟦ C ⟧f ρ) σ

lem3 : ∀ {Δ1 Δ2} (σ : psub Δ1 Δ2) (ρ : gksubst Δ1 obj) X -> (psub-ext σ) ⋆ (ρ , X) ≡ (σ ⋆ ρ) , X
lem3 σ ρ X = cong (λ α -> α , X)
              (begin
                ((wkn-vsub ◆ σ) ⋆ (ρ , X))                       ≡⟨ (gmap-funct σ) ⟩
                ((gmap (λ C → ⟦ [ wkn-vsub ]pv C ⟧f (ρ , X)) σ)   ≡⟨ gmap-cong (λ C → ⟦⟧f-compv wkn-vsub C (ρ , X)) ⟩
                (gmap (λ C → ⟦ C ⟧f ((ρ , X) ⁌ wkn-vsub)) σ)      ≡⟨ gmap-cong (λ C → cong ⟦ C ⟧f (gmap-funct id-vsub)) ⟩
                (gmap (λ C → ⟦ C ⟧f (ρ ⁌ id-vsub)) σ)             ≡⟨ gmap-cong (λ C → cong ⟦ C ⟧f (id-v-right ρ)) ⟩
                (gmap (λ C → ⟦ C ⟧f ρ) σ
              ∎)))

mutual
 lem5 : ∀ {Δ1 Δ2} (σ : psub Δ1 Δ2) F ρ X -> ⟦ [ psub-ext σ ]p F ⟧f (ρ , X) ≡ ⟦ F ⟧f ((σ ⋆ ρ) , X)
 lem5 σ F ρ X = begin
            ⟦ [ psub-ext σ ]p F ⟧f (ρ , X)     ≡⟨ ⟦⟧f-comp (psub-ext σ) F (ρ , X) ⟩
            ⟦ F ⟧f ((psub-ext σ) ⋆ (ρ , X))    ≡⟨ cong ⟦ F ⟧f (lem3 σ ρ X) ⟩
            ⟦ F ⟧f ((σ ⋆ ρ) , X)
          ∎

 ⟦⟧f-comp : ∀ {Δ1 Δ2} (σ : psub Δ1 Δ2) F ρ -> ⟦ [ σ ]p F ⟧f ρ ≡ ⟦ F ⟧f (σ ⋆ ρ)
 ⟦⟧f-comp σ (▹ A) ρ = sym (lookup-gmap (λ x → ⟦ x ⟧f ρ) σ A)
 ⟦⟧f-comp σ (μ F) ρ = cong μ⁺ (funext (lem5 σ F ρ))
 ⟦⟧f-comp σ (ν F) ρ = cong ν⁺ (funext (lem5 σ F ρ))
 ⟦⟧f-comp σ (○ A) ρ = cong ○⁺ (⟦⟧f-comp σ A ρ)
 ⟦⟧f-comp σ (A ⊃ B) ρ = cong (_⊃⁺_ ⟦ A ⟧t) (⟦⟧f-comp σ B ρ)
 ⟦⟧f-comp σ (A ∧ B) ρ = cong₂ _∧⁺_ (⟦⟧f-comp σ A ρ) (⟦⟧f-comp σ B ρ)
 ⟦⟧f-comp σ (A ∨ B) ρ = cong₂ _∨⁺_ (⟦⟧f-comp σ A ρ) (⟦⟧f-comp σ B ρ)
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
