module lam where

data Maybe (A : Set) : Set where
 nothing : Maybe A
 just : A -> Maybe A

postulate
 world : Set
 _↪_ : world -> world -> Set
 ∅ : world
 sw : world -> world
 sl : (α : world) -> α ↪ (sw α) 
 name : world -> Set
 nameOf : {α β : world} -> α ↪ β -> name β
 imp : {α β : world} -> α ↪ β -> name α -> name β 
 export : {α β : world} -> α ↪ β -> name β -> Maybe (name α)

data Exp ψ : Set where
 var : name ψ -> Exp ψ
 ƛ : ∀ {φ} (y : ψ ↪ φ) -> Exp φ -> Exp ψ
 _·_ : Exp ψ -> Exp ψ -> Exp ψ

vsub : ∀ (ψ φ : world) -> Set
vsub ψ φ = name ψ -> name φ

sub : ∀ (ψ φ : world) -> Set
sub ψ φ = name ψ -> Exp φ

_∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
(g ∘ f) x = g (f x)

_×_//_ : ∀ {ψ χ φ ξ} -> vsub ψ φ -> φ ↪ ξ -> ψ ↪ χ -> vsub χ ξ
(σ × y // x) z with (export x z)
(σ × y // x) z | nothing = nameOf y
(σ × y // x) z | just y' = imp y (σ y')

[_] : ∀ {ψ φ} -> vsub ψ φ -> Exp ψ -> Exp φ
[ σ ] (var x) = var (σ x)
[_] {φ = φ} σ (ƛ y m) with sl φ
...                   | z =  ƛ z ([ σ × z // y ] m)
[ σ ] (m · n) = ([ σ ] m) · ([ σ ] n)

_×_/_ : ∀ {ψ χ φ ξ} -> sub ψ φ -> φ ↪ ξ -> ψ ↪ χ -> sub χ ξ
(σ × y / x) z with (export x z)
...           | nothing = var (nameOf y)
...           | just y' = [ imp y ] (σ y')

⟦_⟧ : ∀ {ψ φ} -> sub ψ φ -> Exp ψ -> Exp φ
⟦_⟧ σ (var y) = σ y
⟦_⟧ {φ = φ} σ (ƛ y m) with sl φ
...                   | z = ƛ z (⟦ σ × z / y ⟧ m)
⟦_⟧ σ (m · n) = ⟦ σ ⟧ m · ⟦ σ ⟧ n
 
