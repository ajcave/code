module lam where

data Maybe (A : Set) : Set where
 nothing : Maybe A
 just : A -> Maybe A

data _==_ {A : Set} (a : A) : A -> Set where
 refl : a == a

data _⊎_ (A B : Set) : Set where
 inl : (a : A) -> A ⊎ B
 inr : (b : B) -> A ⊎ B

postulate
 world : Set
 _↪_ : world -> world -> Set
 ∅ : world
 sw : world -> world
 sl : (α : world) -> α ↪ (sw α) 
 name : world -> Set
 ⌞_⌟ : {α β : world} -> α ↪ β -> name β
 ↑ : {α β : world} -> α ↪ β -> name α -> name β 
 export : {α β : world} -> α ↪ β -> name β -> Maybe (name α)

⇑ : {α β : world} -> {x : α ↪ β} -> name α -> name β
⇑ {x = x} y = ↑ x y

data cmpResult {α β} (x : α ↪ β) : name β -> Set where
 same : cmpResult x (⌞ x ⌟)
 diff : (y : name α) -> cmpResult x (↑ x y)

postulate
 cmp : {α β : world} -> (x : α ↪ β) -> ∀ y -> cmpResult x y

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
(σ × y // x) z | nothing = ⌞ y ⌟
(σ × y // x) z | just y' = ↑ y (σ y')

[_] : ∀ {ψ φ} -> vsub ψ φ -> Exp ψ -> Exp φ
[ σ ] (var x) = var (σ x)
[_] {φ = φ} σ (ƛ y m) with sl φ
...                   | z =  ƛ z ([ σ × z // y ] m)
[ σ ] (m · n) = ([ σ ] m) · ([ σ ] n)

_×_/_ : ∀ {ψ χ φ ξ} -> sub ψ φ -> φ ↪ ξ -> ψ ↪ χ -> sub χ ξ
(σ × y / x) z with (export x z)
...           | nothing = var (⌞ y ⌟)
...           | just y' = [ ↑ y ] (σ y')

⟦_⟧ : ∀ {ψ φ} -> sub ψ φ -> Exp ψ -> Exp φ
⟦_⟧ σ (var y) = σ y
⟦_⟧ {φ = φ} σ (ƛ y m) with sl φ
...                   | z = ƛ z (⟦ σ × z / y ⟧ m)
⟦_⟧ σ (m · n) = ⟦ σ ⟧ m · ⟦ σ ⟧ n
 
inst_view : ∀ {ψ} -> (∀ {ψ} -> Exp ψ -> Set) -> (M : Exp ψ) -> Set
inst_view {ψ} view M = {χ : world } -> (σ : vsub ψ χ) -> view ([ σ ] M)

data sview {ψ} : Exp ψ -> Set where
 var : ∀ x -> sview (var x)
 ƛ : ∀ {φ} -> (x : ψ ↪ φ) -> ∀ {m} -> inst_view sview m
           -> sview (ƛ x m)
 _·_ : ∀ {m n} -> inst_view sview m -> inst_view sview n
               -> sview (m · n)

… : ∀ {ψ} -> name ψ -> name ψ
… x = x

_,,_/_ : ∀ {ψ ψ' φ} -> vsub ψ φ -> name φ -> ψ ↪ ψ' -> vsub ψ' φ
(σ ,, y / x) z with (cmp x z)
(σ ,, y / x) .(⌞ x ⌟) | same = y
(σ ,, y / x) .(↑ x z) | diff z = σ z
--... | nothing = y
--... | just y' = σ y'

exch : ∀ {ψ φ χ} -> (x : ψ ↪ φ) -> (y : φ ↪ χ) -> vsub χ χ 
exch x y = ((((↑ y) ∘ (↑ x)) ∘ …) ,, (⌞ y ⌟) / x) ,, (↑ y (⌞ x ⌟)) / y

data nat : Set where
 z : nat
 s : nat -> nat

_+_ : nat -> nat -> nat
z + y = y
(s x) + y = s (x + y)

cnt : ∀ {ψ φ} -> {m : Exp φ} -> (M : sview m) -> (x : ψ ↪ φ) -> nat
cnt (var y) x        with (cmp x y) 
cnt (var .(⌞ x ⌟)) x | same   = s z
cnt (var .(⇑ y)) x   | diff y = z
cnt (ƛ y M) x = cnt (M (exch x y)) y
cnt (M · N) x = (cnt (M …) x) + (cnt (N …) x) 

-- Now we just need some crazy bananas for things like exchange
-- Seems like it may actually be an applicative functor

