module mltt where
open import FinMap
open import Unit
open import Data.Product hiding (_×_)
open import Product

* : Unitz
* = tt

-- Based on Catarina Coquand's "A realizability interpretation of Martin-Lof 's type theory"

-- Can we do this proof in e.g. Coq (i.e. without I-R) by using the trick of encoding IR as indexing?
-- Suspect we would need one more universe to do so

data tm (n : ctx Unit) : Set where
 ▹ : var n * -> tm n
 ƛ : (M : tm (n , *)) -> tm n
 Π : (A : tm n) -> (B : tm (n , *)) -> tm n
 _·_ : (M N : tm n) -> tm n
 tt ff bool set : tm n
 if : (M N P : tm n) -> tm n

[_]r : ∀ {n m} -> vsubst n m -> tm n -> tm m
[_]r σ (▹ x) = ▹ ([ σ ]v x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (Π A B) = Π ([ σ ]r A) ([ vsub-ext σ ]r B)
[_]r σ (M · M₁) = ([ σ ]r M) · ([ σ ]r M₁)
[_]r σ tt = tt
[_]r σ ff = ff
[_]r σ bool = bool
[_]r σ set = set
[_]r σ (if M M₁ M₂) = if ([ σ ]r M) ([ σ ]r M₁) ([ σ ]r M₂)

tsubst : ∀ (n m : ctx Unit) -> Set
tsubst n m = gksubst n (tm m)

tsub-ext : ∀ {n m} -> tsubst n m -> tsubst (n , *) (m , *)
tsub-ext σ = (gmap [ wkn-vsub ]r σ) , (▹ top)

id-tsub : ∀ {n} -> tsubst n n
id-tsub {⊡} = tt
id-tsub {n , T} = tsub-ext id-tsub

[_]t : ∀ {n m} -> tsubst n m -> tm n -> tm m
[_]t σ (▹ x) = [ σ ]v x
[_]t σ (ƛ M) = ƛ ([ tsub-ext σ ]t M)
[_]t σ (Π A B) = Π ([ σ ]t A) ([ tsub-ext σ ]t B)
[_]t σ (M · M₁) = ([ σ ]t M) · ([ σ ]t M₁)
[_]t σ tt = tt
[_]t σ ff = ff
[_]t σ bool = bool
[_]t σ set = set
[_]t σ (if M M₁ M₂) = if ([ σ ]t M) ([ σ ]t M₁) ([ σ ]t M₂)


[_/x] : ∀ {n} -> tm n -> tm (n , *) -> tm n
[ M /x] N = [ id-tsub , M ]t N

data _⟶_ {n} : ∀ (M N : tm n) -> Set where
 β : ∀ M N -> ((ƛ M) · N) ⟶ [ N /x] M
 if1 : ∀ M N -> if tt M N ⟶ M
 if2 : ∀ M N -> if ff M N ⟶ N
 app1 : ∀ {M M' N} -> M ⟶ M' -> (M · N) ⟶ (M' · N)
 ifc : ∀ {M M' N1 N2} -> M ⟶ M' -> if M N1 N2 ⟶ if M' N1 N2

data _⟶*_ {n} : ∀ (M N : tm n) -> Set where
 refl : ∀ {M} -> M ⟶* M
 trans1 : ∀ {M N P} -> M ⟶ N -> N ⟶* P -> M ⟶* P

⟶*-trans : ∀ {n} {M N P : tm n} -> M ⟶* N -> N ⟶* P -> M ⟶* P
⟶*-trans refl s2 = s2
⟶*-trans (trans1 x s1) s2 = trans1 x (⟶*-trans s1 s2)

data neutral {n} : tm n -> Set where
 ▹ : ∀ x -> neutral (▹ x)
 _·_ : ∀ M N -> neutral (M · N)
 if : ∀ M N P -> neutral (if M N P) 

data normal-bool {n} : tm n -> Set where
 tt : normal-bool tt
 ff : normal-bool ff
 neut : ∀ M -> neutral M -> normal-bool M

mutual
 data Ψ {n} : tm n -> Set where
  bool : Ψ bool
  Π : ∀ {A B} -> (p : Ψ A) -> (∀ a -> ψ p a -> Ψ ([ a /x] B)) -> Ψ (Π A B)
  neut : ∀ A -> neutral A -> Ψ A
  closed : ∀ {A B} -> A ⟶* B -> Ψ B -> Ψ A

 ψ : ∀ {n} -> {A : tm n} -> Ψ A -> tm n -> Set
 ψ bool a = ∃ (λ b → (a ⟶* b) × normal-bool b)
 ψ (Π p f) a = ∀ b (q : ψ p b) → ψ (f b q) (a · b)
 ψ (neut A x) a = ∃ (λ b → (a ⟶* b) × neutral b)
 ψ (closed x p) a = ψ p a