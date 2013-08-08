module mltt where
open import FinMap
open import Unit
open import Product

* : Unitz
* = tt

-- Based on Catarina Coquand's "A realizability interpretation of Martin-Lof 's type theory"

-- Can we do this proof in e.g. Coq (i.e. without I-R) by using the trick of encoding IR as indexing?
-- Suspect we would need one more universe to do so

data tm (n : ctx Unit) : Set where
 ▹ : var n * -> tm n
 ƛ Π : (M : tm (n , *)) -> tm n
 _·_ : (M N : tm n) -> tm n
 tt ff bool set : tm n
 if : (M N P : tm n) -> tm n

[_]r : ∀ {n m} -> vsubst n m -> tm n -> tm m
[_]r σ (▹ x) = ▹ ([ σ ]v x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (Π M) = Π ([ vsub-ext σ ]r M)
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
[_]t σ (Π M) = Π ([ tsub-ext σ ]t M)
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