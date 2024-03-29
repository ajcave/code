module mltt-wh where
open import FinMap
open import Unit
open import Data.Product hiding (_×_)
open import Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty

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
 β : ∀ {M N} -> ((ƛ M) · N) ⟶ [ N /x] M
 if1 : ∀ {M N} -> if tt M N ⟶ M
 if2 : ∀ {M N} -> if ff M N ⟶ N
 app1 : ∀ {M M' N} -> M ⟶ M' -> (M · N) ⟶ (M' · N)
-- app2 : ∀ {M N N'} -> N ⟶ N' -> (M · N) ⟶ (M · N')
 ifc : ∀ {M M' N1 N2} -> M ⟶ M' -> if M N1 N2 ⟶ if M' N1 N2

data _⟶*_ {n} : ∀ (M N : tm n) -> Set where
 refl : ∀ {M} -> M ⟶* M
 trans1 : ∀ {M N P} -> M ⟶ N -> N ⟶* P -> M ⟶* P

⟶*-trans : ∀ {n} {M N P : tm n} -> M ⟶* N -> N ⟶* P -> M ⟶* P
⟶*-trans refl s2 = s2
⟶*-trans (trans1 x s1) s2 = trans1 x (⟶*-trans s1 s2)

trans1r : ∀ {n} {M N P : tm n} -> M ⟶* N -> N ⟶ P -> M ⟶* P
trans1r s t = ⟶*-trans s (trans1 t refl)

app1* : ∀ {n} {M M' N : tm n} -> M ⟶* M' -> (M · N) ⟶* (M' · N)
app1* refl = refl
app1* (trans1 x s) = trans1 (app1 x) (app1* s)

{-app2* : ∀ {n} {M M' N : tm n} -> M ⟶* M' -> (N · M) ⟶* (N · M')
app2* refl = refl
app2* (trans1 x s) = trans1 (app2 x) (app2* s) -}

if* : ∀ {n} {M M' N1 N2 : tm n} -> M ⟶* M' -> (if M N1 N2) ⟶* (if M' N1 N2)
if* refl = refl
if* (trans1 x t) = trans1 (ifc x) (if* t)

mutual
 data neutral {n} : tm n -> Set where
  ▹ : ∀ x -> neutral (▹ x)
  _·_ : ∀ {M N} -> neutral M {- -> normal N -} -> neutral (M · N)
  if : ∀ {M N P} -> neutral M {- -> normal N -> normal P -} -> neutral (if M N P) 

 data normal {n} : tm n -> Set where
  ƛ : ∀ {M} {- -> normal M -} -> normal (ƛ M)
  Π : ∀ {A B} {--> normal A -> normal B -} -> normal (Π A B)
  tt : normal tt
  ff : normal ff
  bool : normal bool
  set : normal set
  neut : ∀ {M} -> neutral M -> normal M

data normal-bool {n} : tm n -> Set where
 tt : normal-bool tt
 ff : normal-bool ff
 neut : ∀ {M} -> neutral M -> normal-bool M

data normalizable {n} (M : tm n) : Set where
 norm : ∀ {N} -> M ⟶* N -> normal N -> normalizable M

-- Can I just use "normal" and get rid of normal-bool?
normal-bool-normal : ∀ {n} {M : tm n} -> normal-bool M -> normal M
normal-bool-normal tt = tt
normal-bool-normal ff = ff
normal-bool-normal (neut x) = neut x

normalizable-closed : ∀ {n} {M N : tm n} -> M ⟶* N -> normalizable N -> normalizable M
normalizable-closed p (norm q r) = norm (⟶*-trans p q) r

mutual
 data Ψ {n} : tm n -> Set where
  bool : Ψ bool
  Π : ∀ {A B} -> (p : Ψ A) -> (∀ a -> ψ p a -> Ψ ([ a /x] B)) -> Ψ (Π A B)
  neut : ∀ {A} -> neutral A -> Ψ A
  closed : ∀ {A B} -> A ⟶ B -> Ψ B -> Ψ A

 ψ : ∀ {n} -> {A : tm n} -> Ψ A -> tm n -> Set
 ψ bool a = ∃ (λ b → (a ⟶* b) × normal-bool b)
 ψ (Π p f) a = (normalizable a) × (∀ b (q : ψ p b) → ψ (f b q) (a · b))
 ψ (neut x) a = ∃ (λ b → (a ⟶* b) × neutral b)
 ψ (closed x p) a = ψ p a

Ψ-closed⟶* : ∀ {n} {A B : tm n} -> A ⟶* B -> Ψ B -> Ψ A
Ψ-closed⟶* refl t = t
Ψ-closed⟶* (trans1 x s) t = closed x (Ψ-closed⟶* s t)

ψ-closed : ∀ {n} {A : tm n} {M N} -> (p : Ψ A) -> M ⟶* N -> ψ p N -> ψ p M
ψ-closed bool s (t1 , (s2 , n)) = t1 , ((⟶*-trans s s2) , n)
ψ-closed (Π p x) s (h , t) = normalizable-closed s h , λ b q → ψ-closed (x b q) (app1* s) (t b q)
ψ-closed (neut x) s (t1 , (s2 , neu)) = t1 , ((⟶*-trans s s2) , neu)
ψ-closed (closed x p) s t = ψ-closed p s t

data _≈_ {n} (a b : tm n) : Set where
 common : ∀ {d} -> (a ⟶* d) -> (b ⟶* d) -> a ≈ b

postulate
 sub⟶* : ∀ {n m} (σ : tsubst n m) {M N} -> M ⟶* N -> [ σ ]t M ⟶* [ σ ]t N
 sub⟶*2 : ∀ {n m} {M N : tm m} {σ : tsubst n m} -> M ⟶* N -> ∀ (P : tm (n , *)) -> [ σ , M ]t P ⟶* [ σ , N ]t P
 subeq3 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ ]t M ≡ [ σ , N ]t ([ wkn-vsub ]r M)
 subeq1 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ , ([ σ ]t N) ]t M ≡ [ σ ]t ([ N /x] M) 
 subeq2 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ , N ]t M ≡ [ id-tsub , N ]t ([ tsub-ext σ ]t M)
 subeq4 : ∀ {n} {M : tm n} -> [ id-tsub ]t M ≡ M

⟶*cong2 : ∀ {n} {M1 M2 N1 N2 : tm n} -> M1 ≡ M2 -> N1 ≡ N2 -> M1 ⟶* N1 -> M2 ⟶* N2
⟶*cong2 refl refl t = t

postulate
 cr : ∀ {n} {a b c : tm n} -> a ⟶* b -> a ⟶* c -> b ≈ c

data pi-inj1-res {n} (A : tm n) B : (C : tm n) -> Set where
 yep : ∀ {A' B'} -> A ⟶* A' -> B ⟶* B' -> pi-inj1-res A B (Π A' B')

pi-inj1 : ∀ {n} {A : tm n} {B C} -> (Π A B) ⟶* C -> pi-inj1-res A B C
pi-inj1 refl = yep refl refl
pi-inj1 (trans1 () s) -- More generally...

pi-inj2 : ∀ {n} {A A' : tm n} {B B'} -> (Π A B) ≈ (Π A' B') -> A ≈ A'
pi-inj2 (common x x₁) with pi-inj1 x | pi-inj1 x₁
pi-inj2 (common x x₁) | yep x₂ x₃ | yep x₄ x₅ = common x₂ x₄

pi-inj3 : ∀ {n} {A A' : tm n} {B B'} -> (Π A B) ≈ (Π A' B') -> B ≈ B'
pi-inj3 (common x x₁) with pi-inj1 x | pi-inj1 x₁
... | yep t1 t2 | yep t3 t4 = common t2 t4

[]-cong : ∀ {n m} {A B : tm n} {σ : tsubst n m} -> A ≈ B -> [ σ ]t A ≈ [ σ ]t B
[]-cong (common x x₁) = common (sub⟶* _ x) (sub⟶* _ x₁)

≈-trans : ∀ {n} {A B C : tm n} -> A ≈ B -> B ≈ C -> A ≈ C
≈-trans (common t1 t2) (common t3 t4) with cr t2 t3
... | common t5 t6 = common (⟶*-trans t1 t5) (⟶*-trans t4 t6)

≈-sym : ∀ {n} {A B : tm n} -> A ≈ B -> B ≈ A
≈-sym (common t1 t2) = common t2 t1

≈-refl : ∀ {n} {A : tm n} -> A ≈ A
≈-refl = common refl refl

⟶-≈ : ∀ {n} {A B : tm n} -> A ⟶ B -> A ≈ B
⟶-≈ t = common (trans1 t refl) refl

⟶≈trans : ∀ {n} {A B C : tm n} -> A ≈ B -> B ⟶ C -> A ≈ C
⟶≈trans t u = ≈-trans t (⟶-≈ u)

⟶≈trans' : ∀ {n} {A B C : tm n} -> A ≈ B -> A ⟶ C -> C ≈ B
⟶≈trans' t u = ≈-trans (≈-sym (⟶-≈ u)) t

neutral-step : ∀ {n} {C : Set} {A B : tm n} -> neutral A -> A ⟶ B -> C
neutral-step (▹ x) ()
neutral-step (_·_ ()) β
neutral-step (_·_ t) (app1 s) = neutral-step t s
neutral-step (if ()) if1
neutral-step (if ()) if2
neutral-step (if t) (ifc s) = neutral-step t s

neutral-step* : ∀ {n} {A B : tm n} -> neutral A -> A ⟶* B -> A ≡ B
neutral-step* t refl = refl
neutral-step* t (trans1 x s) = neutral-step t x

normal-step : ∀ {n} {A B : tm n} {C : Set} -> normal A -> A ⟶ B -> C
normal-step ƛ ()
normal-step Π ()
normal-step tt ()
normal-step ff ()
normal-step bool ()
normal-step set ()
normal-step (neut x) s = neutral-step x s

normal-step* : ∀ {n} {A B : tm n} -> normal A -> A ⟶* B -> A ≡ B
normal-step* t refl = refl
normal-step* t (trans1 x s) = normal-step t x

bool-≈-neutral : ∀ {n} {A : tm n} {C : Set} -> neutral A -> bool ≈ A -> C
bool-≈-neutral t (common x x₁) with normal-step* bool x | neutral-step* t x₁
bool-≈-neutral () (common x x₁) | refl | refl

set-≈-neutral : ∀ {n} {A : tm n} {C : Set} -> neutral A -> set ≈ A -> C
set-≈-neutral t (common x x₁) with normal-step* set x | neutral-step* t x₁
set-≈-neutral () (common x x₁) | refl | refl

bool≈Π : ∀ {n} {A : tm n} {B} {C : Set} -> bool ≈ (Π A B) -> C
bool≈Π (common x x₁) with normal-step* bool x | pi-inj1 x₁
bool≈Π (common x x₁) | refl | ()

Π≈neutral : ∀ {n} {A : tm n} {B D} {C : Set} -> neutral A -> (Π B D) ≈ A -> C
Π≈neutral t (common x x₁) with neutral-step* t x₁ | pi-inj1 x
Π≈neutral () (common x x₁) | refl | yep x₂ x₃

set≈Π : ∀ {n} {A : tm n} {B} {C : Set} -> set ≈ (Π A B) -> C
set≈Π (common x x₁) with normal-step* set x | pi-inj1 x₁
set≈Π (common x x₁) | refl | ()

bool≈set : ∀ {n} {C : Set} -> _≈_ {n} bool set -> C
bool≈set (common x x₁) with normal-step* bool x | normal-step* set x₁
bool≈set (common x x₁) | refl | ()

mutual
 lemma3-3 : ∀ {n} {A B M : tm n} (p : Ψ A) (q : Ψ B) -> A ≈ B -> ψ p M -> ψ q M
 lemma3-3 (closed x p) q t r = lemma3-3 p q (⟶≈trans' t x) r
 lemma3-3 p (closed x q) t r = lemma3-3 p q (⟶≈trans t x) r
 lemma3-3 bool bool t r = r
 lemma3-3 bool (Π q x) t r = bool≈Π t
 lemma3-3 bool (neut x) t r = bool-≈-neutral x t
 lemma3-3 (Π p x) bool t r = bool≈Π (≈-sym t)
 lemma3-3 (Π p x) (Π q x₁) t (r1 , r2) = r1 , (λ b q₁ → lemma3-3 (x b (lemma3-3b p q (pi-inj2 t) q₁)) (x₁ b q₁) ([]-cong (pi-inj3 t)) (r2 b (lemma3-3b p q (pi-inj2 t) q₁)))
 lemma3-3 (Π p x) (neut x₁) t r = Π≈neutral x₁ t
 lemma3-3 (neut x) bool t r = bool-≈-neutral x (≈-sym t)
 lemma3-3 (neut x) (Π q x₁) t r = Π≈neutral x (≈-sym t)
 lemma3-3 (neut x) (neut x₁) t r = r

 lemma3-3b : ∀ {n} {A B M : tm n} (p : Ψ A) (q : Ψ B) -> A ≈ B -> ψ q M -> ψ p M
 lemma3-3b (closed x p) q t r = lemma3-3b p q (⟶≈trans' t x) r 
 lemma3-3b p (closed x q) t r = lemma3-3b p q (⟶≈trans t x) r
 lemma3-3b bool bool t r = r
 lemma3-3b bool (Π q x) t r = bool≈Π t
 lemma3-3b bool (neut x) t r = bool-≈-neutral x t
 lemma3-3b (Π p x) bool t r = bool≈Π (≈-sym t)
 lemma3-3b (Π p x) (Π q x₁) t (r1 , r2) = r1 , (λ b q₁ → lemma3-3b (x b q₁) (x₁ b (lemma3-3 p q (pi-inj2 t) q₁)) ([]-cong (pi-inj3 t)) (r2 b (lemma3-3 p q (pi-inj2 t) q₁)))
 lemma3-3b (Π p x) (neut x₁) t r = Π≈neutral x₁ t
 lemma3-3b (neut x) bool t r = bool-≈-neutral x (≈-sym t)
 lemma3-3b (neut x) (Π q x₁) t r = Π≈neutral x (≈-sym t)
 lemma3-3b (neut x) (neut x₁) t r = r

lemma3-3c : ∀ {n} {A M : tm n} (p q : Ψ A) -> ψ p M -> ψ q M
lemma3-3c p q t = lemma3-3 p q ≈-refl t

-- I could use this technique directly for LF (i.e. MLTT without the universe)
-- as an alternative to the erasure-based proof...

{- I think this might be better behaved if I define a set of (weak head) normal types
   and then define Φ by case on the (wh) normal type, and a Φ' as the bar-closure of Φ
   i.e closure under ⟶ and neutral
   by analogy with CBV logical relations...
   Then it is nicer to define φ and a φ' mutually on these
   i.e. we can think of Φ as it's written now as an explicit description of the bar-closure of Φ
   Or somehow simplify the typing derivations... I think we only want to do conv at specific points?
   Require wh normal types most of the type or something?
   Bidirectional? Normal types vs neutral types vs "computation" types?
-}
mutual
 data Φ {n} : tm n -> Set where
  bool : Φ bool
  Π : ∀ {A B} -> (p : Φ A) -> (∀ a -> φ p a -> Φ ([ a /x] B)) -> Φ (Π A B)
  neut : ∀ {A} -> neutral A -> Φ A
  closed : ∀ {A B} -> A ⟶ B -> Φ B -> Φ A
  set : Φ set

 φ : ∀ {n} -> {A : tm n} -> Φ A -> tm n -> Set
 φ bool a = ∃ (λ b → (a ⟶* b) × normal-bool b)
 φ (Π p f) a = (normalizable a) × (∀ b (q : φ p b) → φ (f b q) (a · b))
 φ (neut x) a = ∃ (λ b → (a ⟶* b) × neutral b)
 φ (closed x p) a = φ p a
 φ set a = Ψ a

Φ-closed⟶* : ∀ {n} {A B : tm n} -> A ⟶* B -> Φ B -> Φ A
Φ-closed⟶* refl t = t
Φ-closed⟶* (trans1 x s) t = closed x (Φ-closed⟶* s t)

φ-closed : ∀ {n} {A : tm n} {M N} -> (p : Φ A) -> M ⟶* N -> φ p N -> φ p M
φ-closed bool s (t1 , (s2 , n)) = t1 , ((⟶*-trans s s2) , n)
φ-closed (Π p x) s (h , t) = normalizable-closed s h , λ b q → φ-closed (x b q) (app1* s) (t b q)
φ-closed (neut x) s (t1 , (s2 , neu)) = t1 , ((⟶*-trans s s2) , neu)
φ-closed (closed x p) s t = φ-closed p s t
φ-closed set s t = Ψ-closed⟶* s t

mutual
 lemma3-3' : ∀ {n} {A B M : tm n} (p : Φ A) (q : Φ B) -> A ≈ B -> φ p M -> φ q M
 lemma3-3' bool bool t r = r
 lemma3-3' bool (Π q x) t r = bool≈Π t
 lemma3-3' bool (neut x) t r = bool-≈-neutral x t
 lemma3-3' (Π p x) bool t r = bool≈Π (≈-sym t)
 lemma3-3' (Π p x) (Π q x₁) t (r1 , r2) = r1 , (λ b q₁ → lemma3-3' (x b (lemma3-3b' p q (pi-inj2 t) q₁)) (x₁ b q₁) ([]-cong (pi-inj3 t)) (r2 b (lemma3-3b' p q (pi-inj2 t) q₁)))
 lemma3-3' (Π p x) (neut x₁) t r = Π≈neutral x₁ t
 lemma3-3' (neut x) bool t r = bool-≈-neutral x (≈-sym t)
 lemma3-3' (neut x) (Π q x₁) t r = Π≈neutral x (≈-sym t)
 lemma3-3' (neut x) (neut x₁) t r = r
 lemma3-3' (neut x) set t r = set-≈-neutral x (≈-sym t)
 lemma3-3' (Π p x) set t r = set≈Π (≈-sym t)
 lemma3-3' bool set t r = bool≈set t
 lemma3-3' set bool t r = bool≈set (≈-sym t)
 lemma3-3' set (Π q x) t r = set≈Π t
 lemma3-3' set (neut x) t r = set-≈-neutral x t
 lemma3-3' set set t r = r
 lemma3-3' p (closed x q) t r = lemma3-3' p q (⟶≈trans t x) r
 lemma3-3' (closed x p) q t r = lemma3-3' p q (⟶≈trans' t x) r

 lemma3-3b' : ∀ {n} {A B M : tm n} (p : Φ A) (q : Φ B) -> A ≈ B -> φ q M -> φ p M
 lemma3-3b' (closed x p) q t r = lemma3-3b' p q (⟶≈trans' t x) r 
 lemma3-3b' p (closed x q) t r = lemma3-3b' p q (⟶≈trans t x) r
 lemma3-3b' bool bool t r = r
 lemma3-3b' bool (Π q x) t r = bool≈Π t
 lemma3-3b' bool (neut x) t r = bool-≈-neutral x t
 lemma3-3b' (Π p x) bool t r = bool≈Π (≈-sym t)
 lemma3-3b' (Π p x) (Π q x₁) t (r1 , r2) = r1 , (λ b q₁ → lemma3-3b' (x b q₁) (x₁ b (lemma3-3' p q (pi-inj2 t) q₁)) ([]-cong (pi-inj3 t)) (r2 b (lemma3-3' p q (pi-inj2 t) q₁)))
 lemma3-3b' (Π p x) (neut x₁) t r = Π≈neutral x₁ t
 lemma3-3b' (neut x) bool t r = bool-≈-neutral x (≈-sym t)
 lemma3-3b' (neut x) (Π q x₁) t r = Π≈neutral x (≈-sym t)
 lemma3-3b' (neut x) (neut x₁) t r = r
 lemma3-3b' (neut x) set t r = set-≈-neutral x (≈-sym t)
 lemma3-3b' (Π p x) set t r = set≈Π (≈-sym t)
 lemma3-3b' bool set t r = bool≈set t
 lemma3-3b' set bool t r = bool≈set (≈-sym t)
 lemma3-3b' set (Π q x) t r = set≈Π t
 lemma3-3b' set (neut x) t r = set-≈-neutral x t
 lemma3-3b' set set t r = r 

lemma3-3c' : ∀ {n} {A M : tm n} (p q : Φ A) -> φ p M -> φ q M
lemma3-3c' p q t = lemma3-3' p q ≈-refl t


-- Huh, I haven't even had to use Set₁? I-R is powerful... 
-- This proof might be easier in PTS style, where we don't need to duplicate things?

data dctx : ctx Unitz -> Set where
 ⊡ : dctx ⊡
 _,_ : ∀ {n} -> (Γ : dctx n) -> tm n -> dctx (n , *)

data _∋_∶_ : ∀ {n} -> dctx n -> var n * -> tm n -> Set where
 top : ∀ {n} {Γ : dctx n} {A} -> (Γ , A) ∋ top ∶ ([ wkn-vsub ]r A)
 pop : ∀ {n} {Γ : dctx n} {x} {A B} -> Γ ∋ x ∶ B -> (Γ , A) ∋ (pop x) ∶ ([ wkn-vsub ]r B)

mutual
 data wfctx : ∀ {n} -> dctx n -> Set where
  ⊡ : wfctx ⊡
  _,_ : ∀ {n} {Γ : dctx n} -> wfctx Γ -> ∀ {A} -> Γ ⊢ A type -> wfctx (Γ , A)

 data _⊢_type {n} (Γ : dctx n) : tm n -> Set where
  set : Γ ⊢ set type
  Π : ∀ {A B} -> Γ ⊢ A type -> (Γ , A) ⊢ B type -> Γ ⊢ (Π A B) type
  emb : ∀ {A} -> Γ ⊢ A ∶ set -> Γ ⊢ A type

 data _⊢_∶_ {n} (Γ : dctx n) : tm n -> tm n -> Set where
  bool : Γ ⊢ bool ∶ set
  tt : Γ ⊢ tt ∶ bool
  ff : Γ ⊢ ff ∶ bool
  ▹ : ∀ {A x} -> Γ ⊢ A type -> Γ ∋ x ∶ A -> Γ ⊢ (▹ x) ∶ A
  Π : ∀ {A B} -> Γ ⊢ A ∶ set -> (Γ , A) ⊢ B ∶ set -> Γ ⊢ (Π A B) ∶ set
  ƛ : ∀ {A B M} -> Γ ⊢ A type -> (Γ , A) ⊢ M ∶ B -> Γ ⊢ (ƛ M) ∶ (Π A B)
  _·_ : ∀ {A B M N} -> Γ ⊢ M ∶ (Π A B) -> Γ ⊢ N ∶ A -> Γ ⊢ (M · N) ∶ ([ N /x] B)
  if : ∀ {C M N1 N2} -> (Γ , bool) ⊢ C type -> Γ ⊢ M ∶ bool -> Γ ⊢ N1 ∶ ([ tt /x] C) -> Γ ⊢ N2 ∶ ([ ff /x] C) -> Γ ⊢ (if M N1 N2) ∶ ([ M /x] C)
  conv : ∀ {A B} {M} -> Γ ⊢ A type -> B ≈ A -> Γ ⊢ M ∶ B -> Γ ⊢ M ∶ A

data Φs : ∀ {n m} -> dctx n -> tsubst n m -> Set where
 ⊡ : ∀ {m} -> Φs {m = m} ⊡ tt
 _,_ : ∀ {n m} {Γ} {σ : tsubst n m} {A} {a} -> Φs Γ σ -> Φ ([ σ ]t A) -> Φs (Γ , A) (σ , a)

data φs : ∀ {n m} -> (Γ : dctx n) -> (σ : tsubst n m) -> Φs Γ σ -> Set where
 ⊡ : ∀ {m} -> φs {m = m} ⊡ tt ⊡
 _,[_]_ : ∀ {n m} {Γ} {σ : tsubst n m} {ps} {A} {a} -> φs Γ σ ps -> ∀ p -> φ p a -> φs (Γ , A) (σ , a) (ps , p)

_⊨_type : ∀ {n} (Γ : dctx n) -> tm n -> Set
Γ ⊨ A type = ∀ {m} {σ : tsubst _ m} {ps : Φs Γ σ} -> φs Γ σ ps -> Φ ([ σ ]t A)

{-_⊨_set : ∀ {n} (Γ : dctx n) -> tm n -> Set
Γ ⊨ A set = ∀ {m} {σ : tsubst _ m} {ps : Φs Γ σ} -> φs Γ σ ps -> Ψ ([ σ ]t A)

Π'' : ∀ {n} {Γ} (A : tm n) B -> Γ ⊨ A set -> (Γ , A) ⊨ B set -> Γ ⊨ (Π A B) set
Π'' A B t1 t2 = λ x → Π (t1 x) (λ a x₁ → subst Ψ (subeq2 B) (t2 (x ,[ {!!} ] x₁))) -}

Π' : ∀ {n} {Γ} (A : tm n) B -> Γ ⊨ A type -> (Γ , A) ⊨ B type -> Γ ⊨ (Π A B) type
Π' A B t1 t2 = λ x → Π (t1 x) (λ a x₁ → subst Φ (subeq2 B) (t2 (x ,[ t1 x ] x₁)))

_⊨_∶'_[_] : ∀ {n} (Γ : dctx n) (M : tm n) A -> Γ ⊨ A type -> Set
Γ ⊨ M ∶' A [ d ] = ∀ {m} {σ : tsubst _ m} {ps : Φs Γ σ} (qs : φs Γ σ ps) -> φ (d qs) ([ σ ]t M)

_⊨_∶_ : ∀ {n} (Γ : dctx n) (M : tm n) A -> Set
Γ ⊨ M ∶ A = ∀ {m} {σ : tsubst _ m} {ps : Φs Γ σ} (qs : φs Γ σ ps) (p : Φ ([ σ ]t A)) -> φ p ([ σ ]t M)

κ : ∀ {A B : Set} -> B -> A -> B
κ b = λ _ -> b

Πinv2 : ∀ {n} {Γ : dctx n} A B -> Γ ⊨ (Π A B) type -> (Γ , A) ⊨ B type
Πinv2 A B t (x1 ,[ _ ] x2) with t x1
Πinv2 A B t (x1 ,[ p ] x2) | Π q x = subst Φ (sym (subeq2 B)) (x _ (lemma3-3c' p q x2))
Πinv2 A B t (x1 ,[ p ] x2) | neut ()
Πinv2 A B t (x1 ,[ p ] x2) | closed () q

{-⊨type-cong : ∀ {n} {Γ : dctx n} {A B} -> A ≡ B -> Γ ⊨ A type -> Γ ⊨ B type
⊨type-cong refl t = t -}

⊨subst : ∀ {n} {Γ : dctx n} A B -> (Γ , A) ⊨ B type -> (p : Γ ⊨ A type) -> ∀ {N} -> Γ ⊨ N ∶ A -> Γ ⊨ ([ N /x] B) type
⊨subst A B t p n x = subst Φ (subeq1 B) (t (x ,[ p x ] n x (p x)))

φeqdep : ∀ {n} {B B' M : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> φ p M -> φ q M
φeqdep p q refl t = lemma3-3c' p q t

φeqdep' : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> M ⟶ N -> φ p N -> φ q M
φeqdep' p q refl s t = lemma3-3c' p q (φ-closed p (trans1 s refl) t)

φeq : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B' ⟶* B -> M ⟶* N -> φ p N -> φ q M
φeq p q s1 s t = lemma3-3' p q (common refl s1) (φ-closed p s t)

φeq' : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≈ B' -> M ⟶* N -> φ p N -> φ q M
φeq' p q s1 s t = lemma3-3' p q s1 (φ-closed p s t)

ƛ' : ∀ {n} {Γ} (A : tm n) B M (d1 : Γ ⊨ A type) (d2 : (Γ , A) ⊨ B type) ->  (Γ , A) ⊨ M ∶ B -> Γ ⊨ (ƛ M) ∶' (Π A B) [ Π' A B d1 d2 ]
ƛ' A B M d1 d2 t {σ = σ} qs = (norm refl ƛ) , (λ b q ->
   let z = (d2 (qs ,[ d1 qs ] q))
   in φeqdep' z (subst Φ (subeq2 B) z) (subeq2 B) β (subst (φ z) (subeq2 M) (t (qs ,[ d1 qs ] q) z)))

φeqdep'' : ∀ {n} {B B' M : tm n} (p : Φ B) -> (e : B ≡ B') -> φ p M -> φ (subst Φ e p) M
φeqdep'' p refl t = t

app' : ∀ {n} {Γ} (A : tm n) B M N (d1 : Γ ⊨ A type) (d2 : (Γ , A) ⊨ B type) -> Γ ⊨ M ∶ (Π A B) -> (t : Γ ⊨ N ∶ A) -> Γ ⊨ (M · N) ∶' ([ N /x] B) [ ⊨subst A B d2 d1 t ]
app' A B M N d1 d2 t1 t2 {σ = σ} qs with t1 qs (Π' A B d1 d2 qs)
app' A B M N d1 d2 t1 t2 {σ = σ} qs | q1 , q2 with q2 ([ σ ]t N) (t2 qs (d1 qs))
... | z2 = φeqdep (subst Φ (subeq2 B) (d2 (qs ,[ d1 qs ] t2 qs (d1 qs))))
             (subst Φ (subeq1 B) (d2 (qs ,[ d1 qs ] t2 qs (d1 qs)))) (trans (sym (subeq2 B)) (subeq1 B)) z2

⊨conv : ∀ {n} {Γ} {A B : tm n} M (p : Γ ⊨ B type) (q : Γ ⊨ A type) -> B ≈ A -> Γ ⊨ M ∶ B -> Γ ⊨ M ∶' A [ q ]
⊨conv M p q s t qs = φeq' (p qs) (q qs) ([]-cong s) refl (t qs (p qs))

mutual
 reflect : ∀ {n} {A M : tm n} -> (p : Ψ A) -> neutral M -> ψ p M
 reflect bool r = _ , (refl , (neut r))
 reflect (Π p x) r = norm refl (neut r) , λ b q → reflect (x b q) (_·_ r)
 reflect (neut x) r = _ , (refl , r)
 reflect (closed x p) r = reflect p r

 reify : ∀ {n} {A M : tm n} -> (p : Ψ A) -> ψ p M -> normalizable M
 reify bool (x₁ , (x₂ , x₃)) = norm  x₂ (normal-bool-normal x₃)
 reify (Π p x) (h , _) = h
 reify (neut x) (x₁ , (x₂ , x₃)) = norm x₂ (neut x₃)
 reify (closed x p) r = reify p r

reifyt : ∀ {n} {A : tm n} -> Ψ A -> normalizable A
reifyt bool = norm refl bool
reifyt (Π t x) = norm refl Π
reifyt (neut x) = norm refl (neut x)
reifyt (closed x t) with reifyt t
reifyt (closed x₂ t) | norm x x₁ = norm (trans1 x₂ x) x₁

mutual
 reflect' : ∀ {n} {A M : tm n} -> (p : Φ A) -> neutral M -> φ p M
 reflect' bool r = , refl , neut r
 reflect' (Π p x) r = norm refl (neut r) , (λ b q → reflect' (x b q) (_·_ r))
 reflect' (neut x) r = , refl , r
 reflect' (closed x p) r = reflect' p r
 reflect' set r = neut r

 reify' : ∀ {n} {A M : tm n} -> (p : Φ A) -> φ p M -> normalizable M
 reify' bool (x₁ , (x₂ , x₃)) = norm x₂ (normal-bool-normal x₃)
 reify' (Π t x) (h , _) = h
 reify' (neut x) (x₁ , (x₂ , x₃)) = norm x₂ (neut x₃)
 reify' (closed x t) r = reify' t r
 reify' set r = reifyt r

-- TODO: Try doing this in "premonoidal category" style
if' : ∀ {n} {Γ} (C : tm (n , *)) M N1 N2 (d : (Γ , bool) ⊨ C type) -> (t : Γ ⊨ M ∶ bool) -> Γ ⊨ N1 ∶ ([ tt /x] C) -> Γ ⊨ N2 ∶ ([ ff /x] C) -> Γ ⊨ (if M N1 N2) ∶' ([ M /x] C) [ ⊨subst bool C d (κ bool) t ]
if' C M N1 N2 d t t1 t2 qs with t qs bool
if' C M N1 N2 d t t1 t2 qs | .tt , (q1 , tt) = φeq (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , tt)))) (subst Φ (subeq1 C) (d (qs ,[ bool ] (, q1 , tt))))
    (⟶*cong2 (subeq1 C) (subeq1 C) (sub⟶*2 q1 C)) (⟶*-trans (if* q1) (trans1 if1 refl)) (t1 qs (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , tt)))))
if' C M N1 N2 d t t1 t2 qs | .ff , (q1 , ff) = φeq (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , ff)))) (subst Φ (subeq1 C) (d (qs ,[ bool ] (, q1 , ff))))
    (⟶*cong2 (subeq1 C) (subeq1 C) (sub⟶*2 q1 C)) (⟶*-trans (if* q1) (trans1 if2 refl)) (t2 qs (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , ff)))))
if' C M N1 N2 d t t1 t2 qs | M' , (q1 , neut x) = φ-closed (subst Φ (subeq1 C) (d (qs ,[ bool ] (M' , (q1 , neut x))))) (if* q1) (reflect' (subst Φ (subeq1 C) (d (qs ,[ bool ] (M' , (q1 , neut x))))) (if x))

mem : ∀ {n} {Γ} {A : tm n} x -> Γ ∋ x ∶ A -> Γ ⊨ (▹ x) ∶ A
mem .top (top {_} {_} {A}) (qs ,[ p ] x) p₁ = φeqdep p p₁ (subeq3 A) x
mem .(pop x) (pop {n} {Γ} {x} {A} {B} d) (qs ,[ p ] x₁) p₁ = φeqdep (subst Φ (sym (subeq3 B)) p₁) p₁ (subeq3 B) (mem x d qs (subst Φ (sym (subeq3 B)) p₁))

mutual
 prop1 : ∀ {n} {A : tm n} -> Ψ A -> Φ A
 prop1 bool = bool
 prop1 (Π t x) = Π (prop1 t) (λ a x₁ → prop1 (x a (prop3' t x₁)))
 prop1 (neut x) = neut x
 prop1 (closed x t) = closed x (prop1 t)

 prop3 : ∀ {n} {M A : tm n} (p : Ψ A) -> ψ p M -> φ (prop1 p) M
 prop3 bool r = r
 prop3 (Π t x) (r1 , r2) = r1 , (λ b q → prop3 (x b (prop3' t q)) (r2 b (prop3' t q)))
 prop3 (neut x) r = r
 prop3 (closed x t) r = prop3 t r

 prop3' : ∀ {n} {M A : tm n} (p : Ψ A) -> φ (prop1 p) M -> ψ p M
 prop3' bool r = r
 prop3' (Π t x) (r1 , r2) = r1 , (λ b q → prop3' (x b q) (f b q))
  where f : ∀ b q -> _
        f b q = lemma3-3c' (prop1 (x b (prop3' t (prop3 t q)))) (prop1 (x b q)) (r2 b (prop3 t q))
 prop3' (neut x) r = r
 prop3' (closed x t) r = prop3' t r

mutual
 lem1 : ∀ {n A} (Γ : dctx n) -> Γ ⊢ A type -> Γ ⊨ A type
 lem1 Γ set = κ set
 lem1 Γ (Π {A} {B} t t₁) = Π' A B (lem1 Γ t) (lem1 (Γ , A) t₁)
 lem1 Γ (emb x) = λ x₁ → prop1 (lem3 Γ x x₁ set)
 
  -- .. Could we do this equivalently by showing Γ ⊢ M ∶ A implies Γ ⊢ A type, and then appealing to lem1?
 -- Or alternatively, can we employ the strategy of requiring that Φ A in lem3, analogous to the assumption that Γ ⊢ A type before checking Γ ⊢ M ∶ A?
 lem2 : ∀ {n M A} (Γ : dctx n)  -> Γ ⊢ M ∶ A -> Γ ⊨ A type
 lem2 Γ bool = κ set
 lem2 Γ tt = κ bool
 lem2 Γ ff = κ bool
 lem2 Γ (▹ x₁ x₂) = lem1 Γ x₁
 lem2 Γ (Π t t₁) = κ set
 lem2 Γ (ƛ {A} {B} x t) = Π' A B (lem1 Γ x) (lem2 (Γ , A) t)
 lem2 Γ (_·_ {A} {B} t t₁) = ⊨subst A B (Πinv2 A B (lem2 Γ t)) (lem2 Γ t₁) (lem3 Γ t₁)
 lem2 Γ (if {C} x t t₁ t₂) = ⊨subst bool C (lem1 (Γ , bool) x) (κ bool) (lem3 Γ t)
 lem2 Γ (conv x x₁ t) = lem1 Γ x

 lem3 : ∀ {n M A} (Γ : dctx n) (d : Γ ⊢ M ∶ A) -> Γ ⊨ M ∶ A
 lem3 Γ t qs p = lemma3-3c' (lem2 Γ t qs) p (lem3' Γ t qs)

 lem3' : ∀ {n M A} (Γ : dctx n) (d : Γ ⊢ M ∶ A) -> Γ ⊨ M ∶' A [ lem2 Γ d ]
 lem3' Γ bool = κ bool
 lem3' Γ tt = κ (tt , (refl , tt))
 lem3' Γ ff = κ (ff , (refl , ff))
 lem3' Γ (▹ {A} {x} x₁ x₂) = λ qs → mem x x₂ qs (lem1 Γ x₁ qs)
 lem3' Γ (Π {A} {B} t t₁) = λ qs -> Π (lem3 Γ t qs set) (λ a x → subst Ψ (subeq2 B) (lem3 (Γ , A) t₁ (qs ,[ prop1 (lem3 Γ t qs set) ] prop3 (lem3 Γ t qs set) x) set)) -- TODO: Clean up this case somehow?
 lem3' Γ (ƛ {A} {B} {M} x t) = ƛ' A B M (lem1 Γ x) (lem2 (Γ , A) t) (lem3 (Γ , A) t)
 lem3' Γ (_·_ {A} {B} {M} {N} t t₁) = app' A B M N (lem2 Γ t₁) (Πinv2 A B (lem2 Γ t)) (lem3 Γ t) (lem3 Γ t₁)
 lem3' Γ (if {C} {M} {N1} {N2} x t t₁ t₂) = if' C M N1 N2 (lem1 (Γ , bool) x) (lem3 Γ t) (lem3 Γ t₁) (lem3 Γ t₂)
 lem3' Γ (conv {A} {B} {M} x x₁ t) = ⊨conv M (lem2 Γ t) (lem1 Γ x) x₁ (lem3 Γ t)


-- Huh I think the more natural thing to do for a "weak head normal form"
-- for arrow is to say that any term of arrow type is normal?
-- Maybe use CBPV to motivate? Function types are computation types.. need to thunk to turn into value types...
-- Or.. for weak normalization, could we just add "halts" to the definition of the logical predicate?

yay1 : ∀ {M A}  -> ⊡ ⊢ M ∶ A -> normalizable M
yay1 d = subst normalizable subeq4 (reify' {n = ⊡} (lem2 ⊡ d ⊡) (lem3' _ d ⊡))

{-
mutual
 idΦ : ∀ {n} {Γ : dctx n} -> wfctx Γ -> Φs Γ id-tsub
 idΦ ⊡ = ⊡
 idΦ (d , x) with idΦ d | lem1 _ x (idφ d)
 ... | q1 | q2 = {!!} , {!!} -- TODO: Figure out how to do weakening... Hmm one way is to do it syntactically, then use lem1 with the weakened d
 
 idφ : ∀ {n} {Γ : dctx n} (d : wfctx Γ) -> φs _ id-tsub (idΦ d)
 idφ ⊡ = ⊡
 idφ (d , x) = {!!} ,[ {!!} ] {!!}

yay : ∀ {n M A} {Γ : dctx n} -> wfctx Γ -> Γ ⊢ M ∶ A -> normalizable M
yay d0 d with reify' (lem2 _ d (idφ d0)) (lem3' _ d (idφ d0))
... | q = {!!} -}

-- Do the corollary: type checking is decidable (i.e. define algorithmic typing, show it's complete)