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
 β : ∀ M N -> ((ƛ M) · N) ⟶ [ N /x] M
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
 neut : ∀ M -> neutral M -> normal-bool M

data normalizable {n} (M : tm n) : Set where
 norm : ∀ N -> M ⟶* N -> normal N -> normalizable M

-- Can I just use "normal" and get rid of normal-bool?
normal-bool-normal : ∀ {n} {M : tm n} -> normal-bool M -> normal M
normal-bool-normal tt = tt
normal-bool-normal ff = ff
normal-bool-normal (neut A x) = neut x

normalizable-closed : ∀ {n} {M N : tm n} -> M ⟶* N -> normalizable N -> normalizable M
normalizable-closed p (norm N q r) = norm N (⟶*-trans p q) r

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
 subeq1 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ , ([ σ ]t N) ]t M ≡ [ σ ]t ([ N /x] M) 
 subeq2 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ , N ]t M ≡ [ id-tsub , N ]t ([ tsub-ext σ ]t M)

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
neutral-step (_·_ ()) (β M N)
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

bool≈Π : ∀ {n} {A : tm n} {B} {C : Set} -> bool ≈ (Π A B) -> C
bool≈Π (common x x₁) with normal-step* bool x | pi-inj1 x₁
bool≈Π (common x x₁) | refl | ()

Π≈neutral : ∀ {n} {A : tm n} {B D} {C : Set} -> neutral A -> (Π B D) ≈ A -> C
Π≈neutral t (common x x₁) with neutral-step* t x₁ | pi-inj1 x
Π≈neutral () (common x x₁) | refl | yep x₂ x₃

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

{-
mutual
 invariance : ∀ {n} {A M : tm n} (p q : Ψ A) -> ψ p M -> ψ q M
 invariance bool bool t = t
 invariance bool (neut .bool ()) t
 invariance bool (closed () q) t
 invariance (Π p x) (Π q x₁) (t1 , t2) = t1 , (λ b q₁ → invariance (x b (invariance q p q₁)) (x₁ b q₁) (t2 b (invariance q p q₁)))
 invariance (Π p x) (neut ._ ()) t
 invariance (Π p x) (closed () q) t -- If we're doing full reduction, this isn't trivial
 invariance (neut ._ ()) bool t 
 invariance (neut ._ ()) (Π q x₁) t
 invariance (neut _ x) (neut ._ x₁) t = t
 invariance (neut _ x) (closed x₁ q) t = {!!}
 invariance (closed () p) bool t
 invariance (closed () p) (Π q x₁) t
 invariance (closed x p) (neut ._ x₁) t = {!!}
 invariance (closed x p) (closed x₁ q) t = {!!} -}

-- invariance2 : ∀ {n} {A M : tm n} (p q : Ψ A) -> ψ q M -> ψ q M

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
  neut : ∀ A -> neutral A -> Φ A
  closed : ∀ {A B} -> A ⟶ B -> Φ B -> Φ A
  set : Φ set

 φ : ∀ {n} -> {A : tm n} -> Φ A -> tm n -> Set
 φ bool a = ∃ (λ b → (a ⟶* b) × normal-bool b)
 φ (Π p f) a = (normalizable a) × (∀ b (q : φ p b) → φ (f b q) (a · b))
 φ (neut A x) a = ∃ (λ b → (a ⟶* b) × neutral b)
 φ (closed x p) a = φ p a
 φ set a = Ψ a

Φ-closed⟶* : ∀ {n} {A B : tm n} -> A ⟶* B -> Φ B -> Φ A
Φ-closed⟶* refl t = t
Φ-closed⟶* (trans1 x s) t = closed x (Φ-closed⟶* s t)

φ-closed : ∀ {n} {A : tm n} {M N} -> (p : Φ A) -> M ⟶* N -> φ p N -> φ p M
φ-closed bool s (t1 , (s2 , n)) = t1 , ((⟶*-trans s s2) , n)
φ-closed (Π p x) s (h , t) = normalizable-closed s h , λ b q → φ-closed (x b q) (app1* s) (t b q)
φ-closed (neut A x) s (t1 , (s2 , neu)) = t1 , ((⟶*-trans s s2) , neu)
φ-closed (closed x p) s t = φ-closed p s t
φ-closed set s t = Ψ-closed⟶* s t

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
  _·_ : ∀ {M N A B} -> Γ ⊢ M ∶ (Π A B) -> Γ ⊢ N ∶ A -> Γ ⊢ (M · N) ∶ ([ N /x] B)
  if : ∀ {C M N1 N2} -> (Γ , bool) ⊢ C type -> Γ ⊢ M ∶ bool -> Γ ⊢ N1 ∶ ([ tt /x] C) -> Γ ⊢ N2 ∶ ([ ff /x] C) -> Γ ⊢ (if M N1 N2) ∶ ([ M /x] C)
  conv : ∀ {A B} M -> Γ ⊢ A type -> A ⟶ B -> Γ ⊢ M ∶ B -> Γ ⊢ M ∶ A

Φs : ∀ {n m} -> dctx n -> tsubst n m -> Set
Φs ⊡ σ = Unit
Φs (Γ , A) (σ , a) = Φs Γ σ × Φ ([ σ ]t A)

φs : ∀ {n m} -> (Γ : dctx n) -> (σ : tsubst n m) -> Φs Γ σ -> Set
φs ⊡ σ ps = Unit
φs (Γ , A) (σ , a) (ps , p) = φs Γ σ ps × φ p a

lem0 : ∀ {n} (t : Φ {n} set) -> t ≡ set
lem0 (neut .set ())
lem0 (closed () t)
lem0 set = refl

lem0bool : ∀ {n} (t : Φ {n} bool) -> t ≡ bool
lem0bool bool = refl
lem0bool (neut .bool ())
lem0bool (closed () t)
-- proofs of Φ are unique (I hope), once we properly restrict neutral to also be normal
-- Okay that's trickier: if ⟶ is non-deterministic, proofs of Φ aren't unique
-- However, by Church-rosser, φ doesn't care

lem-a : ∀ {n} {A B M : tm n} {p : Φ B} -> (s : A ⟶* B) -> φ p M -> φ (Φ-closed⟶* s p) M
lem-a refl r = r
lem-a (trans1 x s) r = lem-a s r



{-mutual
 lem1 : ∀ {n m A} (Γ : dctx n) {σ : tsubst n m} {ps : Φs Γ σ} -> φs Γ σ ps -> Γ ⊢ A type -> Φ ([ σ ]t A)
 lem1 Γ qs set = set
 lem1 Γ {σ} {ps} qs (Π {A} {B} d d₁) = Π (lem1 Γ qs d) (λ a x → subst Φ {!!} (lem1 (Γ , A) {σ = σ , a} {ps = ps , lem1 Γ qs d } (qs , x) d₁))
 lem1 Γ qs (emb x) with lem2 Γ qs x
 lem1 Γ qs (emb x) | w1 , w2 with lem0 w1
 lem1 Γ qs (emb x) | .set , w2 | refl = {!!}
 
 lem2 : ∀ {n m M A} (Γ : dctx n) {σ : tsubst n m} {ps : Φs Γ σ} -> (qs : φs Γ σ ps) -> Γ ⊢ M ∶ A -> Σ (Φ ([ σ ]t A)) (λ q -> φ q ([ σ ]t M))
 lem2 Γ qs bool = set , bool
 lem2 Γ qs tt = bool , (tt , (refl , tt))
 lem2 Γ qs ff = bool , (ff , (refl , ff))
 lem2 Γ qs (▹ x₁ x₂) = {!!}
 lem2 Γ qs (Π d d₁) with lem2 Γ qs d
 ... | q1 , q2 with lem0 q1
 lem2 Γ {σ} {ps} qs (Π {A} {B} d d₁) | .set , q2 | refl = set , Π q2 (λ a x → subst Ψ {!!} (f a x))
  where f : ∀ (a : tm _) -> ψ q2 a -> Ψ ([ σ , a ]t B)
        f a x with lem2 (Γ , A) {σ = σ , a} {ps = ps , {!!} } (qs , x) d₁
        ... | q1 , q2 with lem0 q1
        f a x | .set , q3 | refl = q3
 lem2 Γ {σ} {ps} qs (ƛ {A} {B} {M} x d) = (Π (lem1 Γ qs x) (λ a x₁ → subst Φ (subeq2 B) (Σ.proj₁ (f a x₁)))) , ( norm _ refl ƛ ,
   (λ b q → φ-closed (subst Φ (subeq2 B) (Σ.proj₁ (f b q))) (trans1 (β _ _) refl) (subst (φ (subst Φ (subeq2 B) (Σ.proj₁ (f b q)))) (subeq2 M) {!just a bit of eqdep...!})))
   where f : ∀ a -> φ (lem1 Γ qs x) a -> Σ (Φ ([ σ , a ]t B)) (λ q -> φ q ([ σ , a ]t M))
         f a p = lem2 (Γ , A) {σ = σ , a} {ps = ps , lem1 Γ qs x } (qs , p) d
 lem2 Γ qs (d · d₁) with lem2 Γ qs d | lem2 Γ qs d₁
 lem2 Γ {σ} qs (_·_ {M} {N} d d₁) | Π q1 x , q2 | q3 , q4 = (subst Φ {!!} (x ([ σ ]t N) {!!})) , {!!}
 lem2 Γ {σ} qs (_·_ {A} {B} d d₁) | neut ._ () , q2 | q3 , q4 
 lem2 Γ qs (d · d₁) | closed () q1 , q2 | q3 , q4 
 lem2 Γ qs (if x d d₁ d₂) with lem2 Γ qs d
 lem2 Γ qs (if x d d₁ d₂) | x₁ , x₂ with lem0bool x₁
 lem2 Γ qs (if {C} x d d₁ d₂) | .bool , (.tt , (x₂ , tt)) | refl with lem2 Γ qs d₁
 ... | q1 , q2 = d1 , φ-closed d1 (trans1r (if* x₂) if1) (lem-a d0 q2)
    where d0 = (⟶*cong2 (subeq1 C) (subeq1 C) (sub⟶*2 x₂ C))
          d1 = (Φ-closed⟶* d0 q1)
 lem2 Γ {σ} {ps} qs (if {C} {M} x d d₁ d₂) | .bool , (.ff , (x₂ , ff)) | refl with lem2 Γ qs d₂
 ... | q1 , q2 with lem1 (Γ , bool) {σ = σ , [ σ ]t M} {ps = ps , bool} (qs , (ff , (x₂ , ff))) x
 ... | q0 = (subst Φ (subeq1 C) q0) , φ-closed (subst Φ (subeq1 C) q0) (trans1r (if* x₂) (if2 _ _)) {!!}
 lem2 Γ qs (if x₃ d d₁ d₂) | .bool , (x₁ , (x₂ , neut .x₁ x)) | refl = {!!}
 lem2 Γ qs (conv M x x₁ d) with lem2 Γ qs d
 ... | q1 , q2 = (Φ-closed⟶* d0 q1) , lem-a d0 q2
    where d0 = (sub⟶* _ (trans1 x₁ refl)) -}

mutual
 lem1 : ∀ {n m A} (Γ : dctx n) {σ : tsubst n m} {ps : Φs Γ σ} -> φs Γ σ ps -> Γ ⊢ A type -> Φ ([ σ ]t A)
 lem1 Γ qs set = set
 lem1 Γ {σ} {ps} qs (Π {A} {B} d d₁) = Π (lem1 Γ qs d) (λ a x → subst Φ (subeq2 B) (lem1 (Γ , A) {σ = σ , a} {ps = ps , lem1 Γ qs d } (qs , x) d₁))
 lem1 Γ qs (emb x) with lem2 Γ qs x | lem3 Γ qs x
 ... | q0 | q with lem0 q0
 lem1 Γ qs (emb x) | .set | q | refl = {!!}
 
  -- .. Could we do this equivalently by showing Γ ⊢ M ∶ A implies Γ ⊢ A type, and then appealing to lem1?
 -- Or alternatively, can we employ the strategy of requiring that Φ A in lem3, analogous to the assumption that Γ ⊢ A type before checking Γ ⊢ M ∶ A?
 lem2 : ∀ {n m M A} (Γ : dctx n) {σ : tsubst n m} {ps : Φs Γ σ} -> (qs : φs Γ σ ps) -> Γ ⊢ M ∶ A -> Φ ([ σ ]t A)
 lem2 Γ qs bool = set
 lem2 Γ qs tt = bool
 lem2 Γ qs ff = bool
 lem2 Γ qs (▹ x₁ x₂) = {!!}
 lem2 Γ qs (Π d d₁) = set
 lem2 Γ qs (ƛ {A} {B} x d) = Π (lem1 Γ qs x) (λ a x₁ → subst Φ (subeq2 B) (lem2 (Γ , A) {σ = _ , a} {ps = _ , lem1 Γ qs x } (qs , x₁) d))
                             -- Notice that this is the Pi case of lem1
 lem2 Γ qs (d · d₁) = {!!}
 lem2 Γ {σ} qs (if {C} {M} x d d₁ d₂) = subst Φ (subeq1 C) (lem1 (Γ , bool) {σ = σ , [ σ ]t M} {ps = _ , lem2 Γ qs d} (qs , lem3 Γ qs d) x)
 lem2 Γ qs (conv _ x x₁ d) = Φ-closed⟶* (sub⟶* _ (trans1 x₁ refl)) (lem2 Γ qs d)

 lem3 : ∀ {n m M A} (Γ : dctx n) {σ : tsubst n m} {ps : Φs Γ σ} -> (qs : φs Γ σ ps) -> (d : Γ ⊢ M ∶ A) -> φ (lem2 Γ qs d) ([ σ ]t M)
 lem3 Γ qs bool = bool
 lem3 Γ qs tt = _ , (refl , tt)
 lem3 Γ qs ff = _ , (refl , ff)
 lem3 Γ qs (▹ x₁ x₂) = {!!}
 lem3 Γ qs (Π d d₁) with lem2 Γ qs d | lem3 Γ qs d 
 ... | q0 | q1 with lem0 q0
 lem3 Γ qs (Π {A} {B} d d₁) | .set | q1 | refl = Π q1 (λ a x → subst Ψ (subeq2 B) {!!})
 lem3 Γ qs (ƛ x d) = {!!}
 lem3 Γ qs (d · d₁) = {!!}
 lem3 Γ qs (if x d d₁ d₂) with lem2 Γ qs d | lem3 Γ qs d
 ... | q0 | q1 with lem0bool q0
 lem3 Γ qs (if x d d₁ d₂) | .bool | .tt , (q2 , tt) | refl = {!!}
 lem3 Γ qs (if x d d₁ d₂) | .bool | .ff , (q2 , ff) | refl = {!!}
 lem3 Γ qs (if x₁ d d₁ d₂) | .bool | q1 , (q2 , neut ._ x) | refl = {!!}
 lem3 Γ qs (conv M x x₁ d) = lem-a (sub⟶* _ (trans1 x₁ refl)) (lem3 Γ qs d)


-- Huh I think the more natural thing to do for a "weak head normal form"
-- for arrow is to say that any term of arrow type is normal?
-- Maybe use CBPV to motivate? Function types are computation types.. need to thunk to turn into value types...
-- Or.. for weak normalization, could we just add "halts" to the definition of the logical predicate?

mutual
 reflect : ∀ {n} {A M : tm n} -> (p : Ψ A) -> neutral M -> ψ p M
 reflect bool r = _ , (refl , (neut _ r))
 reflect (Π p x) r = norm _ refl (neut r) , λ b q → reflect (x b q) (_·_ r)
  {-where f : ∀ b -> (q : ψ p b) -> ψ (x b q) (_ · b)
        f b q with reify p q
        f b q | norm N x₁ x₂ = ψ-closed (x b q) (app2* x₁) (reflect (x b q) (r · x₂)) -}
 reflect (neut x) r = _ , (refl , r)
 reflect (closed x p) r = reflect p r

 reify : ∀ {n} {A M : tm n} -> (p : Ψ A) -> ψ p M -> normalizable M
 reify bool (x₁ , (x₂ , x₃)) = norm x₁ x₂ (normal-bool-normal x₃)
 reify (Π p x) (h , _) = h
 reify (neut x) (x₁ , (x₂ , x₃)) = norm x₁ x₂ (neut x₃)
 reify (closed x p) r = reify p r