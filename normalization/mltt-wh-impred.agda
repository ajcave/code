{-# OPTIONS --type-in-type #-}
module mltt-wh-impred where
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

mutual
 data tp (δ : ctx Unit) (n : ctx Unit) : Set where
  ▹ : (X : var δ *) -> tp δ n
  Π : (A : tp δ n) -> (B : tp δ (n , *)) -> tp δ n
  ∩ : (B : tp (δ , *) n) -> tp δ n
  if : (M : tm n) (N P : tp δ n) -> tp δ n
  bool : tp δ n

 data tm (n : ctx Unit) : Set where
  ▹ : (x : var n *) -> tm n
  ƛ : (M : tm (n , *)) -> tm n
  _·_ : (M N : tm n) -> tm n
  tt ff : tm n
  if : (M N P : tm n) -> tm n


[_]r : ∀ {n m} -> vsubst n m -> tm n -> tm m
[_]r σ (▹ x) = ▹ ([ σ ]v x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (M · M₁) = ([ σ ]r M) · ([ σ ]r M₁)
[_]r σ tt = tt
[_]r σ ff = ff
[_]r σ (if M M₁ M₂) = if ([ σ ]r M) ([ σ ]r M₁) ([ σ ]r M₂)

[_]rδ : ∀ {δ n m} -> vsubst n m -> tp δ n -> tp δ m
[_]rδ σ (▹ X) = ▹ X
[_]rδ σ (Π T T₁) = Π ([ σ ]rδ T) ([ vsub-ext σ ]rδ T₁)
[_]rδ σ (∩ T) = ∩ ([ σ ]rδ T)
[_]rδ σ (if M T T₁) = if ([ σ ]r M) ([ σ ]rδ T) ([ σ ]rδ T₁)
[_]rδ σ bool = bool

[_]rδt : ∀ {δ1 δ2 n} -> vsubst δ1 δ2 -> tp δ1 n -> tp δ2 n
[_]rδt σ (▹ X) = ▹ ([ σ ]v X)
[_]rδt σ (Π T T₁) = Π ([ σ ]rδt T) ([ σ ]rδt T₁)
[_]rδt σ (∩ T) = ∩ ([ vsub-ext σ ]rδt T)
[_]rδt σ (if M T T₁) = if M ([ σ ]rδt T) ([ σ ]rδt T₁)
[_]rδt σ bool = bool

tpsubst : ∀ (n δ1 δ2 : ctx Unit) -> Set
tpsubst n δ1 δ2 = gksubst δ1 (tp δ2 n)

tpsub-ext : ∀ {n δ1 δ2} -> tpsubst n δ1 δ2 -> tpsubst n (δ1 , *) (δ2 , *)
tpsub-ext σ = (gmap [ wkn-vsub ]rδt σ) , (▹ top)

id-tpsub : ∀ {δ n} -> tpsubst n δ δ
id-tpsub {⊡} = tt
id-tpsub {δ , T} = tpsub-ext id-tpsub

[_]δtp : ∀ {δ1 δ2 n} -> tpsubst n δ1 δ2 -> tp δ1 n -> tp δ2 n
[_]δtp σ (▹ X) = [ σ ]v X
[_]δtp σ (Π T T₁) = Π ([ σ ]δtp T) ([ gmap [ wkn-vsub ]rδ σ ]δtp T₁)
[_]δtp σ (∩ T) = ∩ ([ tpsub-ext σ ]δtp T)
[_]δtp σ (if M T T₁) = if M ([ σ ]δtp T) ([ σ ]δtp T₁)
[_]δtp σ bool = bool

[_/X]δtp : ∀ {δ n} -> tp δ n -> tp (δ , *) n  -> tp δ n
[ C /X]δtp T = [ id-tpsub , C ]δtp T

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
[_]t σ (M · M₁) = ([ σ ]t M) · ([ σ ]t M₁)
[_]t σ tt = tt
[_]t σ ff = ff
[_]t σ (if M M₁ M₂) = if ([ σ ]t M) ([ σ ]t M₁) ([ σ ]t M₂)

[_]tδ : ∀ {δ n m} -> tsubst n m -> tp δ n -> tp δ m
[_]tδ σ (▹ X) = ▹ X
[_]tδ σ (Π M M₁) = Π ([ σ ]tδ M) ([ tsub-ext σ ]tδ M₁)
[_]tδ σ (∩ M) = ∩ ([ σ ]tδ M)
[_]tδ σ (if M M₁ M₂) = if ([ σ ]t M) ([ σ ]tδ M₁) ([ σ ]tδ M₂)
[_]tδ σ bool = bool

[_/x] : ∀ {n} -> tm n -> tm (n , *) -> tm n
[ M /x] N = [ id-tsub , M ]t N

[_/x]δ : ∀ {δ n} -> tm n -> tp δ (n , *) -> tp δ n
[ M /x]δ N = [ id-tsub , M ]tδ N

data _⟶_ {n} : ∀ (M N : tm n) -> Set where
 β : ∀ {M N} -> ((ƛ M) · N) ⟶ [ N /x] M
 if1 : ∀ {M N} -> if tt M N ⟶ M
 if2 : ∀ {M N} -> if ff M N ⟶ N
 app1 : ∀ {M M' N} -> M ⟶ M' -> (M · N) ⟶ (M' · N)
-- app2 : ∀ {M N N'} -> N ⟶ N' -> (M · N) ⟶ (M · N')
 ifc : ∀ {M M' N1 N2} -> M ⟶ M' -> if M N1 N2 ⟶ if M' N1 N2

data _⟶δ_ {δ n} : ∀ (M N : tp δ n) -> Set where

data _⟶*_ {n} : ∀ (M N : tm n) -> Set where
 refl : ∀ {M} -> M ⟶* M
 trans1 : ∀ {M N P} -> M ⟶ N -> N ⟶* P -> M ⟶* P

data _⟶δ*_ {δ n} : ∀ (M N : tp δ n) -> Set where
 refl : ∀ {M} -> M ⟶δ* M
 trans1 : ∀ {M N P} -> M ⟶δ N -> N ⟶δ* P -> M ⟶δ* P

⟶*-trans : ∀ {n} {M N P : tm n} -> M ⟶* N -> N ⟶* P -> M ⟶* P
⟶*-trans refl s2 = s2
⟶*-trans (trans1 x s1) s2 = trans1 x (⟶*-trans s1 s2)

-- trans1r : ∀ {n} {M N P : tm n} -> M ⟶* N -> N ⟶ P -> M ⟶* P
-- trans1r s t = ⟶*-trans s (trans1 t refl)

app1* : ∀ {n} {M M' N : tm n} -> M ⟶* M' -> (M · N) ⟶* (M' · N)
app1* refl = refl
app1* (trans1 x s) = trans1 (app1 x) (app1* s)

-- {-app2* : ∀ {n} {M M' N : tm n} -> M ⟶* M' -> (N · M) ⟶* (N · M')
-- app2* refl = refl
-- app2* (trans1 x s) = trans1 (app2 x) (app2* s) -}

-- if* : ∀ {n} {M M' N1 N2 : tm n} -> M ⟶* M' -> (if M N1 N2) ⟶* (if M' N1 N2)
-- if* refl = refl
-- if* (trans1 x t) = trans1 (ifc x) (if* t)

mutual
 data neutral {n} : tm n -> Set where
  ▹ : ∀ x -> neutral (▹ x)
  _·_ : ∀ {M N} -> neutral M {- -> normal N -} -> neutral (M · N)
  if : ∀ {M N P} -> neutral M {- -> normal N -> normal P -} -> neutral (if M N P) 

 data normal {n} : tm n -> Set where
  ƛ : ∀ {M} {- -> normal M -} -> normal (ƛ M)
  tt : normal tt
  ff : normal ff
  neut : ∀ {M} -> neutral M -> normal M

 data normalδ {δ n} : tp δ n -> Set where
  bool : normalδ bool
  Π : ∀ {A B} -> normalδ (Π A B)
  ∩ : ∀ {B} -> normalδ (∩ B)
  ▹ : ∀ {X} -> normalδ (▹ X)
  if : ∀ {M T1 T2} -> neutral M -> normalδ (if M T1 T2)
  -- ƛ : ∀ {M} {- -> normal M -} -> normal (ƛ M)
  -- tt : normal tt
  -- ff : normal ff
  -- neut : ∀ {M} -> neutral M -> normal M

data normal-bool {n} : tm n -> Set where
 tt : normal-bool tt
 ff : normal-bool ff
 neut : ∀ {M} -> neutral M -> normal-bool M

data normalizable {n} (M : tm n) : Set where
 norm : ∀ {N} -> M ⟶* N -> normal N -> normalizable M

data normalizableδ {δ n} (M : tp δ n) : Set where
 norm : ∀ {N} -> M ⟶δ* N -> normalδ N -> normalizableδ M

-- -- Can I just use "normal" and get rid of normal-bool?
normal-bool-normal : ∀ {n} {M : tm n} -> normal-bool M -> normal M
normal-bool-normal tt = tt
normal-bool-normal ff = ff
normal-bool-normal (neut x) = neut x

normalizable-closed : ∀ {n} {M N : tm n} -> M ⟶* N -> normalizable N -> normalizable M
normalizable-closed p (norm q r) = norm (⟶*-trans p q) r

cand : Set₁
cand = ∀{n} -> tm n -> Set

record isCand (R : cand) : Set where
 field
  cr1 : ∀ {n} {M : tm n} -> R M -> normalizable M
  cr2 : ∀ {n} {M N : tm n} -> M ⟶* N -> R N -> R M
  cr3 : ∀ {n} {M : tm n} -> neutral M -> R M

csub : ∀ δ -> Set₁
csub δ = var δ * -> cand

_,,_ : ∀ {δ} -> csub δ -> cand -> csub (δ , *)
_,,_ ρ R top = R
_,,_ ρ R (pop x) = ρ x

areCands : ∀ {δ} (ρ : csub δ) -> Set
areCands ρ = ∀ x -> isCand (ρ x)

_,,c_ : ∀ {δ} {ρ : csub δ} {C : cand} -> areCands ρ -> isCand C -> areCands (ρ ,, C)
_,,c_ w p top = p
_,,c_ w p (pop x) = w x

-- * I guess that we could uniformly have a substitution for type variables and term variables instead of applying them one at a time
-- * Remember that type-in-type is unsound in Agda for simpler reasons than Hurkens: e.g. it is incompatible with the termination checker in a simple way
-- * If we manage to translate this into Coq, the question becomes: what essential feature of Coq did we make use of that permits the proof to go through?
-- * What if I "only" required that "a" is (wh) normalizable in the Π case of Ψ? Compare with Werner's proof
--   -- no, normalizable does not appear to be enough. We need it to be "recursively normalizable", i.e. *reducible*
-- * I think to encode this in Coq we may need to go up a universe level even with impredicative Set, because the impredicative universes
--   don't permit "strong" (large) eliminations for "non-small" inductive definitions (i.e. inductive defn's which actually quantify over Sets)
--   (this is the "impredicative strong sums are inconsistent" problem)
--   Is this "going up a universe level" a show-stopper?
--    Hopefully it's just the manifestation of Godel's incompleteness theorem
mutual
 data Ψ {δ n} (ρ : csub δ) : tp δ n -> Set where
  bool : Ψ ρ bool
  Π : ∀ {A B} -> (p : Ψ ρ A) -> (∀ a -> ψ ρ p a -> Ψ ρ ([ a /x]δ B)) -> Ψ ρ (Π A B)
  ∩ : ∀ {B} -> (∀ (R : cand) -> isCand R -> Ψ (ρ ,, R) B) -> Ψ ρ (∩ B)
  if : ∀ {M} -> neutral M -> ∀ B1 B2 -> Ψ ρ (if M B1 B2)
  ▹ : (X : var δ *) -> Ψ ρ (▹ X)
  closed : ∀ {A B} -> A ⟶δ B -> Ψ ρ B -> Ψ ρ A

 ψ : ∀ {δ n} -> {A : tp δ n} -> (ρ : csub δ) -> Ψ ρ A -> tm n -> Set
 ψ ρ bool a = ∃ (λ b → (a ⟶* b) × normal-bool b)
 ψ ρ (Π p f) a = (normalizable a) × (∀ b (q : ψ ρ p b) → ψ ρ (f b q) (a · b))
 ψ ρ (∩ b) t = ∀ (R : cand) (pr : isCand R) → ψ (ρ ,, R) (b R pr) t
 ψ ρ (▹ X) t = ρ X t
 ψ ρ (if m B1 B2) a = ∃ (λ b → (a ⟶* b) × neutral b)
 ψ ρ (closed x p) a = ψ ρ p a

Ψ-closed⟶* : ∀ {δ n} {A B : tp δ n} {ρ} -> A ⟶δ* B -> Ψ ρ B -> Ψ ρ A
Ψ-closed⟶* refl t = t
Ψ-closed⟶* (trans1 x s) t = closed x (Ψ-closed⟶* s t)

ψ-closed : ∀ {δ n} {ρ : csub δ} (w : areCands ρ) {A : tp δ n} {M N}
 -> (p : Ψ ρ A) -> M ⟶* N -> ψ ρ p N -> ψ ρ p M
ψ-closed w bool s (t₁ , (t₂ , t₃)) = t₁ , ((⟶*-trans s t₂) , t₃)
ψ-closed w (Π p x) s (h , t) = normalizable-closed s h , λ b q → ψ-closed w (x b q) (app1* s) (t b q)
ψ-closed w (closed x p) s t = ψ-closed w p s t
ψ-closed w (∩ b) s t = λ R pr → ψ-closed (w ,,c pr) (b R pr) s (t R pr)
ψ-closed w (if M₂ T1 T2) s (t₁ , (t₂ , t₃)) = t₁ , ((⟶*-trans s t₂) , t₃)
ψ-closed w (▹ X) s t = isCand.cr2 (w X) s t

data _≈δ_ {δ n} (a b : tp δ n) : Set where
 common : ∀ {d} -> (a ⟶δ* d) -> (b ⟶δ* d) -> a ≈δ b

postulate
 sub⟶* : ∀ {δ n m} (σ : tsubst n m) {M N : tp δ _} -> M ⟶δ* N -> [ σ ]tδ M ⟶δ* [ σ ]tδ N
--  sub⟶*2 : ∀ {n m} {M N : tm m} {σ : tsubst n m} -> M ⟶* N -> ∀ (P : tm (n , *)) -> [ σ , M ]t P ⟶* [ σ , N ]t P
--  subeq3 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ ]t M ≡ [ σ , N ]t ([ wkn-vsub ]r M)
 subeq1 : ∀ {δ n m} {σ : tsubst n m} (M : tp δ _) {N} -> [ σ , ([ σ ]t N) ]tδ M ≡ [ σ ]tδ ([ N /x]δ M) 
 --subeq2 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ , N ]t M ≡ [ id-tsub , N ]t ([ tsub-ext σ ]t M)
 subeq2δ : ∀ {δ n m} {σ : tsubst n m} (M : tp δ _) {N} -> [ σ , N ]tδ M ≡ [ id-tsub , N ]tδ ([ tsub-ext σ ]tδ M)
 subeq4 : ∀ {n} {M : tm n} -> [ id-tsub ]t M ≡ M

-- ⟶*cong2 : ∀ {n} {M1 M2 N1 N2 : tm n} -> M1 ≡ M2 -> N1 ≡ N2 -> M1 ⟶* N1 -> M2 ⟶* N2
-- ⟶*cong2 refl refl t = t

-- postulate
--  cr : ∀ {n} {a b c : tm n} -> a ⟶* b -> a ⟶* c -> b ≈ c

-- data pi-inj1-res {n} (A : tm n) B : (C : tm n) -> Set where
--  yep : ∀ {A' B'} -> A ⟶* A' -> B ⟶* B' -> pi-inj1-res A B (Π A' B')

-- pi-inj1 : ∀ {n} {A : tm n} {B C} -> (Π A B) ⟶* C -> pi-inj1-res A B C
-- pi-inj1 refl = yep refl refl
-- pi-inj1 (trans1 () s) -- More generally...

-- pi-inj2 : ∀ {n} {A A' : tm n} {B B'} -> (Π A B) ≈ (Π A' B') -> A ≈ A'
-- pi-inj2 (common x x₁) with pi-inj1 x | pi-inj1 x₁
-- pi-inj2 (common x x₁) | yep x₂ x₃ | yep x₄ x₅ = common x₂ x₄

-- pi-inj3 : ∀ {n} {A A' : tm n} {B B'} -> (Π A B) ≈ (Π A' B') -> B ≈ B'
-- pi-inj3 (common x x₁) with pi-inj1 x | pi-inj1 x₁
-- ... | yep t1 t2 | yep t3 t4 = common t2 t4

[]-cong : ∀ {δ n m} {A B : tp δ n} {σ : tsubst n m} -> A ≈δ B -> [ σ ]tδ A ≈δ [ σ ]tδ B
[]-cong (common x x₁) = common (sub⟶* _ x) (sub⟶* _ x₁)

-- ≈-trans : ∀ {n} {A B C : tm n} -> A ≈ B -> B ≈ C -> A ≈ C
-- ≈-trans (common t1 t2) (common t3 t4) with cr t2 t3
-- ... | common t5 t6 = common (⟶*-trans t1 t5) (⟶*-trans t4 t6)

-- ≈-sym : ∀ {n} {A B : tm n} -> A ≈ B -> B ≈ A
-- ≈-sym (common t1 t2) = common t2 t1

≈-refl : ∀ {δ n} {A : tp δ n} -> A ≈δ A
≈-refl = common refl refl

-- ⟶-≈ : ∀ {n} {A B : tm n} -> A ⟶ B -> A ≈ B
-- ⟶-≈ t = common (trans1 t refl) refl

-- ⟶≈trans : ∀ {n} {A B C : tm n} -> A ≈ B -> B ⟶ C -> A ≈ C
-- ⟶≈trans t u = ≈-trans t (⟶-≈ u)

-- ⟶≈trans' : ∀ {n} {A B C : tm n} -> A ≈ B -> A ⟶ C -> C ≈ B
-- ⟶≈trans' t u = ≈-trans (≈-sym (⟶-≈ u)) t

-- neutral-step : ∀ {n} {C : Set} {A B : tm n} -> neutral A -> A ⟶ B -> C
-- neutral-step (▹ x) ()
-- neutral-step (_·_ ()) β
-- neutral-step (_·_ t) (app1 s) = neutral-step t s
-- neutral-step (if ()) if1
-- neutral-step (if ()) if2
-- neutral-step (if t) (ifc s) = neutral-step t s

-- neutral-step* : ∀ {n} {A B : tm n} -> neutral A -> A ⟶* B -> A ≡ B
-- neutral-step* t refl = refl
-- neutral-step* t (trans1 x s) = neutral-step t x

-- normal-step : ∀ {n} {A B : tm n} {C : Set} -> normal A -> A ⟶ B -> C
-- normal-step ƛ ()
-- normal-step Π ()
-- normal-step tt ()
-- normal-step ff ()
-- normal-step bool ()
-- normal-step set ()
-- normal-step (neut x) s = neutral-step x s

-- normal-step* : ∀ {n} {A B : tm n} -> normal A -> A ⟶* B -> A ≡ B
-- normal-step* t refl = refl
-- normal-step* t (trans1 x s) = normal-step t x

-- bool-≈-neutral : ∀ {n} {A : tm n} {C : Set} -> neutral A -> bool ≈ A -> C
-- bool-≈-neutral t (common x x₁) with normal-step* bool x | neutral-step* t x₁
-- bool-≈-neutral () (common x x₁) | refl | refl

-- set-≈-neutral : ∀ {n} {A : tm n} {C : Set} -> neutral A -> set ≈ A -> C
-- set-≈-neutral t (common x x₁) with normal-step* set x | neutral-step* t x₁
-- set-≈-neutral () (common x x₁) | refl | refl

-- bool≈Π : ∀ {n} {A : tm n} {B} {C : Set} -> bool ≈ (Π A B) -> C
-- bool≈Π (common x x₁) with normal-step* bool x | pi-inj1 x₁
-- bool≈Π (common x x₁) | refl | ()

-- Π≈neutral : ∀ {n} {A : tm n} {B D} {C : Set} -> neutral A -> (Π B D) ≈ A -> C
-- Π≈neutral t (common x x₁) with neutral-step* t x₁ | pi-inj1 x
-- Π≈neutral () (common x x₁) | refl | yep x₂ x₃

-- set≈Π : ∀ {n} {A : tm n} {B} {C : Set} -> set ≈ (Π A B) -> C
-- set≈Π (common x x₁) with normal-step* set x | pi-inj1 x₁
-- set≈Π (common x x₁) | refl | ()

-- bool≈set : ∀ {n} {C : Set} -> _≈_ {n} bool set -> C
-- bool≈set (common x x₁) with normal-step* bool x | normal-step* set x₁
-- bool≈set (common x x₁) | refl | ()

mutual
 lemma3-3 : ∀ {δ n} {A B : tp δ n} {ρ} {M : tm n} (p : Ψ ρ A) (q : Ψ ρ B) -> A ≈δ B -> ψ ρ p M -> ψ ρ q M
 lemma3-3 = {!!}
--  lemma3-3 (closed x p) q t r = lemma3-3 p q (⟶≈trans' t x) r
--  lemma3-3 p (closed x q) t r = lemma3-3 p q (⟶≈trans t x) r
--  lemma3-3 bool bool t r = r
--  lemma3-3 bool (Π q x) t r = bool≈Π t
--  lemma3-3 bool (neut x) t r = bool-≈-neutral x t
--  lemma3-3 (Π p x) bool t r = bool≈Π (≈-sym t)
--  lemma3-3 (Π p x) (Π q x₁) t (r1 , r2) = r1 , (λ b q₁ → lemma3-3 (x b (lemma3-3b p q (pi-inj2 t) q₁)) (x₁ b q₁) ([]-cong (pi-inj3 t)) (r2 b (lemma3-3b p q (pi-inj2 t) q₁)))
--  lemma3-3 (Π p x) (neut x₁) t r = Π≈neutral x₁ t
--  lemma3-3 (neut x) bool t r = bool-≈-neutral x (≈-sym t)
--  lemma3-3 (neut x) (Π q x₁) t r = Π≈neutral x (≈-sym t)
--  lemma3-3 (neut x) (neut x₁) t r = r

--  lemma3-3b : ∀ {n} {A B M : tm n} (p : Ψ A) (q : Ψ B) -> A ≈ B -> ψ q M -> ψ p M
--  lemma3-3b (closed x p) q t r = lemma3-3b p q (⟶≈trans' t x) r 
--  lemma3-3b p (closed x q) t r = lemma3-3b p q (⟶≈trans t x) r
--  lemma3-3b bool bool t r = r
--  lemma3-3b bool (Π q x) t r = bool≈Π t
--  lemma3-3b bool (neut x) t r = bool-≈-neutral x t
--  lemma3-3b (Π p x) bool t r = bool≈Π (≈-sym t)
--  lemma3-3b (Π p x) (Π q x₁) t (r1 , r2) = r1 , (λ b q₁ → lemma3-3b (x b q₁) (x₁ b (lemma3-3 p q (pi-inj2 t) q₁)) ([]-cong (pi-inj3 t)) (r2 b (lemma3-3 p q (pi-inj2 t) q₁)))
--  lemma3-3b (Π p x) (neut x₁) t r = Π≈neutral x₁ t
--  lemma3-3b (neut x) bool t r = bool-≈-neutral x (≈-sym t)
--  lemma3-3b (neut x) (Π q x₁) t r = Π≈neutral x (≈-sym t)
--  lemma3-3b (neut x) (neut x₁) t r = r

lemma3-3c : ∀ {δ n} {ρ} {A : tp δ n} {M : tm n} (p q : Ψ ρ A) -> ψ ρ p M -> ψ ρ q M
lemma3-3c p q t = lemma3-3 p q ≈-refl t



data dctx δ : ctx Unitz -> Set where
 ⊡ : dctx δ ⊡
 _,_ : ∀ {n} -> (Γ : dctx δ n) -> tp δ n -> dctx δ (n , *)

map-dctx : ∀ {δ1 δ2 n} -> (∀ {m} -> tp δ1 m -> tp δ2 m) -> dctx δ1 n -> dctx δ2 n
map-dctx f ⊡ = ⊡
map-dctx f (Γ , T) = map-dctx f Γ , f T

data _∋_∶_ {δ} : ∀ {n} -> dctx δ n -> var n * -> tp δ n -> Set where
 top : ∀ {n} {Γ : dctx δ n} {A} -> (Γ , A) ∋ top ∶ ([ wkn-vsub ]rδ A)
 pop : ∀ {n} {Γ : dctx δ n} {x} {A B} -> Γ ∋ x ∶ B -> (Γ , A) ∋ (pop x) ∶ ([ wkn-vsub ]rδ B)

↑ : ∀ {δ n} -> dctx δ n -> dctx (δ , *) n
↑ = map-dctx [ wkn-vsub ]rδt

mutual
 data wfctx {δ} : ∀ {n} -> dctx δ n -> Set where
  ⊡ : wfctx ⊡
  _,_ : ∀ {n} {Γ : dctx δ n} -> wfctx Γ -> ∀ {A} -> Γ ⊢ A type -> wfctx (Γ , A)

 data _⊢_type {δ n} (Γ : dctx δ n) : tp δ n -> Set where
  Π : ∀ {A B} -> Γ ⊢ A type -> (Γ , A) ⊢ B type -> Γ ⊢ (Π A B) type
  bool : Γ ⊢ bool type
  if : ∀ {M C1 C2} -> Γ ⊢ M ∶ bool -> Γ ⊢ C1 type -> Γ ⊢ C2 type -> Γ ⊢ (if M C1 C2) type
  ∩ : ∀ {B} -> ↑ Γ ⊢ B type -> Γ ⊢ (∩ B) type
 
 data _⊢_∶_ {δ} {n} (Γ : dctx δ n) : tm n -> tp δ n -> Set where
  tt : Γ ⊢ tt ∶ bool
  ff : Γ ⊢ ff ∶ bool
  ▹ : ∀ {A x} -> Γ ⊢ A type -> Γ ∋ x ∶ A -> Γ ⊢ (▹ x) ∶ A
  ƛ : ∀ {A B M} -> Γ ⊢ A type -> (Γ , A) ⊢ M ∶ B -> Γ ⊢ (ƛ M) ∶ (Π A B)
  _·_ : ∀ {A B M N} -> Γ ⊢ M ∶ (Π A B) -> Γ ⊢ N ∶ A -> Γ ⊢ (M · N) ∶ ([ N /x]δ B)
  if : ∀ {C M N1 N2} -> (Γ , bool) ⊢ C type -> Γ ⊢ M ∶ bool -> Γ ⊢ N1 ∶ ([ tt /x]δ C) -> Γ ⊢ N2 ∶ ([ ff /x]δ C) -> Γ ⊢ (if M N1 N2) ∶ ([ M /x]δ C)
  ∩I : ∀ {M B} -> (↑ Γ) ⊢ M ∶ B -> Γ ⊢ M ∶ (∩ B)
  ∩E : ∀ {M B C} -> Γ ⊢ M ∶ (∩ B) -> Γ ⊢ C type -> Γ ⊢ M ∶ [ C /X]δtp B
  conv : ∀ {A B} {M} -> Γ ⊢ A type -> B ≈δ A -> Γ ⊢ M ∶ B -> Γ ⊢ M ∶ A
  -- Remember this is a "dumbed down" system where we don't check convertible under lambdas, etc.
  -- We "should" consider weak normalization, not just weak head?

data Ψs {δ} ρ : ∀ {n m} -> dctx δ n -> tsubst n m -> Set where
 ⊡ : ∀ {m} -> Ψs ρ {m = m} ⊡ tt
 _,_ : ∀ {n m} {Γ} {σ : tsubst n m} {A} {a} -> Ψs ρ Γ σ -> Ψ ρ ([ σ ]tδ A) -> Ψs ρ (Γ , A) (σ , a)

Ψs-wknδ : ∀ {δ} {ρ} {n m} {Γ : dctx δ n} {σ : tsubst n m} {R : cand} -> Ψs ρ Γ σ -> Ψs (ρ ,, R) (↑ Γ) σ
Ψs-wknδ ⊡ = ⊡
Ψs-wknδ (d , x) = (Ψs-wknδ d) , {!!}

data ψs {δ} ρ : ∀ {n m} -> (Γ : dctx δ n) -> (σ : tsubst n m) -> Ψs ρ Γ σ -> Set where
 ⊡ : ∀ {m} -> ψs ρ {m = m} ⊡ tt ⊡
 _,[_]_ : ∀ {n m} {Γ} {σ : tsubst n m} {ps} {A} {a} -> ψs ρ Γ σ ps -> ∀ p -> ψ ρ p a -> ψs ρ (Γ , A) (σ , a) (ps , p)

ψs-wknδ : ∀ {δ} {ρ} {n m} {Γ : dctx δ n} {σ : tsubst n m} {ps : Ψs ρ Γ σ} {R : cand} -> ψs ρ Γ σ ps -> ψs (ρ ,, R) (↑ Γ) σ (Ψs-wknδ ps)
ψs-wknδ ⊡ = ⊡
ψs-wknδ (d ,[ p ] x) = (ψs-wknδ d) ,[ {!!} ] {!!}

_⊨_type : ∀ {δ n} (Γ : dctx δ n) -> tp δ n -> Set
Γ ⊨ A type = ∀ {ρ} (w : areCands ρ) {m} {σ : tsubst _ m} {ps : Ψs ρ Γ σ} -> ψs ρ Γ σ ps -> Ψ ρ ([ σ ]tδ A)

Π' : ∀ {δ n} {Γ} (A : tp δ n) B -> Γ ⊨ A type -> (Γ , A) ⊨ B type -> Γ ⊨ (Π A B) type
Π' A B t1 t2 = λ {ρ} w x → Π (t1 w x) (λ a x₁ → subst (Ψ ρ) (subeq2δ B) (t2 w (x ,[ t1 w x ] x₁)))

_⊨_∶'_[_] : ∀ {δ n} (Γ : dctx δ n) (M : tm n) A -> Γ ⊨ A type -> Set
Γ ⊨ M ∶' A [ d ] = ∀ {ρ} (w : areCands ρ) {m} {σ : tsubst _ m} {ps : Ψs ρ Γ σ} (qs : ψs ρ Γ σ ps) -> ψ ρ (d w qs) ([ σ ]t M)

_⊨_∶_ : ∀ {δ n} (Γ : dctx δ n) (M : tm n) A -> Set
Γ ⊨ M ∶ A = ∀ {ρ} (w : areCands ρ) {m} {σ : tsubst _ m} {ps : Ψs ρ Γ σ} (qs : ψs ρ Γ σ ps) (p : Ψ ρ ([ σ ]tδ A)) -> ψ ρ p ([ σ ]t M)

κ : ∀ {A B : Set} -> B -> A -> B
κ b = λ _ -> b

Πinv2 : ∀ {δ n} {Γ : dctx δ n} A B -> Γ ⊨ (Π A B) type -> (Γ , A) ⊨ B type
Πinv2 A B t w (x1 ,[ _ ] x2) with t w x1
Πinv2 A B t w (x1 ,[ p ] x2) | Π q x = subst (Ψ _) (sym (subeq2δ B)) (x _ (lemma3-3c p q x2))
Πinv2 A B t w (x1 ,[ p ] x2) | closed () q

-- {-⊨type-cong : ∀ {n} {Γ : dctx n} {A B} -> A ≡ B -> Γ ⊨ A type -> Γ ⊨ B type
-- ⊨type-cong refl t = t -}

⊨subst : ∀ {δ n} {Γ : dctx δ n} A B -> (Γ , A) ⊨ B type -> (p : Γ ⊨ A type) -> ∀ {N} -> Γ ⊨ N ∶ A -> Γ ⊨ ([ N /x]δ B) type
⊨subst A B t p n w x = subst (Ψ _) (subeq1 B) (t w (x ,[ p w x ] n w x (p w x)))

-- φeqdep : ∀ {n} {B B' M : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> φ p M -> φ q M
-- φeqdep p q refl t = lemma3-3c' p q t

-- φeqdep' : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> M ⟶ N -> φ p N -> φ q M
-- φeqdep' p q refl s t = lemma3-3c' p q (φ-closed p (trans1 s refl) t)

-- φeq : ∀ {n} {B B' M N : tm n} (p : Φ B) (q : Φ B') -> B' ⟶* B -> M ⟶* N -> φ p N -> φ q M
-- φeq p q s1 s t = lemma3-3' p q (common refl s1) (φ-closed p s t)

φeq' : ∀ {δ n} {B B' : tp δ n} {M N : tm n} {ρ} (w : areCands ρ) (p : Ψ ρ B) (q : Ψ ρ B') -> B ≈δ B' -> M ⟶* N -> ψ ρ p N -> ψ ρ q M
φeq' w p q s1 s t = lemma3-3 p q s1 (ψ-closed w p s t)

-- ƛ' : ∀ {n} {Γ} (A : tm n) B M (d1 : Γ ⊨ A type) (d2 : (Γ , A) ⊨ B type) ->  (Γ , A) ⊨ M ∶ B -> Γ ⊨ (ƛ M) ∶' (Π A B) [ Π' A B d1 d2 ]
-- ƛ' A B M d1 d2 t {σ = σ} qs = (norm refl ƛ) , (λ b q ->
--    let z = (d2 (qs ,[ d1 qs ] q))
--    in φeqdep' z (subst Φ (subeq2 B) z) (subeq2 B) β (subst (φ z) (subeq2 M) (t (qs ,[ d1 qs ] q) z)))

-- φeqdep'' : ∀ {n} {B B' M : tm n} (p : Φ B) -> (e : B ≡ B') -> φ p M -> φ (subst Φ e p) M
-- φeqdep'' p refl t = t

-- app' : ∀ {n} {Γ} (A : tm n) B M N (d1 : Γ ⊨ A type) (d2 : (Γ , A) ⊨ B type) -> Γ ⊨ M ∶ (Π A B) -> (t : Γ ⊨ N ∶ A) -> Γ ⊨ (M · N) ∶' ([ N /x] B) [ ⊨subst A B d2 d1 t ]
-- app' A B M N d1 d2 t1 t2 {σ = σ} qs with t1 qs (Π' A B d1 d2 qs)
-- app' A B M N d1 d2 t1 t2 {σ = σ} qs | q1 , q2 with q2 ([ σ ]t N) (t2 qs (d1 qs))
-- ... | z2 = φeqdep (subst Φ (subeq2 B) (d2 (qs ,[ d1 qs ] t2 qs (d1 qs))))
--              (subst Φ (subeq1 B) (d2 (qs ,[ d1 qs ] t2 qs (d1 qs)))) (trans (sym (subeq2 B)) (subeq1 B)) z2

⊨conv : ∀ {δ n} {Γ} {A B : tp δ n} M (p : Γ ⊨ B type) (q : Γ ⊨ A type) -> B ≈δ A -> Γ ⊨ M ∶ B -> Γ ⊨ M ∶' A [ q ]
⊨conv M p q s t w qs = φeq' w (p w qs) (q w qs) ([]-cong s) refl (t w qs (p w qs))

norm-is-cand : isCand normalizable
norm-is-cand = record {
  cr1 = λ z → z;
  cr2 = normalizable-closed;
  cr3 = λ x → norm refl (neut x)
 }

mutual
 reflect : ∀ {δ n} {A : tp δ n} {M : tm n} ρ -> areCands ρ -> (p : Ψ ρ A) -> neutral M -> ψ ρ p M
 reflect ρ w bool r = _ , (refl , (neut r))
 reflect ρ w (Π p x) r = norm refl (neut r) , λ b q → reflect ρ w (x b q) (_·_ r)
 reflect ρ w (if x x1 x2) r = _ , (refl , r)
 reflect ρ w (closed x p) r = reflect ρ w p r
 reflect ρ w (∩ b) r = λ R pr → reflect (ρ ,, R) (w ,,c pr) (b R pr) r
 reflect ρ w (▹ X) r = isCand.cr3 (w X) r

 reify : ∀ {δ n} {A : tp δ n} {M : tm n} ρ -> areCands ρ -> (p : Ψ ρ A) -> ψ ρ p M -> normalizable M
 reify ρ w bool (x₁ , (x₂ , x₃)) = norm x₂ (normal-bool-normal x₃)
 reify ρ w (Π p x) (h , _) = h
 reify ρ w (if x x1 x2) (x₁ , (x₂ , x₃)) = norm x₂ (neut x₃)
 reify ρ w (closed x p) r = reify ρ w p r
 reify ρ w (∩ b) r = reify (ρ ,, normalizable)
                            (w ,,c norm-is-cand)
                            (b normalizable norm-is-cand)
                            (r normalizable norm-is-cand)
 reify ρ w (▹ X) r = isCand.cr1 (w X) r

reifyt : ∀ {δ n} {A : tp δ n} ρ -> Ψ ρ A -> normalizableδ A
reifyt ρ bool = norm refl bool
reifyt ρ (Π t x) = norm refl Π
reifyt ρ (if x x1 x2) = norm refl (if x) --(neut x)
reifyt ρ (closed x t) with reifyt ρ t
reifyt ρ (closed x₂ t) | norm x x₁ = norm (trans1 x₂ x) x₁
reifyt ρ (∩ b) = norm refl ∩
reifyt ρ (▹ X) = norm refl ▹

-- -- TODO: Try doing this in "premonoidal category" style
-- if' : ∀ {n} {Γ} (C : tm (n , *)) M N1 N2 (d : (Γ , bool) ⊨ C type) -> (t : Γ ⊨ M ∶ bool) -> Γ ⊨ N1 ∶ ([ tt /x] C) -> Γ ⊨ N2 ∶ ([ ff /x] C) -> Γ ⊨ (if M N1 N2) ∶' ([ M /x] C) [ ⊨subst bool C d (κ bool) t ]
-- if' C M N1 N2 d t t1 t2 qs with t qs bool
-- if' C M N1 N2 d t t1 t2 qs | .tt , (q1 , tt) = φeq (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , tt)))) (subst Φ (subeq1 C) (d (qs ,[ bool ] (, q1 , tt))))
--     (⟶*cong2 (subeq1 C) (subeq1 C) (sub⟶*2 q1 C)) (⟶*-trans (if* q1) (trans1 if1 refl)) (t1 qs (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , tt)))))
-- if' C M N1 N2 d t t1 t2 qs | .ff , (q1 , ff) = φeq (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , ff)))) (subst Φ (subeq1 C) (d (qs ,[ bool ] (, q1 , ff))))
--     (⟶*cong2 (subeq1 C) (subeq1 C) (sub⟶*2 q1 C)) (⟶*-trans (if* q1) (trans1 if2 refl)) (t2 qs (subst Φ (subeq1 C) (d (qs ,[ bool ] (, refl , ff)))))
-- if' C M N1 N2 d t t1 t2 qs | M' , (q1 , neut x) = φ-closed (subst Φ (subeq1 C) (d (qs ,[ bool ] (M' , (q1 , neut x))))) (if* q1) (reflect' (subst Φ (subeq1 C) (d (qs ,[ bool ] (M' , (q1 , neut x))))) (if x))

mem : ∀ {δ n} {Γ} {A : tp δ n} x -> Γ ∋ x ∶ A -> Γ ⊨ (▹ x) ∶ A
mem .top (top {_} {_} {A}) p1 (p2 ,[ p ] x) p3 = {!φeqdep p p3!}
mem .(pop x) (pop {n} {Γ} {x} d) p1 p2 p3 = {!!}
-- mem .top (top {_} {_} {A}) (qs ,[ p ] x) p₁ = φeqdep p p₁ (subeq3 A) x
-- mem .(pop x) (pop {n} {Γ} {x} {A} {B} d) (qs ,[ p ] x₁) p₁ = φeqdep (subst Φ (sym (subeq3 B)) p₁) p₁ (subeq3 B) (mem x d qs (subst Φ (sym (subeq3 B)) p₁))

mutual
 lem1 : ∀ {δ n A} (Γ : dctx δ n) -> Γ ⊢ A type -> Γ ⊨ A type
 lem1 Γ (Π {A} {B} t t₁) = Π' A B (lem1 Γ t) (lem1 (Γ , A) t₁)
 lem1 Γ bool = λ _ _ → bool
 lem1 Γ (if x t t₁) = {!!}
 lem1 Γ (∩ t) = λ w x → ∩ (λ R x₁ → lem1 _ t (w ,,c x₁) (ψs-wknδ x))
 
--   -- .. Could we do this equivalently by showing Γ ⊢ M ∶ A implies Γ ⊢ A type, and then appealing to lem1?
--  -- Or alternatively, can we employ the strategy of requiring that Φ A in lem3, analogous to the assumption that Γ ⊢ A type before checking Γ ⊢ M ∶ A?
 lem2 : ∀ {δ n M A} (Γ : dctx δ n)  -> Γ ⊢ M ∶ A -> Γ ⊨ A type
 lem2 Γ tt = λ _ _ → bool
 lem2 Γ ff = λ _ _ → bool
 lem2 Γ (▹ x₁ x₂) = lem1 Γ x₁
 lem2 Γ (ƛ {A} {B} x d) = Π' A B (lem1 Γ x) (lem2 (Γ , A) d)
 lem2 Γ (_·_ {A} {B} d d₁) = ⊨subst A B (Πinv2 A B (lem2 Γ d)) (lem2 Γ d₁) (lem3 Γ d₁)
 lem2 Γ (if {C} x d d₁ d₂) = ⊨subst bool C (lem1 (Γ , bool) x) (λ _ _ → bool) (lem3 Γ d)
 lem2 Γ (∩I d) = λ w x → ∩ (λ R x₁ → lem2 _ d (w ,,c x₁) (ψs-wknδ x))
 lem2 Γ (∩E d x) = {!!}
 lem2 Γ (conv x x₁ d) = lem1 Γ x
--  lem2 Γ bool = κ set
--  lem2 Γ tt = κ bool
--  lem2 Γ ff = κ bool
--  lem2 Γ (▹ x₁ x₂) = lem1 Γ x₁
--  lem2 Γ (Π t t₁) = κ set
--  lem2 Γ (ƛ {A} {B} x t) = Π' A B (lem1 Γ x) (lem2 (Γ , A) t)
--  lem2 Γ (_·_ {A} {B} t t₁) = ⊨subst A B (Πinv2 A B (lem2 Γ t)) (lem2 Γ t₁) (lem3 Γ t₁)
--  lem2 Γ (if {C} x t t₁ t₂) = ⊨subst bool C (lem1 (Γ , bool) x) (κ bool) (lem3 Γ t)
--  lem2 Γ (conv x x₁ t) = lem1 Γ x

 lem3 : ∀ {δ n M A} (Γ : dctx δ n) (d : Γ ⊢ M ∶ A) -> Γ ⊨ M ∶ A
 lem3 Γ t qs w p = lemma3-3c (lem2 Γ t qs w) p (lem3' Γ t qs w)

 lem3' : ∀ {δ n M A} (Γ : dctx δ n) (d : Γ ⊢ M ∶ A) -> Γ ⊨ M ∶' A [ lem2 Γ d ]
 lem3' Γ tt = λ _ _ -> (tt , (refl , tt))
 lem3' Γ ff = λ _ _ -> (ff , (refl , ff))
 lem3' Γ (▹ {A} {x} x₁ x₂) = λ w qs → mem x x₂ w qs (lem1 Γ x₁ w qs)
 lem3' Γ (ƛ x d) = {!!}
 lem3' Γ (d · d₁) = {!!}
 lem3' Γ (if x d d₁ d₂) = {!!}
 lem3' Γ (∩I d) = {!!}
 lem3' Γ (∩E d x) = {!!}
 lem3' Γ (conv {A} {B} {M} x x₁ d) = ⊨conv M (lem2 Γ d) (lem1 Γ x) x₁ (lem3 Γ d)
--  lem3' Γ (ƛ {A} {B} {M} x t) = ƛ' A B M (lem1 Γ x) (lem2 (Γ , A) t) (lem3 (Γ , A) t)
--  lem3' Γ (_·_ {A} {B} {M} {N} t t₁) = app' A B M N (lem2 Γ t₁) (Πinv2 A B (lem2 Γ t)) (lem3 Γ t) (lem3 Γ t₁)
--  lem3' Γ (if {C} {M} {N1} {N2} x t t₁ t₂) = if' C M N1 N2 (lem1 (Γ , bool) x) (lem3 Γ t) (lem3 Γ t₁) (lem3 Γ t₂)


-- -- Huh I think the more natural thing to do for a "weak head normal form"
-- -- for arrow is to say that any term of arrow type is normal?
-- -- Maybe use CBPV to motivate? Function types are computation types.. need to thunk to turn into value types...
-- -- Or.. for weak normalization, could we just add "halts" to the definition of the logical predicate?

yay1 : ∀ {M} {A : tp ⊡ ⊡}  -> ⊡ ⊢ M ∶ A -> normalizable M
yay1 d = subst normalizable subeq4 (reify {n = ⊡} (λ ()) (λ ()) (lem2 ⊡ d (λ ()) ⊡) (lem3' _ d (λ ()) ⊡))

-- {-
-- mutual
--  idΦ : ∀ {n} {Γ : dctx n} -> wfctx Γ -> Φs Γ id-tsub
--  idΦ ⊡ = ⊡
--  idΦ (d , x) with idΦ d | lem1 _ x (idφ d)
--  ... | q1 | q2 = {!!} , {!!} -- TODO: Figure out how to do weakening... Hmm one way is to do it syntactically, then use lem1 with the weakened d
 
--  idφ : ∀ {n} {Γ : dctx n} (d : wfctx Γ) -> φs _ id-tsub (idΦ d)
--  idφ ⊡ = ⊡
--  idφ (d , x) = {!!} ,[ {!!} ] {!!}

-- yay : ∀ {n M A} {Γ : dctx n} -> wfctx Γ -> Γ ⊢ M ∶ A -> normalizable M
-- yay d0 d with reify' (lem2 _ d (idφ d0)) (lem3' _ d (idφ d0))
-- ... | q = {!!} -}

-- -- Do the corollary: type checking is decidable (i.e. define algorithmic typing, show it's complete)