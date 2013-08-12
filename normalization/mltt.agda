module mltt where
open import FinMap
open import Unit
open import Data.Product hiding (_×_)
open import Product
open import Relation.Binary.PropositionalEquality

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
 if2 : ∀ M N -> if ff M N ⟶ N
 app1 : ∀ {M M' N} -> M ⟶ M' -> (M · N) ⟶ (M' · N)
 app2 : ∀ {M N N'} -> N ⟶ N' -> (M · N) ⟶ (M · N')
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

app2* : ∀ {n} {M M' N : tm n} -> M ⟶* M' -> (N · M) ⟶* (N · M')
app2* refl = refl
app2* (trans1 x s) = trans1 (app2 x) (app2* s)

if* : ∀ {n} {M M' N1 N2 : tm n} -> M ⟶* M' -> (if M N1 N2) ⟶* (if M' N1 N2)
if* refl = refl
if* (trans1 x t) = trans1 (ifc x) (if* t)

mutual
 data neutral {n} : tm n -> Set where
  ▹ : ∀ x -> neutral (▹ x)
  _·_ : ∀ {M N} -> neutral M -> normal N -> neutral (M · N)
  if : ∀ {M N P} -> neutral M -> normal N -> normal P -> neutral (if M N P) 

 data normal {n} : tm n -> Set where
  ƛ : ∀ {M} -> normal M -> normal (ƛ M)
  Π : ∀ {A B} -> normal A -> normal B -> normal (Π A B)
  tt : normal tt
  ff : normal ff
  bool : normal bool
  set : normal set
  neut : ∀ {M} -> neutral M -> normal M

data normal-bool {n} : tm n -> Set where
 tt : normal-bool tt
 ff : normal-bool ff
 neut : ∀ M -> neutral M -> normal-bool M

mutual
 data Ψ {n} : tm n -> Set where
  bool : Ψ bool
  Π : ∀ {A B} -> (p : Ψ A) -> (∀ a -> ψ p a -> Ψ ([ a /x] B)) -> Ψ (Π A B)
  neut : ∀ A -> neutral A -> Ψ A
  closed : ∀ {A B} -> A ⟶ B -> Ψ B -> Ψ A

 ψ : ∀ {n} -> {A : tm n} -> Ψ A -> tm n -> Set
 ψ bool a = ∃ (λ b → (a ⟶* b) × normal-bool b)
 ψ (Π p f) a = ∀ b (q : ψ p b) → ψ (f b q) (a · b)
 ψ (neut A x) a = ∃ (λ b → (a ⟶* b) × neutral b)
 ψ (closed x p) a = ψ p a

Ψ-closed⟶* : ∀ {n} {A B : tm n} -> A ⟶* B -> Ψ B -> Ψ A
Ψ-closed⟶* refl t = t
Ψ-closed⟶* (trans1 x s) t = closed x (Ψ-closed⟶* s t)

ψ-closed : ∀ {n} {A : tm n} {M N} -> (p : Ψ A) -> M ⟶* N -> ψ p N -> ψ p M
ψ-closed bool s (t1 , (s2 , norm)) = t1 , ((⟶*-trans s s2) , norm)
ψ-closed (Π p x) s t = λ b q → ψ-closed (x b q) (app1* s) (t b q)
ψ-closed (neut A x) s (t1 , (s2 , neu)) = t1 , ((⟶*-trans s s2) , neu)
ψ-closed (closed x p) s t = ψ-closed p s t

-- I could use this technique directly for LF (i.e. MLTT without the universe)
-- as an alternative to the erasure-based proof...

mutual
 data Φ {n} : tm n -> Set where
  bool : Φ bool
  Π : ∀ {A B} -> (p : Φ A) -> (∀ a -> φ p a -> Φ ([ a /x] B)) -> Φ (Π A B)
  neut : ∀ A -> neutral A -> Φ A
  closed : ∀ {A B} -> A ⟶ B -> Φ B -> Φ A
  set : Φ set

 φ : ∀ {n} -> {A : tm n} -> Φ A -> tm n -> Set
 φ bool a = ∃ (λ b → (a ⟶* b) × normal-bool b)
 φ (Π p f) a = ∀ b (q : φ p b) → φ (f b q) (a · b)
 φ (neut A x) a = ∃ (λ b → (a ⟶* b) × neutral b)
 φ (closed x p) a = φ p a
 φ set a = Ψ a

Φ-closed⟶* : ∀ {n} {A B : tm n} -> A ⟶* B -> Φ B -> Φ A
Φ-closed⟶* refl t = t
Φ-closed⟶* (trans1 x s) t = closed x (Φ-closed⟶* s t)

φ-closed : ∀ {n} {A : tm n} {M N} -> (p : Φ A) -> M ⟶* N -> φ p N -> φ p M
φ-closed bool s (t1 , (s2 , norm)) = t1 , ((⟶*-trans s s2) , norm)
φ-closed (Π p x) s t = λ b q → φ-closed (x b q) (app1* s) (t b q)
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

postulate
 sub⟶* : ∀ {n m} (σ : tsubst n m) {M N} -> M ⟶* N -> [ σ ]t M ⟶* [ σ ]t N
 sub⟶*2 : ∀ {n m} {M N : tm m} {σ : tsubst n m} -> M ⟶* N -> ∀ (P : tm (n , *)) -> [ σ , M ]t P ⟶* [ σ , N ]t P
 subeq1 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ , ([ σ ]t N) ]t M ≡ [ σ ]t ([ N /x] M) 
 subeq2 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ , N ]t M ≡ [ id-tsub , N ]t ([ tsub-ext σ ]t M)

⟶*cong2 : ∀ {n} {M1 M2 N1 N2 : tm n} -> M1 ≡ M2 -> N1 ≡ N2 -> M1 ⟶* N1 -> M2 ⟶* N2
⟶*cong2 refl refl t = t

{-
mutual
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
 lem2 Γ {σ} {ps} qs (ƛ {A} {B} {M} x d) = (Π (lem1 Γ qs x) (λ a x₁ → subst Φ (subeq2 B) (Σ.proj₁ (f a x₁)))) , (λ b q → φ-closed (subst Φ (subeq2 B) (Σ.proj₁ (f b q))) (trans1 (β _ _) refl) (subst (φ (subst Φ (subeq2 B) (Σ.proj₁ (f b q)))) (subeq2 M) {!just a bit of eqdep...!}))
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

data normalizable {n} (M : tm n) : Set where
 norm : ∀ N -> M ⟶* N -> normal N -> normalizable M

-- Can I just use "normal" and get rid of normal-bool?
normal-bool-normal : ∀ {n} {M : tm n} -> normal-bool M -> normal M
normal-bool-normal tt = tt
normal-bool-normal ff = ff
normal-bool-normal (neut A x) = neut x

-- Huh I think the more natural thing to do for a "weak head normal form"
-- for arrow is to say that any term of arrow type is normal?
-- Maybe use CBPV to motivate? Function types are computation types.. need to thunk to turn into value types...
-- Or.. for weak normalization, could we just add "halts" to the definition of the logical predicate?

mutual
 reflect : ∀ {n} {A M : tm n} -> (p : Ψ A) -> neutral M -> ψ p M
 reflect bool r = _ , (refl , (neut _ r))
 reflect (Π p x) r = f
  where f : ∀ b -> (q : ψ p b) -> ψ (x b q) (_ · b)
        f b q with reify p q
        f b q | norm N x₁ x₂ = ψ-closed (x b q) (app2* x₁) (reflect (x b q) (r · x₂))
 reflect (neut A x) r = _ , (refl , r)
 reflect (closed x p) r = reflect p r

 reify : ∀ {n} {A M : tm n} -> (p : Ψ A) -> ψ p M -> normalizable M
 reify bool (x₁ , (x₂ , x₃)) = norm x₁ x₂ (normal-bool-normal x₃)
 reify (Π p x) r = {!!}
 reify (neut A x) (x₁ , (x₂ , x₃)) = norm x₁ x₂ (neut x₃)
 reify (closed x p) r = reify p r