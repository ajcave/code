module mltt-1dtt where
open import FinMap public
open import Unit public
open import Data.Product public hiding (_×_)
open import Product public hiding (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality public
open import Data.Empty public

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
 Id : (A : tm n) (M N : tm n) -> tm n
 subst : (A : tm n) (B : tm (n , *)) (M N : tm n) (P : tm n) 
{- tt ff bool set : tm n
 if : (M N P : tm n) -> tm n -}

[_]r : ∀ {n m} -> vsubst n m -> tm n -> tm m
[_]r σ (▹ x) = ▹ ([ σ ]v x)
[_]r σ (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[_]r σ (Π A B) = Π ([ σ ]r A) ([ vsub-ext σ ]r B)
[_]r σ (M · M₁) = ([ σ ]r M) · ([ σ ]r M₁)
{- [_]r σ tt = tt
[_]r σ ff = ff
[_]r σ bool = bool
[_]r σ set = set
[_]r σ (if M M₁ M₂) = if ([ σ ]r M) ([ σ ]r M₁) ([ σ ]r M₂) -}

tsubst : ∀ (n m : ctx Unit) -> Set
tsubst n m = gksubst n (tm m)

tsub-ext : ∀ {n m} -> tsubst n m -> tsubst (n , *) (m , *)
tsub-ext σ = (gmap [ wkn-vsub ]r σ) , (▹ top)

id-tsub : ∀ {n} -> tsubst n n
id-tsub {⊡} = tt
id-tsub {n , *} = tsub-ext id-tsub --gmap ▹ id-vsub

[_]t : ∀ {n m} -> tsubst n m -> tm n -> tm m
[_]t σ (▹ x) = [ σ ]v x
[_]t σ (ƛ M) = ƛ ([ tsub-ext σ ]t M)
[_]t σ (Π A B) = Π ([ σ ]t A) ([ tsub-ext σ ]t B)
[_]t σ (M · M₁) = ([ σ ]t M) · ([ σ ]t M₁)
{- [_]t σ tt = tt
[_]t σ ff = ff
[_]t σ bool = bool
[_]t σ set = set
[_]t σ (if M M₁ M₂) = if ([ σ ]t M) ([ σ ]t M₁) ([ σ ]t M₂) -}

[_/x] : ∀ {n} -> tm n -> tm (n , *) -> tm n
[ M /x] N = [ id-tsub , M ]t N

data _⟶_ {n} : ∀ (M N : tm n) -> Set where
 β : ∀ {M N} -> ((ƛ M) · N) ⟶ [ N /x] M
 {- if1 : ∀ {M N} -> if tt M N ⟶ M
 if2 : ∀ {M N} -> if ff M N ⟶ N -}
 app1 : ∀ {M M' N} -> M ⟶ M' -> (M · N) ⟶ (M' · N)
 app2 : ∀ {M N N'} -> N ⟶ N' -> (M · N) ⟶ (M · N')
{- ifc : ∀ {M M' N1 N2} -> M ⟶ M' -> if M N1 N2 ⟶ if M' N1 N2
 ifc1 : ∀ {M N1 N1' N2} -> N1 ⟶ N1' -> if M N1 N2 ⟶ if M N1' N2
 ifc2 : ∀ {M N1 N2 N2'} -> N2 ⟶ N2' -> if M N1 N2 ⟶ if M N1 N2' -}
 ƛ : ∀ {M M'} -> M ⟶ M' -> (ƛ M) ⟶ (ƛ M')
 Π1 : ∀ {A A' B} -> A ⟶ A' -> (Π A B) ⟶ (Π A' B)
 Π2 : ∀ {A B B'} -> B ⟶ B' -> (Π A B) ⟶ (Π A B')
 

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

Π1* : ∀ {n} {M M' : tm n} {N} -> M ⟶* M' -> (Π M N) ⟶* (Π M' N)
Π1* refl = refl
Π1* (trans1 x s) = trans1 (Π1 x) (Π1* s)

Π2* : ∀ {n} {N : tm n} {M M'} -> M ⟶* M' -> (Π N M) ⟶* (Π N M')
Π2* refl = refl
Π2* (trans1 x s) = trans1 (Π2 x) (Π2* s)

Π* : ∀ {n} {N N' : tm n} {M M'} -> N ⟶* N' -> M ⟶* M' -> (Π N M) ⟶* (Π N' M')
Π* s1 s2 = ⟶*-trans (Π1* s1) (Π2* s2)

{- if* : ∀ {n} {M M' N1 N2 : tm n} -> M ⟶* M' -> (if M N1 N2) ⟶* (if M' N1 N2)
if* refl = refl
if* (trans1 x t) = trans1 (ifc x) (if* t) -}

ƛ* : ∀ {n} {M M' : tm (n , *)} -> M ⟶* M' -> (ƛ M) ⟶* (ƛ M')
ƛ* refl = refl
ƛ* (trans1 x t) = trans1 (ƛ x) (ƛ* t)

mutual
 data neutral {n} : tm n -> Set where
  ▹ : ∀ x -> neutral (▹ x)
  _·_ : ∀ {M N} -> neutral M  -> normal N  -> neutral (M · N)
 {- if : ∀ {M N P} -> neutral M  -> normal N -> normal P  -> neutral (if M N P) -}

 data normal {n} : tm n -> Set where
  ƛ : ∀ {M} -> normal M  -> normal (ƛ M)
  Π : ∀ {A B} -> normal A -> normal B  -> normal (Π A B)
{-  tt : normal tt
  ff : normal ff
  bool : normal bool
  set : normal set -}
  neut : ∀ {M} -> neutral M -> normal M

{- data normal-bool {n} : tm n -> Set where
 tt : normal-bool tt
 ff : normal-bool ff
 neut : ∀ {M} -> neutral M -> normal-bool M -}

data normalizable {n} (M : tm n) : Set where
 norm : ∀ {N} -> M ⟶* N -> normal N -> normalizable M

-- Can I just use "normal" and get rid of normal-bool?
{-normal-bool-normal : ∀ {n} {M : tm n} -> normal-bool M -> normal M
normal-bool-normal tt = tt
normal-bool-normal ff = ff
normal-bool-normal (neut x) = neut x -}

normalizable-closed : ∀ {n} {M N : tm n} -> M ⟶* N -> normalizable N -> normalizable M
normalizable-closed p (norm q r) = norm (⟶*-trans p q) r

[_]rs : ∀ {n m k} (w : vsubst m k) (σ : tsubst n m) -> tsubst n k
[ w ]rs σ = gmap [ w ]r σ

[_]tr : ∀ {n m k} (σ : tsubst m k) (w : vsubst n m) -> tsubst n k
[ σ ]tr w = gmap [ σ ]v w

postulate
 ren⟶*' : ∀ {n m} (σ : vsubst n m) {M N} -> M ⟶ N -> [ σ ]r M ⟶ [ σ ]r N
 ren⟶* : ∀ {n m} (σ : vsubst n m) {M N} -> M ⟶* N -> [ σ ]r M ⟶* [ σ ]r N
 sub⟶*' : ∀ {n m} (σ : tsubst n m) {M N} -> M ⟶ N -> [ σ ]t M ⟶ [ σ ]t N
 sub⟶* : ∀ {n m} (σ : tsubst n m) {M N} -> M ⟶* N -> [ σ ]t M ⟶* [ σ ]t N
 ren-ext-comp : ∀ {n m k} {w : vsubst n m} {w' : vsubst m k} B
   -> [ vsub-ext (w' ∘v w) ]r B ≡ [ vsub-ext w' ]r ([ vsub-ext w ]r B)
 sub⟶*2 : ∀ {n m} {M N : tm m} {σ : tsubst n m} -> M ⟶* N -> ∀ (P : tm (n , *)) -> [ σ , M ]t P ⟶* [ σ , N ]t P
 subeq3 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ ]t M ≡ [ σ , N ]t ([ wkn-vsub ]r M)
 subeq1 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ , ([ σ ]t N) ]t M ≡ [ σ ]t ([ N /x] M) 
 --subeq2' : ∀ {n m} {w : vsubst n m} M {N} -> [ ([ id-tsub ]tr w) , N ]t M ≡ [ id-tsub , N ]t ([ vsub-ext w ]r M)
 subeq2 : ∀ {n m} {σ : tsubst n m} M {N} -> [ σ , N ]t M ≡ [ id-tsub , N ]t ([ tsub-ext σ ]t M)
 subeq4 : ∀ {n} {M : tm n} -> [ id-tsub ]t M ≡ M
 reneq4 : ∀ {n} {M : tm n} -> [ id-vsub ]r M ≡ M
 reneq4' : ∀ {n k} {σ : tsubst n k} -> [ id-vsub ]rs σ ≡ σ
 rename-norm : ∀ {n m} {w : vsubst n m} {A} -> normal A -> normal ([ w ]r A)
 rename-neut : ∀ {n m} {w : vsubst n m} {A} -> neutral A -> neutral ([ w ]r A)
 ren-comp : ∀ {n m k} {w : vsubst m k} {v : vsubst n m} M -> [ w ]r ([ v ]r M) ≡ [ w ∘v v ]r M
 ren-sub-comp : ∀ {n m k} {w : vsubst m k} {σ : tsubst n m} M -> [ w ]r ([ σ ]t M) ≡ [ [ w ]rs σ ]t M
 sub-ren-comp : ∀ {n m k} {σ : tsubst m k} {w : vsubst n m} M -> [ σ ]t ([ w ]r M) ≡ [ [ σ ]tr w ]t M
 sub-ren-ext-comp :  ∀ {n m k} {σ : tsubst m k} {w : vsubst n m}
  -> ([ tsub-ext σ ]tr (vsub-ext w)) ≡ (tsub-ext ([ σ ]tr w))
 ren-sub-ext-comp :  ∀ {n m k} {w : vsubst m k} {σ : tsubst n m}
  -> ([ vsub-ext w ]rs (tsub-ext σ)) ≡ (tsub-ext ([ w ]rs σ))
 
subeq6 : ∀ {n m} (B : tm (n , *)) {N} {w : vsubst n m} -> [ N /x] ([ vsub-ext w ]r B) ≡ [ [ id-tsub ]tr w , N ]t B
subeq6 B {N} = trans (sub-ren-comp B) (cong (λ α → [ α , N ]t B) (gmap-funct _))

subeq5 : ∀ {n m k} {σ : tsubst m k} {N} {w : vsubst n m} -> [ σ , N ]tr (gmap pop w) ≡ [ σ ]tr w
subeq5 = gmap-funct _

postulate
 subeq7 : ∀ {n} {B : tm (n , *)} -> [ id-tsub , ▹ top ]t ([ vsub-ext wkn-vsub ]r B) ≡ B
 {-subeq7 {n} {B} = trans
 (subeq6 B)
 (trans (cong (λ α → [ α , ▹ top ]t B) (trans (gmap-funct id-vsub) (trans (gmap-cong {!!}) (sym (gmap-funct id-vsub))))) subeq4) -}
 
{-rename-norm-bool : ∀ {n m} {w : vsubst n m} {A} -> normal-bool A -> normal-bool ([ w ]r A)
rename-norm-bool tt = tt
rename-norm-bool ff = ff
rename-norm-bool (neut y) = neut (rename-neut y) -}

data _≈_ {n} (a b : tm n) : Set where
 common : ∀ {d} -> (a ⟶* d) -> (b ⟶* d) -> a ≈ b


⟶*cong2 : ∀ {n} {M1 M2 N1 N2 : tm n} -> M1 ≡ M2 -> N1 ≡ N2 -> M1 ⟶* N1 -> M2 ⟶* N2
⟶*cong2 refl refl t = t

postulate
 cr : ∀ {n} {a b c : tm n} -> a ⟶* b -> a ⟶* c -> b ≈ c

data pi-inj1-res {n} (A : tm n) B : (C : tm n) -> Set where
 yep : ∀ {A' B'} -> A ⟶* A' -> B ⟶* B' -> pi-inj1-res A B (Π A' B')

pi-inj1 : ∀ {n} {A : tm n} {B C} -> (Π A B) ⟶* C -> pi-inj1-res A B C
pi-inj1 refl = yep refl refl
pi-inj1 (trans1 (Π1 t) s) with pi-inj1 s
pi-inj1 (trans1 (Π1 t) s) | yep x x₁ = yep (trans1 t x) x₁
pi-inj1 (trans1 (Π2 t) s) with pi-inj1 s
pi-inj1 (trans1 (Π2 t) s) | yep x x₁ = yep x (trans1 t x₁)

pi-inj2 : ∀ {n} {A A' : tm n} {B B'} -> (Π A B) ≈ (Π A' B') -> A ≈ A'
pi-inj2 (common x x₁) with pi-inj1 x | pi-inj1 x₁
pi-inj2 (common x x₁) | yep x₂ x₃ | yep x₄ x₅ = common x₂ x₄

pi-inj3 : ∀ {n} {A A' : tm n} {B B'} -> (Π A B) ≈ (Π A' B') -> B ≈ B'
pi-inj3 (common x x₁) with pi-inj1 x | pi-inj1 x₁
... | yep t1 t2 | yep t3 t4 = common t2 t4

[]r-cong : ∀ {n m} {A B : tm n} {σ : vsubst n m} -> A ≈ B -> [ σ ]r A ≈ [ σ ]r B
[]r-cong (common x x₁) = common (ren⟶* _ x) (ren⟶* _ x₁)

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

mutual
 neutral-step : ∀ {n} {C : Set} {A B : tm n} -> neutral A -> A ⟶ B -> C
 neutral-step (▹ x) ()
 neutral-step (() · x) β
 neutral-step (t · x) (app1 s) = neutral-step t s
 neutral-step (t · x) (app2 s) = normal-step x s
 {-neutral-step (if () x x₁) if1
 neutral-step (if () x x₁) if2
 neutral-step (if t x x₁) (ifc s) = neutral-step t s
 neutral-step (if t x x₁) (ifc1 s) = normal-step x s
 neutral-step (if t x x₁) (ifc2 s) = normal-step x₁ s -}

 normal-step : ∀ {n} {A B : tm n} {C : Set} -> normal A -> A ⟶ B -> C
 normal-step (ƛ t) (ƛ s) = normal-step t s
 normal-step (Π t t₁) (Π1 s) = normal-step t s
 normal-step (Π t t₁) (Π2 s) = normal-step t₁ s
 {- normal-step tt ()
 normal-step ff ()
 normal-step bool ()
 normal-step set () -}
 normal-step (neut x) s = neutral-step x s

neutral-step* : ∀ {n} {A B : tm n} -> neutral A -> A ⟶* B -> A ≡ B
neutral-step* t refl = refl
neutral-step* t (trans1 x s) = neutral-step t x


normal-step* : ∀ {n} {A B : tm n} -> normal A -> A ⟶* B -> A ≡ B
normal-step* t refl = refl
normal-step* t (trans1 x s) = normal-step t x

{-bool-≈-neutral : ∀ {n} {A : tm n} {C : Set} -> neutral A -> bool ≈ A -> C
bool-≈-neutral t (common x x₁) with normal-step* bool x | neutral-step* t x₁
bool-≈-neutral () (common x x₁) | refl | refl -}

{-set-≈-neutral : ∀ {n} {A : tm n} {C : Set} -> neutral A -> set ≈ A -> C
set-≈-neutral t (common x x₁) with normal-step* set x | neutral-step* t x₁
set-≈-neutral () (common x x₁) | refl | refl 

bool≈Π : ∀ {n} {A : tm n} {B} {C : Set} -> bool ≈ (Π A B) -> C
bool≈Π (common x x₁) with normal-step* bool x | pi-inj1 x₁
bool≈Π (common x x₁) | refl | () -}

Π≈neutral : ∀ {n} {A : tm n} {B D} {C : Set} -> neutral A -> (Π B D) ≈ A -> C
Π≈neutral t (common x x₁) with neutral-step* t x₁ | pi-inj1 x
Π≈neutral () (common x x₁) | refl | yep x₂ x₃

{-set≈Π : ∀ {n} {A : tm n} {B} {C : Set} -> set ≈ (Π A B) -> C
set≈Π (common x x₁) with normal-step* set x | pi-inj1 x₁
set≈Π (common x x₁) | refl | ()

bool≈set : ∀ {n} {C : Set} -> _≈_ {n} bool set -> C
bool≈set (common x x₁) with normal-step* bool x | normal-step* set x₁
bool≈set (common x x₁) | refl | () -}

-- TODO: Can we define a general enough library by generic program that obtains functoriality 
-- for free for this definition?
mutual
 data Ψ {n} : tm n -> Set where
  --bool : Ψ bool
  Π : ∀ {A B} -> (p : Ψ A) -> (∀ {m} (w : vsubst n m) (a : tm m) -> ψ p w a -> Ψ ([ a /x] ([ vsub-ext w ]r B))) -> Ψ (Π A B)
  neut : ∀ {A} -> neutral A -> Ψ A
  closed : ∀ {A B} -> A ⟶ B -> Ψ B -> Ψ A

 ψ : ∀ {n} -> {A : tm n} -> Ψ A -> ∀ {m} (w : vsubst n m) -> tm m -> Set
 --ψ bool w a = ∃ (λ b → (a ⟶* b) × normal-bool b)
 ψ (Π p f) w a = normalizable a × (∀ {k} (v : vsubst _ k) b (q : ψ p (v ∘v w) b) → ψ (f (v ∘v w) b q) id-vsub ([ v ]r a · b))
 ψ (neut y) w a = ∃ (λ b → (a ⟶* b) × neutral b)
 ψ (closed y y') w a = ψ y' w a

 Ψwkn : ∀ {n m} (w : vsubst n m) {A} -> Ψ A -> Ψ ([ w ]r A)
 --Ψwkn w bool = bool
 Ψwkn w (Π {A} {B} t x) = Π (Ψwkn w t) (λ w' a x' → subst Ψ (cong [ a /x] (ren-ext-comp B)) (x (w' ∘v w) a (ψfunct w w' t x')))
 Ψwkn w (neut x) = neut (rename-neut x)
 Ψwkn w (closed x t) = closed (ren⟶*' w x) (Ψwkn w t)

 ψfunct : ∀ {n m k} {A} (w : vsubst n m) (w' : vsubst m k) (t : Ψ A) {a} -> ψ (Ψwkn w t) w' a -> ψ t (w' ∘v w) a
 --ψfunct w w' bool r = r
 ψfunct w w' (Π {A} {B} p y) (r1 , r2) = r1 , f
  where f : ∀ {k'} (v : vsubst _ k') b q -> _
        f v b q with (ψfunct' w (v ∘v w') p (subst (λ α → ψ p α b) (ren-assoc w) q)) 
        ... | z0 = let q1 = cong [ b /x] (ren-ext-comp {w = w} {w' = (v ∘v w')} B)
                    in ψeqdep (subst Ψ q1 (y ((v ∘v w') ∘v w) b (ψfunct w (v ∘v w') p z0)))
                              (y (v ∘v (w' ∘v w)) b q)
                              (sym (trans (cong (λ α → [ b /x] ([ vsub-ext α ]r B)) (ren-assoc w)) q1))
                              (r2 v b z0)
 ψfunct w w' (neut y) r = r
 ψfunct w w' (closed y y') r = ψfunct w w' y' r

 ψfunct' : ∀ {n m k} {A} (w : vsubst n m) (w' : vsubst m k) (t : Ψ A) {a} -> ψ t (w' ∘v w) a -> ψ (Ψwkn w t) w' a
 --ψfunct' w w' bool r = r
 ψfunct' w w' (Π {A} {B} p y) (r1 , r2) = r1 , f
  where f : ∀ {k'} (v : vsubst _ k') b q -> _
        f v b q with ψfunct w (v ∘v w') p q
        ... | z0 with r2 v b (subst (λ α → ψ p α b) (sym (ren-assoc w)) z0)
        ... | z1 = ψeqdep (y (v ∘v (w' ∘v w)) b (subst (λ α -> ψ p α b) (sym (ren-assoc w)) z0))
                          (subst Ψ (cong [ b /x] (ren-ext-comp B)) (y ((v ∘v w') ∘v w) b (ψfunct w (v ∘v w') p q)))
                          (trans (cong (λ α → [ b /x] ([ vsub-ext α ]r B)) (ren-assoc w)) (cong [ b /x] (ren-ext-comp B)))
                          z1
 ψfunct' w w' (neut y) r = r
 ψfunct' w w' (closed y y') r = ψfunct' w w' y' r

 ψfunctid : ∀ {n m} {A} (w : vsubst n m) (t : Ψ A) {a} -> ψ (Ψwkn w t) id-vsub a -> ψ t w a
 ψfunctid w t {a} p = subst (λ α → ψ t α a) (sym id-v-left) (ψfunct w id-vsub t p)

 ψfunct'id : ∀ {n m} {A} (w : vsubst n m) (t : Ψ A) {a} -> ψ t w a -> ψ (Ψwkn w t) id-vsub a
 ψfunct'id w t {a} p = ψfunct' w id-vsub t (subst (λ α → ψ t α a) id-v-left p)

 lemma3-3 : ∀ {n m} {A B : tm n} {M} (p : Ψ A) (q : Ψ B) (w : vsubst n m) -> A ≈ B -> (ψ p w M -> ψ q w M) × (ψ q w M -> ψ p w M)
 {-lemma3-3 bool bool w s = (λ r -> r) , (λ r -> r)
 lemma3-3 bool (Π p y) w s = bool≈Π s
 lemma3-3 bool (neut y) w s = bool-≈-neutral y s
 lemma3-3 (Π p y) bool w s = bool≈Π (≈-sym s) -}
 lemma3-3 (Π p y) (Π p' y') w s = (λ { (r1 , r2) -> 
     (r1 , (λ v b q' ->
       let q = _×_.proj₂ (lemma3-3 p p' (v ∘v w) (pi-inj2 s)) q'
        in _×_.proj₁ (lemma3-3 (y (v ∘v w) b q) (y' (v ∘v w) b q') id-vsub ([]-cong ([]r-cong (pi-inj3 s)))) (r2 v b q)))
     })
    ,
    (λ { (r1 , r2) →  
      (r1 , (λ v b q ->
        let q' = _×_.proj₁ (lemma3-3 p p' (v ∘v w) (pi-inj2 s)) q
        in _×_.proj₂ (lemma3-3 (y (v ∘v w) b q) (y' (v ∘v w) b q') id-vsub ([]-cong ([]r-cong (pi-inj3 s)))) (r2 v b q')))
     })
 lemma3-3 (Π p y) (neut y') w s = Π≈neutral y' s
 --lemma3-3 (neut y) bool w s = bool-≈-neutral y (≈-sym s)
 lemma3-3 (neut y) (Π p y') w s = Π≈neutral y (≈-sym s)
 lemma3-3 (neut y) (neut y') w s = (λ r -> r) , (λ r -> r)
 lemma3-3 (closed y y') q w s = lemma3-3 y' q w (⟶≈trans' s y)
 lemma3-3 p (closed y y') w s = lemma3-3 p y' w (⟶≈trans s y)

 lemma3-3c : ∀ {n} {A M : tm n} (p q : Ψ A) -> ψ p id-vsub M -> ψ q id-vsub M
 lemma3-3c p q t = _×_.proj₁ (lemma3-3 p q id-vsub ≈-refl) t

 ψeqdep : ∀ {n} {B B' M : tm n} (p : Ψ B) (q : Ψ B') -> B ≡ B' -> ψ p id-vsub M -> ψ q id-vsub M
 ψeqdep p q refl t = lemma3-3c p q t

Ψ-closed⟶* : ∀ {n} {A B : tm n} -> A ⟶* B -> Ψ B -> Ψ A
Ψ-closed⟶* refl t = t
Ψ-closed⟶* (trans1 x s) t = closed x (Ψ-closed⟶* s t)

ψ-closed' : ∀ {n m} {A : tm n} (w : vsubst n m) {M N} -> (p : Ψ A) -> M ⟶* N -> ψ p w N -> ψ p w M
--ψ-closed' w bool s (t1 , (s2 , n)) = t1 , ((⟶*-trans s s2) , n)
ψ-closed' w (Π p y) s (h , t) = normalizable-closed s h ,
  (λ v b q → ψ-closed' id-vsub (y (v ∘v w) b q) (app1* (ren⟶* v s)) (t v b q))
ψ-closed' w (neut y) s (t1 , (s2 , neu)) = t1 , ((⟶*-trans s s2) , neu)
ψ-closed' w (closed y y') s t = ψ-closed' w y' s t

ψ-closed : ∀ {n} {A : tm n} {M N} -> (p : Ψ A) -> M ⟶* N -> ψ p id-vsub N -> ψ p id-vsub M
ψ-closed p s t = ψ-closed' id-vsub p s t

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

{- i.e. if instead of a reduction relation, I used a "step function" (so implicitly deterministic)
   then perhaps I could make lemma3-3 trivial? Gotta make it so there's really only one way to derive Ψ...
   i.e. also need for Pi case that A and B are normal (i.e. step function returns "Nothing") -}
{-mutual
 data Φ {n} : tm n -> Set where
  bool : Φ bool
  Π : ∀ {A B} -> (p : Φ A) -> (∀ {m} (w : vsubst n m) (a : tm m) -> φ p w a -> Φ ([ a /x] ([ vsub-ext w ]r B))) -> Φ (Π A B)
  neut : ∀ {A} -> neutral A -> Φ A
  closed : ∀ {A B} -> A ⟶ B -> Φ B -> Φ A
  set : Φ set

 φ : ∀ {n} -> {A : tm n} -> Φ A -> ∀ {m} (w : vsubst n m) -> tm m -> Set
 φ bool w a = ∃ (λ b → (a ⟶* b) × normal-bool b)
 φ (Π p f) w a = normalizable a × (∀ {k} (v : vsubst _ k) b (q : φ p (v ∘v w) b) → φ (f (v ∘v w) b q) id-vsub ([ v ]r a · b))
 φ (neut y) w a = ∃ (λ b → (a ⟶* b) × neutral b)
 φ (closed y y') w a = φ y' w a
 φ set w a = Ψ a

 Φwkn : ∀ {n m} (w : vsubst n m) {A} -> Φ A -> Φ ([ w ]r A)
 Φwkn w bool = bool
 Φwkn w (Π {A} {B} t x) = Π (Φwkn w t) (λ w' a x' → subst Φ (cong [ a /x] (ren-ext-comp B)) (x (w' ∘v w) a (φfunct w w' t x')))
 Φwkn w (neut x) = neut (rename-neut x)
 Φwkn w (closed x t) = closed (ren⟶*' w x) (Φwkn w t)
 Φwkn w set = set

 φfunct : ∀ {n m k} {A} (w : vsubst n m) (w' : vsubst m k) (t : Φ A) {a} -> φ (Φwkn w t) w' a -> φ t (w' ∘v w) a
 φfunct w w' bool r = r
 φfunct w w' (Π {A} {B} p y) (r1 , r2) = r1 , f
  where f : ∀ {k'} (v : vsubst _ k') b q -> _
        f v b q with (φfunct' w (v ∘v w') p (subst (λ α → φ p α b) (ren-assoc w) q)) 
        ... | z0 = let q1 = cong [ b /x] (ren-ext-comp {w = w} {w' = (v ∘v w')} B)
                    in φeqdep (subst Φ q1 (y ((v ∘v w') ∘v w) b (φfunct w (v ∘v w') p z0)))
                              (y (v ∘v (w' ∘v w)) b q)
                              (sym (trans (cong (λ α → [ b /x] ([ vsub-ext α ]r B)) (ren-assoc w)) q1))
                              (r2 v b z0)
 φfunct w w' (neut y) r = r
 φfunct w w' (closed y y') r = φfunct w w' y' r
 φfunct w w' set r = r

 φfunct' : ∀ {n m k} {A} (w : vsubst n m) (w' : vsubst m k) (t : Φ A) {a} -> φ t (w' ∘v w) a -> φ (Φwkn w t) w' a
 φfunct' w w' bool r = r
 φfunct' w w' (Π {A} {B} p y) (r1 , r2) = r1 , f
  where f : ∀ {k'} (v : vsubst _ k') b q -> _
        f v b q with φfunct w (v ∘v w') p q
        ... | z0 with r2 v b (subst (λ α → φ p α b) (sym (ren-assoc w)) z0)
        ... | z1 = φeqdep (y (v ∘v (w' ∘v w)) b (subst (λ α -> φ p α b) (sym (ren-assoc w)) z0))
                          (subst Φ (cong [ b /x] (ren-ext-comp B)) (y ((v ∘v w') ∘v w) b (φfunct w (v ∘v w') p q)))
                          (trans (cong (λ α → [ b /x] ([ vsub-ext α ]r B)) (ren-assoc w)) (cong [ b /x] (ren-ext-comp B)))
                          z1
 φfunct' w w' (neut y) r = r
 φfunct' w w' (closed y y') r = φfunct' w w' y' r
 φfunct' w w' set r = r

 φfunct'id : ∀ {n m} {A} (w : vsubst n m) (t : Φ A) {a} -> φ t w a -> φ (Φwkn w t) id-vsub a
 φfunct'id w t {a} p = φfunct' w id-vsub t (subst (λ α → φ t α a) id-v-left p)

 lemma3-3' : ∀ {n m} {A B : tm n} {M} (p : Φ A) (q : Φ B) (w : vsubst n m) -> A ≈ B -> (φ p w M -> φ q w M) × (φ q w M -> φ p w M)
 lemma3-3' bool bool w s = (λ r -> r) , (λ r -> r)
 lemma3-3' bool (Π p y) w s = bool≈Π s
 lemma3-3' bool (neut y) w s = bool-≈-neutral y s
 lemma3-3' (Π p y) bool w s = bool≈Π (≈-sym s)
 lemma3-3' (Π p y) (Π p' y') w s = (λ { (r1 , r2) -> 
     (r1 , (λ v b q' ->
       let q = _×_.proj₂ (lemma3-3' p p' (v ∘v w) (pi-inj2 s)) q'
        in _×_.proj₁ (lemma3-3' (y (v ∘v w) b q) (y' (v ∘v w) b q') id-vsub ([]-cong ([]r-cong (pi-inj3 s)))) (r2 v b q)))
     })
    ,
    (λ { (r1 , r2) →  
      (r1 , (λ v b q ->
        let q' = _×_.proj₁ (lemma3-3' p p' (v ∘v w) (pi-inj2 s)) q
        in _×_.proj₂ (lemma3-3' (y (v ∘v w) b q) (y' (v ∘v w) b q') id-vsub ([]-cong ([]r-cong (pi-inj3 s)))) (r2 v b q')))
     })
 lemma3-3' (Π p y) (neut y') w s = Π≈neutral y' s
 lemma3-3' (neut y) bool w s = bool-≈-neutral y (≈-sym s)
 lemma3-3' (neut y) (Π p y') w s = Π≈neutral y (≈-sym s)
 lemma3-3' (neut y) (neut y') w s = (λ r -> r) , (λ r -> r)
 lemma3-3' (closed y y') q w s = lemma3-3' y' q w (⟶≈trans' s y)
 lemma3-3' p (closed y y') w s = lemma3-3' p y' w (⟶≈trans s y)
 lemma3-3' bool set w s = bool≈set s
 lemma3-3' (Π p y) set w s = set≈Π (≈-sym s)
 lemma3-3' (neut y) set w s = set-≈-neutral y (≈-sym s)
 lemma3-3' set set w s = (λ x → x) , (λ x → x)
 lemma3-3' set bool w s = bool≈set (≈-sym s)
 lemma3-3' set (Π p y) w s = set≈Π s
 lemma3-3' set (neut y) w s = set-≈-neutral y s

 lemma3-3c' : ∀ {n} {A M : tm n} (p q : Φ A) -> φ p id-vsub M -> φ q id-vsub M
 lemma3-3c' p q = _×_.proj₁ (lemma3-3' p q id-vsub ≈-refl)

 φeqdep : ∀ {n} {B B' M : tm n} (p : Φ B) (q : Φ B') -> B ≡ B' -> φ p id-vsub M -> φ q id-vsub M
 φeqdep p q refl t = lemma3-3c' p q t

Φ-closed⟶* : ∀ {n} {A B : tm n} -> A ⟶* B -> Φ B -> Φ A
Φ-closed⟶* refl t = t
Φ-closed⟶* (trans1 x s) t = closed x (Φ-closed⟶* s t)

φ-closed' : ∀ {n m} {A : tm n} (w : vsubst n m) {M N} -> (p : Φ A) -> M ⟶* N -> φ p w N -> φ p w M
φ-closed' w bool s (t1 , (s2 , n)) = t1 , ((⟶*-trans s s2) , n)
φ-closed' w (Π p y) s (h , t) = normalizable-closed s h ,
  (λ v b q → φ-closed' id-vsub (y (v ∘v w) b q) (app1* (ren⟶* v s)) (t v b q))
φ-closed' w (neut y) s (t1 , (s2 , neu)) = t1 , ((⟶*-trans s s2) , neu)
φ-closed' w (closed y y') s t = φ-closed' w y' s t
φ-closed' w set s t = Ψ-closed⟶* s t

φ-closed : ∀ {n} {A : tm n} {M N} -> (p : Φ A) -> M ⟶* N -> φ p id-vsub N -> φ p id-vsub M
φ-closed p s t = φ-closed' id-vsub p s t -}
