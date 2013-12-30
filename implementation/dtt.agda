module dtt where
open import FinMap
open import Unit 
open import Data.Product hiding (_×_)
open import Product hiding (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality 
open import Data.Empty

* : Unitz
* = tt
data tm (n : ctx Unit) : Set where
 ▹ : var n * -> tm n
 ƛ : (M : tm (n , *)) -> tm n
 Π : (A : tm n) -> (B : tm (n , *)) -> tm n
 _·_ : (M N : tm n) -> tm n
 tt ff bool set nat zero : tm n
 suc : tm n -> tm n
 rec : tm n -> tm n -> tm ((n , *) , *) -> tm n
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
[_]r σ nat = nat
[_]r σ zero = zero
[_]r σ (suc n) = suc ([ σ ]r n)
[_]r σ (rec n cz cs) = rec ([ σ ]r n) ([ σ ]r cz) ([ vsub-ext (vsub-ext σ) ]r cs)
[_]r σ (if M M₁ M₂) = if ([ σ ]r M) ([ σ ]r M₁) ([ σ ]r M₂)

tsubst : ∀ (n m : ctx Unit) -> Set
tsubst n m = gksubst n (tm m)

wknt : ∀ {n m} -> tsubst n m -> tsubst n (m , *)
wknt σ = gmap [ wkn-vsub ]r σ

tsub-ext : ∀ {n m} -> tsubst n m -> tsubst (n , *) (m , *)
tsub-ext σ = (wknt σ) , (▹ top)

id-tsub : ∀ {n} -> tsubst n n
id-tsub {⊡} = tt
id-tsub {n , *} = tsub-ext id-tsub --gmap ▹ id-vsub

[_]t : ∀ {n m} -> tsubst n m -> tm n -> tm m
[_]t σ (▹ x) = [ σ ]v x
[_]t σ (ƛ M) = ƛ ([ tsub-ext σ ]t M)
[_]t σ (Π A B) = Π ([ σ ]t A) ([ tsub-ext σ ]t B)
[_]t σ (M · M₁) = ([ σ ]t M) · ([ σ ]t M₁)
[_]t σ tt = tt
[_]t σ ff = ff
[_]t σ bool = bool
[_]t σ set = set
[_]t σ nat = nat
[_]t σ zero = zero
[_]t σ (suc n) = suc ([ σ ]t n)
[_]t σ (rec n cz cs) = rec ([ σ ]t n) ([ σ ]t cz) ([ tsub-ext (tsub-ext σ) ]t cs)
[_]t σ (if M M₁ M₂) = if ([ σ ]t M) ([ σ ]t M₁) ([ σ ]t M₂)

[_/x] : ∀ {n} -> tm n -> tm (n , *) -> tm n
[ M /x] N = [ id-tsub , M ]t N

data _⟶_ {n} : ∀ (M N : tm n) -> Set where
 β : ∀ {M N} -> ((ƛ M) · N) ⟶ [ N /x] M
 if1 : ∀ {M N} -> if tt M N ⟶ M
 if2 : ∀ {M N} -> if ff M N ⟶ N
 app1 : ∀ {M M' N} -> M ⟶ M' -> (M · N) ⟶ (M' · N)
 app2 : ∀ {M N N'} -> N ⟶ N' -> (M · N) ⟶ (M · N')
 ifc : ∀ {M M' N1 N2} -> M ⟶ M' -> if M N1 N2 ⟶ if M' N1 N2
 ifc1 : ∀ {M N1 N1' N2} -> N1 ⟶ N1' -> if M N1 N2 ⟶ if M N1' N2
 ifc2 : ∀ {M N1 N2 N2'} -> N2 ⟶ N2' -> if M N1 N2 ⟶ if M N1 N2'
 ƛ : ∀ {M M'} -> M ⟶ M' -> (ƛ M) ⟶ (ƛ M')
 Π1 : ∀ {A A' B} -> A ⟶ A' -> (Π A B) ⟶ (Π A' B)
 Π2 : ∀ {A B B'} -> B ⟶ B' -> (Π A B) ⟶ (Π A B')
 suc : ∀ {M M'} -> M ⟶ M' -> (suc M) ⟶ (suc M')
 recβz : ∀ {M P} -> (rec zero M P) ⟶ M
 recβsuc : ∀ {N M P} -> (rec (suc N) M P) ⟶ [ (id-tsub , N) , (rec N M P) ]t P
 rec1 : ∀ {N N' M P} -> N ⟶ N' -> (rec N M P) ⟶ (rec N' M P)
 rec2 : ∀ {N M M' P} -> M ⟶ M' -> (rec N M P) ⟶ (rec N M' P)
 rec3 : ∀ {N M P P'} -> P ⟶ P' -> (rec N M P) ⟶ (rec N M P')
 

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

if* : ∀ {n} {M M' N1 N2 : tm n} -> M ⟶* M' -> (if M N1 N2) ⟶* (if M' N1 N2)
if* refl = refl
if* (trans1 x t) = trans1 (ifc x) (if* t)

ƛ* : ∀ {n} {M M' : tm (n , *)} -> M ⟶* M' -> (ƛ M) ⟶* (ƛ M')
ƛ* refl = refl
ƛ* (trans1 x t) = trans1 (ƛ x) (ƛ* t)

mutual
 data neutral {n} : tm n -> Set where
  ▹ : ∀ x -> neutral (▹ x)
  _·_ : ∀ {M N} -> neutral M  -> normal N  -> neutral (M · N)
  if : ∀ {M N P} -> neutral M  -> normal N -> normal P -> neutral (if M N P)
  rec : ∀ {N M P} -> neutral N -> normal M -> normal P -> neutral (rec N M P)

 data normal {n} : tm n -> Set where
  ƛ : ∀ {M} -> normal M  -> normal (ƛ M)
  Π : ∀ {A B} -> normal A -> normal B  -> normal (Π A B)
  tt : normal tt
  ff : normal ff
  bool : normal bool
  set : normal set
  nat : normal nat
  zero : normal zero
  suc : ∀ {n} -> normal n -> normal (suc n)
  neut : ∀ {M} -> neutral M -> normal M

data ntp (n : ctx Unitz) : Set where
 Π : ntp n -> ntp (n , *)  -> ntp n
 bool : ntp n
 set : ntp n
 nat : ntp n
 neut : ∀ {M : tm n} -> neutral M -> ntp n

data _≈_ {n} (a b : tm n) : Set where
 common : ∀ {d} -> (a ⟶* d) -> (b ⟶* d) -> a ≈ b

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

{- []r-cong : ∀ {n m} {A B : tm n} {σ : vsubst n m} -> A ≈ B -> [ σ ]r A ≈ [ σ ]r B
[]r-cong (common x x₁) = common (ren⟶* _ x) (ren⟶* _ x₁)

[]-cong : ∀ {n m} {A B : tm n} {σ : tsubst n m} -> A ≈ B -> [ σ ]t A ≈ [ σ ]t B
[]-cong (common x x₁) = common (sub⟶* _ x) (sub⟶* _ x₁) -}

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
 neutral-step (if () x x₁) if1
 neutral-step (if () x x₁) if2
 neutral-step (if t x x₁) (ifc s) = neutral-step t s
 neutral-step (if t x x₁) (ifc1 s) = normal-step x s
 neutral-step (if t x x₁) (ifc2 s) = normal-step x₁ s
 neutral-step (rec () x x₁) recβz
 neutral-step (rec () x x₁) recβsuc
 neutral-step (rec t x x₁) (rec1 s) = neutral-step t s
 neutral-step (rec t x x₁) (rec2 s) = normal-step x s
 neutral-step (rec t x x₁) (rec3 s) = normal-step x₁ s

 normal-step : ∀ {n} {A B : tm n} {C : Set} -> normal A -> A ⟶ B -> C
 normal-step (ƛ t) (ƛ s) = normal-step t s
 normal-step (Π t t₁) (Π1 s) = normal-step t s
 normal-step (Π t t₁) (Π2 s) = normal-step t₁ s
 normal-step tt ()
 normal-step ff ()
 normal-step bool ()
 normal-step set ()
 normal-step nat ()
 normal-step zero ()
 normal-step (suc n₂) (suc s) = normal-step n₂ s
 normal-step (neut x) s = neutral-step x s

neutral-step* : ∀ {n} {A B : tm n} -> neutral A -> A ⟶* B -> A ≡ B
neutral-step* t refl = refl
neutral-step* t (trans1 x s) = neutral-step t x


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

nat≈set : ∀ {n} {C : Set} -> _≈_ {n} nat set -> C
nat≈set (common x x₁) with normal-step* nat x | normal-step* set x₁
nat≈set (common x x₁) | refl | ()

nat≈Π : ∀ {n} {A : tm n} {B} {C : Set} -> nat ≈ (Π A B) -> C
nat≈Π (common x x₁) with normal-step* nat x | pi-inj1 x₁
nat≈Π (common x x₁) | refl | ()

bool≈nat : ∀ {n} {C : Set} -> _≈_ {n} bool nat -> C
bool≈nat (common x x₁) with normal-step* bool x | normal-step* nat x₁
bool≈nat (common x x₁) | refl | ()

nat-≈-neutral : ∀ {n} {A : tm n} {C : Set} -> neutral A -> nat ≈ A -> C
nat-≈-neutral t (common x x₁) with normal-step* nat x | neutral-step* t x₁
nat-≈-neutral () (common x x₁) | refl | refl

data dctx : ctx Unitz -> Set where
 ⊡ : dctx ⊡
 _,_ : ∀ {n} -> (Γ : dctx n) -> tm n -> dctx (n , *)

-- mutual
--  data Ctx : Set where
--   ⊡ : Ctx
--   _,_ : (Γ : Ctx) -> tm 〈 Γ 〉 -> Ctx

--  〈_〉 : Ctx -> ctx Unit
--  〈 ⊡ 〉 = ⊡
--  〈 Γ , x 〉 = 〈 Γ 〉 , *

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
  nat : Γ ⊢ nat ∶ set
  tt : Γ ⊢ tt ∶ bool
  ff : Γ ⊢ ff ∶ bool
  zero : Γ ⊢ zero ∶ nat
  suc : ∀ {M} -> Γ ⊢ M ∶ nat -> Γ ⊢ (suc M) ∶ nat
  rec : ∀ {C N M P} -> (Γ , nat) ⊢ C type -> Γ ⊢ N ∶ nat -> Γ ⊢ M ∶ ([ zero /x] C)
                    -> ((Γ , nat) , C) ⊢ P ∶ [ wknt (wknt id-tsub) , (suc (▹ (pop top))) ]t C
                    -> Γ ⊢ (rec N M P) ∶ ([ N /x] C)
  ▹ : ∀ {A x} -> Γ ⊢ A type -> Γ ∋ x ∶ A -> Γ ⊢ (▹ x) ∶ A
  Π : ∀ {A B} -> Γ ⊢ A ∶ set -> (Γ , A) ⊢ B ∶ set -> Γ ⊢ (Π A B) ∶ set
  ƛ : ∀ {A B M} -> Γ ⊢ A type -> (Γ , A) ⊢ M ∶ B -> Γ ⊢ (ƛ M) ∶ (Π A B)
  _·_ : ∀ {A B M N} -> Γ ⊢ M ∶ (Π A B) -> Γ ⊢ N ∶ A -> Γ ⊢ (M · N) ∶ ([ N /x] B)
  if : ∀ {C M N1 N2} -> (Γ , bool) ⊢ C type -> Γ ⊢ M ∶ bool -> Γ ⊢ N1 ∶ ([ tt /x] C) -> Γ ⊢ N2 ∶ ([ ff /x] C) -> Γ ⊢ (if M N1 N2) ∶ ([ M /x] C)
  conv : ∀ {A B} {M} -> Γ ⊢ A type -> B ≈ A -> Γ ⊢ M ∶ B -> Γ ⊢ M ∶ A

mutual
  data synthable (n : ctx Unitz) : Set where
   ▹  : var n * -> synthable n
   _·_ : synthable n -> checkable n -> synthable n
   rec : (C : checkable (n , *)) -> checkable n -> checkable n -> checkable ((n , *) , *) -> synthable n
   if : (C : checkable (n , *)) -> checkable n -> checkable n -> checkable n -> synthable n -- if_(x. C) b then e1 else e2
   annot : (M : checkable n) -> (T : checkable n) -> synthable n

  data checkable (n : ctx Unitz) : Set where
   tt ff zero bool nat : checkable n
   suc : checkable n -> checkable n
   ƛ : checkable (n , *) -> checkable n
   Π : checkable n -> checkable (n , *) -> checkable n
   ▸ : synthable n -> checkable n

mutual
 ⌊_⌋s : ∀ {n} -> synthable n -> tm n
 ⌊ ▹ x ⌋s = ▹ x
 ⌊ S · M ⌋s = ⌊ S ⌋s · ⌊ M ⌋c
 ⌊ rec C M N₁ N₂ ⌋s = rec ⌊ M ⌋c ⌊ N₁ ⌋c ⌊ N₂ ⌋c
 ⌊ if C M N₁ N₂ ⌋s = if ⌊ M ⌋c ⌊ N₁ ⌋c ⌊ N₂ ⌋c
 ⌊ annot M T ⌋s = ⌊ M ⌋c

 ⌊_⌋c : ∀ {n} -> checkable n -> tm n
 ⌊ tt ⌋c = tt
 ⌊ ff ⌋c = ff
 ⌊ zero ⌋c = zero
 ⌊ bool ⌋c = bool
 ⌊ nat ⌋c = nat
 ⌊ suc M ⌋c = suc ⌊ M ⌋c
 ⌊ ƛ M ⌋c = ƛ ⌊ M ⌋c
 ⌊ Π M M₁ ⌋c = Π ⌊ M ⌋c ⌊ M₁ ⌋c
 ⌊ ▸ M ⌋c = ⌊ M ⌋s

_≉_ : ∀ {n} -> tm n -> tm n -> Set
M ≉ N = M ≈ N -> ⊥

data _⊬_∶_ {n} (Γ : dctx n) : tm n -> tm n -> Set where
 tt : ∀ {T} -> T ≉ bool -> Γ ⊬ tt ∶ T
 

data check-result {n} (Γ : dctx n) (M : checkable n) (T : tm n) : Set where
 yes : {-Γ ⊢ ⌊ M ⌋c ∶ T -> -} check-result Γ M T
 no : {- Γ ⊬ ⌊ M ⌋c ∶ T -> -} check-result Γ M T
 
-- Could implement as returning a bool, and then proving it correct..
-- Would be the same as doing this, plus type theory in color to forget the proof parts
mutual
 check : ∀ {n} (Γ : dctx n) (M : checkable n) (T : ntp n) -> check-result Γ M bool
 check Γ tt (Π T T₁) = no
 check Γ tt bool = yes
 check Γ tt set = no
 check Γ tt nat = no
 check Γ tt (neut x) = no
 check Γ ff (Π T T₁) = no
 check Γ ff bool = yes
 check Γ ff set = no
 check Γ ff nat = no
 check Γ ff (neut x) = no
 check Γ zero (Π T T₁) = no
 check Γ zero bool = no
 check Γ zero set = no
 check Γ zero nat = yes
 check Γ zero (neut x) = no
 check Γ bool (Π T T₁) = no
 check Γ bool bool = no
 check Γ bool set = yes
 check Γ bool nat = no
 check Γ bool (neut x) = no
 check Γ nat (Π T T₁) = no
 check Γ nat bool = no
 check Γ nat set = yes
 check Γ nat nat = no
 check Γ nat (neut x) = no
 check Γ (suc M) (Π T T₁) = no
 check Γ (suc M) bool = no
 check Γ (suc M) set = no
 check Γ (suc M) nat with check Γ M nat
 ... | yes = yes
 ... | no = no
 check Γ (suc M) (neut x) = no
 check Γ (ƛ M) (Π T T₁) with check (Γ , {!!}) M T₁
 check Γ (ƛ M) (Π T T₁) | yes = yes
 check Γ (ƛ M) (Π T T₁) | no = yes
 check Γ (ƛ M) bool = no
 check Γ (ƛ M) set = no
 check Γ (ƛ M) nat = no
 check Γ (ƛ M) (neut x) = no
 check Γ (Π M M₁) T = {!!}
 check Γ (▸ R) T = {!!}



 
