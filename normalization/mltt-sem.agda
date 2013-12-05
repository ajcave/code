{-# OPTIONS --type-in-type #-}
module mltt-sem where
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
  if : ∀ {M N P} -> neutral M  -> normal N -> normal P  -> neutral (if M N P) 

 data normal {n} : tm n -> Set where
  ƛ : ∀ {M} -> normal M  -> normal (ƛ M)
  Π : ∀ {A B} -> normal A -> normal B  -> normal (Π A B)
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
 
rename-norm-bool : ∀ {n m} {w : vsubst n m} {A} -> normal-bool A -> normal-bool ([ w ]r A)
rename-norm-bool tt = tt
rename-norm-bool ff = ff
rename-norm-bool (neut y) = neut (rename-neut y)

data _≈_ {n} (a b : tm n) : Set where
 common : ∀ {d} -> (a ⟶* d) -> (b ⟶* d) -> a ≈ b

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

lem : ∀ {n} (Γ : dctx n) {M} {T} -> Γ ⊢ M ∶ T -> Γ ⊢ T type
lem Γ' bool = set
lem Γ' tt = emb bool
lem Γ' ff = emb bool
lem Γ' (▹ y y') = y
lem Γ' (Π y y') = set
lem Γ' (ƛ y y') = Π y (lem (Γ' , _) y')
lem Γ' (y · y') with lem Γ' y
lem Γ' (y · y1) | Π y' y0 = {!!}
lem Γ' (y · y1) | emb (Π y' y0) = {!!}
lem Γ' (y · y2) | emb (conv y' y0 y1) = {!!}
lem Γ' (if y y' y0 y1) = {!!}
lem Γ' (conv y y' y0) = y

open import Data.Bool

mutual
 ⟦_⟧c : ∀ {n} {Γ : dctx n} -> wfctx Γ -> Set₁
 ⟦ ⊡ ⟧c = Unit
 ⟦ Γ , T ⟧c = Σ ⟦ Γ ⟧c (λ x → ⟦ Γ ⊢ T ⟧t x)

 ⟦_⊢_⟧t : ∀ {n} {Γ : dctx n} (Γwf : wfctx Γ) {T : tm n} -> Γ ⊢ T type -> ⟦ Γwf ⟧c -> Set
 ⟦ Γ ⊢ set ⟧t γ = Set
 ⟦ Γ ⊢ Π T S ⟧t γ = (x : ⟦ Γ ⊢ T ⟧t γ) → ⟦ (Γ , T) ⊢ S ⟧t (γ , x)
 ⟦ Γ ⊢ emb y ⟧t γ = {!!} --⟦ Γ ⊢ y ∶ γ ⟧

 ⟦_⊢_∶_⟧ : ∀ {n} {Γ : dctx n} (Γwf : wfctx Γ) {M : tm n} {T : tm n} -> (d : Γ ⊢ M ∶ T) -> (γ : ⟦ Γwf ⟧c)
   -> ⟦ Γwf ⊢ lem Γ d  ⟧t γ
 ⟦_⊢_∶_⟧ Γ' bool γ = Bool
 ⟦_⊢_∶_⟧ Γ' tt γ = {!!}
 ⟦_⊢_∶_⟧ Γ' ff γ = {!!}
 ⟦_⊢_∶_⟧ Γ' (▹ y y') γ = {!!}
 ⟦_⊢_∶_⟧ Γ' (Π y y') γ = {!!}
 ⟦_⊢_∶_⟧ Γ' (ƛ y y') γ = λ x → {!!}
 ⟦_⊢_∶_⟧ Γ' (y · y') γ = {!!}
 ⟦_⊢_∶_⟧ Γ' (if y y' y0 y1) γ = {!!}
 ⟦_⊢_∶_⟧ Γ' (conv y y' y0) γ = {!!}