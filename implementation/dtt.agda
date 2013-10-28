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
{-
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
ƛ* (trans1 x t) = trans1 (ƛ x) (ƛ* t) -}

mutual
 data neutral {n} : tm n -> Set where
  ▹ : ∀ x -> neutral (▹ x)
  _·_ : ∀ {M N} -> neutral M  -> normal N  -> neutral (M · N)
  if : ∀ {M N P} -> neutral M  -> normal N -> normal P  -> neutral (if M N P)
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

foo : tm ⊡ -> tm ⊡
foo n = {!!}

