module cr where
open import eq

_∘_ : ∀ {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘ g) x = f (g x)


data nat : Set where 
 z : nat
 s : (n : nat) -> nat

_+_ : nat -> nat -> nat
n + z = n
n + (s m) = s (n + m)

record Unit : Set where
 constructor tt

import cc
open module cc1 = cc Unit

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

_*_ : (A B : Set) -> Set
A * B = Σ {A} (λ _ -> B)

data var : nat -> Set where
 z : ∀ {n} -> var (s n)
 s : ∀ {n} -> (x : var n) -> var (s n)

data tm (n : nat) : Set where
 ▹ : (x : var n) -> tm n
 ƛ : (M : tm (s n)) -> tm n
 _·_ : (M : tm n) -> (N : tm n) -> tm n

vsubst : (n m : nat) -> Set
vsubst n m = var n -> var m 

len : tp -> nat
len (cc.▹ a) = s z
len (cc._×_ t u) = len t + len u
len cc.⊤ = z


-- TODO: Try computing vsubst by recursion on n

_,,,_ : ∀ {n m} -> vsubst n m -> var m -> vsubst (s n) m
(θ ,,, x) z = x
(θ ,,, x) (s n) = θ n

vext : ∀ {n m} -> vsubst n m -> vsubst (s n) (s m)
vext θ = (s ∘ θ) ,,, z

vsub : ∀ {n m} -> vsubst n m -> tm n -> tm m
vsub θ (▹ x) = ▹ (θ x)
vsub θ (ƛ M) = ƛ (vsub (vext θ) M)
vsub θ (M · N) = (vsub θ M) · (vsub θ N)

id : ∀ {A : Set} -> A -> A
id x = x

wkn-vsub : ∀ {n} -> vsubst n (s n)
wkn-vsub = s

subst : (n m : nat) -> Set
subst n m = var n -> tm m

► : ∀ {n} (N : tm n) -> subst (s z) n
► N z = N
► N (s ())

wkn-subst : ∀ {n m} (θ : subst n m) -> subst n (s m)
wkn-subst θ = (vsub s) ∘ θ

_,,_ : ∀ {n m} (θ : subst n m) (t : tm m) -> subst (s n) m
_,,_ θ t z = t
_,,_ θ t (s x) = θ x

ext : ∀ {n m} (θ : subst n m) -> subst (s n) (s m)
ext θ = (wkn-subst θ) ,, (▹ z)

sub : ∀ {n m} -> subst n m -> tm n -> tm m
sub θ (▹ x) = θ x
sub θ (ƛ M) = ƛ (sub (ext θ) M)
sub θ (M · N) = (sub θ M) · (sub θ N)

-- Gee I wish we had functional extensionality
ext-resp-≋ : ∀ {n m} {σ1 σ2 : subst n m} -> σ1 ≋ σ2 -> (ext σ1) ≋ (ext σ2)
ext-resp-≋ H z = refl
ext-resp-≋ H (s x) = ≡-cong1 (vsub s) (H x)

sub-resp-≋ : ∀ {n m} {σ1 σ2 : subst n m} -> σ1 ≋ σ2 -> (sub σ1) ≋ (sub σ2)
sub-resp-≋ H (▹ x) = H x
sub-resp-≋ H (ƛ M) = ≡-cong1 ƛ (sub-resp-≋ (ext-resp-≋ H) M)
sub-resp-≋ H (M · N) = ≡-cong2 _·_ (sub-resp-≋ H M) (sub-resp-≋ H N) 

vext-resp-≋ : ∀ {n m} {σ1 σ2 : vsubst n m} -> σ1 ≋ σ2 -> (vext σ1) ≋ (vext σ2)
vext-resp-≋ H z = refl
vext-resp-≋ H (s x) = ≡-cong1 s (H x)

vsub-resp-≋ : ∀ {n m} {σ1 σ2 : vsubst n m} -> σ1 ≋ σ2 -> (vsub σ1) ≋ (vsub σ2)
vsub-resp-≋ H (▹ x) = ≡-cong1 ▹ (H x)
vsub-resp-≋ H (ƛ M) = ≡-cong1 ƛ (vsub-resp-≋ (vext-resp-≋ H) M)
vsub-resp-≋ H (M · N) = ≡-cong2 _·_ (vsub-resp-≋ H M) (vsub-resp-≋ H N) 

_•_ : ∀ {A : Set} {m k} (σ1 : subst m k) (σ2 : A -> tm m) -> A -> tm k
σ1 • σ2 = sub σ1 ∘ σ2

wkn : ∀ {n} -> subst n (s n)
wkn {n} = wkn-subst ▹

pair : ∀ {n m k} -> subst m k -> subst n k -> subst (m + n) k
pair {z} σ1 σ2 = σ1
pair {s n} σ1 σ2 = (pair σ1 (σ2 ∘ s)) ,, (σ2 z)

proj1 : ∀ {m n} -> subst n (n + m)
proj1 {z} = ▹
proj1 {s m} = vsub s ∘ proj1 {m}

proj2 : ∀ {m n} -> subst m (n + m)
proj2 {z} ()
proj2 {s n} z = ▹ z
proj2 {s n} (s x) = vsub s (proj2 x)

∘-resp-≋1 : ∀ {A B C} {f1 f2 : B -> C} -> f1 ≋ f2 -> (g : A -> B) -> (f1 ∘ g) ≋ (f2 ∘ g)
∘-resp-≋1 H1 g x = ≡-cong-app H1 refl

∘-resp-≋2 : ∀ {A B C}  (g : B -> C) {f1 f2 : A -> B} -> f1 ≋ f2 -> (g ∘ f1) ≋ (g ∘ f2)
∘-resp-≋2 g H1 x = ≡-cong1 g (H1 x)

pair-resp-≋ : ∀ {n m k} {σ1a σ1b : subst m k} {σ2a σ2b : subst n k} -> σ1a ≋ σ1b -> σ2a ≋ σ2b -> pair σ1a σ2a ≋ pair σ1b σ2b
pair-resp-≋ {z} H1 H2 x = H1 x
pair-resp-≋ {s n} H1 H2 z = H2 z
pair-resp-≋ {s n} H1 H2 (s x) = pair-resp-≋ H1 (∘-resp-≋1 H2 s) x

-- TODO: Try the generic traversal!
-- TODO: I'm pretty sure I had less of these in the Coq proof for Beluga^mu. Why?
-- TODO: Identify combinators from which functors can automatically be derived

vext-funct : ∀ {m n k} -> (σ1 : vsubst n k) (σ2 : vsubst m n) -> vext (σ1 ∘ σ2) ≋ (vext σ1 ∘ vext σ2)
vext-funct σ1 σ2 z = refl
vext-funct σ1 σ2 (s x) = refl

vsub-funct : ∀ {m n k} -> (σ1 : vsubst n k) (σ2 : vsubst m n) -> vsub (σ1 ∘ σ2) ≋ (vsub σ1 ∘ vsub σ2)
vsub-funct σ1 σ2 (▹ x) = refl
vsub-funct σ1 σ2 (ƛ M) = ≡-cong1 ƛ (≡-trans (vsub-resp-≋ (vext-funct σ1 σ2) M) (vsub-funct (vext σ1) (vext σ2) M))
vsub-funct σ1 σ2 (M · N) = ≡-cong2 _·_ (vsub-funct σ1 σ2 M) (vsub-funct σ1 σ2 N)

_⊙_ : ∀ {m n k} (σ1 : vsubst n k) (σ2 : subst m n) -> subst m k
σ1 ⊙ σ2 = (vsub σ1) ∘ σ2

ext-vext-funct : ∀ {m n k} (σ1 : subst n k) (σ2 : vsubst m n) -> ext (σ1 ∘ σ2) ≋ (ext σ1 ∘ vext σ2)
ext-vext-funct σ1 σ2 z = refl
ext-vext-funct σ1 σ2 (s x) = refl

ext-vext-funct2 : ∀ {m n k} (σ1 : vsubst n k) (σ2 : subst m n) -> ext (σ1 ⊙ σ2) ≋ (vext σ1 ⊙ ext σ2)
ext-vext-funct2 σ1 σ2 z = refl
ext-vext-funct2 σ1 σ2 (s x) = ≡-trans (≡-sym (vsub-funct s σ1 (σ2 x))) (vsub-funct (vext σ1) s (σ2 x))

sub-vsub-funct : ∀ {m n k} (σ1 : subst n k) (σ2 : vsubst m n) -> sub (σ1 ∘ σ2) ≋ (sub σ1 ∘ vsub σ2)
sub-vsub-funct σ1 σ2 (▹ x) = refl
sub-vsub-funct σ1 σ2 (ƛ M) = ≡-cong1 ƛ (≡-trans (sub-resp-≋ (ext-vext-funct σ1 σ2) M) (sub-vsub-funct (ext σ1) (vext σ2) M))
sub-vsub-funct σ1 σ2 (M · N) = ≡-cong2 _·_ (sub-vsub-funct σ1 σ2 M) (sub-vsub-funct σ1 σ2 N)

sub-vsub-funct2 : ∀ {m n k} (σ1 : vsubst n k) (σ2 : subst m n) -> sub (σ1 ⊙ σ2) ≋ (vsub σ1 ∘ sub σ2)
sub-vsub-funct2 σ1 σ2 (▹ x) = refl
sub-vsub-funct2 σ1 σ2 (ƛ M) = ≡-cong1 ƛ (≡-trans (sub-resp-≋ (ext-vext-funct2 σ1 σ2) M) (sub-vsub-funct2 (vext σ1) (ext σ2) M))
sub-vsub-funct2 σ1 σ2 (M · N) = ≡-cong2 _·_ (sub-vsub-funct2 σ1 σ2 M) (sub-vsub-funct2 σ1 σ2 N)

ext-funct : ∀ {m n k} (σ1 : subst n k) (σ2 : subst m n) -> ext (σ1 • σ2) ≋ (ext σ1 • ext σ2)
ext-funct σ1 σ2 z = refl
ext-funct σ1 σ2 (s x) = ≡-trans (≡-sym (sub-vsub-funct2 s σ1 (σ2 x))) (sub-vsub-funct (ext σ1) s (σ2 x))

sub-funct : ∀ {m n k} (σ1 : subst n k) (σ2 : subst m n) -> sub (σ1 • σ2) ≋ (sub σ1 ∘ sub σ2)
sub-funct σ1 σ2 (▹ x) = refl
sub-funct σ1 σ2 (ƛ M) = ≡-cong1 ƛ (≡-trans (sub-resp-≋ (ext-funct σ1 σ2) M) (sub-funct (ext σ1) (ext σ2) M))
sub-funct σ1 σ2 (M · N) = ≡-cong2 _·_ (sub-funct σ1 σ2 M) (sub-funct σ1 σ2 N)

sub-assoc : ∀ {l m n k} (σ1 : subst n k) (σ2 : subst m n) (σ3 : subst l m) -> ((σ1 • σ2) • σ3) ≋ (σ1 • (σ2 • σ3))
sub-assoc σ1 σ2 σ3 x = sub-funct σ1 σ2 (σ3 x)

sub-η-expand : ∀ {m n} (σ : subst (s m) n) -> σ ≋ ((σ ∘ s) ,, σ z)
sub-η-expand σ z = refl
sub-η-expand σ (s x) = refl

sub-id : ∀ {m} -> sub (▹ {m}) ≋ id
sub-id (▹ x) = refl
sub-id (ƛ M) = ≡-cong1 ƛ (≡-trans (sub-resp-≋ (≋-sym (sub-η-expand ▹)) M) (sub-id M))
sub-id (M · N) = ≡-cong2 _·_ (sub-id M) (sub-id N)

β1 : ∀ {m n k} (σ1 : subst n k) (σ2 : subst m k) -> ((pair σ1 σ2) • (proj1 {m})) ≋ σ1
β1 {z} σ1 σ2 x = refl
β1 {s n} σ1 σ2 x = ≡-trans (≡-sym (sub-vsub-funct (pair σ1 (σ2 ∘ s) ,, σ2 z) s (proj1 {n} x))) (β1 σ1 (σ2 ∘ s) x)

β2 : ∀ {m n k} (σ1 : subst n k) (σ2 : subst m k) -> ((pair σ1 σ2) • (proj2 {m})) ≋ σ2
β2 {z} σ1 σ2 ()
β2 {s n} σ1 σ2 z = refl
β2 {s n} σ1 σ2 (s x) = ≡-trans (≡-sym (sub-vsub-funct (pair σ1 (σ2 ∘ s) ,, σ2 z) s (proj2 x))) (β2 σ1 (σ2 ∘ s) x)

sub-η : ∀ {n m k} (σ : subst (m + n) k) -> σ ≋ (pair (σ • (proj1 {n})) (σ • (proj2 {n})))
sub-η {z} σ x = refl
sub-η {s n} σ z = refl
sub-η {s n} σ (s x) = ≡-trans (sub-η {n} (σ ∘ s) x) (≡-sym (pair-resp-≋
           (∘-resp-≋1 (≋-sym (sub-vsub-funct σ s)) (proj1 {n}))
           (∘-resp-≋1 (≋-sym (sub-vsub-funct σ s)) (proj2 {n})) x))

-- Single substitution as a special case of simultaneous
single : ∀ {n} -> tm (s n) -> tm n -> tm n
single M N = sub (▹ ,, N) M 

open module ccsolve1 = ccsolve (λ t s → subst (len s) (len t)) hiding (id)

id1 = cc.ccsolve.id

⟦_⟧ : ∀ {t s} -> exp t s -> subst (len s) (len t)
⟦ M ◦ N ⟧ = ⟦ N ⟧ • ⟦ M ⟧
⟦ cc.ccsolve.id ⟧ = ▹
⟦ ▹ x ⟧ = x
⟦ [ M , N ] ⟧ = pair ⟦ M ⟧ ⟦ N ⟧
⟦_⟧ {.(u × v)} {.u} (π₁ {u} {v}) = proj1 {len v}
⟦_⟧ {.(u × v)} {.v} (π₂ {u} {v}) = proj2 {len v}
⟦ ! ⟧ = λ () 


-- Is it easier to prove these kinds of laws for the 1-at-a-time version?
-- Or what if we made our lambda calculus more closely resemble this structure?
⟦_⟧eq : ∀ {t s} {M N : exp t s} -> M ≈ N -> ⟦ M ⟧ ≋ ⟦ N ⟧
⟦ refl ⟧eq = ≋-refl _
⟦ sym y ⟧eq = ≋-sym ⟦ y ⟧eq
⟦ trans y y' ⟧eq = ≋-trans ⟦ y' ⟧eq ⟦ y ⟧eq
⟦ assoc m n p ⟧eq = sub-assoc ⟦ p ⟧ ⟦ n ⟧ ⟦ m ⟧
⟦ idL ⟧eq = ≋-refl _
⟦ idR ⟧eq = λ x -> sub-id _
⟦ y ◦ y' ⟧eq = λ x -> ≡-cong-app (sub-resp-≋ ⟦ y' ⟧eq) (⟦ y ⟧eq x)
⟦ π₁-β {m = M} {n = N} ⟧eq = β1 ⟦ M ⟧ ⟦ N ⟧
⟦ π₂-β {m = M} {n = N} ⟧eq = β2 ⟦ M ⟧ ⟦ N ⟧
⟦ π-η {s = t} {m = M} ⟧eq = sub-η {len t} ⟦ M ⟧
⟦ [ y , y' ] ⟧eq = pair-resp-≋ ⟦ y ⟧eq ⟦ y' ⟧eq
⟦ ! ⟧eq = λ ()

data pr {n : nat} : tm n -> tm n -> Set where
 ▹ : (x : var n) -> pr (▹ x) (▹ x) 
 ƛ : ∀ {M M'} -> (m : pr M M') -> pr (ƛ M) (ƛ M')
 _·_ : ∀ {M M' N N'} -> (m : pr M M') -> (n : pr N N') -> pr (M · N) (M' · N')
 βp : ∀ {M M' N N'} -> (m : pr M M') -> (n : pr N N') -> pr ((ƛ M) · N) (single M' N')

data cd {n : nat} : tm n -> tm n -> Set where
 ▹ : (x : var n) -> cd (▹ x) (▹ x)
 ƛ : ∀ {M M'} -> (m : cd M M') -> cd (ƛ M) (ƛ M')
 _·₁_ : ∀ {x M' N N'} -> (m : cd (▹ x) M') -> (n : cd N N') -> cd ((▹ x) · N) (M' · N')
 _·₂_ : ∀ {M1 M2 M' N N'} -> (m : cd (M1 · M2) M') -> (n : cd N N') -> cd ((M1 · M2) · N) (M' · N')
 βc : ∀ {M M' N N'} -> (m : cd M M') -> (n : cd N N') -> cd ((ƛ M) · N) (single M' N')

pr-subst : ∀ {n m} (σ1 σ2 : subst n m) -> Set
pr-subst {n} {m} σ1 σ2 = (x : var n) -> pr (σ1 x) (σ2 x)

pr, : ∀ {n m} {σ1 σ2 : subst m n} -> pr-subst σ1 σ2 -> {N1 N2 : tm n} -> pr N1 N2 -> pr-subst (σ1 ,, N1) (σ2 ,, N2)
pr, θ N z = N
pr, θ N (s x) = θ x

pr-ext : ∀ {n m : nat} {σ1 σ2 : subst n m} (θ : pr-subst σ1 σ2) -> pr-subst (ext σ1) (ext σ2)
pr-ext θ = pr, {!!} (▹ z)

-- Okay, we can add constructions to our CC language like "ext", where they reduce to the other primitives
-- This might help the translation




--lem : ∀ {t s} (σ : mvar s t) (N : mvar t (▹ tt)) -> ([ id1 , (▹ N) ] ◦ (▹ σ)) ≈ ([ ((▹ σ) ◦ π₁) , π₂ ] ◦ [ id1 , ((▹ N) ◦ (▹ σ)) ])
--lem σ N = completeness ([ id1 , (▹ N) ] ◦ (▹ σ)) ([ ((▹ σ) ◦ π₁) , π₂ ] ◦ [ id1 , ((▹ N) ◦ (▹ σ)) ]) refl

-- When can I exploit unification in reverse to get one from the other for free?
lem2 : ∀ {n m} (σ : subst n m) (N : tm n) -> (σ • (▹ ,, N)) ≋ ((▹ ,, sub σ N) • (ext σ))
lem2 σ N = ⟦ (completeness ([ id1 , (▹ (► N)) ] ◦ (▹ σ))  ([ ((▹ σ) ◦ π₁) , π₂ ] ◦ [ id1 , ((▹ (► N)) ◦ (▹ σ)) ]) refl) ⟧eq 

pr-subst-app : ∀ {n m} {M1 M2 : tm n} {σ1 σ2 : subst n m} -> pr-subst σ1 σ2 -> pr M1 M2 -> pr (sub σ1 M1) (sub σ2 M2)
pr-subst-app θ (▹ x) = θ x
pr-subst-app θ (ƛ m') = ƛ (pr-subst-app (pr-ext θ) m')
pr-subst-app θ (m' · n') = (pr-subst-app θ m') · (pr-subst-app θ n')
pr-subst-app θ (βp m' n') with βp (pr-subst-app (pr-ext θ) m') (pr-subst-app θ n')
... | w1 = ≡-cong (pr _) {!!} w1


{-prsub : ∀ {n} {M M' : tm (s n)} {N N'} -> pr M M' -> pr N N' -> pr (single M N) (single M' N')
prsub θ p = {!!} -}

triangle : ∀ {n} {M M' N : tm n} -> pr M N -> cd M M' -> pr N M'
triangle (▹ .x) (▹ x) = ▹ x
triangle (ƛ m) (ƛ m') = ƛ (triangle m m')
triangle (m · n') (m' ·₁ n0) = triangle m m' · triangle n' n0
triangle (m · n') (m' ·₂ n0) = triangle m m' · triangle n' n0
triangle (ƛ m · n') (βc m' n0) = βp (triangle m m') (triangle n' n0)
triangle (βp m n') (βc m' n0) = pr-subst-app (pr, ▹ (triangle n' n0)) (triangle m m') --prsub (triangle m m') (triangle n' n0)

cdTotal : ∀ {n} (M : tm n) -> Σ (cd M)
cdTotal (▹ x) = ▹ x , ▹ x
cdTotal (ƛ M) with cdTotal M
cdTotal (ƛ M) | _ , M' = _ , ƛ M'
cdTotal (M · N) with cdTotal M | cdTotal N
cdTotal (▹ x · N) | _ , x' | _ , N'       = _ , (x' ·₁ N')
cdTotal (ƛ M · N) | _ , M' | _ , N'       = _ , (βc (Σ.snd (cdTotal M)) N')
cdTotal ((M · N1) · N2) | _ , M' | _ , N' = _ , (M' ·₂ N')

diamond : ∀ {n} M {N1 N2 : tm n} -> pr M N1 -> pr M N2 -> Σ (λ N -> pr N1 N * pr N2 N)
diamond M p1 p2 with cdTotal M
diamond M p1 p2 | N , n = N , ((triangle p1 n) , (triangle p2 n))
