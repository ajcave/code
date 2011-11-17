module cr where


_∘_ : ∀ {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘ g) x = f (g x)

data nat : Set where 
 z : nat
 s : (n : nat) -> nat

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

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

-- TODO: Try computing vsubst by recursion on n

vext : ∀ {n m} -> vsubst n m -> vsubst (s n) (s m)
vext θ z = z
vext θ (s x) = s (θ x)

vsub : ∀ {n m} -> vsubst n m -> tm n -> tm m
vsub θ (▹ x) = ▹ (θ x)
vsub θ (ƛ M) = ƛ (vsub (vext θ) M)
vsub θ (M · N) = (vsub θ M) · (vsub θ N)

id-vsub : ∀ {n} -> vsubst n n
id-vsub x = x

wkn-vsub : ∀ {n} -> vsubst n (s n)
wkn-vsub = s

subst : (n m : nat) -> Set
subst n m = var n -> tm m

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


id : ∀ {n} -> subst n n
id x = ▹ x

wkn : ∀ {n} -> subst n (s n)
wkn {n} = wkn-subst id

-- Single substitution as a special case of simultaneous
single : ∀ {n} -> tm (s n) -> tm n -> tm n
single M N = sub (id ,, N) M 

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

{-data pr-subst : {n m : nat} (σ1 σ2 : subst n m) -> Set where
 ⊡ : ∀ {m} -> pr-subst {m = m} ⊡ ⊡
 _,_ : ∀ {n m} {σ1 σ2 : subst n m} (θ : pr-subst σ1 σ2) {M1 M2 : tm m} -> pr M1 M2 -> pr-subst (σ1 , M1) (σ2 , M2)

pr-map : ∀ {n m k} {σ1 σ2 : subst n m} {f1 f2 : tm m -> tm k} (F : ∀ {M1 M2} -> pr M1 M2 -> pr (f1 M1) (f2 M2)) (θ : pr-subst σ1 σ2)
 -> pr-subst (subst-map f1 σ1) (subst-map f2 σ2)
pr-map F ⊡ = ⊡
pr-map F (θ , m) = (pr-map F θ) , F m

pr-wkn : ∀ {n m} {σ1 σ2 : subst n m} (θ : pr-subst σ1 σ2) -> pr-subst (wkn-subst σ1) (wkn-subst σ2)
pr-wkn θ = pr-map (λ x → {!!}) {!!}
-}
pr-ext : ∀ {n m : nat} {σ1 σ2 : subst n m} (θ : pr-subst σ1 σ2) -> pr-subst (ext σ1) (ext σ2)
pr-ext θ z = ▹ z
pr-ext θ (s x) = {!!}

-- Okay, we can add constructions to our CC language like "ext", where they reduce to the other primitives
-- This might help the translation

pr-subst-app : ∀ {n m} {M1 M2 : tm n} {σ1 σ2 : subst n m} -> pr-subst σ1 σ2 -> pr M1 M2 -> pr (sub σ1 M1) (sub σ2 M2)
pr-subst-app θ (▹ x) = θ x
pr-subst-app θ (ƛ m') = ƛ (pr-subst-app (pr-ext θ) m')
pr-subst-app θ (m' · n') = (pr-subst-app θ m') · (pr-subst-app θ n')
pr-subst-app θ (βp m' n') with βp (pr-subst-app (pr-ext θ) m') (pr-subst-app θ n')
... | w1 = {!!}


{-prsub : ∀ {n} {M M' : tm (s n)} {N N'} -> pr M M' -> pr N N' -> pr (single M N) (single M' N')
prsub θ p = {!!} -}

triangle : ∀ {n} {M M' N : tm n} -> pr M N -> cd M M' -> pr N M'
triangle (▹ .x) (▹ x) = ▹ x
triangle (ƛ m) (ƛ m') = ƛ (triangle m m')
triangle (m · n') (m' ·₁ n0) = triangle m m' · triangle n' n0
triangle (m · n') (m' ·₂ n0) = triangle m m' · triangle n' n0
triangle (ƛ m · n') (βc m' n0) = βp (triangle m m') (triangle n' n0)
triangle (βp m n') (βc m' n0) = {!!} --prsub (triangle m m') (triangle n' n0)

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
