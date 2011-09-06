module cr where

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

-- A variable for variable substitution is a mapping from variables
-- "in n" to variables "in m". This includes all combinations of
-- exchange, weakening, and contraction
data vsubst : (n m : nat) -> Set where
 ⊡ : ∀ {m} -> vsubst z m
 _,_ : ∀ {n m} (θ : vsubst n m) (x : var m) -> vsubst (s n) m

vsubst-map : ∀ {n m k : nat} (f : var m -> var k) (θ : vsubst n m) -> vsubst n k
vsubst-map f ⊡ = ⊡
vsubst-map f (θ , x) = (vsubst-map f θ) , (f x)

vsubst-app : ∀ {n m} (θ : vsubst n m) (x : var n) -> var m
vsubst-app ⊡ ()
vsubst-app (θ , x) z = x
vsubst-app (θ , x) (s x') = vsubst-app θ x'

vext : ∀ {n m} -> vsubst n m -> vsubst (s n) (s m)
vext θ = (vsubst-map s θ) , z 

vsub : ∀ {n m} -> vsubst n m -> tm n -> tm m
vsub θ (▹ x) = ▹ (vsubst-app θ x)
vsub θ (ƛ M) = ƛ (vsub (vext θ) M)
vsub θ (M · N) = (vsub θ M) · (vsub θ N)

id-vsub : ∀ {n} -> vsubst n n
id-vsub {z} = ⊡
id-vsub {s n} = (vsubst-map s id-vsub) , z

wkn-vsub : ∀ {n} -> vsubst n (s n)
wkn-vsub = vsubst-map s id-vsub

-- A substitution from the domain with n variables to the domain with
-- m variables is a mapping from variables "from n" to terms in m variables
data subst : (n m : nat) -> Set where
 ⊡ : ∀ {n} -> subst z n
 _,_ : ∀ {n m} (θ : subst n m) (x : tm m) -> subst (s n) m

subst-map : ∀ {n m k} (f : tm m -> tm k) (θ : subst n m) -> subst n k
subst-map f ⊡ = ⊡
subst-map f (θ , x) = (subst-map f θ) , (f x) 

subst-app : ∀ {n m} (θ : subst n m) (x : var n) -> tm m
subst-app ⊡ ()
subst-app (θ , x) z = x
subst-app (θ , x) (s x') = subst-app θ x'

wkn-subst : ∀ {n m} (θ : subst n m) -> subst n (s m)
wkn-subst θ = subst-map (vsub wkn-vsub) θ

ext : ∀ {n m} (θ : subst n m) -> subst (s n) (s m)
ext θ = (wkn-subst θ) , (▹ z)

sub : ∀ {n m} -> subst n m -> tm n -> tm m
sub θ (▹ x) = subst-app θ x
sub θ (ƛ M) = ƛ (sub (ext θ) M)
sub θ (M · N) = (sub θ M) · (sub θ N)

_∘_ : ∀ {n m k} (θ1 : subst m k) (θ2 : subst n m) -> subst n k
θ1 ∘ ⊡ = ⊡
θ1 ∘ (θ , M) = (θ1 ∘ θ) , sub θ1 M

id : ∀ {n} -> subst n n
id {z} = ⊡
id {s n} = ext id

wkn : ∀ {n} -> subst n (s n)
wkn {n} = wkn-subst id

extensionality : ∀ {n m} (θ1 θ2 : subst n m) (H : ∀ x -> subst-app θ1 x ≡ subst-app θ2 x) -> θ1 ≡ θ2
extensionality ⊡ ⊡ H = refl
extensionality (θ , x) (θ' , x') H rewrite extensionality θ θ' (λ x0 → H (s x0)) | H z = refl

subst-map-funct : ∀ {n1 n m k} (f : tm m -> tm k) (g : tm n -> tm m) (θ : subst n1 n) -> subst-map f (subst-map g θ) ≡ subst-map (λ x -> f (g x)) θ
subst-map-funct f g θ = {!!}

prod-wkn : ∀ {n m} (θ1 : subst n m) (N : tm m) -> ((θ1 , N) ∘ wkn) ≡ θ1
prod-wkn ⊡ N = refl
prod-wkn (θ , x) N = {!!}

-- Single substitution as a special case of simultaneous
single : ∀ {n} -> tm (s n) -> tm n -> tm n
single M N = sub (id , N) M 

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

data pr-subst : {n m : nat} (σ1 σ2 : subst n m) -> Set where
 ⊡ : ∀ {m} -> pr-subst {m = m} ⊡ ⊡
 _,_ : ∀ {n m} {σ1 σ2 : subst n m} (θ : pr-subst σ1 σ2) {M1 M2 : tm m} -> pr M1 M2 -> pr-subst (σ1 , M1) (σ2 , M2)

pr-map : ∀ {n m k} {σ1 σ2 : subst n m} {f1 f2 : tm m -> tm k} (F : ∀ {M1 M2} -> pr M1 M2 -> pr (f1 M1) (f2 M2)) (θ : pr-subst σ1 σ2)
 -> pr-subst (subst-map f1 σ1) (subst-map f2 σ2)
pr-map F ⊡ = ⊡
pr-map F (θ , m) = (pr-map F θ) , F m

pr-wkn : ∀ {n m} {σ1 σ2 : subst n m} (θ : pr-subst σ1 σ2) -> pr-subst (wkn-subst σ1) (wkn-subst σ2)
pr-wkn θ = pr-map (λ x → {!!}) {!!}

pr-ext : ∀ {n m : nat} {σ1 σ2 : subst n m} (θ : pr-subst σ1 σ2) -> pr-subst (ext σ1) (ext σ2)
pr-ext θ = pr-wkn θ , (▹ z)

pr-subst-app : ∀ {n m} {M1 M2 : tm n} {σ1 σ2 : subst n m} -> pr-subst σ1 σ2 -> pr M1 M2 -> pr (sub σ1 M1) (sub σ2 M2)
pr-subst-app θ (▹ x) = {!!}
pr-subst-app θ (ƛ m') = ƛ (pr-subst-app (pr-ext θ) m')
pr-subst-app θ (m' · n') = (pr-subst-app θ m') · pr-subst-app θ n'
pr-subst-app θ (βp m' n') with βp (pr-subst-app (pr-ext θ) m') (pr-subst-app θ n')
... | q = {!!}


prsub : ∀ {n} {M M' : tm (s n)} {N N'} -> pr M M' -> pr N N' -> pr (single M N) (single M' N')
prsub θ p = {!!}

triangle : ∀ {n} {M M' N : tm n} -> pr M N -> cd M M' -> pr N M'
triangle (▹ .x) (▹ x) = ▹ x
triangle (ƛ m) (ƛ m') = ƛ (triangle m m')
triangle (m · n') (m' ·₁ n0) = triangle m m' · triangle n' n0
triangle (m · n') (m' ·₂ n0) = triangle m m' · triangle n' n0
triangle (ƛ m · n') (βc m' n0) = βp (triangle m m') (triangle n' n0)
triangle (βp m n') (βc m' n0) = prsub (triangle m m') (triangle n' n0)

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
