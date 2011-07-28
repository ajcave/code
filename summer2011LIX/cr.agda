module cr where

data nat : Set where 
 z : nat
 s : (n : nat) -> nat

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

-- A variable for variable substitution is a mapping from variables
-- "in n" to variables "in m". This includes all combinations of
-- exchange, weakening, and contraction
vsubst : (n m : nat) -> Set
vsubst n m = var n -> var m

vext : ∀ {n m} -> vsubst n m -> vsubst (s n) (s m)
vext θ z = z
vext θ (s x) = s (θ x)

vsub : ∀ {n m} -> vsubst n m -> tm n -> tm m
vsub θ (▹ x) = ▹ (θ x)
vsub θ (ƛ M) = ƛ (vsub (vext θ) M)
vsub θ (M · N) = (vsub θ M) · (vsub θ N)

-- A substitution from the domain with n variables to the domain with
-- m variables is a mapping from variables "from n" to terms in m variables
subst : (n m : nat) -> Set
subst n m = var n -> tm m

ext : ∀ {n m} -> subst n m -> tm m -> subst (s n) m
ext θ t z = t
ext θ t (s x) = θ x

sub : ∀ {n m} -> subst n m -> tm n -> tm m
sub θ (▹ x) = θ x
sub θ (ƛ M) = ƛ (sub (ext (λ x → vsub s (θ x)) (▹ z)) M)
sub θ (M · N) = (sub θ M) · (sub θ N)

id : ∀ {n} -> subst n n
id x = ▹ x

-- Single substitution as a special case of simultaneous
single : ∀ {n} -> tm (s n) -> tm n -> tm n
single M N = sub (ext id N) M -- Just extend the identity substitution with N

data pr {n : nat} : tm n -> tm n -> Set where
 ▹ : (x : var n) -> pr (▹ x) (▹ x) 
 ƛ : ∀ {M M'} -> (m : pr M M') -> pr (ƛ M) (ƛ M')
 _·_ : ∀ {M M' N N'} -> (m : pr M M') -> (n : pr N N') -> pr (M · N) (M' · N')
 β : ∀ {M M' N N'} -> (m : pr M M') -> (n : pr N N') -> pr ((ƛ M) · N) (single M' N')

data cd {n : nat} : tm n -> tm n -> Set where
 ▹ : (x : var n) -> cd (▹ x) (▹ x)
 ƛ : ∀ {M M'} -> (m : cd M M') -> cd (ƛ M) (ƛ M')
 _·₁_ : ∀ {x M' N N'} -> (m : cd (▹ x) M') -> (n : cd N N') -> cd ((▹ x) · N) (M' · N')
 _·₂_ : ∀ {M1 M2 M' N N'} -> (m : cd (M1 · M2) M') -> (n : cd N N') -> cd ((M1 · M2) · N) (M' · N')
 β : ∀ {M M' N N'} -> (m : cd M M') -> (n : cd N N') -> cd ((ƛ M) · N) (single M' N')

prsub : ∀ {n} {M M' : tm (s n)} {N N'} -> pr M M' -> pr N N' -> pr (single M N) (single M' N')
prsub θ p = {!!}

triangle : ∀ {n} {M M' N : tm n} -> pr M N -> cd M M' -> pr N M'
triangle (▹ .x) (▹ x) = ▹ x
triangle (ƛ m) (ƛ m') = ƛ (triangle m m')
triangle (m · n') (m' ·₁ n0) = triangle m m' · triangle n' n0
triangle (m · n') (m' ·₂ n0) = triangle m m' · triangle n' n0
triangle (ƛ m · n') (β m' n0) = β (triangle m m') (triangle n' n0)
triangle (β m n') (β m' n0) = prsub (triangle m m') (triangle n' n0)

cdTotal : ∀ {n} (M : tm n) -> Σ (cd M)
cdTotal (▹ x) = ▹ x , ▹ x
cdTotal (ƛ M) with cdTotal M
cdTotal (ƛ M) | _ , M' = _ , ƛ M'
cdTotal (M · N) with cdTotal M | cdTotal N
cdTotal (▹ x · N) | _ , x' | _ , N'       = _ , (x' ·₁ N')
cdTotal (ƛ M · N) | _ , M' | _ , N'       = _ , (β (Σ.snd (cdTotal M)) N')
cdTotal ((M · N1) · N2) | _ , M' | _ , N' = _ , (M' ·₂ N')

diamond : ∀ {n} M {N1 N2 : tm n} -> pr M N1 -> pr M N2 -> Σ (λ N -> pr N1 N * pr N2 N)
diamond M p1 p2 with cdTotal M
diamond M p1 p2 | N , n = N , ((triangle p1 n) , (triangle p2 n))
