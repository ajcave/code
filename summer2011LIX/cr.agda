module cr where

data nat : Set where 
 z : nat
 s : (n : nat) -> nat

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
ext θ t (s x) = θ x -- vsub s (θ x) -- s is the weakening substitution

sub : ∀ {n m} -> subst n m -> tm n -> tm m
sub θ (▹ x) = θ x
sub θ (ƛ M) = ƛ (sub (ext (λ x → vsub s (θ x)) (▹ z)) M)
sub θ (M · N) = (sub θ M) · (sub θ N)

id : ∀ {n} -> subst n n
id x = ▹ x

-- Single substitution as a special case of simultaneous
single : ∀ {n} -> tm (s n) -> tm n -> tm n
single M N = sub (ext id N) M

data pr {n : nat} : tm n -> tm n -> Set where
 ▹ : (x : var n) -> pr (▹ x) (▹ x) 
 ƛ : ∀ {M M'} -> (m : pr M M') -> pr (ƛ M) (ƛ M')
 _·_ : ∀ {M M' N N'} -> (m : pr M M') -> (n : pr N N') -> pr (M · N) (M' · N')
 β : ∀ {M M' N N'} -> (m : pr M M') -> (n : pr N N') -> pr ((ƛ M) · N) (single M' N')

data nonlam (n : nat) : Set where
 ▹ : (x : var n) -> nonlam n
 _·_ : (M : tm n) -> (N : tm n) -> nonlam n

〈_〉 : ∀ {n} -> nonlam n -> tm n
〈 ▹ x 〉 = ▹ x
〈 M · N 〉 = M · N

data cd {n : nat} : tm n -> tm n -> Set where
 ▹ : (x : var n) -> cd (▹ x) (▹ x)
 ƛ : ∀ {M M'} -> (m : cd M M') -> cd (ƛ M) (ƛ M')
 _·_ : ∀ {M M' N N'} -> (m : cd 〈 M 〉 M') -> (n : cd N N') -> cd (〈 M 〉 · N) (M' · N')
 β : ∀ {M M' N N'} -> (m : cd M M') -> (n : cd N N') -> cd ((ƛ M) · N) (single M' N')
 