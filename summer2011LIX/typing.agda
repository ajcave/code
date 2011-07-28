module typing where

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

data sort : Set where
 ⋆ : sort
 □ : sort

data tm (n : nat) : Set where
 ▹ : (x : var n) -> tm n
 ƛ : (U : tm n) -> (M : tm (s n)) -> tm n
 _·_ : (M : tm n) -> (N : tm n) -> tm n
 Π : (U : tm n) -> (T : tm (s n)) -> tm n
 ▸ : (S : sort) -> tm n

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
vsub θ (ƛ U M) = ƛ (vsub θ U) (vsub (vext θ) M)
vsub θ (M · N) = (vsub θ M) · (vsub θ N)
vsub θ (Π U T) = Π (vsub θ U) (vsub (vext θ) T)
vsub θ (▸ S) = ▸ S

-- A substitution from the domain with n variables to the domain with
-- m variables is a mapping from variables "from n" to terms in m variables
subst : (n m : nat) -> Set
subst n m = var n -> tm m

ext : ∀ {n m} -> subst n m -> tm m -> subst (s n) m
ext θ t z = t
ext θ t (s x) = θ x

sub : ∀ {n m} -> subst n m -> tm n -> tm m
sub θ (▹ x) = θ x
sub θ (ƛ U M) = ƛ (sub θ U) (sub (ext (λ x → vsub s (θ x)) (▹ z)) M)
sub θ (M · N) = (sub θ M) · (sub θ N)
sub θ (Π U T) = Π (sub θ U) (sub (ext (λ x → vsub s (θ x)) (▹ z)) T)
sub θ (▸ S) = ▸ S

id : ∀ {n} -> subst n n
id x = ▹ x

-- Single substitution as a special case of simultaneous
single : ∀ {n} -> tm (s n) -> tm n -> tm n
single M N = sub (ext id N) M

wkn : ∀ {n} -> tm n -> tm (s n)
wkn t = vsub s t

{- Typing -}
data axiom : sort -> sort -> Set where
 ⋆∶□ : axiom ⋆ □

data rule : sort -> sort -> sort -> Set where
 ⋆ : rule ⋆ ⋆ ⋆

data ctx : (n : nat) -> Set where
 ⊡ : ctx z
 _,_ : ∀ {n} (Γ : ctx n) -> (T : tm n) -> ctx (s n)

data vof : ∀ {n} (Γ : ctx n) -> var n -> tm n -> Set where
 z : ∀ {n} {Γ : ctx n} {T} -> vof (Γ , T) z (wkn T)
 s : ∀ {n} {Γ : ctx n} {T S x} -> vof Γ x T -> vof (Γ , S) (s x) (wkn T)

_,* : nat -> nat
Γ ,* = s Γ
data _⊢_≡β_ : (Γ : nat) -> (M N : tm Γ) -> Set where
 ▹ : ∀ {Γ x}
   -> Γ     ⊢ (▹ x) ≡β (▹ x)
 ƛ : ∀ {Γ U1 U2 M N}
   -> Γ     ⊢ U1 ≡β U2 
   -> Γ ,*  ⊢ M  ≡β N
   -> Γ     ⊢ (ƛ U1 M) ≡β (ƛ U2 N)
 -- etc

-- The length of a context
〚_〛 : ∀ {n} -> ctx n -> nat
〚_〛 {n} Γ = n

data of {n : nat} (Γ : ctx n) : (M : tm n) -> (T : tm n) -> Set where
 ▹ : ∀ {x T} (X : vof Γ x T) -> of Γ (▹ x) T
 ax : ∀ {S1 S2} -> axiom S1 S2 -> of Γ (▸ S1) (▸ S2)
 ƛ : ∀ {U T M S1 S2 S3}
     -> rule S1 S2 S3
     -> of Γ U (▸ S1)
     -> of (Γ , U) T (▸ S2)
     -> of (Γ , U) T M
     -> of Γ (ƛ U M) (Π U T) 
 Π : ∀ {U T S1 S2 S3}
     -> rule S1 S2 S3
     -> of Γ U (▸ S1)
     -> of (Γ , U) T (▸ S2)
     -> of Γ (Π U T) (▸ S3)
 _·_ : ∀ {M N U T}
     -> of Γ M (Π U T)
     -> of Γ N U
     -> of Γ (M · N) (single T N)
 ≡-conv : ∀ {M T U S}
     -> of Γ M U
     -> of Γ T (▸ S)
     -> 〚 Γ 〛 ⊢ U ≡β T
     -> of Γ M T
 
 

