module stlc2 where

postulate
 atype : Set

data nat : Set where
 z : nat
 s : nat -> nat

data fin : nat -> Set where
 z : ∀ {n} -> fin (s n)
 s : ∀ {n} -> fin n -> fin (s n)

mutual 
 data type : Set where
  _[_] : ∀ {n} -> (α : atype) -> (fin n -> type) -> type
 ctx : nat -> Set
 ctx n = fin n -> type

_+_ : nat -> nat -> nat
n + z = n
n + s y = s (n + y)

inl : ∀ {n m} -> fin n -> fin (n + m)
inl {n} {z} x = x
inl {n} {s y} x = s (inl {n} {y} x)

inr : ∀ {n m} -> fin m -> fin (n + m)
inr {n} {z} ()
inr {n} {s y} z = z
inr {n} {s y} (s y') = s (inr y')

data inlr {n m} : fin (n + m) -> Set where
 is_l : ∀ {i} -> inlr (inl {n} {m} i)
 is_r : ∀ {j} -> inlr (inr {n} {m} j) 

inlrDec : ∀ {n m} (i : fin (n + m)) -> inlr {n} {m} i
inlrDec {n} {z} i = is_l
inlrDec {n} {s y} z = is_r
inlrDec {n} {s y} (s y') with inlrDec {n} {y} y'
inlrDec {n} {s y} (s .(inl {n} {y} i)) | is_l {i} = is_l
inlrDec {n} {s y} (s .(inr {n} {y} j)) | is_r {j} = is_r

_⊕_ : ∀ {n m} -> ctx n -> ctx m -> ctx (n + m)
_⊕_ {n} {m} Γ1 Γ2 x with inlrDec {n} {m} x
_⊕_ {n} {m} Γ1 Γ2 .(inl {n} {m} i) | is_l {i} = Γ1 i
_⊕_ {n} {m} Γ1 Γ2 .(inr {n} {m} j) | is_r {j} = Γ2 j

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
   fst : A
   snd : B fst

⊡ : ctx z
⊡ ()

_,,_ : ∀ {n} -> ctx n -> type -> ctx (s n)
(Γ ,, τ) z = τ
(Γ ,, τ) (s y) = Γ y

mutual
 data nf : ∀ {n} -> ctx n -> atype -> Set where
  ▹ : ∀ {n m k α i} {Γ : ctx n} {φ : ctx k} {ψ : ctx m} -> Γ i ≡ (α [ ψ ]) -> spine (Γ ⊕ φ) ψ -> nf (Γ ⊕ φ) α
 data spine {n} (Γ : ctx n) : ∀ {m} -> ctx m -> Set where
  ε : spine Γ {z} (λ())
  _,_ : ∀ {m k} {ψ : ctx m} {φ : ctx k} {α} -> spine Γ ψ -> nf (Γ ⊕ φ) α -> spine Γ (ψ ,, α [ φ ])

_∘_ : ∀ {A B C : Set} -> (f : B -> C) -> (g : A -> B) -> (A -> C)
(f ∘ g) x = f (g x)

subst : ∀ {n m} -> ctx n -> ctx m -> Set
subst {n} {m} Γ Δ = Σ {fin n -> fin m} (λ f -> ∀ i -> Γ i ≡ Δ (f i))

{-sem : ∀ {n} -> ctx n -> type -> Set
sem Γ (α [ ψ ]) = ∀ {m} {Δ : ctx m} → subst Γ Δ → (∀ i -> sem Δ (ψ i)) → nf Δ α

appSubst : ∀ {n m} {Γ : ctx n} {Δ : ctx m} {S} -> subst Δ Γ -> nf Δ S -> nf Γ S
appSubst (σ , pf) (▹ y' sp) = {!!}

reflect : ∀ {n m} (Γ : ctx n) (ψ : ctx m) α -> nf (Γ ⊕ ψ) α -> sem Γ (α [ ψ ])
reflect {n} {m1} Γ ψ α M = λ σ → λ s' → {!!}

reify : ∀ {n m} (Γ : ctx n) α (ψ : ctx m) -> sem Γ (α [ ψ ]) -> nf (Γ ⊕ ψ) α
reify {n} {m} Γ α ψ M = M (inl {n} {m}, {!!}) (λ i → {!!}) -}

sem : ∀ {n} -> ctx n -> atype -> Set
sem ψ α = ∀ {m} {Δ : ctx m} → subst ψ Δ → (∀ i -> sem Δ (ψ i)) → nf Δ α

