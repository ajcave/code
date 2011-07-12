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
  _[_] :  (α : atype) -> ctx -> type
 data ctx : Set where
  ⊡ : ctx
  _,_ : ctx -> type -> ctx

 --ctx : nat -> Set
 --ctx n = fin n -> type

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

{-_⊕_ : ∀ {n m} -> ctx n -> ctx m -> ctx (n + m)
_⊕_ {n} {m} Γ1 Γ2 x with inlrDec {n} {m} x
_⊕_ {n} {m} Γ1 Γ2 .(inl {n} {m} i) | is_l {i} = Γ1 i
_⊕_ {n} {m} Γ1 Γ2 .(inr {n} {m} j) | is_r {j} = Γ2 j -}

_⊕_ : ctx -> ctx -> ctx
Γ1 ⊕ ⊡ = Γ1
Γ1 ⊕ (Γ2 , τ) = (Γ1 ⊕ Γ2) , τ

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
   fst : A
   snd : B fst

{-⊡ : ctx z
⊡ ()

_,,_ : ∀ {n} -> ctx n -> type -> ctx (s n)
(Γ ,, τ) z = τ
(Γ ,, τ) (s y) = Γ y -}

data var : ctx -> type -> Set where
 z : ∀ {Γ τ} -> var (Γ , τ) τ
 s : ∀ {Γ τ σ} -> var Γ τ -> var (Γ , σ) τ

mutual
 data nf : ctx -> atype -> Set where
  ▹ : ∀ α Γ φ ψ -> var Γ (α [ ψ ]) -> spine (Γ ⊕ φ) ψ -> nf (Γ ⊕ φ) α
 data spine (Γ : ctx) : ctx -> Set where
  ε : spine Γ ⊡
  _,_ : ∀ {ψ : ctx} {φ : ctx} {α} -> spine Γ ψ -> nf (Γ ⊕ φ) α -> spine Γ (ψ , α [ φ ])

_∘_ : ∀ {A B C : Set} -> (f : B -> C) -> (g : A -> B) -> (A -> C)
(f ∘ g) x = f (g x)

--subst : ∀ {n m} -> ctx -> ctx m -> Set
--subst {n} {m} Γ Δ = Σ {fin n -> fin m} (λ f -> ∀ i -> Γ i ≡ Δ (f i))

varl : ∀ {Γ ψ τ} -> var Γ τ -> var (Γ ⊕ ψ) τ
varl {Γ} {⊡} x = x
varl {Γ} {ψ , σ} x = s (varl {Γ} {ψ} x)

appSubst : ∀ {Γ Δ α} -> nf Γ α -> (∀ {β ψ} -> var Γ (β [ ψ ]) -> nf (Δ ⊕ ψ) β) -> nf Δ α
appSubst {.(Γ ⊕ φ)} {Δ} {α} (▹ .α Γ φ ψ y y') σ with Δ ⊕ ψ | σ (varl {Γ} {φ} y)
appSubst {.(Γ ⊕ φ)} {.(y' ⊕ ψ')} {α} (▹ .α Γ φ ψ y y1) σ | .(Γ' ⊕ φ') | ▹ .α Γ' φ' ψ' y' y0 = ?
