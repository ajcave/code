module abella where

postulate
 btype : Set

data nat : Set where
 z : nat
 s : nat -> nat

data fin : nat -> Set where
 z : ∀ {n} -> fin (s n)
 s : ∀ {n} -> fin n -> fin (s n)

data type : Set where
 ▻ : btype -> type
 _⇒_ : type -> type -> type

data ctx : Set where
 ε : ctx
 _,_ : ctx -> type -> ctx

data var : (Γ : ctx) (τ : type) -> Set where
 z : ∀ {Γ τ} -> var (Γ , τ) τ
 s : ∀ {Γ τ σ} -> var Γ τ -> var (Γ , σ) τ

postulate
 con : ∀ n -> (fin n -> type) -> Set
 tcon : type -> Set

data tm (Γ : ctx) : type -> Set where 
 ▹ : ∀ {τ} -> var Γ τ -> tm Γ τ
 _·_ : ∀ {τ σ} -> tm Γ (τ ⇒ σ) -> tm Γ τ -> tm Γ σ
 ƛ : ∀ {τ σ} -> tm (Γ , τ) σ -> tm Γ (τ ⇒ σ)
 ▸ : ∀ {τ} -> tcon τ -> tm Γ τ

data atomic (Γ : ctx) : Set where
 _·_ : ∀ {n τs} -> con n τs -> ((i : fin n) -> tm Γ (τs i)) -> atomic Γ

data goal (Γ : ctx) : Set where
 ▹ : atomic Γ -> goal Γ
 ∧ : ∀ {n} -> (fin n -> goal Γ) -> goal Γ
 _⊃_ : ∀ {n} -> (fin n -> atomic Γ) -> goal Γ -> goal Γ
 ∀· : ∀ {τ} -> goal (Γ , τ) -> goal Γ

data clause : Set where
 ▹ : ∀ {Γ n} -> (fin n -> goal Γ) -> atomic Γ -> clause




 