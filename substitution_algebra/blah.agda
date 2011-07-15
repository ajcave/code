module blah where

postulate
 atype : Set

data type : Set where
 ▹ : atype -> type
-- _⇒_ : type -> type -> type
 _×_ : type -> type -> type
 ⊤ : type

postulate
 var : type -> type -> Set

mutual
 data nf (Γ : type) : type -> Set where
  ▹ : ∀ {τ} -> (S : spine Γ (▹ τ)) -> nf Γ (▹ τ)
  <_,_> : ∀ {σ τ} -> (N : nf Γ τ) -> (M : nf Γ σ) -> nf Γ (τ × σ)
  ! : nf Γ ⊤
 data spine : type -> type -> Set where
  id : ∀ {ρ} -> spine ρ ρ
  _∘πl : ∀ {τ σ ρ} -> (S : spine σ ρ) -> spine (σ × τ) ρ
  _∘πr : ∀ {τ σ ρ} -> (S : spine τ ρ) -> spine (σ × τ) ρ
  _∘v[_]∘_ : ∀ {τ σ ρ α } -> (S : spine σ ρ) -> var τ σ -> nf α τ -> spine α ρ


πl∘ : ∀ {τ σ ρ} -> (S : spine ρ (σ × τ)) -> spine ρ σ
πl∘ id = id ∘πl
πl∘ (S ∘πl) = πl∘ S ∘πl
πl∘ (S ∘πr) = πl∘ S ∘πr
πl∘ (S ∘v[ y ]∘ y') = πl∘ S ∘v[ y ]∘ y'

πr∘ : ∀ {τ σ ρ} -> (S : spine ρ (σ × τ)) -> spine ρ τ
πr∘ id = id ∘πr
πr∘ (S ∘πl) = πr∘ S ∘πl
πr∘ (S ∘πr) = πr∘ S ∘πr
πr∘ (S ∘v[ y ]∘ y') = πr∘ S ∘v[ y ]∘ y'

η-exp : ∀ {τ σ} -> spine σ τ -> nf σ τ
η-exp {▹ B} S = ▹ S
η-exp {τ × σ} S = < (η-exp (πl∘ S)) , (η-exp (πr∘ S)) >
η-exp {⊤} S = !

mutual
 _∘_ : ∀ {Γ σ τ} -> nf Γ τ -> nf σ Γ -> nf σ τ
 (▹ S) ∘ N = S ◇ N
 < M , N > ∘ N' = < (M ∘ N') , (N ∘ N') >
 ! ∘ N = !

 _◇_ : ∀ {Γ τ σ} -> spine σ τ -> nf Γ σ -> nf Γ τ
 id ◇ N  = N
 (S ∘πl) ◇ < N , M > = S ◇ N
 (S ∘πr) ◇ < N , M > = S ◇ M
 (S ∘v[ y ]∘ f) ◇ N = η-exp (S ∘v[ y ]∘ (f ∘ N))