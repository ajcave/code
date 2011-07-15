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
 -- Why not restrict the second to atype?
 data spine : type -> type -> Set where
  id : ∀ {ρ} -> spine ρ ρ
  _∘πl : ∀ {τ σ ρ} -> (S : spine σ ρ) -> spine (σ × τ) ρ
  _∘πr : ∀ {τ σ ρ} -> (S : spine τ ρ) -> spine (σ × τ) ρ
  -- Why here? Why not in nf? 3rd category?
  _∘v[_]∘_ : ∀ {τ σ ρ α } -> (S : spine σ ρ) -> var τ σ -> nf α τ -> spine α ρ

_∘₁_ : ∀ {Γ σ τ} -> spine Γ τ -> spine σ Γ -> spine σ τ
t ∘₁ id = t
t ∘₁ (S ∘πl) = (t ∘₁ S) ∘πl
t ∘₁ (S ∘πr) = (t ∘₁ S) ∘πr
t ∘₁ (S ∘v[ y ]∘ y') = (t ∘₁ S) ∘v[ y ]∘ y'

η-exp : ∀ {τ σ} -> spine σ τ -> nf σ τ
η-exp {▹ B} S = ▹ S
η-exp {τ × σ} S = < (η-exp ((id ∘πl) ∘₁ S)) , (η-exp ((id ∘πr) ∘₁ S)) >
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