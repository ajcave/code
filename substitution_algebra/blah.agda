module blah where

postulate
 atype : Set

data type : Set where
 ▹ : atype -> type
 _⇒_ : type -> type -> type
 _×_ : type -> type -> type
 ⊤ : type

mutual
 data nf (Γ : type) : type -> Set where
  ▹ : ∀ {τ} -> (S : spine Γ (▹ τ)) -> nf Γ (▹ τ)
  <_,_> : ∀ {σ τ} -> (N : nf Γ τ) -> (M : nf Γ σ) -> nf Γ (τ × σ)
 data spine : type -> type -> Set where
  id : ∀ {ρ} -> spine ρ ρ
  _∘πl : ∀ {τ σ ρ} -> (S : spine σ ρ) -> spine (σ × τ) ρ
  _∘πr : ∀ {τ σ ρ} -> (S : spine τ ρ) -> spine (σ × τ) ρ

mutual
 _[[:=_]] : ∀ {Γ σ τ} -> nf Γ τ -> nf σ Γ -> nf σ τ
 ▹ S [[:= N' ]] = N' ◇ S 
 < M , N > [[:= N' ]] = < (M [[:= N' ]]) , (N [[:= N' ]]) >

 _◇_ : ∀ {Γ τ σ} -> nf Γ σ -> spine σ τ -> nf Γ τ
 N ◇ id = N
 < N , M > ◇ (S ∘πl) = N ◇ S
 < N , M > ◇ (S ∘πr) = M ◇ S