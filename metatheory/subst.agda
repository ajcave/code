module subst where

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ S T} -> var Γ T -> var (Γ , S) T

data tp : Set where
 i : tp
 _⇝_ : (T S : tp) -> tp

data exp (Γ : ctx tp) : tp -> Set where
 ▹ : ∀ {T} -> var Γ T -> exp Γ T
 _·_ : ∀ {T S} (M : exp Γ (T ⇝ S)) (N : exp Γ T) -> exp Γ S
 ƛ : ∀ {T S} (M : exp (Γ , T) S) -> exp Γ (T ⇝ S)

data sub : (Γ : ctx tp) -> ctx tp -> Set where
 ⊡ : ∀ {Γ} -> sub Γ ⊡
 _,_ : ∀ {Γ Δ T} (σ : sub Γ Δ) (M : exp Γ T) -> sub Γ (Δ , T)
 ext : ∀ {Γ Δ T} (σ : sub Γ Δ) -> sub (Γ , T) (Δ , T)
