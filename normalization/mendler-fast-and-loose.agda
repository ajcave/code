data var : Set where
 top : var
 pop : var -> var

data tm : Set where
 ▹ : var -> tm
 ƛ : tm -> tm
 _·_ : tm -> tm -> tm
 rec : tm -> tm
 tt ff : tm

data tp : Set where
 ▹ : var -> tp
 μ : tp -> tp
 _⇒_ : tp -> tp -> tp
 bool : tp

data ctx : Set where
 ⊡ : ctx
 _,_ : ctx -> tp -> ctx

data tctx : Set where
 ⊡ : tctx
 _,⋆ : tctx -> tctx

data _∶_∈_ : var -> tp -> ctx -> Set where
 top : ∀ {Γ T} -> top ∶ T ∈ (Γ , T)
 pop : ∀ {Γ T S x} -> x ∶ T ∈ Γ -> (pop x) ∶ T ∈ (Γ , S)

data _*_⊢_∶_ (Δ : tctx) (Γ : ctx) : tm -> tp -> Set where
 ▹ : ∀ {x T} -> x ∶ T ∈ Γ -> Δ * Γ ⊢ ▹ x ∶ T
 ƛ : ∀ {T S t} -> Δ * (Γ , S) ⊢ t ∶ T -> Δ * Γ ⊢ (ƛ t) ∶ (S ⇒ T)
 _·_ : ∀ {T S t1 t2} -> Δ * Γ ⊢ t1 ∶ (S ⇒ T) -> Δ * Γ ⊢ t2 ∶ S -> Δ * Γ ⊢ (t1 · t2) ∶ T
 rec : ∀ {T C} -> (Δ ,⋆) * (Γ , (▹ top ⇒ C
 