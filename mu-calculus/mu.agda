module mu where

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : ctx A -> A -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ S T} -> var Γ T -> var (Γ , S) T

record type : Set where
 constructor #prop

postulate
 atomic-prop : Set

data prop (ζ : ctx type) : Set where
 ▸ : (P : atomic-prop) -> prop ζ
 ▹ : (A : var ζ #prop) -> prop ζ
 μ : (A : prop (ζ , #prop)) -> prop ζ
 □ : (A : prop ζ) -> prop ζ
 ◇ : (A : prop ζ) -> prop ζ
 _⊃_ : (A B : prop ζ) -> prop ζ

data validJ (ζ : ctx type) : Set where
 _valid : (A : prop ζ) -> validJ ζ

data trueJ (ζ : ctx type) : Set where
 _true : (A : prop ζ) -> trueJ ζ

mutual
 data _,_,_⊢_true (ζ : ctx type) (Δ : ctx (validJ ζ)) (Γ : ctx (trueJ ζ)) : prop ζ -> Set where
  ▹ : {A : prop ζ} (x : var Γ (A true))
                -> -------------------
                    ζ , Δ , Γ ⊢ A true
  ƛ : {A B : prop ζ} -> ζ , Δ , (Γ , A true) ⊢ B true
                     -> -----------------------------
                        ζ , Δ , Γ ⊢ (A ⊃ B) true
  _·_ : {A B : prop ζ} -> ζ , Δ , Γ ⊢ (A ⊃ B) true  ->  ζ , Δ , Γ ⊢ A true
                       -> -------------------------------------------------
                                            ζ , Δ , Γ ⊢ B true
  