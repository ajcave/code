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


mutual
 data _,_,_⊢_true (ζ : ctx type) (Δ : ctx (prop ζ)) (Γ : ctx (prop ζ)) : prop ζ -> Set where
  ▹ : {A : prop ζ} (x : var Γ A)
                -> -------------------
                    ζ , Δ , Γ ⊢ A true
  ƛ : {A B : prop ζ} -> (M : ζ , Δ , (Γ , A) ⊢ B true)
                     -> -----------------------------------
                        ζ , Δ , Γ ⊢ (A ⊃ B) true
  _·_ : {A B : prop ζ}    (M : ζ , Δ , Γ ⊢ (A ⊃ B) true) (N : ζ , Δ , Γ ⊢ A true)
                       -> -------------------------------------------------------
                                            ζ , Δ , Γ ⊢ B true
  let-box : ∀ {A C} (M : ζ , Δ , Γ ⊢ (□ A) true) (N : ζ , (Δ , A) , Γ ⊢ C true)
                  -> ---------------------------------------------------------------
                                          ζ , Δ , Γ ⊢ C true
  box : ∀ {A} -> (M : ζ , ⊡ , Δ ⊢ A true)
              -> ------------------------
                   ζ , Δ , Γ ⊢ (□ A) true

sub-valid : ∀ {ζ Δ Γ A C} (D : ζ , ⊡ , Δ ⊢ A true) (E : ζ , (Δ , A) , Γ ⊢ C true)
 ->  ζ , Δ , Γ ⊢ C true
sub-valid D (▹ x) = ▹ x
sub-valid D (ƛ M) = ƛ (sub-valid D M)
sub-valid D (M · N) = (sub-valid D M) · (sub-valid D N)
sub-valid D (let-box M N) = {!!}
sub-valid D (box M) = box {!!}

data step {ζ Δ Γ} : {A : prop ζ} -> ζ , Δ , Γ ⊢ A true -> ζ , Δ , Γ ⊢ A true -> Set where
 box-red : ∀ {A C} (D : ζ , ⊡ , Δ ⊢ A true) (E : ζ , (Δ , A) , Γ ⊢ C true)
                -> step (let-box (box D) E) (sub-valid D E)