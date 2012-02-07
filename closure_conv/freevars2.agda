module freevars2 where

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

_∘_ : {A B C : Set} (f : B -> C) (g : A -> B) -> A -> C
(f ∘ g) x = f (g x) 

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

data _+_ (A B : Set) : Set where
 inl : A -> A + B
 inr : B -> A + B

data ⊥ : Set where

record Unit : Set where
 constructor tt

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : ctx A -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

data tm (Γ : ctx Unit) : Unit -> Set where
 ▹ : (x : var Γ tt) -> tm Γ tt
 ƛ : (M : tm (Γ , tt) tt) -> tm Γ tt
 _·_ : (M : tm Γ tt) -> (N : tm Γ tt) -> tm Γ tt

data psub {A} : ctx A -> ctx A -> Set where
 end : psub ⊡ ⊡
 keep : ∀ {Γ Δ} (σ : psub Γ Δ) T -> psub (Γ , T) (Δ , T)
 drop : ∀ {Γ Δ} (σ : psub Γ Δ) T -> psub Γ (Δ , T)

app-psub : ∀ {A} {T : A} {Γ Δ} -> psub Γ Δ -> var Γ T -> var Δ T
app-psub end ()
app-psub (keep σ T) top = top
app-psub (keep σ T) (pop y) = pop (app-psub σ y)
app-psub (drop σ T) x = pop (app-psub σ x)

! : ∀ {A} {Γ : ctx A} -> psub ⊡ Γ
! {A} {⊡} = end
! {A} {Γ , T} = drop ! T

id : ∀ {A} {Γ : ctx A} -> psub Γ Γ
id {A} {⊡} = end
id {A} {Γ , T} = keep id T

record union {A} (Γ1 Γ2 Δ : ctx A) : Set where
 constructor uc
 field
  Δ' : ctx A
  σ1' : psub Γ1 Δ'
  σ2' : psub Γ2 Δ'
  σ' : psub Δ' Δ

_∪₁_ : ∀ {A} {Γ1 Γ2 Δ : ctx A} -> psub Γ1 Δ -> psub Γ2 Δ -> union Γ1 Γ2 Δ
end ∪₁ end = uc ⊡ end end end 
keep σ1 T ∪₁ keep σ2 .T with σ1 ∪₁ σ2
keep σ1 T ∪₁ keep σ2 .T | uc Δ' σ1' σ2' σ' = uc (Δ' , T) (keep σ1' T) (keep σ2' T) (keep σ' T)
keep σ1 T ∪₁ drop σ2 .T with σ1 ∪₁ σ2
keep σ1 T ∪₁ drop σ2 .T | uc Δ' σ1' σ2' σ' = uc (Δ' , T) (keep σ1' T) (drop σ2' T) (keep σ' T)
drop σ1 T ∪₁ keep σ2 .T with σ1 ∪₁ σ2
drop σ1 T ∪₁ keep σ2 .T | uc Δ' σ1' σ2' σ' = uc (Δ' , T) (drop σ1' T) (keep σ2' T) (keep σ' T)
drop σ1 T ∪₁ drop σ2 .T with σ1 ∪₁ σ2
drop σ1 T ∪₁ drop σ2 .T | uc Δ' σ1' σ2' σ' = uc Δ' σ1' σ2' (drop σ' T)

