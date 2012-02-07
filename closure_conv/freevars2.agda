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

-- Could separate this out into 4 functions
_∪_ : ∀ {A} {Γ1 Γ2 Δ : ctx A} -> psub Γ1 Δ -> psub Γ2 Δ -> union Γ1 Γ2 Δ
end ∪ end = uc ⊡ end end end
keep σ1 T ∪ keep σ2 .T with σ1 ∪ σ2
keep σ1 T ∪ keep σ2 .T | uc Δ' σ1' σ2' σ' = uc (Δ' , T) (keep σ1' T) (keep σ2' T) (keep σ' T)
keep σ1 T ∪ drop σ2 .T with σ1 ∪ σ2
keep σ1 T ∪ drop σ2 .T | uc Δ' σ1' σ2' σ' = uc (Δ' , T) (keep σ1' T) (drop σ2' T) (keep σ' T)
drop σ1 T ∪ keep σ2 .T with σ1 ∪ σ2
drop σ1 T ∪ keep σ2 .T | uc Δ' σ1' σ2' σ' = uc (Δ' , T) (drop σ1' T) (keep σ2' T) (keep σ' T)
drop σ1 T ∪ drop σ2 .T with σ1 ∪ σ2
drop σ1 T ∪ drop σ2 .T | uc Δ' σ1' σ2' σ' = uc Δ' σ1' σ2' (drop σ' T)

rem : ∀ {A T} {Γ Δ : ctx A} -> psub Γ (Δ , T) -> Σ (λ Γ' -> (psub Γ' Γ) * ((psub Γ (Γ' , T)) * (psub Γ' Δ)))
rem {A} {T} {Γ , .T} (keep σ .T) = Γ , (drop id T , (id , σ))
rem {A} {T} {Γ}      (drop σ .T) = Γ , (id , (drop id T , σ))
-- I think this is canonical...

_[_] : ∀ {Γ Δ T} -> tm Γ T -> psub Γ Δ -> tm Δ T
▹ x [ σ ] = ▹ (app-psub σ x)
ƛ M [ σ ] = ƛ (M [ keep σ tt ])
(M · N) [ σ ] = (M [ σ ]) · (N [ σ ])

singleton : ∀ {A T} {Γ : ctx A} -> var Γ T -> psub (⊡ , T) Γ
singleton top = keep ! _
singleton (pop y) = drop (singleton y) _

fv : ∀ {Δ T} -> tm Δ T -> Σ (λ Γ -> (psub Γ Δ) * (tm Γ T))
fv (▹ x) = (⊡ , _) , (singleton x , ▹ top)
fv (ƛ M) with fv M
fv (ƛ M) | Γ , (σ , M') with rem σ
fv (ƛ M) | Γ , (σ , M') | Γ' , (_ , (σ' , σ'')) = Γ' , (σ'' , (ƛ (M' [ σ' ])))
fv (M · N) with fv M | fv N
fv (M · N) | Γ1 , (σ1 , M') | Γ2 , (σ2 , N') with σ1 ∪ σ2
fv (M · N) | Γ1 , (σ1 , M') | Γ2 , (σ2 , N') | uc Δ' σ1' σ2' σ = Δ' , (σ , ((M' [ σ1' ]) · (N' [ σ2' ])))
-- Prove universality in that if there is another solution, it factors into this one?