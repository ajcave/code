module blah where

postulate
 atype : Set

data type : Set where
 ▹ : atype -> type
 _⇒_ : type -> type -> type
 _×_ : type -> type -> type
 ⊤ : type

postulate
 var : type -> type -> Set

mutual
 -- Could define these by recursion on the types
 data nf (Γ : type) : type -> Set where
  ▹ : ∀ {τ} -> (S : spine Γ (▹ τ)) -> nf Γ (▹ τ)
  <_,_> : ∀ {σ τ} -> (N : nf Γ τ) -> (M : nf Γ σ) -> nf Γ (τ × σ)
  ! : nf Γ ⊤
  ƛ : ∀ {σ τ} -> (N : nf (Γ × τ) σ) -> nf Γ (τ ⇒ σ)
 -- Why not restrict the second to atype?
 data spine : type -> type -> Set where
  id : ∀ {ρ} -> spine ρ ρ
  _∘πl : ∀ {τ σ ρ} -> (S : spine σ ρ) -> spine (σ × τ) ρ
  _∘πr : ∀ {τ σ ρ} -> (S : spine τ ρ) -> spine (σ × τ) ρ
  -- Why here? Why not in nf? 3rd category?
  _∘v[_]∘_ : ∀ {τ σ ρ α} -> (S : spine σ ρ) -> var τ σ -> nf α τ -> spine α ρ
  _∘app_ : ∀ {τ σ ρ} -> (S : spine σ ρ) -> (N : nf ⊤ τ) -> spine (τ ⇒ σ) ρ

_∘₁_ : ∀ {Γ σ τ} -> spine Γ τ -> spine σ Γ -> spine σ τ
t ∘₁ id = t
t ∘₁ (S ∘πl) = (t ∘₁ S) ∘πl
t ∘₁ (S ∘πr) = (t ∘₁ S) ∘πr
t ∘₁ (S ∘v[ y ]∘ y') = (t ∘₁ S) ∘v[ y ]∘ y'
t ∘₁ (S ∘app N) = (t ∘₁ S) ∘app N

ap : ∀ {τ σ ρ} -> spine σ (τ ⇒ ρ) -> nf ⊤ τ -> spine σ ρ
ap id N = id ∘app N
ap (S ∘πl) N = ap {!!} {!!}
ap (S ∘πr) N = {!!}
ap (S ∘v[ y ]∘ y') N = {!!}
ap (S ∘app N) N' = (ap S N') ∘app N

η-exp : ∀ {τ σ} -> spine σ τ -> nf σ τ
η-exp {▹ B} S = ▹ S
η-exp {τ × σ} S = < (η-exp ((id ∘πl) ∘₁ S)) , (η-exp ((id ∘πr) ∘₁ S)) >
η-exp {⊤} S = !
η-exp {τ ⇒ σ} S = ƛ (η-exp {!!})

{- Would my life be easier with linear logic? -}
wkns : ∀ {Γ σ τ} -> spine Γ τ -> spine (Γ × σ) τ
wkns id = id ∘πl
wkns (S ∘πl) = {!!}
wkns (S ∘πr) = {!!}
wkns (S ∘v[ y ]∘ y') = {!!}
wkns (S ∘app N) = {!!}

wkn : ∀ {Γ σ τ} -> nf Γ τ -> nf (Γ × σ) τ
wkn (▹ S) = ▹ {!!}
wkn < N , M > = < (wkn N) , (wkn M) >
wkn ! = !
wkn (ƛ N) = ƛ {!!}

mutual
 _∘_ : ∀ {Γ σ τ} -> nf Γ τ -> nf σ Γ -> nf σ τ
 (▹ S) ∘ N = S ◇ N
 < M , N > ∘ N' = < (M ∘ N') , (N ∘ N') >
 ! ∘ N = !
 (ƛ N) ∘ N' = ƛ (N ∘ < {!!} , {!!} >)

 _◇_ : ∀ {Γ τ σ} -> spine σ τ -> nf Γ σ -> nf Γ τ
 id ◇ N  = N
 (S ∘πl) ◇ < N , M > = S ◇ N
 (S ∘πr) ◇ < N , M > = S ◇ M
 (S ∘v[ y ]∘ f) ◇ N = η-exp (S ∘v[ y ]∘ (f ∘ N))
 (S ∘app M) ◇ N = {!!}

mutual
 data _⟹_ : type -> type -> Set where
  v : ∀ {A B} -> var A B -> A ⟹ B
  <_,_> : ∀ {Γ T S} -> Γ ⟶ T -> Γ ⟶ S -> Γ ⟹ (T × S)
  πl : ∀ {T S} -> (T × S) ⟹ T
  πr : ∀ {T S} -> (T × S) ⟹ S
  ! : ∀ {T} -> T ⟹ ⊤
 data _⟶_ : type -> type -> Set where
  id : ∀ {A} -> A ⟶ A
  _·_ : ∀ {A B C} -> (f : B ⟹ C) -> (fs : A ⟶ B) -> (A ⟶ C)

[_] : ∀ {A B} -> A ⟹ B -> A ⟶ B
[ t ] = t · id

_◆_ : ∀ {A B C} -> (B ⟶ C) -> (A ⟶ B) -> (A ⟶ C)
id ◆ f = f
(g · gs) ◆ f = g · (gs ◆ f) 

ev : ∀ {A B C} -> B ⟶ C -> nf A B -> nf A C
ev id s = s
ev (v y · fs) s = η-exp (id ∘v[ y ]∘ (ev fs s))
ev (< y , y' > · fs) s = < ev y (ev fs s) , ev y' (ev fs s) >
ev (πl · fs) s with ev fs s
... | < N , M > = N
ev (πr · fs) s with ev fs s
... | < N , M > = M
ev (! · fs) s = !

nbe : ∀ {A B} -> A ⟶ B -> nf A B
nbe t = ev t (η-exp id)