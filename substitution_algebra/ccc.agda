module ccc where

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
  _∘eval[_,_] : ∀ {C τ σ ρ} -> (S1 : spine σ ρ) -> (S : spine C (τ ⇒ σ)) -> (N : nf C τ) -> spine C ρ

_∘₁_ : ∀ {Γ σ τ} -> spine Γ τ -> spine σ Γ -> spine σ τ
t ∘₁ id = t
t ∘₁ (S ∘πl) = (t ∘₁ S) ∘πl
t ∘₁ (S ∘πr) = (t ∘₁ S) ∘πr
t ∘₁ (S ∘v[ y ]∘ y') = (t ∘₁ S) ∘v[ y ]∘ y'
t ∘₁ (S ∘eval[ N , M ]) = (t ∘₁ S) ∘eval[ N , M ]

data ctx : Set where
 [_]×_ : (C : ctx) -> (τ : type) -> ctx
 _×[_] : (τ : type) -> (C : ctx) -> ctx
 ● : ctx

plug : ctx -> type -> type
plug ([ C ]× τ) τ' = (plug C τ') × τ
plug (τ ×[ C ]) τ' = τ × (plug C τ')
plug ● τ = τ 

plugc : ctx -> ctx -> ctx
plugc ([ C ]× τ) c = [ plugc C c ]× τ
plugc (τ ×[ C ]) c = τ ×[ plugc C c ]
plugc ● c = c

wkns : ∀ C {σ τ} -> spine σ τ -> spine (plug C σ) τ
wkns ([ C ]× τ) t = (wkns C t) ∘πl
wkns (τ ×[ C ]) t = wkns C t ∘πr
wkns ● t = t

wkns2 : ∀ C D {σ τ} -> spine (plug C σ) τ -> spine (plug C (plug D σ)) τ
wkns2 ([ C ]× τ) D t = {!!}
wkns2 (τ ×[ C ]) D t = {!!}
wkns2 ● D t = wkns D t

wkn : ∀ C D {σ τ} -> nf (plug C σ) τ -> nf (plug C (plug D σ)) τ
wkn C D (▹ S) = ▹ (wkns2 C D S)
wkn C D < N , M > = < (wkn C D N) , (wkn C D M) >
wkn C D ! = !
wkn C D {σ} (ƛ {ρ} {τ} N) = ƛ (wkn ([ C ]× τ) D N)

wknl : ∀ {Γ σ τ} -> nf Γ τ -> nf (Γ × σ) τ
wknl t = wkn ● ([ ● ]× _) t

wknr : ∀ {Γ σ τ} -> nf Γ τ -> nf (σ × Γ) τ
wknr t = wkn ● (_ ×[ ● ]) t 

η-exp : ∀ {τ σ} -> spine σ τ -> nf σ τ
η-exp {▹ B} S = ▹ S
η-exp {τ × σ} S = < (η-exp ((id ∘πl) ∘₁ S)) , (η-exp ((id ∘πr) ∘₁ S)) >
η-exp {⊤} S = !
η-exp {τ ⇒ σ} S = ƛ (η-exp (id ∘eval[ S ∘πl , η-exp (id ∘πr) ]))

mutual
 _∘_ : ∀ {Γ σ τ} -> nf Γ τ -> nf σ Γ -> nf σ τ
 (▹ S) ∘ N = S ◇ N
 < M , N > ∘ N' = < (M ∘ N') , (N ∘ N') >
 ! ∘ N = !
 (ƛ N) ∘ N' = ƛ (N ∘ < wknl N' , wknr (η-exp id) >)

 _◇_ : ∀ {Γ τ σ} -> spine σ τ -> nf Γ σ -> nf Γ τ
 id ◇ N  = N
 (S ∘πl) ◇ < N , M > = S ◇ N
 (S ∘πr) ◇ < N , M > = S ◇ M
 (S ∘v[ y ]∘ f) ◇ N = η-exp (S ∘v[ y ]∘ (f ∘ N))
 (S ∘eval[ R , M ]) ◇ N with R ◇ N
 (S ∘eval[ R , M ]) ◇ N | ƛ N' = S ◇ (N' ∘ < (η-exp id) , (M ∘ N) >)

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