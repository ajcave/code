module ccc3 where

postulate
 atype : Set

data type : Set where
 ▹ : (α : atype) -> type
 _⇒_ : (τ σ : type) -> type
 _×_ : (τ σ : type) -> type
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

record Unit : Set where
 constructor !

record _⊗_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

sem : ∀ (Γ τ : type) -> Set
sem Γ (▹ τ) = spine Γ (▹ τ)
sem Γ (τ ⇒ σ) = {Δ : _} (s : spine Δ Γ) → sem Δ τ → sem Δ σ
sem Γ (τ × σ) = sem Γ τ ⊗ sem Γ σ
sem Γ ⊤ = Unit 

_∘₁_ : ∀ {Γ σ τ} -> spine Γ τ -> spine σ Γ -> spine σ τ
t ∘₁ id = t
t ∘₁ (S ∘πl) = (t ∘₁ S) ∘πl
t ∘₁ (S ∘πr) = (t ∘₁ S) ∘πr
t ∘₁ (S ∘v[ y ]∘ y') = (t ∘₁ S) ∘v[ y ]∘ y'
t ∘₁ (S ∘eval[ N , M ]) = (t ∘₁ S) ∘eval[ N , M ]

mutual
 reflect : ∀ {τ σ} -> spine σ τ -> sem σ τ
 reflect {▹ α} s = s
 reflect {τ ⇒ σ} s = λ ρ t → reflect {σ} (id ∘eval[ (s ∘₁ ρ) , reify {τ} t ])
 reflect {τ × σ} s = (reflect {τ} ((id ∘πl) ∘₁ s)) , (reflect {σ} ((id ∘πr) ∘₁ s))
 reflect {⊤} s = !

 reify : ∀ {τ σ} -> sem σ τ -> nf σ τ
 reify {▹ α} s = ▹ s
 reify {τ ⇒ σ} s = ƛ (reify {σ} (s (id ∘πl) (reflect {τ} (id ∘πr))))
 reify {τ × σ} (s1 , s2) = < (reify {τ} s1) , reify {σ} s2 >
 reify {⊤} s = !

mutual
 data _⟹_ : type -> type -> Set where
  v : ∀ {A B} -> var A B -> A ⟹ B
  <_,_> : ∀ {Γ T S} -> Γ ⟶ T -> Γ ⟶ S -> Γ ⟹ (T × S)
  πl : ∀ {T S} -> (T × S) ⟹ T
  πr : ∀ {T S} -> (T × S) ⟹ S
  ! : ∀ {T} -> T ⟹ ⊤
  ƛ : ∀ {Γ T S} -> (Γ × T) ⟶ S -> Γ ⟹ (T ⇒ S)
  eval : ∀ {T S} -> ((T ⇒ S) × T) ⟹ S
 data _⟶_ : type -> type -> Set where
  id : ∀ {A} -> A ⟶ A
  _·_ : ∀ {A B C} -> (f : B ⟹ C) -> (fs : A ⟶ B) -> (A ⟶ C)

appSubst : ∀ {C A B} -> sem B C -> spine A B -> sem A C
appSubst {▹ α} s t = s ∘₁ t
appSubst {τ ⇒ σ} s t = λ s' x → s (t ∘₁ s') x
appSubst {τ × σ} (s1 , s2) t = (appSubst s1 t) , (appSubst s2 t)
appSubst {⊤} s t = !

{- Can sell this as "NbE for explicit substitutions" -}
ev : ∀ {A B C} -> B ⟶ C -> sem A B -> sem A C
ev id s = s
ev (v y · fs) s = reflect (id ∘v[ y ]∘ reify (ev fs s))
ev (< y , y' > · fs) s = (ev y (ev fs s)) , (ev y' (ev fs s))
ev (πl · fs) s = _⊗_.fst (ev fs s)
ev (πr · fs) s = _⊗_.snd (ev fs s)
ev (! · fs) s = !
ev (ƛ y · fs) s = λ s' x → ev y ((ev fs (appSubst s s')) , x)
ev (eval · fs) s with ev fs s
... | f , m = f id m

nbe : ∀ {A B} -> A ⟶ B -> nf A B
nbe t = reify (ev t (reflect id))