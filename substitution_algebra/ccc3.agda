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
  ▹ : ∀ {τ} -> (S : neut Γ (▹ τ)) -> nf Γ (▹ τ)
  <_,_> : ∀ {σ τ} -> (N : nf Γ τ) -> (M : nf Γ σ) -> nf Γ (τ × σ)
  ! : nf Γ ⊤
  ƛ : ∀ {σ τ} -> (N : nf (Γ × τ) σ) -> nf Γ (τ ⇒ σ)
 -- Why not restrict the second to atype?
 data neut : type -> type -> Set where
  id : ∀ {ρ} -> neut ρ ρ
  πl : ∀ {τ σ ρ} -> (R : neut ρ (σ × τ)) -> neut ρ σ
  πr : ∀ {τ σ ρ} -> (R : neut ρ (σ × τ)) -> neut ρ τ
  v[_] : ∀ {τ ρ σ} -> var τ σ -> nf ρ τ -> neut ρ σ
  app : ∀ {C τ σ} -> (R : neut C (τ ⇒ σ)) -> (N : nf C τ) -> neut C σ

record Unit : Set where
 constructor !

record _⊗_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

data ctx : Set where
 [_]×_ : (C : ctx) -> (τ : type) -> ctx
 _×[_] : (τ : type) -> (C : ctx) -> ctx 
 ● : ctx

plug : ctx -> type -> type
plug ([ C ]× τ) τ' = (plug C τ') × τ
plug (τ ×[ C ]) τ' = τ × (plug C τ')
plug ● τ = τ

data list (A : Set) : Set where
 ⊡ : list A
 _,_ : list A -> A -> list A

append : type -> list type -> type
append σ ⊡ = σ
append σ (y , y') = y' × (append σ y)

sem : ∀ (Γ τ : type) -> Set
sem Γ (▹ τ) = neut Γ (▹ τ)
sem Γ (τ ⇒ σ) = (C : _) → sem (append Γ C) τ → sem (append Γ C) σ
sem Γ (τ × σ) = sem Γ τ ⊗ sem Γ σ
sem Γ ⊤ = Unit 

mutual
 wkn : ∀ C {τ σ} -> nf σ τ -> nf (append σ C) τ
 wkn C (▹ S) = ▹ (nwkn C S)
 wkn C < N , M > = < (wkn C N) , (wkn C M) >
 wkn C ! = !
 wkn C (ƛ N) = ƛ {!!}

 nwkn : ∀ C {τ σ} -> neut σ τ -> neut (append σ C) τ
 nwkn C id = {!!}
 nwkn C (πl R) = πl (nwkn C R)
 nwkn C (πr R) = πr (nwkn C R)
 nwkn C (v[_] y y') = v[ y ] (wkn C y')
 nwkn C (app R N) = app (nwkn C R) (wkn C N)

mutual
 reflect : ∀ {τ σ} -> neut σ τ -> sem σ τ
 reflect {▹ α} s = s
 reflect {τ ⇒ σ} s = λ ρ t → reflect {σ} (app {!!} (reify {τ} t)) --(nwkn ρ ● s) (reify {τ} t))
 reflect {τ × σ} s = reflect {τ} (πl s) , (reflect {σ} (πr s))
 reflect {⊤} s = !

 reify : ∀ {τ σ} -> sem σ τ -> nf σ τ
 reify {▹ α} s = ▹ s
 reify {τ ⇒ σ} s = ƛ (reify {σ} {!!}) -- (s ([ ● ]× τ) (reflect {τ} (πr id))))
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


{- Can sell this as "NbE for explicit substitutions" -}
ev : ∀ {A B C} -> B ⟶ C -> sem A B -> sem A C
ev id s = s
ev (v y · fs) s = reflect (v[ y ] (reify (ev fs s)))
ev (< y , y' > · fs) s = (ev y (ev fs s)) , (ev y' (ev fs s))
ev (πl · fs) s = _⊗_.fst (ev fs s)
ev (πr · fs) s = _⊗_.snd (ev fs s)
ev (! · fs) s = !
ev (ƛ y · fs) s = λ s' x → ev y {!!} --((ev fs (swkn s' s)) , x)
ev (eval · fs) s with ev fs s
... | f , m = f ⊡ m

nbe : ∀ {A B} -> A ⟶ B -> nf A B
nbe t = reify (ev t (reflect id))