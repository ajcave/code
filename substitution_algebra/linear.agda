module linear where

postulate
 atype : Set

data type : Set where
 ▹ : (α : atype) -> type
 _⇒_ : (τ σ : type) -> type
 _⊗_ : (τ σ : type) -> type
 ⊤ : type

postulate
 var : type -> type -> Set

mutual
 -- Could define these by recursion on the types
 data nf : type -> type -> Set where
  ▹ : ∀ {Γ τ} -> (S : neut Γ (▹ τ)) -> nf Γ (▹ τ)
  <_,_> : ∀ {σ Γ Δ τ} -> (N : nf Γ τ) -> (M : nf Δ σ) -> nf (Γ ⊗ Δ) (τ ⊗ σ)
  ! : nf ⊤ ⊤
  ƛ : ∀ {Γ σ τ} -> (N : nf (Γ ⊗ τ) σ) -> nf Γ (τ ⇒ σ)
 -- Why not restrict the second to atype?
 data neut : type -> type -> Set where
  id : ∀ {ρ} -> neut ρ ρ
--  πl : ∀ {τ σ ρ} -> (R : neut ρ (σ × τ)) -> neut ρ σ
--  πr : ∀ {τ σ ρ} -> (R : neut ρ (σ × τ)) -> neut ρ τ
  v[_] : ∀ {τ ρ σ} -> var τ σ -> nf ρ τ -> neut ρ σ
  app : ∀ {C τ σ} -> (R : neut C (τ ⇒ σ)) -> (N : nf C τ) -> neut C σ

record Unit : Set where
 constructor !

record _×_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

{-
data ctx : Set where
 [_]×_ : (C : ctx) -> (τ : type) -> ctx
 _×[_] : (τ : type) -> (C : ctx) -> ctx 
 ● : ctx

plug : ctx -> type -> type
plug ([ C ]× τ) τ' = (plug C τ') × τ
plug (τ ×[ C ]) τ' = τ × (plug C τ')
plug ● τ = τ -}

data Void : Set where

sem : ∀ (Γ τ : type) -> Set
sem Γ (▹ τ) = neut Γ (▹ τ)
sem Γ (τ ⇒ σ) = sem Γ τ → sem Γ σ
sem (Γ1 ⊗ Γ2) (τ ⊗ σ) = sem Γ1 τ × sem Γ2 σ
sem ⊤ ⊤ = Unit
sem _ _ = Void

{-mutual
 _∘₁_ : ∀ {Γ σ τ} -> neut Γ τ -> neut σ Γ -> neut σ τ
 id ∘₁ s = s
 πl R ∘₁ s = πl (R ∘₁ s)
 πr R ∘₁ s = πr (R ∘₁ s)
 v[ y ] y' ∘₁ s = v[ y ] (y' ∘₂ s)
 app R N ∘₁ s = app (R ∘₁ s) (N ∘₂ s)

 _∘₂_ : ∀ {Γ σ τ} -> nf Γ τ -> neut σ Γ -> nf σ τ
 ▹ S ∘₂ s = ▹f (S ∘₁ s)
 < N , M > ∘₂ s = < (N ∘₂ s) , (M ∘₂ s) >
 ! ∘₂ s = !
 ƛ N ∘₂ s = ƛ ({!!} ∘₂ {!!}) -}

{-
mutual
 nwkn : ∀ C {τ σ} -> neut τ σ -> neut (plug C τ) σ
 nwkn C id = foo C
 nwkn C (πl R) = πl (nwkn C R)
 nwkn C (πr R) = πr (nwkn C R)
 nwkn C (v[ y ] y') = v[ y ] {!!}
 nwkn C (app R N) = app (nwkn C R) {!!}

 wkn : ∀ C {τ σ} -> nf τ σ -> nf (plug C τ) σ
 wkn C (▹ S) = ▹ (nwkn C S)
 wkn C < N , M > = < (wkn C N) , (wkn C M) >
 wkn C ! = !
 wkn C {τ} (ƛ {ρ} {σ} N) = ƛ {!!} -}

mutual
 reflect : ∀ {τ σ} -> neut σ τ -> sem σ τ
 reflect {▹ α} s = s
 reflect {τ ⇒ σ} s = λ t → reflect {σ} (app {! (s ∘₁ ρ) !} (reify {τ} t))
 reflect {τ ⊗ σ} {Γ1 ⊗ Γ2} s = {!!} , {!!} --reflect {τ} (πl s) , (reflect {σ} (πr s))
 reflect {τ ⊗ σ} {_} s = {!!}
 reflect {⊤} {⊤} s = !
 reflect {⊤} {t} s = {!!}

 reify : ∀ {τ σ} -> sem σ τ -> nf σ τ
 reify {▹ α} s = ▹ s
 reify {τ ⇒ σ} s = ƛ (reify {σ} {!!}) --ƛ (reify {σ} (s {!!} (reflect {τ} (πr id))))
 reify {τ ⊗ σ} {Γ1 ⊗ Γ2} (s1 , s2) = {!!} --< (reify {τ} s1) , reify {σ} s2 >
 reify {_ ⊗ _} {▹ _} ()
 reify {_ ⊗ _} {_ ⇒ _} ()
 reify {_ ⊗ _} {⊤} ()
 reify {⊤} {⊤} s = !
 reify {⊤} {▹ _} ()
 reify {⊤} {_ ⇒ _} ()
 reify {⊤} {_ ⊗ _} ()
 
mutual
 data _⟹_ : type -> type -> Set where
  v : ∀ {A B} -> var A B -> A ⟹ B
  <_,_> : ∀ {Γ T S} -> Γ ⟶ T -> Γ ⟶ S -> Γ ⟹ (T ⊗ S)
  πl : ∀ {T S} -> (T ⊗ S) ⟹ T
  πr : ∀ {T S} -> (T ⊗ S) ⟹ S
  ! : ∀ {T} -> T ⟹ ⊤
  ƛ : ∀ {Γ T S} -> (Γ ⊗ T) ⟶ S -> Γ ⟹ (T ⇒ S)
  eval : ∀ {T S} -> ((T ⇒ S) ⊗ T) ⟹ S
 data _⟶_ : type -> type -> Set where
  id : ∀ {A} -> A ⟶ A
  _·_ : ∀ {A B C} -> (f : B ⟹ C) -> (fs : A ⟶ B) -> (A ⟶ C)

appSubst : ∀ {C A B} -> sem B C -> neut A B -> sem A C
appSubst {▹ α} s t = {! s ∘₁ t !}
appSubst {τ ⇒ σ} s t = {!!} -- λ x → s x
appSubst {τ ⊗ σ} {B = Γ1 ⊗ Γ2} (s1 , s2) t = {!!} --(appSubst s1 t) , (appSubst s2 t)
appSubst {⊤} s t = {!!} --!
appSubst s t = {!!}

{- Can sell this as "NbE for explicit substitutions" -}
ev : ∀ {A B C} -> B ⟶ C -> sem A B -> sem A C
ev id s = s
ev (v y · fs) s = reflect (v[ y ] (reify (ev fs s)))
ev (< y , y' > · fs) s = {!!} --(ev y (ev fs s)) , (ev y' (ev fs s))
ev (πl · fs) s = {!!} --_×_.fst (ev fs s)
ev (πr · fs) s = {!!} -- _×_.snd (ev fs s)
ev (! · fs) s = {!!} --!
ev (ƛ y · fs) s = {!!} -- λ s' x → ev y ((ev fs {!!}) , x)
ev (eval · fs) s with ev fs s
... | w = {!!}

nbe : ∀ {A B} -> A ⟶ B -> nf A B
nbe t = reify (ev t (reflect id))