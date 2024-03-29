{-# OPTIONS --type-in-type #-}
module nbe-sums-pnf-alt where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

data _⊎_ (A B : Set) : Set where
 inl : A -> A ⊎ B
 inr : B -> A ⊎ B

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

data False : Set where

record Unit : Set where
 constructor tt

data tp : Set where
 _⇝_ : (T : tp) -> (S : tp) -> tp
 _×_ : (T S : tp) -> tp
 _+_ : (T S : tp) -> tp
 unit : tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

vsubst : ctx -> ctx -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U



mutual 
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> pntm Γ T -> rtm Γ S
  π₁ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ T
  π₂ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ S
 data pntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> pntm (Γ , T) S -> pntm Γ (T ⇝ S)
  <_,_> : ∀ {T S} -> (M : pntm Γ T) -> (N : pntm Γ S) -> pntm Γ (T × S)
  tt : pntm Γ unit
  embed : ∀ {T S} -> sum Γ (λ Γ' -> pntm Γ' T) (λ Γ' -> pntm Γ' S) -> pntm Γ (T + S)

 data sum Γ (F G : ctx -> Set) : Set where
  inl : F Γ -> sum Γ F G
  inr : G Γ -> sum Γ F G
  case : ∀ {A B} (s' : rtm Γ (A + B)) -> sum (Γ , A) F G -> sum (Γ , B) F G -> sum Γ F G

sum-map : ∀ {Γ} {F G} {F' G'} -> (∀ {Δ} -> F Δ -> F' Δ) -> (∀ {Δ} -> G Δ -> G' Δ) -> sum Γ F G -> sum Γ F' G'
sum-map f g (inl x) = inl (f x)
sum-map f g (inr x) = inr (g x)
sum-map f g (case s' x x₁) = case s' (sum-map f g x) (sum-map f g x₁)

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (σ y)
 rappSubst σ (R · N) = rappSubst σ R · pnappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 pnappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> pntm Δ S -> pntm Γ S 
 pnappSubst σ (ƛ M) = ƛ (pnappSubst (ext σ) M)
 pnappSubst σ < M , N > = < pnappSubst σ M , pnappSubst σ N >
 pnappSubst σ tt = tt
 pnappSubst σ (embed M) = embed (sumSubst σ M)

 sumSubst : ∀ {Γ Δ T S} -> vsubst Δ Γ -> sum Δ (λ Γ' → pntm Γ' T) (λ Γ' → pntm Γ' S) -> sum Γ (λ Γ' → pntm Γ' T) (λ Γ' → pntm Γ' S)
 sumSubst σ (inl x) = inl (pnappSubst σ x)
 sumSubst σ (inr x) = inr (pnappSubst σ x)
 sumSubst σ (case s' x x₁) = case (rappSubst σ s') (sumSubst (ext σ) x) (sumSubst (ext σ) x₁)

{-
 pnappSubst σ (inl M) = inl (pnappSubst σ M)
 pnappSubst σ (inr M) = inr (pnappSubst σ M)-}

-- nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
-- nappSubst σ (case M of N1 - N2) = case (rappSubst σ M) of (nappSubst (ext σ) N1) - (nappSubst (ext σ) N2)
-- nappSubst σ (pure M) = pure (pnappSubst σ M)

sem : (T : tp) -> (Γ : ctx) -> Set
sem (T ⇝ S) Γ = ∀ Δ -> vsubst Γ Δ -> sem T Δ → sem S Δ 
sem (T × S) Γ = sem T Γ * sem S Γ
sem unit Γ = Unit
sem (T + S) Γ = sum Γ (sem T) (sem S)


appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem S Δ -> sem S Γ
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s
appSubst (T × S) σ M = (appSubst T σ (_*_.fst M)) , (appSubst S σ (_*_.snd M))
appSubst unit σ M = tt
appSubst (T + S) σ (inl x) = inl (appSubst T σ x)
appSubst (T + S) σ (inr x) = inr (appSubst S σ x)
appSubst (T + S) σ (case s' M M₁) = case (rappSubst σ s') (appSubst (T + S) (ext σ) M) (appSubst (T + S) (ext σ) M₁)

-- Case analysis is pasting
isSheaf : ∀ {Γ} T {A B} (s : rtm Γ (A + B)) (f0 : sem T (Γ , A)) (f1 : sem T (Γ , B)) -> sem T Γ
isSheaf (T ⇝ T₁) s' f0 f1 = λ Δ w x → isSheaf T₁ (rappSubst w s') (f0 _ (ext w) (appSubst T wkn x)) (f1 _ (ext w) (appSubst T wkn x))
isSheaf (T × T₁) s' f0 f1 = isSheaf T s' (_*_.fst f0) (_*_.fst f1) , isSheaf T₁ s' (_*_.snd f0) (_*_.snd f1)
isSheaf (T + T₁) s' f0 f1 = case s' f0 f1
isSheaf unit s' f0 f1 = tt
-- In terms of rewriting... Pushing/pulling case analysis through?
-- Think of using a syntactic model where we have weak head normalization (i.e. evaluation). Hence "Normalization by EVALUATION"


id : ∀ {Γ} -> vsubst Γ Γ
id x = x

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem T Γ
 reflect {T ⇝ S} {Γ} N = λ Δ w s → reflect (rappSubst w N · (reify s))
 reflect {T × S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt
 reflect {T + S} N = case N (inl (reflect (v z))) (inr (reflect (v z)))

 reify : ∀ {T Γ} -> sem T Γ -> pntm Γ T
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z))))
 reify {T × S} M = < (reify (_*_.fst M)) , (reify (_*_.snd M)) >
 reify {unit} _ = tt
 reify {T + S} M = embed (sum-map reify reify M)

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem T Δ

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem T Δ -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 π₁ : ∀ {T S} -> tm Γ (T × S) -> tm Γ T
 π₂ : ∀ {T S} -> tm Γ (T × S) -> tm Γ S
 <_,_> : ∀ {T S} -> tm Γ T -> tm Γ S -> tm Γ (T × S)
 tt : tm Γ unit
 inl : ∀ {T S} (M : tm Γ T) -> tm Γ (T + S)
 inr : ∀ {T S} (M : tm Γ S) -> tm Γ (T + S)
 case_of_-_ : ∀ {T S C} (M : tm Γ (T + S)) (N1 : tm (Γ , T) C) (N2 : tm (Γ , S) C) -> tm Γ C

arr : ∀ Γ T -> Set
arr Γ T = ∀ {Δ} -> subst Γ Δ -> sem T Δ
                                                                   --- This is unrolling arr (Γ , (A + B)) T (and applying some isomorphisms)
case' : ∀ {Γ} {T} {A B} (f0 : arr (Γ , A) T) (f1 : arr (Γ , B) T) -> ∀ {Δ} -> subst Γ Δ -> sem (A + B) Δ -> sem T Δ
case' f0 f1 θ (inl x) = f0 (extend θ x)
case' f0 f1 θ (inr x) = f1 (extend θ x)
case' f0 f1 θ (case s' r r₁) = isSheaf _ s' (case' f0 f1 (λ x → appSubst _ wkn (θ x)) r) (case' f0 f1 (λ x → appSubst _ wkn (θ x)) r₁)

-- Traditional nbe
eval : ∀ {Γ T} -> tm Γ T -> arr Γ T
eval (v y) θ = θ y
eval (M · N) θ = eval M θ _ id (eval N θ)
eval (ƛ M) θ = λ _ σ s -> eval M (extend (λ x → appSubst _ σ (θ x)) s)
eval (π₁ M) θ = _*_.fst (eval M θ)
eval (π₂ N) θ = _*_.snd (eval N θ)
eval < M , N > θ = eval M θ , eval N θ
eval tt θ = tt
eval (inl M) θ = inl (eval M θ)
eval (inr M) θ = inr (eval M θ)
eval (case M of N1 - N2) θ = case' (eval N1) (eval N2) θ (eval M θ)

nbe : ∀ {Γ T} -> tm Γ T -> pntm Γ T
nbe M = reify (eval M (λ x → reflect (v x)))

bool = unit + unit

t1 : tm ⊡ ((bool ⇝ bool) ⇝ (bool ⇝ bool))
t1 = ƛ (ƛ ((v (s z)) · ((v (s z)) · ((v (s z)) · (v z)))))

t2 : tm ⊡ ((bool ⇝ bool) ⇝ (bool ⇝ bool))
t2 = ƛ (v z)

nt1 = nbe t1
nt2 = nbe t2

-- Now the problem is to implement a conversion test on these normal forms...
-- Or what about trying to follow the path of the LICS 2001 paper to make these normal forms unique?
-- Just add redundancy freeness and the variable condition?
-- Actually look at nt1 and nt2. These are difficult to identity as the same...