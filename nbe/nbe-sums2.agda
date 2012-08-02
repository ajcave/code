{-# OPTIONS --type-in-type #-}
module nbe-sums2 where

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

postulate
 atomic_tp : Set

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp
 _×_ : (T S : tp) -> tp
 _+_ : (T S : tp) -> tp
 ⊥ : tp
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
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
  π₁ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ T
  π₂ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T × S)
  tt : ntm Γ unit
  inl : ∀ {T S} (M : ntm Γ T) -> ntm Γ (T + S)
  inr : ∀ {T S} (M : ntm Γ S) -> ntm Γ (T + S)
  case_of_-_ : ∀ {C T S} (M : rtm Γ (T + S)) (N1 : ntm (Γ , T) C) (N2 : ntm (Γ , S) C) -> ntm Γ C
  abort : ∀ {T} (M : rtm Γ ⊥) -> ntm Γ T


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
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt
 nappSubst σ (inl M) = inl (nappSubst σ M)
 nappSubst σ (inr M) = inr (nappSubst σ M)
 nappSubst σ (case M of N1 - N2) = case (rappSubst σ M) of (nappSubst (ext σ) N1) - (nappSubst (ext σ) N2)
 nappSubst σ (abort R) = abort (rappSubst σ R)

-- BAD: Currently using Set : Set here...
-- How to fix this? Impredicative set? Lift this definition to Set₁?

-- Γ ◃ P means P is a set of contexts, such that no matter which path we take, we must eventually hit one of the Ps
data _◃_ (Γ : ctx) : (P : ctx -> Set) -> Set where
 base : Γ ◃ (vsubst Γ)
 step : ∀ {A B P Q} -> rtm Γ (A + B) -> (Γ , A) ◃ P -> (Γ , B) ◃ Q -> Γ ◃ (λ Δ -> P Δ ⊎ Q Δ)
 step2 : ∀ {P} -> rtm Γ ⊥ -> Γ ◃ P
 monotone : ∀ {Γ' P} -> Γ' ◃ P -> vsubst Γ' Γ -> Γ ◃ P
 union : ∀ {P Q} -> Γ ◃ P -> (∀ Δ -> P Δ -> Δ ◃ Q) -> Γ ◃ Q

{-
blah : ∀ {Γ P Δ} -> Γ ◃ P -> P Δ -> vsubst Γ Δ
blah base p = p
blah (step y y' y0) (inl y1) = λ x → blah y' y1 (s x)
blah (step y y' y0) (inr y1) = λ x → blah y0 y1 (s x)
blah (step2 y) p = {!!}
blah (monotone y y') p = {!!}
blah {Γ} {Q} {Δ} (union {P} y y') p with blah1 y
... | q1 , q2 = (blah (y' q1 q2) p) ∘ (blah y q2) -}

blah : ∀ {Γ P Q} -> Γ ◃ P -> (∀ Δ -> P Δ -> Q Δ) -> Γ ◃ Q
blah base f = {!!}
blah (step y y' y0) f = {!!}
blah (step2 y) f = step2 y
blah (monotone y y') f = monotone (blah y f) y'
blah (union y y') f = union y (λ Δ x → blah (y' Δ x) f)

sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = ntm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S 
sem Γ (T × S) = sem Γ T * sem Γ S
sem Γ unit = Unit
sem Γ (T + S) = Σ (λ P -> (Γ ◃ P) * (∀ Δ -> P Δ -> sem Δ T ⊎ sem Δ S))
sem Γ ⊥ = Γ ◃ (λ _ -> False)

paste : ∀ {Γ P T} -> Γ ◃ P -> (∀ Δ -> P Δ -> ntm Δ T) -> ntm Γ T
paste base f = f _ (λ x → x)
paste (step y y' y0) f = case y of (paste y' (λ Δ x → f _ (inl x))) - paste y0 (λ Δ x → f _ (inr x))
paste (step2 r) f = abort r
paste (monotone t σ) f = nappSubst σ (paste t f)
paste (union p q) f = paste p (λ Δ x → paste (q _ x) f)

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = nappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s
appSubst (T × S) σ M = (appSubst T σ (_*_.fst M)) , (appSubst S σ (_*_.snd M))
appSubst unit σ M = tt
appSubst (T + S) σ M = (Σ.fst M) , (monotone (_*_.fst (Σ.snd M)) σ , (_*_.snd (Σ.snd M)))
appSubst ⊥ σ M = monotone M σ


paste2 : ∀ {T Γ P} -> Γ ◃ P -> (∀ Δ -> P Δ -> sem Δ T) -> sem Γ T
paste2 {atom A} t p = paste t p
paste2 {T ⇝ S} t p = λ Δ x x' → paste2 {!!} (λ Δ' x0 → p _ x0 _ {!!} {!!})
paste2 {T × S} t p = (paste2 t (λ Δ x → _*_.fst (p _ x))) , (paste2 t (λ Δ x → _*_.snd (p _ x)))
paste2 {T + S} {Γ} {P} t p = (λ Δ → Σ (λ Δ' → Σ (λ (x : P Δ') → Σ.fst (p Δ' x) Δ))) , (union t (λ Δ x → {!!}) , λ Δ x → _*_.snd (Σ.snd (p (Σ.fst x) (Σ.fst (Σ.snd x)))) Δ (Σ.snd (Σ.snd x)))
paste2 {⊥} t p = union t p
paste2 {unit} t p = tt

id : ∀ {Γ} -> vsubst Γ Γ
id x = x


mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = neut N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)
 reflect {T × S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt
 reflect {T + S} {Γ} N = (λ Δ → vsubst (Γ , T) Δ ⊎ vsubst (Γ , S) Δ) , ((step N base base) , f)
  where f : ∀ Δ -> (x : vsubst (Γ , T) Δ ⊎ vsubst (Γ , S) Δ) -> sem Δ T ⊎ sem Δ S
        f Δ (inl y) = inl (reflect (v (y z)))
        f Δ (inr y) = inr (reflect (v (y z)))
 reflect {⊥} M = step2 M

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z))))
 reify {T × S} M = < reify (_*_.fst M) , reify (_*_.snd M) >
 reify {unit} _ = tt
 reify {T + S} M = paste (_*_.fst (Σ.snd M)) (λ Δ x -> f Δ x (_*_.snd (Σ.snd M) Δ x))
  where f : ∀ Δ -> Σ.fst M Δ -> sem Δ T ⊎ sem Δ S -> ntm Δ (T + S)
        f Δ x (inl y) = inl (reify y)
        f Δ x (inr y) = inr (reify y)
 reify {⊥} M = paste M (λ Δ ())

{-
paste3 : ∀ {Γ P T} -> Γ ◃ P -> (∀ Δ -> P Δ -> sem Δ T) -> sem Γ T
paste3 base p = p _ (λ x → x)
paste3 (step y y' y0) p with reflect y
... | Q , (q1 , q2) = {!!}
paste3 (step2 y) p = {!!}
paste3 (monotone y y') p = {!!}
paste3 (union y y') p = {!!} -}

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
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
 abort : ∀ {T} (M : tm Γ ⊥) -> tm Γ T

-- Traditional nbe
eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
eval θ (M · N) = eval θ M _ id (eval θ N)
eval θ (ƛ M) = λ _ σ s -> eval (extend (λ x → appSubst _ σ (θ x)) s) M
eval θ (π₁ M) = _*_.fst (eval θ M)
eval θ (π₂ N) = _*_.snd (eval θ N)
eval θ < M , N > = eval θ M , eval θ N
eval θ tt = tt
eval θ (inl M) = _ , (base , λ Δ σ → inl (eval (λ x → appSubst _ σ (θ x)) M))
eval θ (inr M) = _ , (base , λ Δ σ → inr (eval (λ x → appSubst _ σ (θ x)) M))
eval {Γ} {Δ} θ (case_of_-_ {T} {S} {C} M N1 N2) with eval θ M
eval {Γ} {Δ} θ (case_of_-_ {T} {S} {C} M N1 N2) | R = paste2 (_*_.fst (Σ.snd R)) (λ Δ x → f _ x (_*_.snd (Σ.snd R) Δ x))
 where f : ∀ Δ' -> Σ.fst R Δ' -> sem Δ' T ⊎ sem Δ' S -> sem Δ' C
       f Δ' x (inl y) = eval (extend (λ x' → appSubst _ {!!} (θ x')) y) N1
       f Δ' x (inr y) = eval (extend (λ x' → appSubst _ {!!} (θ x')) y) N2
eval θ (abort R) with eval θ R
eval _ (abort R) | M = paste2 M (λ Δ ())

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval (λ x → reflect (v x)) M) 
