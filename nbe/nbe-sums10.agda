module nbe-sums10 where

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
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> pntm Γ (T ⇝ S)
  <_,_> : ∀ {T S} -> (M : pntm Γ T) -> (N : pntm Γ S) -> pntm Γ (T × S)
  tt : pntm Γ unit
  inl : ∀ {T S} (M : pntm Γ T) -> pntm Γ (T + S)
  inr : ∀ {T S} (M : pntm Γ S) -> pntm Γ (T + S)
 data ntm (Γ : ctx) : (T : tp) -> Set where
  case_of_-_ : ∀ {C T S} (M : rtm Γ (T + S)) (N1 : ntm (Γ , T) C) (N2 : ntm (Γ , S) C) -> ntm Γ C
  pure : ∀ {T} -> pntm Γ T -> ntm Γ T

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
 pnappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 pnappSubst σ < M , N > = < pnappSubst σ M , pnappSubst σ N >
 pnappSubst σ tt = tt
 pnappSubst σ (inl M) = inl (pnappSubst σ M)
 pnappSubst σ (inr M) = inr (pnappSubst σ M)

 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (case M of N1 - N2) = case (rappSubst σ M) of (nappSubst (ext σ) N1) - (nappSubst (ext σ) N2)
 nappSubst σ (pure M) = pure (pnappSubst σ M)

data sum Γ (F G : ctx -> Set) : Set where
 inl : F Γ -> sum Γ F G
 inr : G Γ -> sum Γ F G
 case : ∀ {A B} (s' : rtm Γ (A + B)) -> sum (Γ , A) F G -> sum (Γ , B) F G -> sum Γ F G
                                      -- This is the sheafification of F + G (well, technically it needs to be quotiented or given a more unique representation)
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


id : ∀ {Γ} -> vsubst Γ Γ
id x = x

pair1 : ∀ {Γ T S} -> ntm Γ T -> pntm Γ S -> ntm Γ (T × S)
pair1 (case M of N - N₁) P = case M of pair1 N (pnappSubst wkn P) - pair1 N₁ (pnappSubst wkn P)
pair1 (pure x) P = pure < x , P >

pair : ∀ {Γ T S} -> ntm Γ T -> ntm Γ S -> ntm Γ (T × S)
pair P (case M of N - N₁) = case M of pair (nappSubst wkn P) N - pair (nappSubst wkn P) N₁
pair P (pure x) = pair1 P x 
-- This is a source of commuting problems right here! We arbitrarily picked an order!

pinl : ∀ {Γ T S} -> ntm Γ T -> ntm Γ (T + S)
pinl (case M of N - N₁) = case M of pinl N - pinl N₁
pinl (pure x) = pure (inl x)

pinr : ∀ {Γ T S} -> ntm Γ T -> ntm Γ (S + T)
pinr (case M of N - N₁) = case M of pinr N - pinr N₁
pinr (pure x) = pure (inr x)

ncase : ∀ {Γ T S C} -> rtm Γ (T + S) -> ntm (Γ , T) C -> ntm (Γ , S) C -> ntm Γ C
ncase R N1 N2 = case R of N1 - N2

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem T Γ
 reflect {T ⇝ S} {Γ} N = λ Δ w s → f Δ w (reify s)
   where f : (Δ : ctx) → vsubst Γ Δ → ntm Δ T → sem S Δ
         f Δ w (case M of s' - s'') = isSheaf _ M (f _ (wkn ∘ w) s') (f _ (wkn ∘ w) s'')
         f Δ w (pure x) = reflect (rappSubst w N · x)
 reflect {T × S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt
 reflect {T + S} N = case N (inl (reflect (v z))) (inr (reflect (v z)))


 reify : ∀ {T Γ} -> sem T Γ -> ntm Γ T
 reify {T ⇝ S} M = pure (ƛ (reify (M _ wkn (reflect (v z)))))
 reify {T × S} M = pair (reify (_*_.fst M)) (reify (_*_.snd M))
 reify {unit} _ = pure tt
 reify {T + S} (inl x) = pinl (reify x)
 reify {T + S} (inr x) = pinr (reify x)
 reify {T + S} (case s' M M₁) = ncase s' (reify M) (reify M₁)

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

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval M (λ x → reflect (v x)))

bool = unit + unit

t1 : tm ⊡ ((bool ⇝ bool) ⇝ (bool ⇝ bool))
t1 = ƛ (ƛ ((v (s z)) · ((v (s z)) · ((v (s z)) · (v z)))))

t2 : tm ⊡ ((bool ⇝ bool) ⇝ (bool ⇝ bool))
t2 = ƛ (v z)

nt1 = nbe t1
nt2 = nbe t2

-- Can I define a simple algorithm for deciding equality on these normal forms now?
-- Hmm crap we still have the variable condition to deal with
-- e.g. λ z. case (f (λ x. case z of ... ...)) ... ... = case z of (case f (λ x. ...) ... ...) (case f (λ x. ...) ... ...)
-- Crap I think because of the "up to ordering" and "same in both branches" we have trouble detecting when it really is
-- safe to pull something out? (under lambdas like that...)
