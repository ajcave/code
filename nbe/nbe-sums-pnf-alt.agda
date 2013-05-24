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


open import Data.Maybe

data IsEq {A : Set} (x : A) : (y : A) -> Set where
 yep : IsEq x x
 nope : ∀ {y} -> IsEq x y

tpEq : ∀ (T S : tp) -> IsEq T S
tpEq (T ⇝ T₁) (S ⇝ S₁) with tpEq T S | tpEq T₁ S₁
tpEq (.S ⇝ .S₁) (S ⇝ S₁) | yep | yep = yep
tpEq (T ⇝ T₁) (S ⇝ S₁) | _ | _ = nope
tpEq (T × T₁) (S × S₁) with tpEq T S | tpEq T₁ S₁
tpEq (.S × .S₁) (S × S₁) | yep | yep = yep
tpEq (T × T₁) (S × S₁) | _ | _ = nope
tpEq (T + T₁) (S + S₁) with tpEq T S | tpEq T₁ S₁
tpEq (.S + .S₁) (S + S₁) | yep | yep = yep
tpEq (T + T₁) (S + S₁) | _ | _ = nope
tpEq unit unit = yep
tpEq _ _ = nope

varEq : ∀ {Γ T} (x y : var Γ T) -> IsEq x y
varEq z z = yep
varEq (s x) (s y) with varEq x y
varEq (s x) (s .x) | yep = yep
varEq (s x) (s y) | nope = nope
varEq _ _ = nope

_<$>'_ : ∀ {A B} (f : A -> B) {x y} -> IsEq x y -> IsEq (f x) (f y)
f <$>' yep = yep
f <$>' nope = nope

_<$>_ : ∀ {A B} -> (A -> B) -> Maybe A -> Maybe B
f <$> nothing = nothing
f <$> (just x) = just (f x)
infixl 9 _<$>_

_<*>_ : ∀ {A B} -> Maybe (A -> B) -> Maybe A -> Maybe B
(just f) <*> (just x) = just (f x)
_ <*> _ = nothing
infixl 9 _<*>_

varInImage : ∀ Γ {T} {Δ} -> vsubst Γ Δ -> var Δ T -> Maybe (var Γ T)
varInImage ⊡ σ x = nothing
varInImage (Γ , T) {S} σ x with tpEq T S
varInImage (Γ , .T) {T} σ x | yep with varEq x (σ z)
varInImage (Γ , .T) {T} σ .(σ z) | yep | yep = just z
varInImage (Γ , .T) {T} σ x | yep | nope = s <$> (varInImage Γ (σ ∘ s) x)
varInImage (Γ , T) σ x | nope = s <$> (varInImage Γ (σ ∘ s) x)

{-
mutual
-- ntmInImage : ∀ {Γ T Δ} -> vsubst Γ Δ -> ntm Δ T -> Maybe (ntm Γ T)
-- ntmInImage σ (case M of N - N₁) = case_of_-_ <$> (rtmInImage σ M) <*> (ntmInImage (ext σ) N) <*> (ntmInImage (ext σ) N₁)
-- ntmInImage σ (pure x) = pure <$> (pntmInImage σ x)

 rtmInImage : ∀ {Γ T Δ} -> vsubst Γ Δ -> rtm Δ T -> Maybe (rtm Γ T)
 rtmInImage σ (v x) = v <$> varInImage _ σ x
 rtmInImage σ (R · x) = _·_ <$> rtmInImage σ R <*> pntmInImage σ x
 rtmInImage σ (π₁ R) = π₁ <$> rtmInImage σ R
 rtmInImage σ (π₂ R) = π₂ <$> rtmInImage σ R

 pntmInImage : ∀ {Γ T Δ} -> vsubst Γ Δ -> pntm Δ T -> Maybe (pntm Γ T)
 pntmInImage σ (ƛ x) = ƛ <$> pntmInImage (ext σ) x
 pntmInImage σ < P , P₁ > = <_,_> <$> pntmInImage σ P <*> pntmInImage σ P₁
 pntmInImage σ tt = just tt
 pntmInImage σ (embed M) = embed <$> {!!} -}
{- pntmInImage σ (inl P) = inl <$> pntmInImage σ P
 pntmInImage σ (inr P) = inr <$> pntmInImage σ P -}

{- mutual
 ntmEq : ∀ {T Γ} (N M : ntm Γ T) -> IsEq N M
 ntmEq (case_of_-_ {C} {T} {S} M N N₁) (case_of_-_ {.C} {T'} {S'} M₁ N' N₁') with tpEq T T' | tpEq S S'
 ntmEq (case M of N - N₁) (case M₁ of N' - N₁') | yep | yep with rtmEq M M₁ | ntmEq N N' | ntmEq N₁ N₁'
 ntmEq (case .M₁ of .N' - .N₁') (case M₁ of N' - N₁') | yep | yep | yep | yep | yep = yep
 ntmEq (case M of N - N₁) (case M₁ of N' - N₁') | yep | yep | _ | _ | _ = nope
 ntmEq (case M of N - N₁) (case M₁ of N' - N₁') | _ | _ = nope
 ntmEq (pure N) (pure M) with pntmEq N M
 ntmEq (pure .M) (pure M) | yep = yep
 ntmEq (pure N) (pure M) | nope = nope
 ntmEq _ _ = nope -}
{-
 rtmEq : ∀ {Γ T} (N M : rtm Γ T) -> IsEq N M
 rtmEq (v x) (v x') = v <$>' varEq x x'
 rtmEq (_·_ {T} {S} N M) (_·_ {T'} {.S} N' M') with tpEq T T'
 rtmEq (N · M) (N' · M') | yep with rtmEq N N' | pntmEq M M'
 rtmEq (.N' · .M') (N' · M') | yep | yep | yep = yep
 rtmEq (N · M) (N' · M') | yep | _ | _ = nope
 rtmEq (N · M) (N' · M') | nope = nope
 rtmEq (π₁ {T} {S} N) (π₁ {.T} {S'} N') with tpEq S S'
 rtmEq (π₁ N) (π₁ N') | yep = π₁ <$>' rtmEq N N'
 rtmEq (π₁ N) (π₁ N') | nope = nope
 rtmEq (π₂ {T} {S} N) (π₂ {T'} {.S} N') with tpEq T T'
 rtmEq (π₂ N) (π₂ N') | yep = π₂ <$>' rtmEq N N'
 rtmEq (π₂ N) (π₂ N') | nope = nope
 rtmEq _ _ = nope

 pntmEq : ∀ {Γ T} (N M : pntm Γ T) -> IsEq N M
 pntmEq (ƛ N) (ƛ M) = ƛ <$>' pntmEq N M
 pntmEq < N , N₁ > < M , M₁ > with pntmEq N M | pntmEq N₁ M₁
 pntmEq < .M , .M₁ > < M , M₁ > | yep | yep = yep
 pntmEq < N , N₁ > < M , M₁ > | _ | _ = nope 
 pntmEq tt tt = yep
 pntmEq (inl N) (inl M) = inl <$>' pntmEq N M
 pntmEq (inr N) (inr M) = inr <$>' pntmEq N M
 pntmEq _ _ = nope -}


{-
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

-- This ugly part can be left out and you still have something pretty cool
-- This removes redundant case splits
ncase : ∀ {Γ T S C} -> rtm Γ (T + S) -> ntm (Γ , T) C -> ntm (Γ , S) C -> ntm Γ C
ncase R N1 N2 with ntmInImage wkn N1 | ntmInImage wkn N2
ncase R N1 N2 | just x | just x₁ with ntmEq x x₁
ncase R N1 N2 | just .x | just x | yep = x
ncase R N1 N2 | just x | just x₁ | nope = case R of N1 - N2
ncase R N1 N2 | _ | _ = case R of N1 - N2
-}

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