{-# OPTIONS --type-in-type #-}
module sysfold where

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

record Σ {A : Set}(B : A -> Set) : Set where
  constructor _,_ 
  field
    fst : A
    snd : B fst

record _*_ (A : Set) (B : Set) : Set where
  constructor _,_ 
  field
    fst : A
    snd : B

record sort : Set where
 constructor ⋆

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : ∀ (Δ : ctx A) (x : A) -> Set where
 top : ∀ {Δ T} -> var (Δ , T) T
 pop : ∀ {Δ T S} -> var Δ T -> var (Δ , S) T

record unit : Set where
 constructor tt

data tp (Δ : ctx sort) : Set where
 v : var Δ ⋆ -> tp Δ 
 _⇒_ : ∀ (T : tp Δ) -> (S : tp Δ) -> tp Δ
 Π : ∀ (T : tp (Δ , _)) -> tp Δ

map : ∀ {A B} (f : A -> B) -> ctx A -> ctx B
map f ⊡ = ⊡
map f (Γ , x) = map f Γ , f x 

data gsubst {A : Set} (Exp : A -> Set) : ctx A -> Set where
 ⊡ : gsubst Exp ⊡
 _,_ : ∀ {Γ T} -> (σ : gsubst Exp Γ) -> (x : Exp T) -> gsubst Exp (Γ , T)

gmap : ∀ {A} {Exp1 : A -> Set} {Exp2 : A -> Set} {Γ : ctx A} (f : ∀ {T} -> Exp1 T -> Exp2 T) -> gsubst Exp1 Γ -> gsubst Exp2 Γ
gmap f ⊡ = ⊡
gmap f (σ , x) = (gmap f σ) , f x 

gapp : ∀ {A T} {Exp : A -> Set} {Γ : ctx A} (σ : gsubst Exp Γ) (x : var Γ T) -> Exp T
gapp ⊡ ()
gapp (σ , x) top = x
gapp (σ , x) (pop y) = gapp σ y

tvsubst : ctx sort -> ctx sort -> Set
tvsubst Δ1 Δ2 = gsubst (λ ⋆ -> var Δ2 ⋆) Δ1

tsubst : ctx sort -> ctx sort -> Set
tsubst Δ1 Δ2 = gsubst (λ ⋆ -> tp Δ2) Δ1

_∘_ : ∀ {A} {Δ1 Δ2 : ctx A} {B : A -> Set} (σ1 : gsubst B Δ2) (σ2 : gsubst (var Δ2) Δ1) -> gsubst B Δ1
σ1 ∘ σ2 = gmap (gapp σ1) σ2

ext : ∀ {A} {Γ Γ' : ctx A} {T} -> gsubst (var Γ') Γ -> gsubst (var (Γ' , T)) (Γ , T)
ext σ = (gmap pop σ) , top

-- It seems like we can do this in general given projection functions.
-- How about with an accumulator or CPS?
-- I think using emb : (f : {T} -> var Δ T -> Exp Γ T) -> gsubst (Exp Γ) Δ is nice
-- because then emb is functorial
ids : ∀ {A} {Δ : ctx A} -> gsubst (var Δ) Δ
ids {Δ = ⊡} = ⊡
ids {Δ = Γ , T} = (gmap pop ids) , top

vwkn : ∀ {A} {Δ1 : ctx A} T -> gsubst (var (Δ1 , T)) Δ1
vwkn T = gmap pop ids

[_] : ∀ {Δ1 Δ2} -> tvsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[ σ ] (v y) = v (gapp σ y)
[ σ ] (T ⇒ S) = [ σ ] T ⇒ [ σ ] S
[ σ ] (Π T) = Π ([ ext σ ] T)

t-ext : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 ->  tsubst (Δ1 , ⋆) (Δ2 , ⋆)
t-ext θ = (gmap [ vwkn ⋆ ] θ) , (v top)

[[_]] : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[[ θ ]] (v y) = gapp θ y
[[ θ ]] (T ⇒ S) = [[ θ ]] T ⇒ [[ θ ]] S
[[ θ ]] (Π T) = Π ([[ t-ext θ ]] T)

id : ∀ {A} -> A -> A
id x = x

id-tsubst : ∀ {Δ1} -> tsubst Δ1 Δ1
id-tsubst {⊡} = ⊡
id-tsubst {Δ , T} = (gmap [ vwkn ⋆ ] (id-tsubst {Δ})) , v top

mutual
 data rtm (Δ : ctx sort) (Γ : ctx (tp Δ)) : tp Δ -> Set where
  v : ∀ {T : tp Δ} -> var Γ T -> rtm Δ Γ T
  _·_ : ∀ {T : tp Δ} {S : tp Δ} -> rtm Δ Γ (T ⇒ S) -> ntm Δ Γ T -> rtm Δ Γ S
  _$_ : ∀ {T : tp (Δ , _)} -> rtm Δ Γ (Π T) -> (S : tp Δ)
         -> rtm Δ Γ ([[ id-tsubst , S ]] T)
 data ntm (Δ : ctx sort) (Γ : ctx (tp Δ)) : tp Δ -> Set where 
  ƛ : ∀ {T S : tp Δ} -> ntm Δ (Γ , T) S -> ntm Δ Γ (T ⇒ S)
  Λ : ∀ {T : tp (Δ , _)} -> ntm (Δ , _) (map [ vwkn ⋆ ] Γ) T -> ntm Δ Γ (Π T)
  ▹ : ∀ {A} -> rtm Δ Γ (v A) -> ntm Δ Γ (v A)

vsubst : ∀ {Δ : ctx sort} (Γ Γ' : ctx (tp Δ)) -> Set
vsubst Γ Γ' = gsubst (var Γ') Γ

-- Technically I can't use a record here. That's strange.
-- It seems that (A : Set) -> P A -> B is not interchangible with Σ (A : Set). P A -> B,
-- If I understand the "strong sums in impredicative type theory" issue correctly...
record cand Δ T : Set₁ where
 field
  sem : (Γ : ctx (tp Δ)) -> Set
  funct : ∀ {Γ1 Γ2} -> vsubst Γ1 Γ2 -> sem Γ1 -> sem Γ2
  reflect : ∀ {Γ} -> rtm Δ Γ T -> sem Γ
  reify : ∀ {Γ} -> sem Γ -> ntm Δ Γ T

record candidate Δ1 (T : tp Δ1) : Set₁ where
 field
  candi : ∀ Δ2 (σ : tvsubst Δ1 Δ2) -> cand Δ2 ([ σ ] T)
--  Funct : ∀ Δ2 (σ : tvsubst Δ1 Δ2) (Γ : ctx (tp Δ1)) -> cand.sem (candi Δ1 …) Γ -> cand.sem (candi Δ2 σ) (map [ σ ] Γ)

-- TODO: Rewrite this as an inductive type.
〚_〛 : (Δ1 : ctx sort) {Δ2 : ctx sort} (θ : tsubst Δ1 Δ2) -> Set
〚 ⊡ 〛 θ = unit
〚 Δ , l 〛 (θ , U) = (〚 Δ 〛 θ) * (candidate _ U)

lem1' : ∀ {Δ1 Δ2 Δ3} (σ1 : tvsubst Δ2 Δ3) (σ2 : tvsubst Δ1 Δ2) -> ((ext σ1) ∘ (ext σ2)) ≡ ext (σ1 ∘ σ2)
lem1' σ1 ⊡ = refl
lem1' σ1 (σ , x) = {!!}

lem1 : ∀ {Δ1 Δ2 Δ3} (σ1 : tvsubst Δ2 Δ3) (σ2 : tvsubst Δ1 Δ2) (T : tp Δ1) -> [ σ1 ] ([ σ2 ] T) ≡ [ σ1 ∘ σ2 ] T
lem1 σ1 σ2 (v y) = {!!}
lem1 σ1 σ2 (T ⇒ S) rewrite lem1 σ1 σ2 T | lem1 σ1 σ2 S = refl
lem1 σ1 σ2 (Π T) rewrite lem1 (ext σ1) (ext σ2) T | lem1' σ1 σ2 = refl 

cand-app' : ∀ {Δ1 Δ2} (σ : tvsubst Δ1 Δ2) {U : tp _} (R : candidate Δ1 U) {Δ3} (σ' : tvsubst Δ2 Δ3)  -> cand Δ3 ([ σ' ] ([ σ ] U))
cand-app' σ {U} R σ' rewrite lem1 σ' σ U = candidate.candi R _ (σ' ∘ σ)

cand-app-funct : ∀ {Δ1 Δ2 Δ3} (σ : tvsubst Δ1 Δ2) (σ' : tvsubst Δ2 Δ3) {U} (R : candidate Δ1 U) {Γ : ctx (tp Δ2)}
 -> cand.sem (cand-app' σ R ids) Γ -> cand.sem (cand-app' σ R σ') (map [ σ' ] Γ)
cand-app-funct σ σ' {U} R M with [ σ' ] ([ σ ] U) | lem1 σ' σ U
cand-app-funct σ σ' {U} R M | .([ σ' ∘ σ ] U) | refl = {!!} -- Oops, Funct isn't general enough...
 
cand-app : ∀ {Δ1 Δ2} (σ : tvsubst Δ1 Δ2) {U : tp _} (R : candidate Δ1 U) -> candidate Δ2 ([ σ ] U)
cand-app {Δ1} {Δ2} σ {U} R = record { candi = λ Δ3 σ' → cand-app' σ R σ' }

st-subst-app : ∀ {Δ1 Δ2 Δ3} (σ : tvsubst Δ2 Δ3) {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ)  -> 〚 Δ1 〛 (gmap [ σ ] θ)
st-subst-app σ {⊡} Δ' = tt
st-subst-app {Δ1 , _} {Δ2} {Δ3} σ {θ , T} (Δ' , R) = st-subst-app σ Δ' , (cand-app σ R)

vari : ∀ {Δ1 Δ2 : ctx sort} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) (α : var Δ1 ⋆) -> candidate Δ2 (gapp θ α)
vari {θ = ⊡} _ ()
vari {θ = θ , T} (Δ' , α) top = α
vari {θ = θ , T} (Δ' , α) (pop y) = vari Δ' y

sem : ∀ {Δ1 Δ2} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) (T : tp Δ1) -> (Γ : ctx (tp Δ2)) -> Set
sem {Δ1} {Δ2} Δ' (v y) Γ = cand.sem (candidate.candi (vari Δ' y) _ ids) Γ -- Is this what we want?
sem Δ' (T ⇒ S) Γ = ∀ Γ' -> vsubst Γ Γ' -> sem Δ' T Γ' → sem Δ' S Γ'
sem {Δ1} {Δ2} Δ' (Π T) Γ = ∀ Δ2' (σ : tvsubst Δ2 Δ2') (U : tp Δ2') (R : candidate Δ2' U)
                                 → sem {θ = _ , U} ((st-subst-app σ Δ') , R) T (map [ σ ] Γ)

varTsubst : ∀ {Δ1 Δ2 Γ T} (σ : tvsubst Δ1 Δ2) -> var Γ T -> var (map [ σ ] Γ) ([ σ ] T)
varTsubst σ top = top
varTsubst σ (pop y) = pop (varTsubst σ y)

lift : ∀ {Δ1 Δ2 Γ1 Γ2} (σ : tvsubst Δ1 Δ2) -> vsubst Γ1 Γ2 -> vsubst (map [ σ ] Γ1) (map [ σ ] Γ2)
lift σ ⊡ = ⊡
lift σ (σ' , x) = (lift σ σ') , (varTsubst σ x)

mutual
 rappSubst : ∀ {Δ Γ Γ' S} -> vsubst Γ Γ' -> rtm Δ Γ S -> rtm Δ Γ' S
 rappSubst σ (v y) = v (gapp σ y)
 rappSubst σ (R · N) = (rappSubst σ R) · nappSubst σ N
 rappSubst σ (R $ S) = (rappSubst σ R) $ S
 nappSubst : ∀ {Δ Γ Γ' S} -> vsubst Γ Γ' -> ntm Δ Γ S -> ntm Δ Γ' S 
 nappSubst σ (ƛ N) = ƛ (nappSubst (ext σ) N)
 nappSubst σ (Λ N) = Λ (nappSubst (lift (vwkn ⋆) σ) N)
 nappSubst σ (▹ R) = ▹ (rappSubst σ R)

mutual
 rappTSubst : ∀ {Δ Δ' Γ S} (σ : tvsubst Δ Δ') -> rtm Δ Γ S -> rtm Δ' (map [ σ ] Γ) ([ σ ] S)
 rappTSubst σ (v y) = v (varTsubst σ y)
 rappTSubst σ (R · N) = (rappTSubst σ R) · nappTSubst σ N
 rappTSubst σ (R $ S) with rappTSubst σ R
 ... | w = {!!}
 nappTSubst : ∀ {Δ Δ' Γ S} (σ : tvsubst Δ Δ') -> ntm Δ Γ S -> ntm Δ' (map [ σ ] Γ) ([ σ ] S)
 nappTSubst σ (ƛ N) = ƛ (nappTSubst σ N)
 nappTSubst σ (Λ N) = Λ {!!}
 nappTSubst σ (▹ R) = ▹ (rappTSubst σ R)


appSubst : ∀ {Δ1 Δ2} {Γ1 Γ2 : ctx (tp Δ2)} {θ : tsubst Δ1 Δ2} {Δ' : 〚 Δ1 〛 θ} S -> vsubst Γ1 Γ2 -> sem Δ' S Γ1 -> sem Δ' S Γ2
appSubst {Δ' = Δ'} (v α) θ M = cand.funct (candidate.candi (vari Δ' α) _ ids) θ M
appSubst (T ⇒ S) θ M = λ Γ' σ x → M Γ' (σ ∘ θ) x
appSubst (Π T) θ M = λ Δ σ U R → appSubst T (lift σ θ) (M Δ σ U R)

data eqdep {B} (A : B -> Set) {b} (x : A b) : ∀ {c} -> A c -> Set where
 refl : eqdep A x x

{-lem0 : ∀ {Δ1 Δ2 Δ3} {θ : tsubst Δ1 Δ2} (σ : tvsubst Δ2 Δ3) (Δ' : 〚 Δ1 〛 θ) (y : tvar Δ1 tt)
  -> (candidate.candi (vari (st-subst-app σ Δ') y) _ …) ≡ (cand-app' σ (vari Δ' y) …)
lem0 σ Δ' y = {!!} -}

appTSubst : ∀ {Δ1 Δ2 Δ3 Γ} {θ : tsubst Δ1 Δ2} {Δ' : 〚 Δ1 〛 θ} S -> (σ : tvsubst Δ2 Δ3) -> sem Δ' S Γ -> sem (st-subst-app σ Δ') S (map [ σ ] Γ)
appTSubst {Γ = Γ} {Δ' = Δ'} (v y) σ M = {!!}
appTSubst (T ⇒ S) σ M = λ Γ' σ' x → {!!} -- Crap, this will have to quantify over extensions to Δ too.. Or.. ?
appTSubst (Π T) σ M = λ Δ2' σ' U R → {!!} -- "Easy"

lem : ∀ {Δ1 Δ2 Δ3} (θ1 : tsubst Δ1 Δ2) (θ2 : tsubst Δ2 Δ3) T -> [[ θ2 ]] ([[ θ1 ]] T) ≡ [[ gmap [[ θ2 ]] θ1 ]] T
lem θ1 θ2 T = {!!}

lem2 : ∀ {Δ1 Δ2 Δ3 Δ4} (f : tp Δ1 -> tp Δ2) (g : tp Δ2 -> tp Δ3) (θ : tsubst Δ4 Δ1)
  -> gmap g (gmap f θ) ≡ gmap (λ x -> g (f x)) θ
lem2 f g ⊡ = refl
lem2 f g (θ , T) rewrite lem2 f g θ = refl

neut-candidate : ∀ {Δ} -> candidate (Δ , ⋆) (v top)
neut-candidate {Δ} = record { candi = λ Δ2 σ → record { sem = λ Γ → rtm Δ2 Γ ([ σ ] (v top)); funct = rappSubst; reflect = id; reify = ▹ } } 

mutual
 reflect : ∀ {Δ1 Δ2} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) T {Γ} -> rtm Δ2 Γ ([[ θ ]] T) -> sem Δ' T Γ
 reflect Δ' (v α) r = cand.reflect (candidate.candi (vari Δ' α) _ ids) {!!} -- Easy
 reflect Δ' (T ⇒ S) r = λ Γ' σ x → reflect Δ' S (rappSubst σ r · reify Δ' T x)
 reflect {Δ2 = Δ2} {θ = θ} Δ' (Π T) {Γ} r = foo --foo
   where foo : ∀ Δ2' (σ : tvsubst Δ2 Δ2') (U : tp Δ2') (R : candidate Δ2' U) -> sem {θ = gmap [ σ ] θ , U} (st-subst-app σ Δ' , R) T (map [ σ ] Γ)
         foo Δ2' σ U R with (rappTSubst σ r) $ U
         ... | w = reflect {θ = gmap [ σ ] θ , U} (st-subst-app σ Δ' , R) T {!!} -- "Easy"
 reify : ∀ {Δ1 Δ2} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) T {Γ} -> sem Δ' T Γ -> ntm Δ2 Γ ([[ θ ]] T)
 reify Δ' (v α) M with cand.reify (candidate.candi (vari Δ' α) _ ids) M
 ... | w = {!!} -- "Easy"
 reify {θ = θ} Δ' (T ⇒ S) M = ƛ (reify Δ' S (M (_ , [[ θ ]] T) (vwkn _) (reflect Δ' T (v top))))
 reify {θ = θ} Δ' (Π T) M = Λ (reify (st-subst-app (vwkn ⋆) Δ' , neut-candidate) T (M _ (vwkn ⋆) (v top) neut-candidate))

sem-cand : ∀ {Δ1 Δ2} (θ : tsubst Δ1 Δ2) (Δ' : 〚 Δ1 〛 θ) (T : tp Δ1) -> candidate Δ2 ([[ θ ]] T)
sem-cand θ Δ' T = record { candi = λ Δ2 σ → record { sem = sem {θ = gmap [ σ ] θ} (st-subst-app σ Δ') T; funct = appSubst T; reflect = {!!}; reify = {!!} } } -- Easy

subst : ∀ {Δ1 Δ2} {θ : tsubst Δ1 Δ2} (Γ1 : ctx (tp Δ1)) (Γ1 : ctx (tp Δ2)) (Δ' : 〚 Δ1 〛 θ) -> Set
subst Γ1 Γ2 Δ' = ∀ {T} -> var Γ1 T -> sem Δ' T Γ2

{-slift : ∀ {Δ1 Γ1 Δ2 Δ3 Γ2} {θ : tsubst Δ1 Δ2} {Δ' : 〚 Δ1 〛 θ} (ρ : tvsubst Δ2 Δ3) -> subst Γ1 Γ2 Δ' -> subst Γ1 (tctxM [ ρ ] Γ2) (st-subst-app ρ Δ')
slift ρ σ z = {!!}
slift ρ σ (s y) = {!!} -}

extend : ∀ {Δ1 Δ2} {θ : tsubst Δ1 Δ2} {Γ1 : ctx (tp Δ1)} {Γ2 : ctx (tp Δ2)} (Δ' : 〚 Δ1 〛 θ) {T} -> subst Γ1 Γ2 Δ' -> sem Δ' T Γ2 -> subst (Γ1 , T) Γ2 Δ'
extend Δ' θ M top = M
extend Δ' θ M (pop y) = θ y

tsubstLookup-map : ∀ {A} {Exp1 Exp2 : A -> Set} {Δ1} (f : ∀ {T} -> Exp1 T -> Exp2 T) (θ : gsubst Exp1 Δ1) {T} (y : var Δ1 T) -> gapp (gmap f θ) y ≡ f (gapp θ y)
tsubstLookup-map f ⊡ ()
tsubstLookup-map f (θ , T) top = refl
tsubstLookup-map f (θ , T) (pop y) = tsubstLookup-map f θ y

trans : ∀ {A} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl f = f

tsubstLookup-id : ∀ {Δ} (y : var Δ _) -> gapp id-tsubst y ≡ v y
tsubstLookup-id top = refl
tsubstLookup-id (pop y) = trans (tsubstLookup-map [ vwkn ⋆ ] id-tsubst y) foo
 where foo : [ vwkn ⋆ ] (gapp id-tsubst y) ≡ v (pop y)
       foo rewrite tsubstLookup-id y with tsubstLookup-map pop ids y
       ... | w = {!!}

mutual
 sem-subst1 :  ∀ {Δ1 Δ2} Γ {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) S T -> sem {θ = θ , [[ θ ]] S} (Δ' , sem-cand θ Δ' S) T Γ -> sem Δ' ([[ id-tsubst , S ]] T) Γ
 sem-subst1 Γ Δ S (v top) = λ x → {!!} -- "Easy"
 sem-subst1 Γ Δ S (v (pop y)) rewrite tsubstLookup-id y = λ x → x
 sem-subst1 Γ Δ S (T ⇒ S') = λ M Γ' σ x → sem-subst1 Γ' Δ S S' (M Γ' σ (sem-subst2 Γ' Δ S T x))
 sem-subst1 Γ Δ S (Π T) = λ M Δ2' σ U R → {!!} -- Gonna have to generalize this...

 sem-subst2 :  ∀ {Δ1 Δ2} Γ {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) S T -> sem Δ' ([[ id-tsubst , S ]] T) Γ -> sem {θ = θ , [[ θ ]] S} (Δ' , sem-cand θ Δ' S) T Γ
 sem-subst2 Γ Δ S (v top) = λ x → {!!} -- "Easy"
 sem-subst2 Γ Δ S (v (pop y)) rewrite tsubstLookup-id y = λ x → x
 sem-subst2 Γ Δ S (T ⇒ S') = λ M Γ' σ x → sem-subst2 Γ' Δ S S' (M Γ' σ (sem-subst1 Γ' Δ S T x))
 sem-subst2 Γ Δ S (Π T) = λ x Δ2' σ U R → {!!} -- Generalize...

--st-subst-app-id : ∀ {Δ1 Δ2} (θ : tsubst Δ1 Δ2) (Δ' : 〚 Δ1 〛 θ) -> (st-subst-app … Δ') ≡ Δ'
--st-subst-app-id θ Δ' = ?

mutual
 srSubst : ∀ {Δ1 Δ2 Γ1 Γ2 T} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) -> subst Γ1 Γ2 Δ' -> rtm Δ1 Γ1 T -> sem Δ' T Γ2
 srSubst Δ' σ (v y) = σ y
 srSubst Δ' σ (R · N) = (srSubst Δ' σ R) _ ids (sSubst Δ' σ N)
 srSubst {Γ2 = Γ2} {θ = θ} Δ' σ (_$_ {T} R S) with srSubst Δ' σ R _ ids ([[ θ ]] S) (sem-cand θ Δ' S)
 ... | w = sem-subst1 Γ2 Δ' S T {!!} -- "Easy"

 sSubst : ∀ {Δ1 Δ2 Γ1 Γ2 T} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) -> subst Γ1 Γ2 Δ' -> ntm Δ1 Γ1 T -> sem Δ' T Γ2
 sSubst Δ' σ (ƛ {T} {S} N) = λ Γ' σ' s → sSubst Δ' (extend Δ' (λ {T0} x → appSubst T0 σ' (σ x)) s) N
 sSubst {θ = θ} Δ' σ (Λ N) = λ Δ3 σt U R → sSubst {θ = gmap [ σt ] θ , U} (st-subst-app σt Δ' , R) (λ x → {!!}) N -- Ugly
 sSubst Δ' σ (▹ R) = srSubst Δ' σ R

nsubst : ∀ {Δ} (Γ1 Γ2 : ctx (tp Δ)) -> Set
nsubst {Δ} Γ1 Γ2 = ∀ {T} -> var Γ1 T -> ntm Δ Γ2 T
cut : ∀ {Δ Γ1 Γ2 T} -> nsubst Γ1 Γ2 -> ntm Δ Γ1 T -> ntm Δ Γ2 T -- TODO: I probably need to cut the types simultaneously.
cut θ N = {!!} --reify id-cands _ (sSubst (λ x → sSubst (λ x' → reflect _ _ (v x')) (θ x)) N)

