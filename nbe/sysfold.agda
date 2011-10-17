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

wkn : ∀ {A} {Δ1 : ctx A} T -> gsubst (var (Δ1 , T)) Δ1
wkn T = gmap pop ids

[_] : ∀ {Δ1 Δ2} -> tvsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[ σ ] (v y) = v (gapp σ y)
[ σ ] (T ⇒ S) = [ σ ] T ⇒ [ σ ] S
[ σ ] (Π T) = Π ([ ext σ ] T)

t-ext : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 ->  tsubst (Δ1 , ⋆) (Δ2 , ⋆)
t-ext θ = (gmap [ wkn ⋆ ] θ) , (v top)

[[_]] : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[[ θ ]] (v y) = gapp θ y
[[ θ ]] (T ⇒ S) = [[ θ ]] T ⇒ [[ θ ]] S
[[ θ ]] (Π T) = Π ([[ t-ext θ ]] T)

id : ∀ {A} -> A -> A
id x = x

id-tsubst : ∀ {Δ1} -> tsubst Δ1 Δ1
id-tsubst {⊡} = ⊡
id-tsubst {Δ , T} = (gmap [ wkn ⋆ ] (id-tsubst {Δ})) , v top

mutual
 data rtm (Δ : ctx sort) (Γ : ctx (tp Δ)) : tp Δ -> Set where
  v : ∀ {T : tp Δ} -> var Γ T -> rtm Δ Γ T
  _·_ : ∀ {T : tp Δ} {S : tp Δ} -> rtm Δ Γ (T ⇒ S) -> ntm Δ Γ T -> rtm Δ Γ S
  _$_ : ∀ {T : tp (Δ , _)} -> rtm Δ Γ (Π T) -> (S : tp Δ)
         -> rtm Δ Γ ([[ id-tsubst , S ]] T)
 data ntm (Δ : ctx sort) (Γ : ctx (tp Δ)) : tp Δ -> Set where 
  ƛ : ∀ {T S : tp Δ} -> ntm Δ (Γ , T) S -> ntm Δ Γ (T ⇒ S)
  Λ : ∀ {T : tp (Δ , _)} -> ntm (Δ , _) (map [ wkn ⋆ ] Γ) T -> ntm Δ Γ (Π T)
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
data Subst Δ2 : (Δ1 : ctx sort) (σ : tsubst Δ1 Δ2) -> Set where
 ⊡ : Subst Δ2 ⊡ ⊡
 _,_ : ∀ {Δ1} {σ : tsubst Δ1 Δ2} -> Subst Δ2 Δ1 σ -> {U : tp Δ2} (R : candidate Δ2 U) -> Subst Δ2 (Δ1 , ⋆) (σ , U)

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

st-subst-app : ∀ {Δ1 Δ2 Δ3} (σ : tvsubst Δ2 Δ3) {θ : tsubst Δ1 Δ2} (Δ' : Subst Δ2 Δ1 θ)  -> Subst Δ3 Δ1 (gmap [ σ ] θ)
st-subst-app σ {⊡} Δ' = ⊡
st-subst-app {Δ1 , _} {Δ2} {Δ3} σ {θ , T} (Δ' , R) = st-subst-app σ Δ' , (cand-app σ R)

vari : ∀ {Δ1 Δ2 : ctx sort} {σ : tsubst Δ1 Δ2} (θ : Subst Δ2 Δ1 σ) (α : var Δ1 ⋆) -> candidate Δ2 (gapp σ α)
vari {σ = ⊡} _ ()
vari {σ = σ , T} (Δ' , α) top = α
vari {σ = σ , T} (Δ' , α) (pop y) = vari Δ' y

sem : ∀ {Δ1 Δ2} {σ : tsubst Δ1 Δ2} (θ : Subst Δ2 Δ1 σ) (T : tp Δ1) -> (Γ : ctx (tp Δ2)) -> Set
sem {Δ1} {Δ2} θ (v y) Γ = cand.sem (candidate.candi (vari θ y) _ ids) Γ -- Is this what we want?
sem {Δ1} {Δ2} θ (T ⇒ S) Γ = ∀ Γ' -> vsubst Γ Γ' -> sem θ T Γ' → sem θ S Γ'
sem {Δ1} {Δ2} θ (Π T) Γ = ∀ Δ2' (σ : tvsubst Δ2 Δ2') (U : tp Δ2') (R : candidate Δ2' U)
                                 → sem {σ = _ , U} ((st-subst-app σ θ) , R) T (map [ σ ] Γ)

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
 nappSubst σ (Λ N) = Λ (nappSubst (lift (wkn ⋆) σ) N)
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

appSubst : ∀ {Δ1 Δ2} {Γ1 Γ2 : ctx (tp Δ2)} {θ : tsubst Δ1 Δ2} {Δ' : Subst Δ2 Δ1 θ} -> vsubst Γ1 Γ2 -> ∀ {S} ->  sem Δ' S Γ1 -> sem Δ' S Γ2
appSubst {Δ' = Δ'} θ {v α} M = cand.funct (candidate.candi (vari Δ' α) _ ids) θ M
appSubst θ {T ⇒ S} M = λ Γ' σ x → M Γ' (σ ∘ θ) x
appSubst θ {Π T} M = λ Δ σ U R → appSubst (lift σ θ) {T} (M Δ σ U R)

data eqdep {B} (A : B -> Set) {b} (x : A b) : ∀ {c} -> A c -> Set where
 refl : eqdep A x x

{-lem0 : ∀ {Δ1 Δ2 Δ3} {θ : tsubst Δ1 Δ2} (σ : tvsubst Δ2 Δ3) (Δ' : 〚 Δ1 〛 θ) (y : tvar Δ1 tt)
  -> (candidate.candi (vari (st-subst-app σ Δ') y) _ …) ≡ (cand-app' σ (vari Δ' y) …)
lem0 σ Δ' y = {!!} -}

appTSubst : ∀ {Δ1 Δ2 Δ3 Γ} {θ : tsubst Δ1 Δ2} {Δ' : Subst Δ2 Δ1 θ} S -> (σ : tvsubst Δ2 Δ3) -> sem Δ' S Γ -> sem (st-subst-app σ Δ') S (map [ σ ] Γ)
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
 reflect : ∀ {Δ1 Δ2} {σ : tsubst Δ1 Δ2} (θ : Subst Δ2 Δ1 σ) T {Γ} -> rtm Δ2 Γ ([[ σ ]] T) -> sem θ T Γ
 reflect Δ' (v α) r = cand.reflect (candidate.candi (vari Δ' α) _ ids) {!!} -- Easy
 reflect Δ' (T ⇒ S) r = λ Γ' σ x → reflect Δ' S (rappSubst σ r · reify Δ' T x)
 reflect {Δ2 = Δ2} {σ} θ (Π T) {Γ} r = foo --foo
   where foo : ∀ Δ2' (σ' : tvsubst Δ2 Δ2') (U : tp Δ2') (R : candidate Δ2' U) -> sem {σ = gmap [ σ' ] σ , U} (st-subst-app σ' θ , R) T (map [ σ' ] Γ)
         foo Δ2' σ' U R with (rappTSubst σ' r) $ U
         ... | w = reflect {σ = gmap [ σ' ] σ , U} (st-subst-app σ' θ , R) T {!!} -- "Easy"
 reify : ∀ {Δ1 Δ2} {σ : tsubst Δ1 Δ2} (θ : Subst Δ2 Δ1 σ) T {Γ} -> sem θ T Γ -> ntm Δ2 Γ ([[ σ ]] T)
 reify Δ' (v α) M with cand.reify (candidate.candi (vari Δ' α) _ ids) M
 ... | w = {!!} -- "Easy"
 reify {σ = σ} θ (T ⇒ S) M = ƛ (reify θ S (M (_ , [[ σ ]] T) (wkn _) (reflect θ T (v top))))
 reify {σ = σ} θ (Π T) M = Λ (reify (st-subst-app (wkn ⋆) θ , neut-candidate) T (M _ (wkn ⋆) (v top) neut-candidate))

sem-cand : ∀ {Δ1 Δ2} (σ : tsubst Δ1 Δ2) (θ : Subst Δ2 Δ1 σ) (T : tp Δ1) -> candidate Δ2 ([[ σ ]] T)
sem-cand σ θ T = record { candi = λ Δ2 σ' → record { sem = sem {σ = gmap [ σ' ] σ} (st-subst-app σ' θ) T; funct = {!!}; reflect = {!!}; reify = {!!} } } -- Easy

subst : ∀ {Δ1 Δ2} {θ : tsubst Δ1 Δ2} (Γ1 : ctx (tp Δ1)) (Γ1 : ctx (tp Δ2)) (Δ' : Subst Δ2 Δ1 θ) -> Set
subst Γ1 Γ2 Δ' = gsubst (λ T -> sem Δ' T Γ2) Γ1

tsubstLookup-map : ∀ {A} {Exp1 Exp2 : A -> Set} {Δ1} (f : ∀ {T} -> Exp1 T -> Exp2 T) (θ : gsubst Exp1 Δ1) {T} (y : var Δ1 T) -> gapp (gmap f θ) y ≡ f (gapp θ y)
tsubstLookup-map f ⊡ ()
tsubstLookup-map f (θ , T) top = refl
tsubstLookup-map f (θ , T) (pop y) = tsubstLookup-map f θ y

trans : ∀ {A} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl f = f

tsubstLookup-id : ∀ {Δ} (y : var Δ _) -> gapp id-tsubst y ≡ v y
tsubstLookup-id top = refl
tsubstLookup-id (pop y) = trans (tsubstLookup-map [ wkn ⋆ ] id-tsubst y) foo
 where foo : [ wkn ⋆ ] (gapp id-tsubst y) ≡ v (pop y)
       foo rewrite tsubstLookup-id y with tsubstLookup-map pop ids y
       ... | w = {!!}

mutual
 sem-subst1 :  ∀ {Δ1 Δ2} Γ {σ : tsubst Δ1 Δ2} (θ : Subst Δ2 Δ1 σ) S T -> sem {σ = σ , [[ σ ]] S} (θ , sem-cand σ θ S) T Γ -> sem θ ([[ id-tsubst , S ]] T) Γ
 sem-subst1 Γ Δ S (v top) = λ x → {!!} -- "Easy"
 sem-subst1 Γ Δ S (v (pop y)) rewrite tsubstLookup-id y = λ x → x
 sem-subst1 Γ Δ S (T ⇒ S') = λ M Γ' σ x → sem-subst1 Γ' Δ S S' (M Γ' σ (sem-subst2 Γ' Δ S T x))
 sem-subst1 Γ Δ S (Π T) = λ M Δ2' σ U R → {!!} -- Gonna have to generalize this...

 sem-subst2 :  ∀ {Δ1 Δ2} Γ {σ : tsubst Δ1 Δ2} (θ : Subst Δ2 Δ1 σ) S T -> sem θ ([[ id-tsubst , S ]] T) Γ -> sem {σ = σ , [[ σ ]] S} (θ , sem-cand σ θ S) T Γ
 sem-subst2 Γ Δ S (v top) = λ x → {!!} -- "Easy"
 sem-subst2 Γ Δ S (v (pop y)) rewrite tsubstLookup-id y = λ x → x
 sem-subst2 Γ Δ S (T ⇒ S') = λ M Γ' σ x → sem-subst2 Γ' Δ S S' (M Γ' σ (sem-subst1 Γ' Δ S T x))
 sem-subst2 Γ Δ S (Π T) = λ x Δ2' σ U R → {!!} -- Generalize...

--st-subst-app-id : ∀ {Δ1 Δ2} (θ : tsubst Δ1 Δ2) (Δ' : 〚 Δ1 〛 θ) -> (st-subst-app … Δ') ≡ Δ'
--st-subst-app-id θ Δ' = ?

mutual
 srSubst : ∀ {Δ1 Δ2 Γ1 Γ2 T} {σ : tsubst Δ1 Δ2} (θ : Subst Δ2 Δ1 σ) -> subst Γ1 Γ2 θ -> rtm Δ1 Γ1 T -> sem θ T Γ2
 srSubst θ σ (v y) = gapp σ y
 srSubst θ σ (R · N) = (srSubst θ σ R) _ ids (sSubst θ σ N)
 srSubst {Γ2 = Γ2} {σ = σ1} θ σ (_$_ {T} R S) with srSubst θ σ R _ ids ([[ σ1 ]] S) (sem-cand σ1 θ S)
 ... | w = sem-subst1 Γ2 θ S T {!!} -- "Easy"

 sSubst : ∀ {Δ1 Δ2 Γ1 Γ2 T} {σ : tsubst Δ1 Δ2} (θ : Subst Δ2 Δ1 σ) -> subst Γ1 Γ2 θ -> ntm Δ1 Γ1 T -> sem θ T Γ2
 sSubst {σ = σ1} θ σ (ƛ {T} {S} N) = λ Γ' σ' s → sSubst θ ((gmap (appSubst σ') σ) , s) N
 sSubst {σ = σ1} θ σ (Λ N) = λ Δ3 σt U R → sSubst {σ = gmap [ σt ] σ1 , U} (st-subst-app σt θ , R) {!!} N -- Ugly
 sSubst θ σ (▹ R) = srSubst θ σ R

nsubst : ∀ {Δ} (Γ1 Γ2 : ctx (tp Δ)) -> Set
nsubst {Δ} Γ1 Γ2 = ∀ {T} -> var Γ1 T -> ntm Δ Γ2 T
cut : ∀ {Δ Γ1 Γ2 T} -> nsubst Γ1 Γ2 -> ntm Δ Γ1 T -> ntm Δ Γ2 T -- TODO: I probably need to cut the types simultaneously.
cut θ N = {!!} --reify id-cands _ (sSubst (λ x → sSubst (λ x' → reflect _ _ (v x')) (θ x)) N)

