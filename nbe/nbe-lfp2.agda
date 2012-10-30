{-# OPTIONS --type-in-type #-}
-- Type in type is temporary until I make FinMap universe polymorphic
module nbe-lfp2 where
open import FinMap
open import Product
open import Data.Unit hiding (⊤)
open import Relation.Binary.PropositionalEquality hiding ([_])

record Kind : Set where
 constructor *

mutual
 data functor (ζ : ctx Kind) : Set where
  ▹ : (A : var ζ *) -> functor ζ
  μ : (F : functor (ζ , *)) -> functor ζ
  _⇝_ : (A : tp) (B : functor ζ) -> functor ζ
  _∧_ : (A B : functor ζ) -> functor ζ
  ⊤ : functor ζ

 tp : Set
 tp = functor ⊡

psub : ∀ (ζ1 ζ2 : ctx Kind) -> Set
psub ζ1 ζ2 = gsubst ζ2 (λ _ -> functor ζ1)

[_]pv : ∀ {ζ1 ζ2} -> vsubst ζ1 ζ2 -> functor ζ1 -> functor ζ2
[ σ ]pv (▹ A) = ▹ ([ σ ]v A)
[ σ ]pv (μ F) = μ ([ vsub-ext σ ]pv F)
[ σ ]pv (A ⇝ B) = A ⇝ ([ σ ]pv B)
[ σ ]pv (A ∧ B) = ([ σ ]pv A) ∧ ([ σ ]pv B)
[ σ ]pv ⊤ = ⊤

id-psub : ∀ {ζ} -> psub ζ ζ
id-psub {⊡} = unit
id-psub {ζ , #prop} = (gmap [ wkn-vsub ]pv id-psub) , (▹ top)

psub-wkn : ∀ {ζ1 ζ2} (σ : psub ζ1 ζ2) -> psub (ζ1 , *) ζ2
psub-wkn σ = gmap [ wkn-vsub ]pv σ

psub-ext : ∀ {ζ1 ζ2} -> psub ζ1 ζ2 -> psub (ζ1 , *) (ζ2 , *)
psub-ext σ = (psub-wkn σ) , ▹ top

[_]p : ∀ {ζ1 ζ2} -> psub ζ2 ζ1 -> functor ζ1 -> functor ζ2
[ σ ]p (▹ A) = [ σ ]v A
[ σ ]p (μ F) = μ ([ psub-ext σ ]p F)
[ σ ]p (A ⇝ B) = A ⇝ ([ σ ]p B)
[ σ ]p (A ∧ B) = ([ σ ]p A) ∧ ([ σ ]p B)
[ σ ]p ⊤ = ⊤

[_/x]p : ∀ {ζ} -> functor ζ -> functor (ζ , *) -> functor ζ
[ M /x]p A = [ id-psub , M ]p A

mutual 
 data rtm (Γ : ctx tp) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
  π₁ : ∀ {T S} -> rtm Γ (T ∧ S) -> rtm Γ T
  π₂ : ∀ {T S} -> rtm Γ (T ∧ S) -> rtm Γ S
  -- TODO: Try other forms for this rule..
  fold : ∀ F {C} -> rtm Γ (μ F) -> ntm (⊡ , [ C /x]p F) C -> rtm Γ C
 data ntm (Γ : ctx tp) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {F} -> rtm Γ (μ F) -> ntm Γ (μ F)
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T ∧ S)
  tt : ntm Γ ⊤
  inj : ∀ F -> ntm Γ ([ μ F /x]p F) -> ntm Γ (μ F)

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v ([ σ ]v y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 rappSubst σ (fold F R N) = fold F (rappSubst σ R) N
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (vsub-ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt
 nappSubst σ (inj F N) = inj F (nappSubst σ N)

mutual
 [_]r : ∀ {Γ Δ S} -> gsubst Δ (rtm Γ) -> rtm Δ S -> rtm Γ S
 [ σ ]r R = {!!}
 [_]n : ∀ {Γ Δ S} -> gsubst Δ (rtm Γ) -> ntm Δ S -> ntm Γ S 
 [ σ ]n N = {!!}

η-expand : ∀ {T} {Γ} -> rtm Γ T -> ntm Γ T
η-expand {▹ ()} R
η-expand {μ F} R = neut R
η-expand {A ⇝ B} R = ƛ (η-expand ((rappSubst wkn-vsub R) · (η-expand (v top))))
η-expand {A ∧ B} R = < (η-expand (π₁ R)) , (η-expand (π₂ R)) >
η-expand {⊤} R = tt

data arrow : ∀ {ζ} -> psub ⊡ ζ -> psub ⊡ ζ -> Set where
 ⊡ : arrow unit unit
 _,_ : ∀ {ζ} {σ1 σ2 : psub ⊡ ζ} (θ : arrow σ1 σ2) {A B} (N : ntm (⊡ , A) B) -> arrow {ζ , *} (σ1 , A) (σ2 , B)

arrow-lookup : ∀ {ζ} {σ1 σ2 : psub ⊡ ζ} (θ : arrow σ1 σ2) (A : var ζ *) -> ntm (⊡ , ([ σ1 ]v A)) ([ σ2 ]v A)
arrow-lookup {ζ} θ A = {!!}

lemma : ∀ {ζ1 ζ2} A (σ : psub ζ1 ζ2) B -> ([ A /x]p ([ psub-ext σ ]p B)) ≡ ([ σ , A ]p B)
lemma A σ B = {!!}

map : ∀ {ζ} F {σ1 σ2 : psub ⊡ ζ} (θ : arrow σ1 σ2) -> ntm (⊡ , [ σ1 ]p F) ([ σ2 ]p F)
map (▹ A) θ = arrow-lookup θ A
map (μ F) {σ1} {σ2} θ = η-expand (fold ([ psub-ext σ1 ]p F) (v top) (inj ([ psub-ext σ2 ]p F)
  (subst₂ (λ α β → ntm (⊡ , α) β)
    (sym (lemma (μ ([ gmap (λ {T} → [ unit ]pv) σ2 , ▹ top ]p F)) σ1 F))
    (sym (lemma (μ ([ gmap (λ {T} → [ unit ]pv) σ2 , ▹ top ]p F)) σ2 F))
  (map F (θ , (η-expand (v top)))))))
map (A ⇝ B) θ = ƛ ([ unit , ((v (pop top)) · (η-expand (v top))) ]n (map B θ))
map (A ∧ B) θ = < [ unit , (π₁ (v top)) ]n (map A θ) , [ unit , (π₂ (v top)) ]n (map B θ) >
map ⊤ θ = tt

sem : (Γ : ctx tp) -> tp -> Set
sem Γ (▹ ())
sem Γ (μ F) = ntm Γ (μ F)
sem Γ (A ⇝ B) = (Δ : _) (σ : vsubst Γ Δ) → sem Δ A → sem Δ B
sem Γ (A ∧ B) = sem Γ A × sem Γ B
sem Γ ⊤ = Unit


appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (▹ ()) σ M
appSubst (μ F) σ M = nappSubst σ M
appSubst (A ⇝ B) σ M = λ Δ σ' x → M Δ (σ' ∘v σ) x
appSubst (A ∧ B) σ M = (appSubst A σ (proj₁ M)) , (appSubst B σ (proj₂ M))
appSubst ⊤ σ M = unit

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {▹ ()} R
 reflect {μ F} R = neut R
 reflect {A ⇝ B} R = λ Δ σ x → reflect ((rappSubst σ R) · reify x)
 reflect {A ∧ B} R = reflect (π₁ R) , reflect (π₂ R)
 reflect {⊤} R = unit

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {▹ ()} t
 reify {μ F} t = t
 reify {A ⇝ B} t = ƛ (reify (t _ wkn-vsub (reflect {A} (v top))))
 reify {A ∧ B} t = < reify (proj₁ t) , reify (proj₂ t) >
 reify {⊤} t = tt


mutual
 srSubst : ∀ {Γ Δ T} -> gsubst Γ (sem Δ) -> rtm Γ T -> sem Δ T
 srSubst θ (v y) = lookup θ y
 srSubst θ (R · N) = srSubst θ R _ id-vsub (sSubst θ N)
 srSubst θ (π₁ R) = proj₁ (srSubst θ R)
 srSubst θ (π₂ R) = proj₂ (srSubst θ R)
 srSubst θ (fold F R N) = {!!}

 sSubst : ∀ {Γ Δ T} -> gsubst Γ (sem Δ) -> ntm Γ T -> sem Δ T
 sSubst θ (ƛ M) = λ Δ σ s → sSubst (gmap (appSubst _ σ) θ , s) M
 sSubst θ (neut y) = srSubst θ y
 sSubst θ < M , N > = sSubst θ M , sSubst θ N
 sSubst θ tt = unit
 sSubst θ (inj F N) = inj F (reify (sSubst θ N))

{-
nSubst : ctx -> ctx -> Set
nSubst Γ Δ = ∀ {S} -> var Γ S -> ntm Δ S
cut : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Γ T -> ntm Δ T
cut θ t = reify (sSubst (λ x → sSubst (λ x' → reflect (v x')) (θ x)) t)

nv : ∀ {Γ T} -> var Γ T -> ntm Γ T
nv x = reify (reflect (v x))

nExtend : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Δ T -> nSubst (Γ , T) Δ
nExtend θ N z = N
nExtend θ N (s y) = θ y

nId : ∀ {Γ} -> nSubst Γ Γ
nId x = nv x

napp : ∀ {Γ T S} -> ntm Γ (T ⇝ S) -> ntm Γ T -> ntm Γ S
napp (ƛ N) M = cut (nExtend nId M) N

nfst : ∀ {Γ T S} -> ntm Γ (T × S) -> ntm Γ T
nfst < M , N > = M

nsnd : ∀ {Γ T S} -> ntm Γ (T × S) -> ntm Γ S
nsnd < M , N > = N
-}

data tm (Γ : ctx tp) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 π₁ : ∀ {T S} -> tm Γ (T ∧ S) -> tm Γ T
 π₂ : ∀ {T S} -> tm Γ (T ∧ S) -> tm Γ S
 <_,_> : ∀ {T S} -> tm Γ T -> tm Γ S -> tm Γ (T ∧ S)
 tt : tm Γ ⊤
 inj : ∀ F -> tm Γ ([ μ F /x]p F) -> tm Γ (μ F)
 fold : ∀ F {C} -> tm Γ (μ F) -> tm (⊡ , [ C /x]p F) C -> tm Γ C

{-
complete : ∀ {Γ T} -> tm Γ T -> ntm Γ T
complete (v y) = nv y
complete (M · N) = napp (complete M) (complete N)
complete (ƛ M) = ƛ (complete M)
complete (π₁ M) = nfst (complete M)
complete (π₂ N) = nsnd (complete N)
complete < M , N > = < complete M , complete N >
complete tt = tt
-}

-- Traditional nbe


fold' : ∀ {Γ} F {C} -> ntm Γ (μ F) -> ntm (⊡ , [ C /x]p F) C -> ntm Γ C
fold' F (neut y) N = η-expand (fold F y N)
fold' F (inj .F y) N = {!!}  

eval : ∀ {Γ Δ T} -> gsubst Γ (sem Δ) -> tm Γ T -> sem Δ T
eval θ (v y) = [ θ ]v y
eval θ (M · N) = eval θ M _ id-vsub (eval θ N)
eval θ (ƛ M) = λ _ σ s -> eval ((gmap (appSubst _ σ) θ) , s) M
eval θ (π₁ M) = proj₁ (eval θ M)
eval θ (π₂ N) = proj₂ (eval θ N)
eval θ < M , N > = eval θ M , eval θ N
eval θ tt = unit
eval θ (inj F M) = inj F (reify (eval θ M))
eval θ (fold F M N) with eval θ M --| eval (unit , {!!}) N
... | q1 = {!!}

{-

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval (λ x → reflect (v x)) M) -}
