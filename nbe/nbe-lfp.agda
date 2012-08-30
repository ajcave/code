{-# OPTIONS --type-in-type --no-positivity-check #-}
-- Type in type is temporary until I make FinMap universe polymorphic
module nbe-lfp where
open import FinMap
open import Product
open import Data.Unit hiding (⊤)

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

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
  neut : ∀ {A} -> rtm Γ A -> ntm Γ A -- don't worry about eta longness for now
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T ∧ S)
  tt : ntm Γ ⊤
  inj : ∀ F -> ntm Γ ([ μ F /x]p F) -> ntm Γ (μ F)

mutual
 data μ⁺ {ζ} (F : functor (ζ , *)) (σ : gksubst ζ (ctx tp -> Set)) (Γ : ctx tp) : Set where
  ⟨_⟩ : ⟦ F ⟧ (σ , μ⁺ F σ) Γ -> μ⁺ F σ Γ

 ⟦_⟧ : ∀ {ζ} -> (F : functor ζ) (σ : gksubst ζ (ctx tp -> Set)) -> (Γ : ctx tp) -> Set
 ⟦_⟧ (▹ A) σ Γ = lookup σ A Γ
 ⟦_⟧ (μ F) σ Γ = μ⁺ F σ Γ
 ⟦_⟧ (A ⇝ B) σ Γ = (Δ : _) → vsubst Γ Δ → ⟦ A ⟧ unit Δ → ⟦ B ⟧ σ Δ
 ⟦_⟧ (A ∧ B) σ Γ = ⟦ A ⟧ σ Γ × ⟦ B ⟧ σ Γ
 ⟦_⟧ ⊤ σ Γ = Unit

 sem : (Γ : ctx tp) -> tp -> Set
 sem Γ T = ⟦ T ⟧ unit Γ

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

functorial₀ : (F : ctx tp -> Set) -> Set
functorial₀ F = ∀ {Γ Δ} -> (σ : vsubst Γ Δ) -> (x : F Γ) -> F Δ

⟦⟧-functorial₀ : ∀ {ζ} F -> (θ : gksubst ζ (ctx tp -> Set)) (θf : gsubst-pred functorial₀ θ) -> functorial₀ (⟦ F ⟧ θ)
⟦⟧-functorial₀ (▹ A) θ θf σ t = lookup-pred θf A σ t
⟦⟧-functorial₀ (μ F) θ θf σ ⟨ y ⟩ = ⟨ (⟦⟧-functorial₀ F (θ , (μ⁺ F θ)) (θf , ⟦⟧-functorial₀ (μ F) θ θf) σ y) ⟩
⟦⟧-functorial₀ (A ⇝ B) θ θf σ t = λ Δ σ' x → t _ (σ' ∘v σ) x
⟦⟧-functorial₀ (A ∧ B) θ θf σ t = (⟦⟧-functorial₀ A θ θf σ (proj₁ t)) , (⟦⟧-functorial₀ B θ θf σ (proj₂ t))
⟦⟧-functorial₀ ⊤ θ θf σ t = unit

{-
appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = rappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s
appSubst (T × S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
appSubst unit σ tt = tt

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)
 reflect {T × S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = neut M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z))))
 reify {T × S} M = < reify (_*_.fst M) , reify (_*_.snd M) >
 reify {unit} tt = tt

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

-- Here we have admissibility of cut for ntm. Not necessary for nbe,
-- but nice to state.
mutual
 srSubst : ∀ {Γ Δ T} -> subst Γ Δ -> rtm Γ T -> sem Δ T
 srSubst θ (v y) = θ y
 srSubst θ (R · N) = srSubst θ R _ id (sSubst θ N)
 srSubst θ (π₁ R) = _*_.fst (srSubst θ R)
 srSubst θ (π₂ R) = _*_.snd (srSubst θ R)

 sSubst : ∀ {Γ Δ T} -> subst Γ Δ -> ntm Γ T -> sem Δ T
 sSubst θ (ƛ M) = λ Δ σ s → sSubst (extend (λ x → appSubst _ σ (θ x)) s) M
 sSubst θ (neut y) = srSubst θ y
 sSubst θ < M , N > = sSubst θ M , sSubst θ N
 sSubst θ tt = tt

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

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 π₁ : ∀ {T S} -> tm Γ (T × S) -> tm Γ T
 π₂ : ∀ {T S} -> tm Γ (T × S) -> tm Γ S
 <_,_> : ∀ {T S} -> tm Γ T -> tm Γ S -> tm Γ (T × S)
 tt : tm Γ unit

complete : ∀ {Γ T} -> tm Γ T -> ntm Γ T
complete (v y) = nv y
complete (M · N) = napp (complete M) (complete N)
complete (ƛ M) = ƛ (complete M)
complete (π₁ M) = nfst (complete M)
complete (π₂ N) = nsnd (complete N)
complete < M , N > = < complete M , complete N >
complete tt = tt

-- Traditional nbe
eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
eval θ (M · N) = eval θ M _ id (eval θ N)
eval θ (ƛ M) = λ _ σ s -> eval (extend (λ x → appSubst _ σ (θ x)) s) M
eval θ (π₁ M) = _*_.fst (eval θ M)
eval θ (π₂ N) = _*_.snd (eval θ N)
eval θ < M , N > = eval θ M , eval θ N
eval θ tt = tt

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval (λ x → reflect (v x)) M) -}
