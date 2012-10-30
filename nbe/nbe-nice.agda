module nbe-nice where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Unit : Set where
 constructor tt

data tp : Set where
 i : tp -- Some base type (proposition).
 _⇝_ : (T S : tp) -> tp
 _×_ : (T S : tp) -> tp
 unit : tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

-- Well-scoped, well-typed de Bruijn indices
data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

-- β-normal, η-long terms
mutual
 -- Neutral terms
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
  π₁ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ T
  π₂ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ S
 -- Normal terms
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  -- Restrict terms to be η-long by only embedding neutral terms at base type, not arrow type or product type
  neut : rtm Γ i -> ntm Γ i
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T × S)
  tt : ntm Γ unit

-- Variable-for-variable substitutions (weakening, exchange, and contraction)
vsubst : ctx -> ctx -> Set 
vsubst Γ Δ = ∀ {U} -> var Γ U -> var Δ U

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

mutual
 -- Simulaneous substitution of variables for variables in neutral/normal terms
 -- (Means we can weaken terms)
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

-- Types are semantically interpreted as functors from ctx to Set
-- i.e. Types are interpreted as objects of the category of presheaves
-- eval (below) interprets terms as arrows in the category of presheaves
sem : (T : tp) -> (ctx -> Set)
sem i Γ = ntm Γ i
                -- This is the exponential in the category of presheaves
sem (T ⇝ S) Γ = ∀ Δ -> vsubst Γ Δ -> sem T Δ → sem S Δ 
sem (T × S) Γ = sem T Γ * sem S Γ
sem unit Γ = Unit

-- The arrow part of the functor
appSubst : ∀ {Γ Δ} S -> vsubst Γ Δ -> (sem S Γ -> sem S Δ)
appSubst i σ M = nappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s
appSubst (T × S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
appSubst unit σ tt = tt

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 -- Has the pattern of η-expansion
 -- These are structurally recursive on the type, which
 -- is an implicit argument.
 reflect : ∀ {T Γ} -> rtm Γ T -> sem T Γ
 reflect {i} N = neut N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)
 reflect {T × S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt

 reify : ∀ {T Γ} -> sem T Γ -> ntm Γ T
 reify {i} M = M
 -- Call M on a "fresh variable" by giving it the weakening substitution
 -- Nicer than using a global gensym
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z)))) 
 reify {T × S} M = < reify (_*_.fst M) , reify (_*_.snd M) >
 reify {unit} tt = tt

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 π₁ : ∀ {T S} -> tm Γ (T × S) -> tm Γ T
 π₂ : ∀ {T S} -> tm Γ (T × S) -> tm Γ S
 <_,_> : ∀ {T S} -> tm Γ T -> tm Γ S -> tm Γ (T × S)
 tt : tm Γ unit

-- Generalize semantic interpretation of types to contexts
subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem T Δ

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem T Δ -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

-- Interpret a term Γ ⊢ T as a natural transformation (subst Γ) ⇒ (sem T)
-- i.e. as an arrow in the category of presheaves
-- aka "evaluate in an environment"
eval : ∀ {Γ T} -> tm Γ T -> (∀ {Δ} -> subst Γ Δ -> sem T Δ)
eval (v y) θ = θ y
eval (M · N) θ = eval M θ _ id (eval N θ)
eval (ƛ M) θ = λ _ σ s -> eval M (extend (λ x → appSubst _ σ (θ x)) s)
eval (π₁ M) θ = _*_.fst (eval M θ)
eval (π₂ N) θ = _*_.snd (eval N θ)
eval < M , N > θ = eval M θ , eval N θ
eval tt θ = tt

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval M (λ x → reflect (v x)))

-- Termination checks, coverage checks.
-- Proves consistency of propositional logic

data False : Set where

noClosedNeutral : ∀ {A} -> rtm ⊡ A -> False
noClosedNeutral (v ())
noClosedNeutral (y · y') = noClosedNeutral y
noClosedNeutral (π₁ y) = noClosedNeutral y
noClosedNeutral (π₂ y) = noClosedNeutral y

-- There are no closed proofs of i
consistent : tm ⊡ i -> False
consistent t with nbe t
consistent t | neut R = noClosedNeutral R
