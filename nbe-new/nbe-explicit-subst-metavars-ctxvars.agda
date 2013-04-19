module nbe-explicit-subst-metavars-ctxvars where
open import FinMap
open import Product
open import Data.Product hiding (<_,_>; _×_)
open import Relation.Binary.PropositionalEquality hiding ([_]; subst)
open import Unit

postulate
 atomic_tp : Set

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp
 _⊗_ : (T S : tp) -> tp
 unit : tp

data sctx (Ω : ctx Unit) : Set where
 ⊡ : sctx Ω
 cv : var Ω tt -> sctx Ω
 _,_ : (ψ : sctx Ω) -> (T : tp) -> sctx Ω

data svar (Ω : ctx Unit) : (Γ : sctx Ω) -> tp -> Set  where
 top : ∀ {Γ T} -> svar Ω (Γ , T) T
 pop : ∀ {Γ T S} -> svar Ω Γ T -> svar Ω (Γ , S) T

data mtp (Ω : ctx Unit) : Set where
 _[_] : (A : tp) -> (Ψ : sctx Ω) -> mtp Ω
 ♯_[_] : (A : tp) -> (Ψ : sctx Ω) -> mtp Ω
 $_[_] : (Φ : sctx Ω) -> (Ψ : sctx Ω) -> mtp Ω

_<<_ : ∀ {Ω} -> sctx Ω -> ctx tp -> sctx Ω
Γ << ⊡ = Γ
Γ << (ψ , T) = (Γ << ψ) , T

data sgsubst {Ω : ctx Unit}  (A : sctx Ω -> tp -> Set) : (Γ Γ' : sctx Ω) -> Set where
 ⊡ : ∀ {Γ} -> sgsubst A Γ ⊡ 
 _,_ : ∀ {Γ Γ' T} -> sgsubst A Γ Γ' -> A Γ T -> sgsubst A Γ (Γ' , T)
 id : ∀ φ Ψ -> sgsubst A ((cv φ) << Ψ) (cv φ)


mutual 
 data rtm (Ω : ctx Unit) (Δ : ctx (mtp Ω)) (Γ : sctx Ω) : (T : tp) -> Set where
  v : ∀ {T} -> svar Ω Γ T -> rtm Ω Δ Γ T
  _·_ : ∀ {T S} -> rtm Ω Δ Γ (T ⇝ S) -> ntm Ω Δ Γ T -> rtm Ω Δ Γ S
  π₁ : ∀ {T S} -> rtm Ω Δ Γ (T ⊗ S) -> rtm Ω Δ Γ T
  π₂ : ∀ {T S} -> rtm Ω Δ Γ (T ⊗ S) -> rtm Ω Δ Γ S
  _[_] : ∀ {Φ A} -> var Δ (A [ Φ ]) -> nsub Ω Δ Γ Φ -> rtm Ω Δ Γ A
  top : ∀ {Φ A} -> rsub Ω Δ Γ (Φ , A) -> rtm Ω Δ Γ A
 data ntm (Ω : ctx Unit) (Δ : ctx (mtp Ω)) (Γ : sctx Ω) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm Ω Δ (Γ , T) S -> ntm Ω Δ Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Ω Δ Γ (atom A) -> ntm Ω Δ Γ (atom A)
  <_,_> : ∀ {T S} -> (M : ntm Ω Δ Γ T) -> (N : ntm Ω Δ Γ S) -> ntm Ω Δ Γ (T ⊗ S)
  tt : ntm Ω Δ Γ unit
 data nsub (Ω : ctx Unit) (Δ : ctx (mtp Ω)) : (Ψ : sctx Ω) (Φ : sctx Ω) -> Set where
  _,_ : ∀ {Ψ Φ A} -> nsub Ω Δ Ψ Φ -> ntm Ω Δ Ψ A -> nsub Ω Δ Ψ (Φ , A)
  ⊡ : ∀ {Ψ} -> nsub Ω Δ Ψ ⊡
  id : ∀ φ Ψ -> nsub Ω Δ ((cv φ) << Ψ) (cv φ)
  r : ∀ {φ Ψ} -> rsub Ω Δ Ψ (cv φ) -> nsub Ω Δ Ψ (cv φ)
 --nsub : (Ω : ctx Unit) (Δ : ctx (mtp Ω)) (Ψ : sctx Ω) (Φ : sctx Ω) -> Set
 --nsub Ω Δ Ψ Φ = sgsubst (ntm Ω Δ) Ψ Φ
 data rsub (Ω : ctx Unit) (Δ : ctx (mtp Ω)) : (Ψ : sctx Ω) (Φ : sctx Ω) -> Set where
  _[_] : ∀ {Ψ Φ Φ'} -> var Δ ($ Φ [ Ψ ]) -> nsub Ω Δ Φ' Ψ -> rsub Ω Δ Φ' Φ
--  id : ∀ {Ψ} -> rsub Ω Δ Ψ Ψ
  ↑ : ∀ {Ψ Φ A} -> rsub Ω Δ Ψ (Φ , A) -> rsub Ω Δ Ψ Φ

svsubst : {Ω : ctx Unit} (Γ Γ' : sctx Ω) -> Set
svsubst Γ Γ' = sgsubst (svar _) Γ Γ'

--svsubst Γ Γ' = ∀ {T} -> svar _ Γ T -> svar _ Γ' T

slookup : ∀ {Ω} {Γ Γ' T} -> svsubst Γ Γ' -> svar Ω Γ' T -> svar Ω Γ T
slookup (σ , x) top = x
slookup (σ , x) (pop y0) = slookup σ y0
slookup ⊡ ()
slookup (id _ _) ()

svwkn : ∀ {Ω} {Γ Γ' : sctx Ω} {T} -> svsubst Γ Γ' -> svsubst (Γ , T) Γ'
svwkn ⊡ = ⊡
svwkn (σ , x) = (svwkn σ) , (pop x)
svwkn (id φ Ψ) = id φ (Ψ , _)

sid : ∀ {Ω} {Γ : sctx Ω} -> svsubst Γ Γ
sid {Ω} {⊡} = ⊡
sid {Ω} {cv φ} = id φ ⊡
sid {Ω} {ψ , T} = (svwkn sid) , top

wkn-svsub : ∀ {Ω} {Γ : sctx Ω} {T} -> svsubst (Γ , T) Γ
wkn-svsub = svwkn sid

svsub-ext : ∀ {Ω} {Γ Γ' : sctx Ω} {T} -> svsubst Γ Γ' -> svsubst (Γ , T) (Γ' , T)
svsub-ext σ = svwkn σ , top

invert-id : ∀ Ψ {Ω Γ φ} -> svsubst {Ω} Γ (cv φ << Ψ) -> ∃ (λ Φ -> Γ ≡ (cv φ << Φ))
invert-id ⊡ {Ω} {.(cv φ << Ψ)} {φ} (id .φ Ψ) = Ψ , refl
invert-id (ψ , T) (σ , x) = invert-id ψ σ

svcomp : ∀ {Ω} {Γ Γ' Γ'' : sctx Ω} -> svsubst Γ Γ' -> svsubst Γ'' Γ -> svsubst Γ'' Γ'
svcomp ⊡ σ2 = ⊡
svcomp (σ1 , x) σ2 = (svcomp σ1 σ2) , (slookup σ2 x)
svcomp (id φ Ψ) σ2 with invert-id Ψ σ2
svcomp (id φ Ψ) σ2 | Φ , refl = id φ Φ

sem : {Ω : ctx Unit} (Δ : ctx (mtp Ω)) (Γ : sctx Ω) -> (T : tp) -> Set
sem Δ Γ (atom A) = rtm _ Δ Γ (atom A)
sem Δ Γ (T ⇝ S) = ∀ Γ' -> svsubst Γ' Γ -> sem Δ Γ' T → sem Δ Γ' S 
sem Δ Γ (T ⊗ S) = sem Δ Γ T × sem Δ Γ S
sem Δ Γ unit = Unit

mutual
 rappSubst : ∀ {Ω Δ Γ Γ' S} -> svsubst Γ Γ' -> rtm Ω Δ Γ' S -> rtm Ω Δ Γ S
 rappSubst σ (v y) = v (slookup σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 rappSubst σ (u [ σ' ]) = u [ nsappSubst σ σ' ]
 rappSubst σ (top ρ) = top (rsappSubst σ ρ)
 nappSubst : ∀ {Ω Δ Γ Γ' S} -> svsubst Γ Γ' -> ntm Ω Δ Γ' S -> ntm Ω Δ Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (svsub-ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt
 rsappSubst : ∀ {Ω Δ Γ Γ' S} -> svsubst Γ Γ' -> rsub Ω Δ Γ' S -> rsub Ω Δ Γ S
 rsappSubst σ (s [ σ' ]) = s [ nsappSubst σ σ' ]
 rsappSubst σ (↑ ρ) = ↑ (rsappSubst σ ρ)
 nsappSubst : ∀ {Ω S Δ Γ Γ'} -> svsubst Γ Γ' -> nsub Ω Δ Γ' S -> nsub Ω Δ Γ S
 nsappSubst σ ⊡ = ⊡
 nsappSubst σ (σ' , N) = nsappSubst σ σ' , nappSubst σ N
 nsappSubst σ (id φ Ψ) with invert-id Ψ σ
 nsappSubst σ (id φ Ψ) | Φ , refl = id φ Φ
 nsappSubst σ (r ρ) = r (rsappSubst σ ρ)


appSubst : ∀ {Ω Δ Γ Γ'} S -> svsubst Γ Γ' -> sem {Ω} Δ Γ' S -> sem Δ Γ S
appSubst (atom A) σ M = rappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (svcomp σ σ') s
appSubst (T ⊗ S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
appSubst unit σ tt = tt



--subst : ∀ {Ω} -> ctx (mtp Ω) -> sctx Ω -> sctx Ω -> Set
--subst Δ Γ Γ' = sgsubst (sem Δ) Γ Γ'

mutual
 reflect : ∀ {T Ω Δ Γ} -> rtm Ω Δ Γ T -> sem Δ Γ T
 reflect {atom A} N = N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)
 reflect {T ⊗ S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt

 reify : ∀ {T Ω Δ Γ} -> sem Δ Γ T -> ntm Ω Δ Γ T
 reify {atom A} M = neut M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn-svsub (reflect (v top))))
 reify {T ⊗ S} M = < reify (_×_.proj₁ M) , reify (_×_.proj₂ M) >
 reify {unit} tt = tt

data subst {Ω} (Δ : ctx (mtp Ω)) : (Ψ : sctx Ω) (Φ : sctx Ω) -> Set where
 _,_ : ∀ {Ψ Φ A} -> subst Δ Ψ Φ -> sem Δ Ψ A -> subst Δ Ψ (Φ , A)
 ⊡ : ∀ {Ψ} -> subst Δ Ψ ⊡
 id : ∀ φ Ψ -> subst Δ ((cv φ) << Ψ) (cv φ)
 r : ∀ {φ Ψ} -> rsub Ω Δ Ψ (cv φ) -> subst Δ Ψ (cv φ)

semlookup : ∀ {Ω} {Δ Γ Γ' T} -> subst Δ Γ Γ' -> svar Ω Γ' T -> sem Δ Γ T
semlookup (θ , y) top = y
semlookup (θ , y) (pop y') = semlookup θ y'
semlookup ⊡ ()
semlookup (id φ Ψ) ()
semlookup (r ρ) ()

semcomp : ∀ {Ω} {Δ} {Γ Γ' Γ'' : sctx Ω} -> subst Δ Γ Γ' -> svsubst Γ'' Γ -> subst Δ Γ'' Γ'
semcomp (θ , s) σ = (semcomp θ σ) , (appSubst _ σ s)
semcomp ⊡ σ = ⊡
semcomp (id φ Ψ) σ with invert-id Ψ σ
... | Φ , refl = id φ Φ
semcomp (r y) σ = r (rsappSubst σ y)

mutual
 reflects : ∀ {Ω T Δ Γ} -> rsub Ω Δ Γ T -> subst Δ Γ T
 reflects {Ω} {⊡} ρ = ⊡
 reflects {Ω} {ψ , T} ρ = (reflects (↑ ρ)) , reflect (top ρ)
 reflects {Ω} {cv φ} ρ = r ρ

 reifys : ∀ {Ω T Δ Γ} -> subst Δ Γ T -> nsub Ω Δ Γ T
 reifys {Ω} {⊡} θ = ⊡
 reifys {Ω} {cv φ} (id .φ Ψ) = id φ Ψ
 reifys {Ω} {cv φ} (r ρ) = r ρ
 reifys {Ω} {ψ , T} (θ , N) = reifys θ , reify N


mutual
 data tm {Ω} (Δ : ctx (mtp Ω)) : (Γ : sctx Ω) (T : tp) -> Set where
  v : ∀ {Γ T} -> svar Ω Γ T -> tm Δ Γ T
  _·_ : ∀ {Γ T S} -> tm Δ Γ (T ⇝ S) -> tm Δ Γ T -> tm Δ Γ S
  ƛ : ∀ {Γ T S} -> tm Δ (Γ , T) S -> tm Δ Γ (T ⇝ S)
  π₁ : ∀ {Γ T S} -> tm Δ Γ (T ⊗ S) -> tm Δ Γ T
  π₂ : ∀ {Γ T S} -> tm Δ Γ (T ⊗ S) -> tm Δ Γ S
  <_,_> : ∀ {Γ T S} -> tm Δ Γ T -> tm Δ Γ S -> tm Δ Γ (T ⊗ S)
  tt : ∀ {Γ} -> tm Δ Γ unit
  mv : ∀ {A Ψ} -> var Δ (A [ Ψ ]) -> tm Δ Ψ A
  _[_] : ∀ {Ψ Φ A} -> tm Δ Φ A -> sub Δ Ψ Φ -> tm Δ Ψ A
 data sub {Ω} (Δ : ctx (mtp Ω)) : (Ψ : sctx Ω) (Φ : sctx Ω) -> Set where
  sv : ∀ {Ψ Φ} -> var Δ ($ Φ [ Ψ ]) -> sub Δ Ψ Φ
  _[_] : ∀ {Ψ Φ Φ'} -> sub Δ Ψ Φ -> sub Δ Φ' Ψ -> sub Δ Φ' Φ
  _,_ : ∀ {Ψ Φ A} -> sub Δ Ψ Φ -> tm Δ Ψ A -> sub Δ Ψ (Φ , A)
  id : ∀ {Ψ} -> sub Δ Ψ Ψ
  · : ∀ {Ψ} -> sub Δ Ψ ⊡
  ↑ : ∀ {Ψ A} -> sub Δ (Ψ , A) Ψ


-- Traditional nbe

mutual
 eval : ∀ {Ω Γ Γ' Δ T} -> subst {Ω} Δ Γ' Γ -> tm Δ Γ T -> sem Δ Γ' T
 eval θ (v y) = semlookup θ y
 eval θ (M · N) = eval θ M _ sid (eval θ N)
 eval θ (ƛ M) = λ Γ'' σ s -> eval (semcomp θ σ , s) M
 eval θ (π₁ M) = _×_.proj₁ (eval θ M)
 eval θ (π₂ N) = _×_.proj₂ (eval θ N)
 eval θ < M , N > = eval θ M , eval θ N
 eval θ tt = tt
 eval θ (mv u) = reflect (u [ reifys θ ])
 eval θ (N [ σ ]) = eval (evals θ σ) N

 evals : ∀ {Ω Γ Γ' Δ Γ''} -> subst {Ω} Δ Γ' Γ -> sub Δ Γ Γ'' -> subst Δ Γ' Γ''
 evals θ (sv y) = reflects (y [ reifys θ ])
 evals θ (σ1 [ σ2 ]) = evals (evals θ σ2) σ1
 evals θ (σ , N) = evals θ σ , eval θ N
 evals θ id = θ
 evals θ · = ⊡
 evals (θ , s) ↑ = θ


ids : ∀ {Ω Γ Δ} -> subst {Ω} Δ Γ Γ
ids {Ω} {⊡} = ⊡
ids {Ω} {ψ , T} = (semcomp ids wkn-svsub) , (reflect (v top))
ids {Ω} {cv φ} = id φ ⊡

nbe : ∀ {Ω Γ Δ T} -> tm Δ Γ T -> ntm Ω Δ Γ T
nbe M = reify (eval ids M) 


