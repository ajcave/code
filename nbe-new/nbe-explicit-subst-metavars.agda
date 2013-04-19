module nbe-explicit-subst-metavars where
open import FinMap
open import Product
open import Unit

postulate
 atomic_tp : Set

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp
 _⊗_ : (T S : tp) -> tp
 unit : tp

data mtp : Set where
 _[_] : (A : tp) -> (Ψ : ctx tp) -> mtp
 ♯_[_] : (A : tp) -> (Ψ : ctx tp) -> mtp
 $_[_] : (Φ : ctx tp) -> (Ψ : ctx tp) -> mtp

mutual 
 data rtm (Δ : ctx mtp) (Γ : ctx tp) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Δ Γ T
  _·_ : ∀ {T S} -> rtm Δ Γ (T ⇝ S) -> ntm Δ Γ T -> rtm Δ Γ S
  π₁ : ∀ {T S} -> rtm Δ Γ (T ⊗ S) -> rtm Δ Γ T
  π₂ : ∀ {T S} -> rtm Δ Γ (T ⊗ S) -> rtm Δ Γ S
  _[_] : ∀ {Φ A} -> var Δ (A [ Φ ]) -> nsub Δ Γ Φ -> rtm Δ Γ A
  top : ∀ {Φ A} -> rsub Δ Γ (Φ , A) -> rtm Δ Γ A
 data ntm (Δ : ctx mtp) (Γ : ctx tp) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm Δ (Γ , T) S -> ntm Δ Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Δ Γ (atom A) -> ntm Δ Γ (atom A)
  <_,_> : ∀ {T S} -> (M : ntm Δ Γ T) -> (N : ntm Δ Γ S) -> ntm Δ Γ (T ⊗ S)
  tt : ntm Δ Γ unit
 nsub : (Δ : ctx mtp) (Ψ : ctx tp) (Φ : ctx tp) -> Set
 nsub Δ Ψ Φ = gsubst Φ (ntm Δ Ψ)
--  id : ∀ {Ψ} -> sub Δ Ψ Ψ -- only necessary if we have context vars?
 data rsub (Δ : ctx mtp) : (Ψ : ctx tp) (Φ : ctx tp) -> Set where
  _[_] : ∀ {Ψ Φ Φ'} -> var Δ ($ Φ [ Ψ ]) -> nsub Δ Φ' Ψ -> rsub Δ Φ' Φ
  ↑ : ∀ {Ψ Φ A} -> rsub Δ Ψ (Φ , A) -> rsub Δ Ψ Φ


sem : (Δ : ctx mtp) (Γ : ctx tp) -> (T : tp) -> Set
sem Δ Γ (atom A) = rtm Δ Γ (atom A)
sem Δ Γ (T ⇝ S) = ∀ Γ' -> vsubst Γ Γ' -> sem Δ Γ' T → sem Δ Γ' S 
sem Δ Γ (T ⊗ S) = sem Δ Γ T × sem Δ Γ S
sem Δ Γ unit = Unit


mutual
 rappSubst : ∀ {Δ Γ Γ' S} -> vsubst Γ' Γ -> rtm Δ Γ' S -> rtm Δ Γ S
 rappSubst σ (v y) = v (lookup σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 rappSubst σ (u [ σ' ]) = u [ nsappSubst σ σ' ]
 rappSubst σ (top ρ) = top (rsappSubst σ ρ)
 nappSubst : ∀ {Δ Γ Γ' S} -> vsubst Γ' Γ -> ntm Δ Γ' S -> ntm Δ Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (vsub-ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt
 rsappSubst : ∀ {Δ Γ Γ' S} -> vsubst Γ' Γ -> rsub Δ Γ' S -> rsub Δ Γ S
 rsappSubst σ (s [ σ' ]) = s [ nsappSubst σ σ' ]
 rsappSubst σ (↑ ρ) = ↑ (rsappSubst σ ρ)
 nsappSubst : ∀ {S Δ Γ Γ'} -> vsubst Γ' Γ -> nsub Δ Γ' S -> nsub Δ Γ S
 nsappSubst {⊡} σ σ' = tt
 nsappSubst {ψ , T} σ (σ' , N) = nsappSubst σ σ' , nappSubst σ N


appSubst : ∀ {Δ Γ Γ'} S -> vsubst Γ' Γ -> sem Δ Γ' S -> sem Δ Γ S
appSubst (atom A) σ M = rappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘v σ) s
appSubst (T ⊗ S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
appSubst unit σ tt = tt


subst : ctx mtp -> ctx tp -> ctx tp -> Set
subst Δ Γ Γ' = gsubst Γ (sem Δ Γ')

{-
rsub-expand : ∀ {Ψ Δ Γ} -> rsub Δ Γ Ψ -> nsub Δ Γ Ψ
rsub-expand {⊡} ρ = tt
rsub-expand {ψ , T} ρ = rsub-expand (↑ ρ) , {!!} -}

mutual
 reflect : ∀ {T Δ Γ} -> rtm Δ Γ T -> sem Δ Γ T
 reflect {atom A} N = N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)
 reflect {T ⊗ S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt

 reify : ∀ {T Δ Γ} -> sem Δ Γ T -> ntm Δ Γ T
 reify {atom A} M = neut M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn-vsub (reflect (v top))))
 reify {T ⊗ S} M = < reify (_×_.proj₁ M) , reify (_×_.proj₂ M) >
 reify {unit} tt = tt

 reflects : ∀ {T Δ Γ} -> rsub Δ Γ T -> subst Δ T Γ
 reflects {⊡} ρ = tt
 reflects {ψ , T} ρ = (reflects (↑ ρ)) , reflect (top ρ)

 reifys : ∀ {T Δ Γ} -> subst Δ T Γ -> nsub Δ Γ T
 reifys θ = gmap reify θ


mutual
 data tm (Δ : ctx mtp) : (Γ : ctx tp) (T : tp) -> Set where
  v : ∀ {Γ T} -> var Γ T -> tm Δ Γ T
  _·_ : ∀ {Γ T S} -> tm Δ Γ (T ⇝ S) -> tm Δ Γ T -> tm Δ Γ S
  ƛ : ∀ {Γ T S} -> tm Δ (Γ , T) S -> tm Δ Γ (T ⇝ S)
  π₁ : ∀ {Γ T S} -> tm Δ Γ (T ⊗ S) -> tm Δ Γ T
  π₂ : ∀ {Γ T S} -> tm Δ Γ (T ⊗ S) -> tm Δ Γ S
  <_,_> : ∀ {Γ T S} -> tm Δ Γ T -> tm Δ Γ S -> tm Δ Γ (T ⊗ S)
  tt : ∀ {Γ} -> tm Δ Γ unit
  mv : ∀ {A Ψ} -> var Δ (A [ Ψ ]) -> tm Δ Ψ A
  _[_] : ∀ {Ψ Φ A} -> tm Δ Φ A -> sub Δ Ψ Φ -> tm Δ Ψ A
 data sub (Δ : ctx mtp) : (Ψ : ctx tp) (Φ : ctx tp) -> Set where
  sv : ∀ {Ψ Φ} -> var Δ ($ Φ [ Ψ ]) -> sub Δ Ψ Φ
  _[_] : ∀ {Ψ Φ Φ'} -> sub Δ Ψ Φ -> sub Δ Φ' Ψ -> sub Δ Φ' Φ
  _,_ : ∀ {Ψ Φ A} -> sub Δ Ψ Φ -> tm Δ Ψ A -> sub Δ Ψ (Φ , A)
  id : ∀ {Ψ} -> sub Δ Ψ Ψ
  · : ∀ {Ψ} -> sub Δ Ψ ⊡
  ↑ : ∀ {Ψ A} -> sub Δ (Ψ , A) Ψ

-- Traditional nbe

mutual
 eval : ∀ {Γ Γ' Δ T} -> subst Δ Γ Γ' -> tm Δ Γ T -> sem Δ Γ' T
 eval θ (v y) = lookup θ y
 eval θ (M · N) = eval θ M _ id-vsub (eval θ N)
 eval θ (ƛ M) = λ _ σ s -> eval (gmap (appSubst _ σ) θ , s) M
 eval θ (π₁ M) = _×_.proj₁ (eval θ M)
 eval θ (π₂ N) = _×_.proj₂ (eval θ N)
 eval θ < M , N > = eval θ M , eval θ N
 eval θ tt = tt
 eval θ (mv u) = reflect (u [ reifys θ ])
 eval θ (N [ σ ]) = eval (evals θ σ) N

 evals : ∀ {Γ Γ' Δ Γ''} -> subst Δ Γ Γ' -> sub Δ Γ Γ'' -> subst Δ Γ'' Γ'
 evals θ (sv y) = reflects (y [ reifys θ ])
 evals θ (σ1 [ σ2 ]) = evals (evals θ σ2) σ1
 evals θ (σ , N) = evals θ σ , eval θ N
 evals θ id = θ
 evals θ · = tt
 evals (θ , r) ↑ = θ

ids : ∀ {Γ Δ} -> subst Δ Γ Γ
ids {⊡} = tt
ids {ψ , T} = (gmap (appSubst _ wkn-vsub) ids) , reflect (v top)

nbe : ∀ {Γ Δ T} -> tm Δ Γ T -> ntm Δ Γ T
nbe M = reify (eval ids M) 

