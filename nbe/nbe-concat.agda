module nbe-concat where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Unit : Set where
 constructor tt

postulate
 atomic_tp : Set

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

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
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)


_<<_ : ctx -> ctx -> ctx
Γ << ⊡ = Γ
Γ << (Γ' , T) = (Γ << Γ') , T

sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = rtm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> sem (Γ << Δ) T → sem (Γ << Δ) S 

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

mutual
 rappWkn : ∀ {Γ S} Δ -> rtm Γ S -> rtm (Γ << Δ) S
 rappWkn Δ R = {!!}
 nappWkn : ∀ {Γ S} Δ -> ntm Γ S -> ntm (Γ << Δ) S
 nappWkn Δ N = {!!}

appWkn : ∀ {Γ} Δ S -> sem Γ S -> sem (Γ << Δ) S
appWkn Δ (atom A) t = rappWkn Δ t
appWkn {Γ} Δ (T ⇝ S) t = f
 where f : ∀ Δ' (x : sem ((Γ << Δ) << Δ') T) -> sem ((Γ << Δ) << Δ') S
       f Δ' x with t (Δ << Δ')
       ... | q = {!!}

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = N
 reflect {T ⇝ S} N = λ Δ x → reflect (rappWkn Δ N · (reify x))

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = neut M
 reify {T ⇝ S} M = ƛ (reify (M (⊡ , T) (reflect (v z))))

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y


data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)


-- Traditional nbe
eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
eval θ (M · N) = eval θ M ⊡ (eval θ N)
eval θ (ƛ M) = λ Δ x → eval (extend (λ x' → appWkn Δ _ (θ x')) x) M

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval (λ x → reflect (v x)) M) 
