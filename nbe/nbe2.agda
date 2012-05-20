
module nbe2 where

postulate
 atomic_tp : Set
 i : atomic_tp

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

record Σ_ {A : Set} (B : A -> Set) : Set where
 constructor _,_ 
 field
    fst : A
    snd : B fst

record _×_ (A B : Set) : Set where
 constructor _,_
 field
    fst : A
    snd : B

data _==_ {A : Set} (x : A) : A -> Set where
 refl : x == x


mutual 
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)

mutual
 sem : (Γ : ctx) -> (T : tp) -> Set
 sem Γ (atom A) = tm Γ (atom A)
 sem Γ (T ⇝ S) = ∀ {Δ} -> vsubst Γ Δ -> sem Δ T → sem Δ S 

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> tm Δ S -> tm Γ S
nappSubst σ (v y) = v (σ y)
nappSubst σ (M · N) = nappSubst σ M · nappSubst σ N
nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = nappSubst σ M
appSubst (T ⇝ S) σ M = λ σ' → λ s → M (σ' ∘ σ) s

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {Γ} T -> tm Γ T -> sem Γ T
 reflect (atom A) N = N
 reflect (T ⇝ S) N = λ σ -> λ s → reflect S (nappSubst σ N · reify T s)

 reify : ∀ {Γ} T -> sem Γ T -> tm Γ T
 reify (atom A) M = M
 reify (T ⇝ S) M = ƛ (reify S (M wkn (reflect T (v z))))

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T


extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
eval θ (M · N) with eval θ M
eval θ (M · N) | f = ? --f id (eval θ N)
eval θ (ƛ M) = λ σ → λ s → eval (extend (λ x → appSubst _ σ (θ x)) s) M

--reflect : ∀ {Γ T} -> neu Γ T -> sem Γ T
--reflect {T = atom P} R = neut R
--reflect {T = U ⇝ S} R = ƛ (λ σ → λ s → reflect (nappSubst σ R · s))


--mutual
-- reify : ∀ {Γ T} -> sem Γ T -> tm Γ T
-- reify (neut R) = nreify R
-- reify (ƛ f) = ƛ (reify (f wkn (reflect (v z))))
 
-- nreify : ∀ {Γ T} -> neu Γ T -> tm Γ T
-- nreify (v y) = v y
-- nreify (R · N) = (nreify R) · (reify N)





--app : ∀ {Γ T U} -> sem Γ (T ⇝ U) -> sem Γ T -> sem Γ U
--app (ƛ f) N = f id N

--eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
--eval θ (v y) = θ y
--eval θ (M · N) = app (eval θ M) (eval θ N)
--eval θ (ƛ M) = ƛ (λ σ → λ s → eval (extend (λ x → appSubst σ (θ x)) s) M)

--init : subst ⊡ ⊡
--init ()

--nbe : ∀ {T} -> tm ⊡ T -> tm ⊡ T
--nbe M = reify (eval init M)

--- Alternative: Do it properly:


--mutual
-- reify' : ∀ {Γ T} -> sem Γ T -> ntm Γ T
-- reify' (neut R) = neut (nreify' R)
-- reify' (ƛ f) = ƛ (reify' (f wkn (reflect (v z))))
 
-- nreify' : ∀ {Γ T} -> neu Γ T -> rtm Γ T
-- nreify' (v y) = v y
-- nreify' (R · N) = (nreify' R) · (reify' N)

--nbe' : ∀ {T} -> tm ⊡ T -> ntm ⊡ T
--nbe' M = reify' (eval init M)
