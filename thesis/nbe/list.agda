module list where
open import Data.List hiding (sum)

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Unit : Set where
 constructor tt

data tp : Set where
 nat : tp
 _⇝_ : (T : tp) -> (S : tp) -> tp
 _×_ : (T S : tp) -> tp
 unit : tp
 list : tp -> tp

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
  π₁ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ T
  π₂ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ S
  iter : ∀ {C} -> rtm Γ nat * List (rtm Γ nat) -> ntm (Γ , C) C -> ntm Γ C -> rtm Γ C
  fold : ∀ {T C} -> rtm Γ (list T) -> ntm ((Γ , T) , C) C -> ntm Γ C -> rtm Γ C
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  suc : ntm Γ nat -> ntm Γ nat
  sum : List (rtm Γ nat) -> ntm Γ nat
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T × S)
  tt : ntm Γ unit
  nil : ∀ {T} -> ntm Γ (list T)
  cons : ∀ {T} -> ntm Γ T -> ntm Γ (list T) -> ntm Γ (list T)
  mapp : ∀ {T S} -> ntm (Γ , T) S -> rtm Γ (list T) -> ntm Γ (list S) -> ntm Γ (list S)

data L (Γ : ctx) (T : tp) (M : ctx -> Set) : Set where
 nil : L Γ T M
 cons : M Γ -> L Γ T M -> L Γ T M
 mapp : ∀ {S} -> (∀ Δ -> vsubst Γ Δ -> rtm Δ S -> M Δ) -> rtm Γ (list S) -> L Γ T M -> L Γ T M

sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ nat = ntm Γ nat
sem Γ (list T) = L Γ T (λ Δ -> sem Δ T)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S 
sem Γ (T × S) = sem Γ T * sem Γ S
sem Γ unit = Unit

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 rappSubst σ (π₁ R) = π₁ (rappSubst σ R)
 rappSubst σ (π₂ R) = π₂ (rappSubst σ R)
 rappSubst σ (iter (x , xs) f b) = iter (rappSubst σ x , rlSubst σ xs) (nappSubst (ext σ) f) (nappSubst σ b)
 rappSubst σ (fold xs f b) = fold (rappSubst σ xs) (nappSubst (ext (ext σ)) f) (nappSubst σ b)

 rlSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> List (rtm Δ S) -> List (rtm Γ S)
 rlSubst σ [] = []
 rlSubst σ (x ∷ Rs) = (rappSubst σ x) ∷ (rlSubst σ Rs)

 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (sum Rs) = sum (rlSubst σ Rs)
 nappSubst σ (suc N) = suc (nappSubst σ N)
 nappSubst σ < M , N > = < nappSubst σ M , nappSubst σ N >
 nappSubst σ tt = tt
 nappSubst σ nil = nil
 nappSubst σ (cons H T) = cons (nappSubst σ H) (nappSubst σ T)
 nappSubst σ (mapp f xs ys) = mapp (nappSubst (ext σ) f) (rappSubst σ xs) (nappSubst σ ys)

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

mutual
 appSubstl : ∀ {Γ Δ S} -> vsubst Γ Δ -> L Γ S (λ x -> sem x S) -> L Δ S (λ x -> sem x S)
 appSubstl π nil = nil
 appSubstl π (cons x l) = cons (appSubst _ π x) (appSubstl π l)
 appSubstl π (mapp f x₁ l) = mapp (λ Δ π' → f _ (π' ∘ π)) (rappSubst π x₁) (appSubstl π l)

 appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
 appSubst nat σ M = nappSubst σ M
 appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s
 appSubst (T × S) σ (M , N) = (appSubst T σ M) , (appSubst S σ N)
 appSubst unit σ tt = tt
 appSubst (list T) σ M = appSubstl σ M

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {nat} N = sum (N ∷ [])
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)
 reflect {T × S} N = reflect (π₁ N) , reflect (π₂ N)
 reflect {unit} N = tt
 reflect {list T} N = mapp (λ Δ x x₁ → reflect x₁) N nil

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {nat} M = M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z))))
 reify {T × S} M = < reify (_*_.fst M) , reify (_*_.snd M) >
 reify {unit} tt = tt
 reify {list T} M = reifyl M

 reifyl : ∀ {Γ T} -> L Γ T (λ Δ -> sem Δ T) -> ntm Γ (list T)
 reifyl nil = nil
 reifyl (cons x l) = cons (reify x) (reifyl l)
 reifyl (mapp x x₁ l) = mapp (reify (x _ s (v z))) x₁ (reifyl l)

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

ext' : ∀ {Γ Δ T} -> subst Γ Δ -> subst (Γ , T) (Δ , T)
ext' σ = extend (λ x → appSubst _ s (σ x)) (reflect (v z))

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 π₁ : ∀ {T S} -> tm Γ (T × S) -> tm Γ T
 π₂ : ∀ {T S} -> tm Γ (T × S) -> tm Γ S
 <_,_> : ∀ {T S} -> tm Γ T -> tm Γ S -> tm Γ (T × S)
 tt : tm Γ unit
 suc : tm Γ nat -> tm Γ nat
 zero : tm Γ nat
 _+'_ : tm Γ nat -> tm Γ nat -> tm Γ nat
 iter : ∀ {C} -> tm Γ nat -> tm (Γ , C) C -> tm Γ C -> tm Γ C
 nil : ∀ {T} -> tm Γ (list T)
 cons : ∀ {T} -> tm Γ T -> tm Γ (list T) -> tm Γ (list T)
 map' : ∀ {T S} -> tm (Γ , T) S -> tm Γ (list T) -> tm Γ (list S)
 fold : ∀ {T C} -> tm Γ (list T) -> tm ((Γ , T) , C) C -> tm Γ C -> tm Γ C

_⊕_ : ∀ {Γ} -> ntm Γ nat -> ntm Γ nat -> ntm Γ nat
suc n ⊕ m = suc (n ⊕ m)
n ⊕ suc m = suc (n ⊕ m)
sum x ⊕ sum x₁ = sum (x ++ x₁)

arr : ∀ Γ T -> Set
arr Γ T = ∀ {Δ} -> subst Γ Δ -> sem Δ T

iter' : ∀ {Γ T} -> arr (Γ , T) T -> arr Γ T -> ∀ {Δ} -> subst Γ Δ -> sem Δ nat -> sem Δ T
iter' f b σ (suc n) = f (extend σ (iter' f b σ n))
iter' f b σ (sum []) = b σ
iter' f b σ (sum (x ∷ x₁)) = reflect (iter (x , x₁) (reify (f (ext' σ))) (reify (b σ)))

map'' : ∀ {Γ T S} -> arr (Γ , T) S -> ∀ {Δ} -> subst Γ Δ -> sem Δ (list T) -> sem Δ (list S)
map'' f θ nil = nil
map'' f θ (cons x xs) = cons (f (extend θ x)) (map'' f θ xs)
map'' f θ (mapp g x₁ xs) = mapp (λ Δ π x → f (extend (λ x₂ → appSubst _ π (θ x₂)) (g _ π x))) x₁ (map'' f θ xs)

fold'' : ∀ {Γ T C} -> arr ((Γ , T) , C) C -> arr Γ C -> ∀ {Δ} -> subst Γ Δ -> sem Δ (list T) -> sem Δ C
fold'' f b θ nil = b θ
fold'' f b θ (cons x xs) = f (extend (extend θ x) (fold'' f b θ xs))
fold'' f b θ (mapp g xs ys) = reflect (fold xs (reify (f (extend (extend (λ x → appSubst _ (s ∘ s) (θ x)) (g _ (s ∘ s) (v (s z)))) (reflect (v z))))) (reify (b θ)))

eval : ∀ {Γ T} -> tm Γ T -> arr Γ T
eval (v y) θ = θ y
eval (M · N) θ = eval M θ _ id (eval N θ)
eval (ƛ M) θ = λ _ σ s -> eval M (extend (λ x → appSubst _ σ (θ x)) s)
eval (π₁ M) θ = _*_.fst (eval M θ)
eval (π₂ N) θ = _*_.snd (eval N θ)
eval < M , N > θ = eval M θ , eval N θ
eval tt θ = tt
eval (suc n) θ = suc (eval n θ)
eval zero θ = sum []
eval (m +' n) θ = (eval m θ) ⊕ (eval n θ)
eval (iter xs f b) θ = iter' (eval f) (eval b) θ (eval xs θ)
eval nil θ = nil
eval (cons H T) θ = cons (eval H θ) (eval T θ)
eval (map' f xs) θ = map'' (eval f) θ (eval xs θ)
eval (fold xs f b) θ = fold'' (eval f) (eval b) θ (eval xs θ)

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval M (λ x → reflect (v x))) 

