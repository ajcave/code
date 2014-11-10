module bigstep-open-env where
open import Data.Nat

record Unit : Set where
 constructor tt

data tp : Set where
 base : tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data tm : Set where
 idx : ℕ -> tm -- de Bruijn index
 _·_ : tm -> tm -> tm -- application
 ƛ : tm -> tm -- lambda
 tt ff : tm

data _∶_∈_ : (x : ℕ) -> (T : tp) -> (Γ : ctx) -> Set where
 z : ∀ {Γ T} -> zero ∶ T ∈ (Γ , T)
 s : ∀ {Γ x T S} -> x ∶ T ∈ Γ -> (suc x) ∶ T ∈ (Γ , S)

data _⊢_∶_ (Γ : ctx) : (M : tm) -> (T : tp) -> Set where
 idx : ∀ {T x} -> x ∶ T ∈ Γ -> Γ ⊢ (idx x) ∶ T
 _·_ : ∀ {T S M N} -> Γ ⊢ M ∶ (T ⇝ S) -> Γ ⊢ N ∶ T -> Γ ⊢ (M · N) ∶ S
 ƛ : ∀ {T S M} -> (Γ , T) ⊢ M ∶  S -> Γ ⊢ (ƛ M) ∶ (T ⇝ S)
 tt : Γ ⊢ tt ∶ base
 ff : Γ ⊢ ff ∶ base

mutual
 data val : Set where
  ƛ_[_]' : tm -> env -> val
  ↑[_] : (T : tp) -> (e : Dne) -> val
  tt ff : val

 data Dne : Set where
  lvl : (x : ℕ) -> Dne
  _·_ : (e : Dne) -> (d : Dnf) -> Dne

 data Dnf : Set where
  ↓[_] : (T : tp) -> (a : val) -> Dnf

 data env :  Set where
  ⊡ : env
  _,_ : env -> val -> env

data comp : Set where 
 _[_] : tm -> env -> comp
 _·_ : val -> val -> comp -- This is not exactly what we did on the board

data lookup : env -> ℕ -> val -> Set where
 top : ∀ {σ v} -> lookup (σ , v) zero v
 pop : ∀ {σ x v u} -> lookup σ x v -> lookup (σ , u) (suc x) v

data _⇓_ : comp -> val -> Set where
 app : ∀ {M N σ f u v}
       -> M [ σ ] ⇓ f
       -> N [ σ ] ⇓ u
       -> (f · u) ⇓ v
       -> (M · N) [ σ ] ⇓ v
 var : ∀ {x σ v} -> lookup σ x v -> (idx x) [ σ ] ⇓ v
 ƛ : ∀ {M σ} -> (ƛ M) [ σ ] ⇓ (ƛ M [ σ ]')
 apƛ : ∀ {M σ v u} -> M [ σ , v ] ⇓ u -> ((ƛ M [ σ ]') · v) ⇓ u -- This is not exactly what we did on the board
 ↑ : ∀ {T S e a} -> (↑[ T ⇝ S ] e · a) ⇓ ↑[ S ] (e · ↓[ T ] a) -- Could this part be a function if we use intrinsically typed terms?
 tt : ∀ {σ} -> tt [ σ ] ⇓ tt
 ff : ∀ {σ} -> ff [ σ ] ⇓ ff

-- Just some notation
_∈_ : ∀ {A : Set} -> A -> (P : A -> Set) -> Set
x ∈ P = P x

record Clo (R : val -> Set) (c : comp) : Set where
 constructor inj
 field
  v : val
  ev : c ⇓ v
  red : v ∈ R

data minus : ℕ -> ℕ -> ℕ -> Set where
 zero : ∀ {n} -> minus n zero n
 suc : ∀ {n m k} -> minus n m k -> minus (suc n) (suc m) k

mutual
 data Rnf_,_∶_↘_ : ℕ -> val -> tp -> tm -> Set where
  arr : ∀ {n f b A B v} -> (f · ↑[ A ] (lvl n)) ⇓ b -> Rnf (suc n) , b ∶ B ↘ v
     -> Rnf n , f ∶ A ⇝ B ↘ ƛ v
  Neut : ∀ {n e v} -> Rne n , e ↘ v -> Rnf n , (↑[ base ] e) ∶ base ↘ v
  tt : ∀ {n} -> Rnf n , tt ∶ base ↘ tt
  ff : ∀ {n} -> Rnf n , ff ∶ base ↘ ff
 data Rne_,_↘_ : ℕ -> Dne -> tm -> Set where
  lvl : ∀ {n} k -> Rne n , (lvl k) ↘ idx (n ∸ suc k)
  _·_ : ∀ {n e d u v A} -> Rne n , e ↘ u -> Rnf n , d ∶ A ↘ v -> Rne n , (e · (↓[ A ] d)) ↘ (u · v)

open import Data.Product
⊤ : Dnf -> Set
⊤ (↓[ A ] a) = ∀ n -> ∃ (λ v -> Rnf n , a ∶ A ↘ v)

⊥ : Dne -> Set
⊥ e = ∀ n -> ∃ (λ u -> Rne n , e ↘ u)

data IsBase : val -> Set where
 tt : IsBase tt
 ff : IsBase ff
 neu : ∀ {e} -> e ∈ ⊥ -> ↑[ base ] e ∈ IsBase

mutual
 V[_] : ∀ T -> val -> Set
 V[ base ] v = IsBase v
 V[ T ⇝ S ] v = ∀ {u} -> u ∈ V[ T ] -> (v · u) ∈ Clo V[ S ]

E[_] : ∀ T -> comp -> Set
E[ T ] = Clo V[ T ]

data G[_] : ctx -> env -> Set where
 ⊡ : ⊡ ∈ G[ ⊡ ]
 _,_ : ∀ {Γ T σ v} -> σ ∈ G[ Γ ] -> v ∈ V[ T ] -> (σ , v) ∈ G[ Γ , T ]

thmv : ∀ {Γ x T} -> x ∶ T ∈ Γ -> ∀ {σ} -> σ ∈ G[ Γ ] -> (idx x) [ σ ] ∈ E[ T ]
thmv z (gΓ , x) = inj _ (var top) x
thmv (s d) (gΓ , x₁) with thmv d gΓ
thmv (s d) (gΓ , x₁) | inj v (var d') red = inj _ (var (pop d')) red

thm-app : ∀ {T T₁} {M N} {σ} →
         Clo (V[ T₁ ⇝ T ]) (M [ σ ]) →
         Clo V[ T₁ ] (N [ σ ]) → Clo V[ T ] ((M · N) [ σ ])
thm-app (inj v ev red) (inj v₁ ev₁ red₁) with red red₁
thm-app (inj v ev₁ red) (inj v₁ ev₂ red₁) | inj v₂ ev red₂ = inj _ (app ev₁ ev₂ ev) red₂

thm : ∀ {Γ t T} -> Γ ⊢ t ∶ T -> ∀ {σ} -> σ ∈ G[ Γ ] -> t [ σ ] ∈ E[ T ]
thm (idx x₁) gΓ = thmv x₁ gΓ
thm (d · d₁) gΓ = thm-app (thm d gΓ) (thm d₁ gΓ)
thm (ƛ {T} {S} {M}  d) {σ} gΓ = inj _ ƛ helper
 where helper : ∀ {u} -> u ∈ V[ T ] -> (ƛ M [ σ ]' · u) ∈ E[ S ]
       helper x with thm d (gΓ , x)
       helper x | inj v ev red = inj v (apƛ ev) red
thm tt gΓ = inj tt tt tt
thm ff gΓ = inj ff ff ff


mutual
 reify : ∀ {a} A -> a ∈ V[ A ] -> ↓[ A ] a ∈ ⊤
 reify base tt n = tt , tt
 reify base ff n = ff , ff
 reify base (neu d) n = _ , (Neut (proj₂ (d n)))
 reify (A ⇝ A₁) p n with p (reflect A (λ n₁ → , lvl n))
 reify (A ⇝ A₁) p n | inj v ev red = , (arr ev (proj₂ (reify A₁ red (suc n))))

 reflect : ∀ {e} A -> e ∈ ⊥ -> ↑[ A ] e ∈ V[ A ]
 reflect base p = neu p
 reflect (A ⇝ A₁) p = reflect-arr
  where reflect-arr : ↑[ A ⇝ A₁ ] _ ∈ V[ A ⇝ A₁ ]
        reflect-arr x with reify A x
        ... | q = inj _ ↑ (reflect A₁ (λ n → , proj₂ (p n) · proj₂ (q n)))

len : ctx -> ℕ
len ⊡ = zero
len (Γ , T) = suc (len Γ)

idenv : ctx -> env
idenv ⊡ = ⊡
idenv (Γ , T) = idenv Γ , ↑[ T ] (lvl (len Γ)) -- !!!! We could put zero here and nothing would care!

idenv' : ∀ Γ -> (idenv Γ) ∈ G[ Γ ]
idenv' ⊡ = ⊡
idenv' (Γ , T) = (idenv' Γ) , reflect T (λ n → , lvl (len Γ))

corollary : ∀ {Γ a} A -> Γ ⊢ a ∶ A -> ∃ (λ v -> a [ idenv Γ ] ⇓ v × (∃ (λ nf -> Rnf (len Γ) , v ∶ A ↘ nf)))
corollary A d with thm d (idenv' _)
corollary {Γ} A d | inj v ev red with reify A red (len Γ)
corollary A d | inj v ev red | r = , (ev , r)