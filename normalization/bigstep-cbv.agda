module bigstep-cbv where

record Unit : Set where
 constructor tt

data tp : Set where
 unit : tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data ℕ : Set where
 zero : ℕ
 suc : ℕ -> ℕ

data tm : Set where
 var : ℕ -> tm -- de Bruijn index
 _·_ : tm -> tm -> tm -- application
 ƛ : tm -> tm -- lambda

data _∶_∈_ : (x : ℕ) -> (T : tp) -> (Γ : ctx) -> Set where
 z : ∀ {Γ T} -> zero ∶ T ∈ (Γ , T)
 s : ∀ {Γ x T S} -> x ∶ T ∈ Γ -> (suc x) ∶ T ∈ (Γ , S)

data _⊢_∶_ (Γ : ctx) : (M : tm) -> (T : tp) -> Set where
 var : ∀ {T x} -> x ∶ T ∈ Γ -> Γ ⊢ (var x) ∶ T
 _·_ : ∀ {T S M N} -> Γ ⊢ M ∶ (T ⇝ S) -> Γ ⊢ N ∶ T -> Γ ⊢ (M · N) ∶ S
 ƛ : ∀ {T S M} -> (Γ , T) ⊢ M ∶  S -> Γ ⊢ (ƛ M) ∶ (T ⇝ S)

mutual
 data val : Set where
  ƛ_[_]' : tm -> env -> val
  c : val

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
 app : ∀ {M N M' σ u σ' v}
       -> M [ σ ] ⇓ (ƛ M' [ σ' ]')
       -> N [ σ ] ⇓ u
       -> M' [ σ' , u ] ⇓ v
       -> (M · N) [ σ ] ⇓ v
 var : ∀ {x σ v} -> lookup σ x v -> (var x) [ σ ] ⇓ v
 ƛ : ∀ {M σ} -> (ƛ M) [ σ ] ⇓ (ƛ M [ σ ]')
 apƛ : ∀ {M σ v u} -> M [ σ , v ] ⇓ u -> ((ƛ M [ σ ]') · v) ⇓ u -- This is not exactly what we did on the board

-- Just some notation
_∈_ : ∀ {A : Set} -> A -> (P : A -> Set) -> Set
x ∈ P = P x

record Clo (R : val -> Set) (c : comp) : Set where
 constructor inj
 field
  v : val
  ev : c ⇓ v
  red : v ∈ R

mutual
 V[_] : ∀ T -> val -> Set
 V[ unit ] v = Unit
 V[ T ⇝ S ] v = ∀ {u} -> u ∈ V[ T ] -> (v · u) ∈ Clo V[ S ]

E[_] : ∀ T -> comp -> Set
E[ T ] = Clo V[ T ]

data G[_] : ctx -> env -> Set where
 ⊡ : ⊡ ∈ G[ ⊡ ]
 _,_ : ∀ {Γ T σ v} -> σ ∈ G[ Γ ] -> v ∈ V[ T ] -> (σ , v) ∈ G[ Γ , T ]

thmv : ∀ {Γ x T} -> x ∶ T ∈ Γ -> ∀ {σ} -> σ ∈ G[ Γ ] -> (var x) [ σ ] ∈ E[ T ]
thmv z (gΓ , x) = inj _ (var top) x
thmv (s d) (gΓ , x₁) with thmv d gΓ
thmv (s d) (gΓ , x₁) | inj v (var d') red = inj _ (var (pop d')) red

thm : ∀ {Γ t T} -> Γ ⊢ t ∶ T -> ∀ {σ} -> σ ∈ G[ Γ ] -> t [ σ ] ∈ E[ T ]
thm (var x₁) gΓ = thmv x₁ gΓ
thm (d · d₁) gΓ with thm d gΓ | thm d₁ gΓ
thm (d · d₁) gΓ | inj v ev red | inj v₁ ev₁ red₁ with red red₁
thm (d · d₁) gΓ | inj .(ƛ M [ σ ]') ev₁ red | inj v₁ ev₂ red₁ | inj v₂ (apƛ {M} {σ} ev) red₂ = inj v₂ (app ev₁ ev₂ ev) red₂
thm (ƛ {T} {S} {M}  d) {σ} gΓ = inj _ ƛ helper
 where helper : ∀ {u} -> u ∈ V[ T ] -> (ƛ M [ σ ]' · u) ∈ E[ S ]
       helper x with thm d (gΓ , x)
       helper x | inj v ev red = inj v (apƛ ev) red

record normalizes (t : tm) : Set where
 field
  v : val
  ev : t [ ⊡ ] ⇓ v

norm : ∀ {t T} -> ⊡ ⊢ t ∶ T -> normalizes t
norm d with thm d ⊡
norm d | inj v ev red = record { v = v; ev = ev }
