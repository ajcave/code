module bigstep-cbpv where

record Unit : Set where
 constructor tt

mutual
 data vtp : Set where
  bool : vtp
  U : ctp -> vtp
 data ctp : Set where
  _⇝_ : (A : vtp) -> (B : ctp) -> ctp
  F : vtp -> ctp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : vtp) -> ctx

data ℕ : Set where
 zero : ℕ
 suc : ℕ -> ℕ

mutual
 data comp : Set where
  _·_ : comp -> val -> comp
  ƛ : comp -> comp
  produce : val -> comp
  _to_ : comp -> comp -> comp
  if : val -> comp -> comp -> comp
  _[_] : comp -> env -> comp
  force : val -> comp

 data val : Set where
  var : ℕ -> val
  tt ff : val
  thunk : comp -> val
  _[_] : val -> env -> val

 data env :  Set where
  ⊡ : env
  _,_ : env -> val -> env


data _∶_∈_ : (x : ℕ) -> (T : vtp) -> (Γ : ctx) -> Set where
 z : ∀ {Γ T} -> zero ∶ T ∈ (Γ , T)
 s : ∀ {Γ x T S} -> x ∶ T ∈ Γ -> (suc x) ∶ T ∈ (Γ , S)

mutual
 data _⊢c_∶_ (Γ : ctx) : (M : comp) -> (T : ctp) -> Set where
  _·_ : ∀ {T S M N} -> Γ ⊢c M ∶ (T ⇝ S) -> Γ ⊢v N ∶ T -> Γ ⊢c (M · N) ∶ S
  ƛ : ∀ {T S M} -> (Γ , T) ⊢c M ∶  S -> Γ ⊢c (ƛ M) ∶ (T ⇝ S)
  _to_ : ∀ {A B M N} -> Γ ⊢c M ∶ F A -> (Γ , A) ⊢c N ∶ B -> Γ ⊢c (M to N) ∶ B
  produce : ∀ {A V} -> Γ ⊢v V ∶ A -> Γ ⊢c produce V ∶ F A
  force : ∀ {B V} -> Γ ⊢v V ∶ U B -> Γ ⊢c force V ∶ B
  if : ∀ {V M N B} -> Γ ⊢v V ∶ bool -> Γ ⊢c M ∶ B -> Γ ⊢c N ∶ B -> Γ ⊢c (if V M N) ∶ B
  _[_] : ∀ {Δ ρ M B} -> Δ ⊢c M ∶ B -> Γ ⊢vs ρ ∶ Δ -> Γ ⊢c M [ ρ ] ∶ B

 data _⊢v_∶_ (Γ : ctx) : (M : val) -> (T : vtp) -> Set where
  var : ∀ {T x} -> x ∶ T ∈ Γ -> Γ ⊢v (var x) ∶ T
  tt : Γ ⊢v tt ∶ bool
  ff : Γ ⊢v ff ∶ bool
  thunk : ∀ {M B} -> Γ ⊢c M ∶ B -> Γ ⊢v thunk M ∶ U B

 data _⊢vs_∶_ (Γ : ctx) : (ρ : env) -> (Δ : ctx) -> Set where
  ⊡ : Γ ⊢vs ⊡ ∶ Γ
  _,_ : ∀ {Δ A ρ V} -> Γ ⊢vs ρ ∶ Δ -> Γ ⊢v V ∶ A -> Γ ⊢vs (ρ , V) ∶ (Δ , A)

data lookup : env -> ℕ -> val -> Set where
 top : ∀ {σ v} -> lookup (σ , v) zero v
 pop : ∀ {σ x v u} -> lookup σ x v -> lookup (σ , u) (suc x) v

_≐_ : val -> val -> Set
V ≐ V2 = {!!}

data _⇓_ : comp -> comp -> Set where
 app : ∀ {M V M' σ σ' T}
       -> M [ σ ] ⇓ ((ƛ M') [ σ' ])
       -> M' [ σ' , (V [ σ ]) ] ⇓ T
       -> (M · V) [ σ ] ⇓ T
 ƛ : ∀ {M σ} -> (ƛ M) [ σ ] ⇓ (ƛ M) [ σ ]
 to : ∀ {M N V σ T} 
     -> M [ σ ] ⇓ produce V
     -> N [ σ , V ] ⇓ T
     -> (M to N) [ σ ] ⇓ T
 force : ∀ {M V σ T} 
     -> V [ σ ] ≐ thunk M
     -> M ⇓ T  
     -> (force V) [ σ ] ⇓ T
 produce : ∀ {V σ} -> (produce V) [ σ ] ⇓ produce (V [ σ ])
 _[_] : ∀ {M ρ σ T}
    -> {!!}
    -> (M [ ρ ]) [ σ ] ⇓ T

-- -- Just some notation
-- _∈_ : ∀ {A : Set} -> A -> (P : A -> Set) -> Set
-- x ∈ P = P x

-- record Clo (R : val -> Set) (c : comp) : Set where
--  constructor inj
--  field
--   v : val
--   ev : c ⇓ v
--   red : v ∈ R

-- mutual
--  V[_] : ∀ T -> val -> Set
--  V[ unit ] v = Unit
--  V[ T ⇝ S ] v = ∀ {u} -> u ∈ V[ T ] -> (v · u) ∈ Clo V[ S ]

-- E[_] : ∀ T -> comp -> Set
-- E[ T ] = Clo V[ T ]

-- data G[_] : ctx -> env -> Set where
--  ⊡ : ⊡ ∈ G[ ⊡ ]
--  _,_ : ∀ {Γ T σ v} -> σ ∈ G[ Γ ] -> v ∈ V[ T ] -> (σ , v) ∈ G[ Γ , T ]

-- thmv : ∀ {Γ x T} -> x ∶ T ∈ Γ -> ∀ {σ} -> σ ∈ G[ Γ ] -> (var x) [ σ ] ∈ E[ T ]
-- thmv z (gΓ , x) = inj _ (var top) x
-- thmv (s d) (gΓ , x₁) with thmv d gΓ
-- thmv (s d) (gΓ , x₁) | inj v (var d') red = inj _ (var (pop d')) red

-- thm : ∀ {Γ t T} -> Γ ⊢ t ∶ T -> ∀ {σ} -> σ ∈ G[ Γ ] -> t [ σ ] ∈ E[ T ]
-- thm (var x₁) gΓ = thmv x₁ gΓ
-- thm (d · d₁) gΓ with thm d gΓ | thm d₁ gΓ
-- thm (d · d₁) gΓ | inj v ev red | inj v₁ ev₁ red₁ with red red₁
-- thm (d · d₁) gΓ | inj .(ƛ M [ σ ]') ev₁ red | inj v₁ ev₂ red₁ | inj v₂ (apƛ {M} {σ} ev) red₂ = inj v₂ (app ev₁ ev₂ ev) red₂
-- thm (ƛ {T} {S} {M}  d) {σ} gΓ = inj _ ƛ helper
--  where helper : ∀ {u} -> u ∈ V[ T ] -> (ƛ M [ σ ]' · u) ∈ E[ S ]
--        helper x with thm d (gΓ , x)
--        helper x | inj v ev red = inj v (apƛ ev) red

-- record normalizes (t : tm) : Set where
--  field
--   v : val
--   ev : t [ ⊡ ] ⇓ v

-- norm : ∀ {t T} -> ⊡ ⊢ t ∶ T -> normalizes t
-- norm d with thm d ⊡
-- norm d | inj v ev red = record { v = v; ev = ev }
