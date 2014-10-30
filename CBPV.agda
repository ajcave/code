module CBPV where

open import Prelude
open import DeBruijn renaming (⟦_⟧ to ⟦_⟧a)

mutual
  data VType : Set where
    U : CType → VType
    _+_ : VType → VType → VType
    unit : VType
    _×_ : VType → VType → VType

  data CType : Set where
    F : VType → CType
    _∧_ : CType → CType → CType
    _⇒_ : VType → CType → CType

Ctx = Context VType

mutual
  data VTerm (Γ : Ctx) : VType → Set where 
    var   : ∀ {α} → Var Γ α → VTerm Γ α
    thunk : ∀ {β} → CTerm Γ β → VTerm Γ (U β)
    inl   : ∀ {α₁ α₂} → VTerm Γ α₁ → VTerm Γ (α₁ + α₂) 
    inr   : ∀ {α₁ α₂} → VTerm Γ α₂ → VTerm Γ (α₁ + α₂) 
    _,_   : ∀ {α₁ α₂} → VTerm Γ α₁ → VTerm Γ α₂ → VTerm Γ (α₁ × α₂)

  data CTerm (Γ : Ctx) : CType → Set where
    produce       : ∀ {α} → VTerm Γ α → CTerm Γ (F α)
    ⟨_,_⟩          : ∀ {β₁ β₂} → CTerm Γ β₁ → CTerm Γ β₂ → CTerm Γ (β₁ ∧ β₂)
    ƛ             : ∀ {α β} → CTerm (Γ , α) β → CTerm Γ (α ⇒ β)
    letbe         : ∀ {α β} → VTerm Γ α → CTerm (Γ , α) β → CTerm Γ β
    _to_          : ∀ {α β} → CTerm Γ (F α) → CTerm (Γ , α) β → CTerm Γ β
    force         : ∀ {β} → VTerm Γ (U β) → CTerm Γ β
    pm_left_right : ∀ {α₁ α₂ β} → VTerm Γ (α₁ + α₂) → CTerm (Γ , α₁) β → CTerm (Γ , α₂) β → CTerm Γ β
    pm_as         : ∀ {α₁ α₂ β} → VTerm Γ (α₁ × α₂) → CTerm ((Γ , α₂) , α₁) β → CTerm Γ β
    π₁            : ∀ {β₁ β₂} → CTerm Γ (β₁ ∧ β₂) → CTerm Γ β₁
    π₂            : ∀ {β₁ β₂} → CTerm Γ (β₁ ∧ β₂) → CTerm Γ β₂
    _′_            : ∀ {α β} → VTerm Γ α → CTerm Γ (α ⇒ β) → CTerm Γ β



TRen : Ctx → Ctx → Set
TRen Γ Γ₁ = Sub (Var Γ₁) Γ

TSub : Ctx → Ctx → Set
TSub Γ Γ₁ = Sub (VTerm Γ₁) Γ

wkn-tren : ∀ {Γ Γ₁ : Ctx} {α} → TRen Γ Γ₁ → TRen Γ (Γ₁ , α)
wkn-tren r = map pop r

id-tren : ∀ {Γ : Ctx} → TRen Γ Γ
id-tren {Γ = ∅} = ⊡
id-tren {Γ = Γ , α} = top ∷ wkn-tren id-tren

⇑ : ∀ {Γ : Ctx} {α} → TRen Γ (Γ , α)
⇑ = wkn-tren id-tren

mutual
  ∥_∥v : ∀ {Γ Γ₁ α} → TRen Γ Γ₁ → VTerm Γ α → VTerm Γ₁ α
  ∥_∥v ρ (var x) = var (⟦ ρ ⟧a x)
  ∥_∥v ρ (thunk x) = thunk (∥ ρ ∥ x)
  ∥_∥v ρ (inl x) = inl (∥ ρ ∥v x)
  ∥_∥v ρ (inr x) = inr (∥ ρ ∥v x)
  ∥_∥v ρ (t , t₁) = ∥ ρ ∥v t , ∥ ρ ∥v t₁ 

  ∥_∥ : ∀ {Γ Γ₁ β} → TRen Γ Γ₁ → CTerm Γ β → CTerm Γ₁ β
  ∥_∥ ρ (produce t) = produce (∥ ρ ∥v t)
  ∥_∥ ρ ⟨ t₁ , t₂ ⟩ = ⟨ ∥ ρ ∥ t₁ , ∥ ρ ∥ t₂ ⟩
  ∥_∥ ρ (ƛ t) = ƛ (∥ top ∷ (wkn-tren ρ) ∥ t)
  ∥_∥ ρ (letbe x t) = letbe (∥ ρ ∥v x) (∥ top ∷ wkn-tren ρ ∥ t)
  ∥_∥ ρ (t to t₁) = (∥ ρ ∥ t) to (∥ top ∷ wkn-tren ρ ∥ t₁)
  ∥_∥ ρ (force x) = force (∥ ρ ∥v x)
  ∥_∥ ρ (pm x left x₁ right x₂) = pm ∥ ρ ∥v x left ∥ top ∷ wkn-tren ρ ∥ x₁ right (∥ top ∷ wkn-tren ρ ∥ x₂)
  ∥_∥ ρ (pm x as t) = pm ∥ ρ ∥v x as (∥ (top ∷ ((pop top) ∷ (wkn-tren (wkn-tren ρ)))) ∥ t)
  ∥_∥ ρ (π₁ x) = π₁ (∥ ρ ∥ x)
  ∥_∥ ρ (π₂ x) = π₂ (∥ ρ ∥ x)
  ∥_∥ ρ (x ′ t) = (∥ ρ ∥v x) ′ (∥ ρ ∥ t)

wkn : ∀ {Γ Γ₁ : Ctx} {α} → TSub Γ Γ₁ → TSub Γ (Γ₁ , α)
wkn r = map ∥ ⇑ ∥v r

id : ∀ {Γ : Ctx} → TSub Γ Γ
id {Γ = ∅} = ⊡
id {Γ = Γ , α} = var top ∷ wkn id

⇡ : ∀ {Γ : Ctx} {α} → TSub Γ (Γ , α)
⇡ = wkn id

mutual
  ⟦_⟧v : ∀ {Γ Γ₁ α} → TSub Γ Γ₁ → VTerm Γ α → VTerm Γ₁ α
  ⟦_⟧v σ (var x) = ⟦ σ ⟧a x
  ⟦_⟧v σ (thunk x) = thunk (⟦ σ ⟧ x)
  ⟦_⟧v ρ (inl x) = inl (⟦ ρ ⟧v x)
  ⟦_⟧v ρ (inr x) = inr (⟦ ρ ⟧v x)
  ⟦_⟧v σ (t , t₁) = ⟦ σ ⟧v t , ⟦ σ ⟧v t₁

  ⟦_⟧ : ∀ {Γ Γ₁ β} → TSub Γ Γ₁ → CTerm Γ β → CTerm Γ₁ β
  ⟦_⟧ σ (produce t) = produce (⟦ σ ⟧v t)
  ⟦_⟧ ρ ⟨ t₁ , t₂ ⟩ = ⟨ ⟦ ρ ⟧ t₁ , ⟦ ρ ⟧ t₂ ⟩
  ⟦_⟧ σ (ƛ t) = ƛ (⟦ var top ∷ wkn σ ⟧ t)
  ⟦_⟧ σ (letbe x t) = letbe (⟦ σ ⟧v x) (⟦ var top ∷ wkn σ ⟧ t)
  ⟦_⟧ σ (t to t₁) = (⟦ σ ⟧ t) to ⟦ var top ∷ wkn σ ⟧ t₁
  ⟦_⟧ σ (force x) = force (⟦ σ ⟧v x)
  ⟦_⟧ ρ (pm x left x₁ right x₂) = pm ⟦ ρ ⟧v x left ⟦ var top ∷ wkn ρ ⟧ x₁ right (⟦ var top ∷ wkn ρ ⟧ x₂)
  ⟦_⟧ σ (pm x as t) = pm ⟦ σ ⟧v x as (⟦ var top ∷ (var (pop top) ∷ wkn (wkn σ)) ⟧ t)
  ⟦_⟧ ρ (π₁ x) = π₁ (⟦ ρ ⟧ x)
  ⟦_⟧ ρ (π₂ x) = π₂ (⟦ ρ ⟧ x)
  ⟦_⟧ σ (x ′ t) = ⟦ σ ⟧v x ′ ⟦ σ ⟧ t

data _⇓_ {Γ : Ctx} : ∀ {β : CType} → CTerm Γ β → CTerm Γ β → Set where
  ev-prod  : ∀ {α} {v : VTerm Γ α} → (produce v) ⇓ (produce v)
  ev-∧     : ∀ {β₁ β₂} {m₁ : CTerm Γ β₁} {m₂ : CTerm Γ β₂} → ⟨ m₁ , m₂ ⟩ ⇓ ⟨ m₁ , m₂ ⟩
  ev-ƛ     : ∀ {α β} {t : CTerm (Γ , α) β} → ƛ t ⇓ ƛ t
  ev-let   : ∀ {α β v t} {m : CTerm (Γ , α) β} → (⟦ v ∷ id ⟧ m) ⇓ t → letbe v m ⇓ t 
  ev-to    : ∀ {α β m v t} {n : CTerm (Γ , α) β} → m ⇓ (produce v) → ⟦ v ∷ id ⟧ n ⇓ t → (m to n) ⇓ t
  ev-force : ∀ {β} {m t : CTerm Γ β} → m ⇓ t → force (thunk m) ⇓ t
  ev-pml   : ∀ {α₁ α₂ β} {v t} {m₁ : CTerm (Γ , α₁) β} {m₂ : CTerm (Γ , α₂) β} → 
              ⟦ v ∷ id ⟧ m₁ ⇓ t → pm (inl v) left m₁ right m₂ ⇓ t
  ev-pmr   : ∀ {α₁ α₂ β} {v t} {m₁ : CTerm (Γ , α₁) β} {m₂ : CTerm (Γ , α₂) β} → 
              ⟦ v ∷ id ⟧ m₂ ⇓ t → pm (inr v) left m₁ right m₂ ⇓ t
  ev-pm    : ∀ {α₁ α₂ β} {v₁ v₂ t} {m : CTerm ((Γ , α₂) , α₁) β } → 
              ⟦ v₁ ∷ (v₂ ∷ id) ⟧ m ⇓ t → (pm v₁ , v₂ as m) ⇓ t
  ev-π₁    : ∀ {β₁ β₂} {m : CTerm Γ (β₁ ∧ β₂)} {m₁ m₂ t} → m ⇓ ⟨ m₁ , m₂ ⟩ → m₁ ⇓ t → π₁ m ⇓ t
  ev-π₂    : ∀ {β₁ β₂} {m : CTerm Γ (β₁ ∧ β₂)} {m₁ m₂ t} → m ⇓ ⟨ m₁ , m₂ ⟩ → m₂ ⇓ t → π₂ m ⇓ t
  ev-′     : ∀ {α β} {m v t} {m' : CTerm (Γ , α) β} → m ⇓ ƛ m' → ⟦ v ∷ id ⟧ m' ⇓ t → (v ′ m) ⇓ t

data Outside (Γ : Ctx) (∁ : CType) : CType → Set where
  nil     : Outside Γ ∁ ∁
  []to_∷_ : ∀ {α β} → CTerm (Γ , α) β → Outside Γ ∁ β → Outside Γ ∁ (F α)
  π₁∷_    : ∀ {β₁ β₂} → Outside Γ ∁ β₁ → Outside Γ ∁ (β₁ ∧ β₂)
  π₂∷_    : ∀ {β₁ β₂} → Outside Γ ∁ β₂ → Outside Γ ∁ (β₁ ∧ β₂)
  _∷v_    : ∀ {α β} → VTerm Γ α → Outside Γ ∁ β → Outside Γ ∁ (α ⇒ β)

data CK {Γ : Ctx} {∁ : CType} : ∀ {β} → CTerm Γ β → Outside Γ ∁ β → Set where
  _,_ : ∀ {β} (t : CTerm Γ β) (k : Outside Γ ∁ β) → CK t k
  
data _↝_ {Γ : Ctx} {∁ : CType} : ∀ {β₁ β₂} {t₁ : CTerm Γ β₁} {k₁ : Outside Γ ∁ β₁} 
             {t₂ : CTerm Γ β₂} {k₂ : Outside Γ ∁ β₂} → CK t₁ k₁ → CK t₂ k₂ → Set where
  tr-let   : ∀ {α β} {m : CTerm (Γ , α) β} {v k} → (letbe v m , k) ↝ (⟦ v ∷ id ⟧ m , k)
  tr-to    : ∀ {α β} {n : CTerm (Γ , α) β} {m k} → ((m to n) , k) ↝ (m , []to n ∷ k)
  tr-prod  : ∀ {α β v k} {n : CTerm (Γ , α) β} → (produce v , []to n ∷ k) ↝ (⟦ v ∷ id ⟧ n , k)
  tr-force : ∀ {β k} {m : CTerm Γ β} → (force (thunk m) , k) ↝ (m , k)
  tr-pml   : ∀ {α₁ α₂ β v k} {m₁ : CTerm (Γ , α₁) β} {m₂ : CTerm (Γ , α₂) β} →
             ((pm (inl v) left m₁ right m₂) , k) ↝ (⟦ v ∷ id ⟧ m₁ , k)
  tr-pmr   : ∀ {α₁ α₂ β v k} {m₁ : CTerm (Γ , α₁) β} {m₂ : CTerm (Γ , α₂) β} →
             ((pm (inr v) left m₁ right m₂) , k) ↝ (⟦ v ∷ id ⟧ m₂ , k)
  tr-pm    : ∀ {α₁ α₂ β v₁ v₂ k} {m : CTerm ((Γ , α₂) , α₁) β} → 
             ((pm v₁ , v₂ as m) , k) ↝ (⟦ v₁ ∷ (v₂ ∷ id) ⟧ m , k)
  tr-π₁    : ∀ {β₁ β₂ k} {m : CTerm Γ (β₁ ∧ β₂)} → (π₁ m , k) ↝ (m , π₁∷ k)
  tr-π₂    : ∀ {β₁ β₂ k} {m : CTerm Γ (β₁ ∧ β₂)} → (π₂ m , k) ↝ (m , π₂∷ k)
  tr-∧₁    : ∀ {β₁ β₂ k} {m₁ : CTerm Γ β₁} {m₂ : CTerm Γ β₂} → (⟨ m₁ , m₂ ⟩ , π₁∷ k) ↝ (m₁ , k)
  tr-∧₂    : ∀ {β₁ β₂ k} {m₁ : CTerm Γ β₁} {m₂ : CTerm Γ β₂} → (⟨ m₁ , m₂ ⟩ , π₂∷ k) ↝ (m₂ , k)
  tr-′     :  ∀ {α β v k} {m : CTerm Γ (α ⇒ β)} → ((v ′ m) , k) ↝ (m , (v ∷v k)) 
  tr-ƛ     : ∀ {α β v k} {m : CTerm (Γ , α) β} → ((ƛ m) , (v ∷v k)) ↝ (⟦ v ∷ id ⟧ m , k)

data Terminal {Γ : Ctx} : ∀ {β} {m : CTerm Γ β} → CK m nil → Set where
  term-prod : ∀ {α} {v : VTerm Γ α} → Terminal (produce v , nil)
  term-∧    : ∀ {β₁ β₂} {m₁ : CTerm Γ β₁} {m₂ : CTerm Γ β₂} → Terminal (⟨ m₁ , m₂ ⟩ , nil)
  term-ƛ    : ∀ {α β} {m : CTerm (Γ , α) β} → Terminal (ƛ m , nil)

data _↝⋆_ {Γ : Ctx} {∁ : CType} : ∀ {β₁ β₂} {t₁ : CTerm Γ β₁} {k₁ : Outside Γ ∁ β₁} 
             {t₂ : CTerm Γ β₂} {k₂ : Outside Γ ∁ β₂} → CK t₁ k₁ → CK t₂ k₂ → Set where
   ↝refl  : ∀ {β} {m : CTerm Γ β} {k : Outside Γ ∁ β} → (m , k) ↝⋆ (m , k)
   ↝trans : ∀ {β₁ β₂ β₃} {m₁ : CTerm Γ β₁} {m₂ : CTerm Γ β₂} {m₃ : CTerm Γ β₃} 
               {k₁ : Outside Γ ∁ β₁} {k₂ : Outside Γ ∁ β₂} {k₃ : Outside Γ ∁ β₃} →
            (m₁ , k₁) ↝ (m₂ , k₂) → (m₂ , k₂) ↝⋆ (m₃ , k₃) → (m₁ , k₁) ↝⋆ (m₃ , k₃)

↝⋆trans : ∀ {Γ ∁} {β₁ β₂ β₃} {m₁ : CTerm Γ β₁} {m₂ : CTerm Γ β₂} {m₃ : CTerm Γ β₃} 
               {k₁ : Outside Γ ∁ β₁} {k₂ : Outside Γ ∁ β₂} {k₃ : Outside Γ ∁ β₃} →
  (m₁ , k₁) ↝⋆ (m₂ , k₂) → (m₂ , k₂) ↝⋆ (m₃ , k₃) → (m₁ , k₁) ↝⋆ (m₃ , k₃) 
↝⋆trans ↝refl tr₂ = tr₂
↝⋆trans (↝trans x tr₁) tr₂ = ↝trans x (↝⋆trans tr₁ tr₂)

⇓to↝∀k : ∀ {β} {m t : CTerm ∅ β} → m ⇓ t → 
           {∁ : CType} → {k : Outside ∅ ∁ β} → (m , k) ↝⋆ (t , k)
⇓to↝∀k {β = F α} ev-prod = ↝refl
⇓to↝∀k {β = β₁ ∧ β₂} ev-∧ = ↝refl
⇓to↝∀k {β = α ⇒ β} ev-ƛ = ↝refl
⇓to↝∀k (ev-let e) = ↝trans tr-let (⇓to↝∀k e)
⇓to↝∀k (ev-to e e₁) = ↝trans tr-to (↝⋆trans (⇓to↝∀k e) (↝trans tr-prod (⇓to↝∀k e₁)))
⇓to↝∀k (ev-force e) = ↝trans tr-force (⇓to↝∀k e)
⇓to↝∀k (ev-pml e) = ↝trans tr-pml (⇓to↝∀k e)
⇓to↝∀k (ev-pmr e) = ↝trans tr-pmr (⇓to↝∀k e)
⇓to↝∀k (ev-pm e) = ↝trans tr-pm (⇓to↝∀k e)
⇓to↝∀k (ev-π₁ e e₁) = ↝⋆trans (↝trans tr-π₁ (⇓to↝∀k e)) (↝trans tr-∧₁ (⇓to↝∀k e₁))
⇓to↝∀k (ev-π₂ e e₁) = ↝⋆trans (↝trans tr-π₂ (⇓to↝∀k e)) (↝trans tr-∧₂ (⇓to↝∀k e₁))
⇓to↝∀k (ev-′ e e₁) = ↝⋆trans (↝trans tr-′ (⇓to↝∀k e)) (↝trans tr-ƛ (⇓to↝∀k e₁))

↝∀kto↝nil : ∀ {β} {m t : CTerm ∅ β} → ({∁ : CType} → (k : Outside ∅ ∁ β) → 
              (m , k) ↝⋆ (t , k)) → (m , nil) ↝⋆ (t , nil)
↝∀kto↝nil {β = β} e = e {β} nil

_∙_ : ∀ {β ∁} → CTerm ∅ β → Outside ∅ ∁ β → CTerm ∅ ∁
m ∙ nil = m
m ∙ ([]to m' ∷ k) = (m to m') ∙ k
m ∙ (π₁∷ k) = π₁ m ∙ k
m ∙ (π₂∷ k) = π₂ m ∙ k
m ∙ (v ∷v k) = (v ′ m) ∙ k

m⇓n⇓→mk⇓nk⇓ : ∀ {∁ β} {m n : CTerm ∅ β} → (∀ {t} → m ⇓ t → n ⇓ t) → {t : CTerm ∅ ∁}
              (k : Outside ∅ ∁ β) → (m ∙ k) ⇓ t → (n ∙ k) ⇓ t
m⇓n⇓→mk⇓nk⇓ f nil x = f x
m⇓n⇓→mk⇓nk⇓ {m = m} {n = n} f ([]to x ∷ k) x₁ = m⇓n⇓→mk⇓nk⇓ helper k x₁
  where helper : ∀ {t} → (m to x) ⇓ t → (n to x) ⇓ t
        helper (ev-to w w₁) = ev-to (f w) w₁
m⇓n⇓→mk⇓nk⇓ {m = m} {n = n} f (π₁∷ k) x = m⇓n⇓→mk⇓nk⇓ helper k x
  where helper : ∀ {t} -> π₁ m ⇓ t -> π₁ n ⇓ t
        helper (ev-π₁ x₁ x₂) = ev-π₁ (f x₁) x₂
m⇓n⇓→mk⇓nk⇓ {m = m} {n = n} f (π₂∷ k) x = m⇓n⇓→mk⇓nk⇓ helper k x
  where helper : ∀ {t} -> π₂ m ⇓ t -> π₂ n ⇓ t
        helper (ev-π₂ x₁ x₂) = ev-π₂ (f x₁) x₂
m⇓n⇓→mk⇓nk⇓ {m = m} {n = n} f (x ∷v k) x₁ = m⇓n⇓→mk⇓nk⇓ helper k x₁
  where helper : ∀ {t} → (x ′ m) ⇓ t → (x ′ n) ⇓ t
        helper (ev-′ w w₁) = ev-′ (f w) w₁

↝⋆nilto∙⇓ : ∀ {∁ β m t} {k : Outside ∅ ∁ β} → Terminal (t , nil) → 
          (m , k) ↝⋆ (t , nil) → (m ∙ k) ⇓ t
↝⋆nilto∙⇓ {m = produce x} {k = nil} τ ↝refl = ev-prod
↝⋆nilto∙⇓ {m = ⟨ m , m₁ ⟩} {k = nil} τ ↝refl = ev-∧
↝⋆nilto∙⇓ {m = ƛ m} {k = nil} τ ↝refl = ev-ƛ
↝⋆nilto∙⇓ {m = letbe x m} {k = nil} () ↝refl
↝⋆nilto∙⇓ {m = m to m₁} {k = nil} () ↝refl
↝⋆nilto∙⇓ {m = force x} {k = nil} () ↝refl
↝⋆nilto∙⇓ {m = pm_left_right x m m₁} {k = nil} () ↝refl
↝⋆nilto∙⇓ {m = pm_as x m} {k = nil} () ↝refl
↝⋆nilto∙⇓ {m = π₁ m} {k = nil} () ↝refl
↝⋆nilto∙⇓ {m = π₂ m} {k = nil} () ↝refl
↝⋆nilto∙⇓ {m = x ′ m} {k = nil} () ↝refl
↝⋆nilto∙⇓ {m = produce x} {k = nil} τ (↝trans () e)
↝⋆nilto∙⇓ {m = ⟨ m , m₁ ⟩} {k = nil} τ (↝trans () e)
↝⋆nilto∙⇓ {m = ƛ m} {k = nil} τ (↝trans () e)
↝⋆nilto∙⇓ {m = letbe x m} {k = nil} τ (↝trans tr-let e) = 
          m⇓n⇓→mk⇓nk⇓ ev-let nil (↝⋆nilto∙⇓ τ e)
↝⋆nilto∙⇓ {m = m to m₁} {k = nil} τ (↝trans tr-to e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = force ._} {k = nil} τ (↝trans tr-force e) = 
          m⇓n⇓→mk⇓nk⇓ ev-force nil (↝⋆nilto∙⇓ τ e)
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = nil} τ (↝trans tr-pml e) = 
          m⇓n⇓→mk⇓nk⇓ ev-pml nil (↝⋆nilto∙⇓ τ e)
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = nil} τ (↝trans tr-pmr e) = 
          m⇓n⇓→mk⇓nk⇓ ev-pmr nil (↝⋆nilto∙⇓ τ e)
↝⋆nilto∙⇓ {m = pm_as ._ m} {k = nil} τ (↝trans tr-pm e) = 
          m⇓n⇓→mk⇓nk⇓ ev-pm nil (↝⋆nilto∙⇓ τ e)
↝⋆nilto∙⇓ {m = π₁ m} {k = nil} τ (↝trans tr-π₁ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = π₂ m} {k = nil} τ (↝trans tr-π₂ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = x ′ m} {k = nil} τ (↝trans tr-′ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = produce x} {k = []to x₁ ∷ k} τ (↝trans tr-prod e) = 
          m⇓n⇓→mk⇓nk⇓ (ev-to ev-prod) k (↝⋆nilto∙⇓ τ e)
↝⋆nilto∙⇓ {m = letbe x m} {k = []to x₁ ∷ k} τ (↝trans tr-let e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (⟦ x ∷ ⊡ ⟧ m to x₁) ⇓ t → (letbe x m to x₁) ⇓ t
        helper (ev-to w w₁) = ev-to (ev-let w) w₁
↝⋆nilto∙⇓ {m = m to m₁} {k = []to x ∷ k} τ (↝trans tr-to e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = force ._} {k = []to x₁ ∷ k} τ (↝trans {m₂ = m₂} tr-force e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (m₂ to x₁) ⇓ t → (force (thunk m₂) to x₁) ⇓ t
        helper (ev-to w w₁) = ev-to (ev-force w) w₁
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = []to x₁ ∷ k} τ (↝trans (tr-pml {v = v}) e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (⟦ v ∷ ⊡ ⟧ m to x₁) ⇓ t → (pm inl v left m right m₁ to x₁) ⇓ t
        helper (ev-to w w₁) = ev-to (ev-pml w) w₁
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = []to x₁ ∷ k} τ (↝trans (tr-pmr {v = v}) e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (⟦ v ∷ ⊡ ⟧ m₁ to x₁) ⇓ t → (pm inr v left m right m₁ to x₁) ⇓ t
        helper (ev-to w w₁) = ev-to (ev-pmr w) w₁
↝⋆nilto∙⇓ {m = pm_as ._ m} {k = []to x₁ ∷ k} τ (↝trans (tr-pm {v₁ = v₁} {v₂ = v₂}) e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (⟦ v₁ ∷ (v₂ ∷ ⊡) ⟧ m to x₁) ⇓ t → (pm v₁ , v₂ as m to x₁) ⇓ t
        helper (ev-to w w₁) = ev-to (ev-pm w) w₁
↝⋆nilto∙⇓ {m = π₁ m} {k = []to x ∷ k} τ (↝trans tr-π₁ e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (π₁ m to x) ⇓ t → (π₁ m to x) ⇓ t
        helper (ev-to w w₁) = ev-to w w₁
↝⋆nilto∙⇓ {m = π₂ m} {k = []to x ∷ k} τ (↝trans tr-π₂ e) =           
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (π₂ m to x) ⇓ t → (π₂ m to x) ⇓ t
        helper (ev-to w w₁) = ev-to w w₁
↝⋆nilto∙⇓ {m = x ′ m} {k = []to x₁ ∷ k} τ (↝trans tr-′ e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → ((x ′ m) to x₁) ⇓ t → ((x ′ m) to x₁) ⇓ t
        helper (ev-to w w₁) = ev-to w w₁
↝⋆nilto∙⇓ {m = ⟨ m , m₁ ⟩} {k = π₁∷ k} τ (↝trans tr-∧₁ e) =  
          m⇓n⇓→mk⇓nk⇓ (ev-π₁ ev-∧) k (↝⋆nilto∙⇓ τ e)
↝⋆nilto∙⇓ {m = letbe x m} {k = π₁∷ k} τ (↝trans tr-let e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₁ (⟦ x ∷ ⊡ ⟧ m) ⇓ t → π₁ (letbe x m) ⇓ t
        helper (ev-π₁ w w₁) = ev-π₁ (ev-let w) w₁
↝⋆nilto∙⇓ {m = m to m₁} {k = π₁∷ k} τ (↝trans tr-to e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = force ._} {k = π₁∷ k} τ (↝trans {m₂ = m₂} tr-force e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₁ m₂ ⇓ t → π₁ (force (thunk m₂)) ⇓ t
        helper (ev-π₁ w w₁) = ev-π₁ (ev-force w) w₁
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = π₁∷ k} τ (↝trans (tr-pml {v = v}) e) =  
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₁ (⟦ v ∷ ⊡ ⟧ m) ⇓ t → π₁ (pm inl v left m right m₁) ⇓ t
        helper (ev-π₁ w w₁) = ev-π₁ (ev-pml w) w₁
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = π₁∷ k} τ (↝trans (tr-pmr {v = v}) e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₁ (⟦ v ∷ ⊡ ⟧ m₁) ⇓ t → π₁ (pm inr v left m right m₁) ⇓ t
        helper (ev-π₁ w w₁) = ev-π₁ (ev-pmr w) w₁
↝⋆nilto∙⇓ {m = pm_as ._ m} {k = π₁∷ k} τ (↝trans (tr-pm {v₁ = v₁} {v₂ = v₂}) e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₁ (⟦ v₁ ∷ (v₂ ∷ ⊡) ⟧ m) ⇓ t → π₁ (pm v₁ , v₂ as m) ⇓ t
        helper (ev-π₁ w w₁) = ev-π₁ (ev-pm w) w₁
↝⋆nilto∙⇓ {m = π₁ m} {k = π₁∷ k} τ (↝trans tr-π₁ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = π₂ m} {k = π₁∷ k} τ (↝trans tr-π₂ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = x ′ m} {k = π₁∷ k} τ (↝trans tr-′ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = ⟨ m , m₁ ⟩} {k = π₂∷ k} τ (↝trans tr-∧₂ e) = 
          m⇓n⇓→mk⇓nk⇓ (ev-π₂ ev-∧) k (↝⋆nilto∙⇓ τ e)
↝⋆nilto∙⇓ {m = letbe x m} {k = π₂∷ k} τ (↝trans tr-let e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₂ (⟦ x ∷ ⊡ ⟧ m) ⇓ t → π₂ (letbe x m) ⇓ t
        helper (ev-π₂ w w₁) = ev-π₂ (ev-let w) w₁
↝⋆nilto∙⇓ {m = m to m₁} {k = π₂∷ k} τ (↝trans tr-to e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = force ._} {k = π₂∷ k} τ (↝trans {m₂ = m₂} tr-force e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₂ m₂ ⇓ t → π₂ (force (thunk m₂)) ⇓ t
        helper (ev-π₂ w w₁) = ev-π₂ (ev-force w) w₁
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = π₂∷ k} τ (↝trans (tr-pml {v = v}) e) =  
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₂ (⟦ v ∷ ⊡ ⟧ m) ⇓ t → π₂ (pm inl v left m right m₁) ⇓ t
        helper (ev-π₂ w w₁) = ev-π₂ (ev-pml w) w₁
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = π₂∷ k} τ (↝trans (tr-pmr {v = v}) e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₂ (⟦ v ∷ ⊡ ⟧ m₁) ⇓ t → π₂ (pm inr v left m right m₁) ⇓ t
        helper (ev-π₂ w w₁) = ev-π₂ (ev-pmr w) w₁
↝⋆nilto∙⇓ {m = pm_as ._ m} {k = π₂∷ k} τ (↝trans (tr-pm {v₁ = v₁} {v₂ = v₂}) e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → π₂ (⟦ v₁ ∷ (v₂ ∷ ⊡) ⟧ m) ⇓ t → π₂ (pm v₁ , v₂ as m) ⇓ t
        helper (ev-π₂ w w₁) = ev-π₂ (ev-pm w) w₁
↝⋆nilto∙⇓ {m = π₁ m} {k = π₂∷ k} τ (↝trans tr-π₁ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = π₂ m} {k = π₂∷ k} τ (↝trans tr-π₂ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = x ′ m} {k = π₂∷ k} τ (↝trans tr-′ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = ƛ m} {k = x ∷v k} τ (↝trans tr-ƛ e) = 
          m⇓n⇓→mk⇓nk⇓ (ev-′ ev-ƛ) k (↝⋆nilto∙⇓ τ e)
↝⋆nilto∙⇓ {m = letbe x m} {k = x₁ ∷v k} τ (↝trans tr-let e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (x₁ ′ ⟦ x ∷ ⊡ ⟧ m) ⇓ t → (x₁ ′ letbe x m) ⇓ t
        helper (ev-′ w w₁) = ev-′ (ev-let w) w₁
↝⋆nilto∙⇓ {m = m to m₁} {k = x ∷v k} τ (↝trans tr-to e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = force ._} {k = x₁ ∷v k} τ (↝trans {m₂ = m₂} tr-force e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (x₁ ′ m₂) ⇓ t → (x₁ ′ force (thunk m₂)) ⇓ t
        helper (ev-′ w w₁) = ev-′ (ev-force w) w₁
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = x₁ ∷v k} τ (↝trans (tr-pml {v = v}) e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (x₁ ′ ⟦ v ∷ ⊡ ⟧ m) ⇓ t → (x₁ ′ pm inl v left m right m₁) ⇓ t
        helper (ev-′ w w₁) = ev-′ (ev-pml w) w₁
↝⋆nilto∙⇓ {m = pm_left_right ._ m m₁} {k = x₁ ∷v k} τ (↝trans (tr-pmr {v = v}) e) =
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (x₁ ′ ⟦ v ∷ ⊡ ⟧ m₁) ⇓ t → (x₁ ′ pm inr v left m right m₁) ⇓ t
        helper (ev-′ w w₁) = ev-′ (ev-pmr w) w₁
↝⋆nilto∙⇓ {m = pm_as ._ m} {k = x₁ ∷v k} τ (↝trans (tr-pm {v₁ = v₁} {v₂ = v₃}) e) = 
          m⇓n⇓→mk⇓nk⇓ helper k (↝⋆nilto∙⇓ τ e)
  where helper : ∀ {t} → (x₁ ′ ⟦ v₁ ∷ (v₃ ∷ ⊡) ⟧ m) ⇓ t → (x₁ ′ pm v₁ , v₃ as m) ⇓ t
        helper (ev-′ w w₁) = ev-′ (ev-pm w) w₁ 
↝⋆nilto∙⇓ {m = π₁ m} {k = x ∷v k} τ (↝trans tr-π₁ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = π₂ m} {k = x ∷v k} τ (↝trans tr-π₂ e) = ↝⋆nilto∙⇓ τ e
↝⋆nilto∙⇓ {m = x ′ m} {k = x₁ ∷v k} τ (↝trans tr-′ e) = ↝⋆nilto∙⇓ τ e

↝nilto⇓ : ∀ {β} {m t : CTerm ∅ β} → Terminal (t , nil) → (m , nil) ↝⋆ (t , nil) → m ⇓ t
↝nilto⇓ τ e = ↝⋆nilto∙⇓ τ e


helper : ∀ {∁ : CType} {m : CTerm ∅ ∁} → Terminal (m , nil) → m ⇓ m
helper term-prod = ev-prod
helper term-∧ = ev-∧
helper term-ƛ = ev-ƛ

helper2 : ∀ {∁ β : CType} {m : CTerm ∅ β} {t : CTerm ∅ ∁}
            (k : Outside ∅ ∁ β) {β₂ : CType} {m₂ : CTerm ∅ β₂}
            {k₂ : Outside ∅ ∁ β₂} →
          (m , k) ↝ (m₂ , k₂) → (m₂ ∙ k₂) ⇓ t → (m ∙ k) ⇓ t
helper2 k tr-let s = m⇓n⇓→mk⇓nk⇓ ev-let k s
helper2 k tr-to s = s
helper2 ._ tr-prod s = m⇓n⇓→mk⇓nk⇓ (ev-to ev-prod) _ s
helper2 k tr-force s = {!!}
helper2 k tr-pml s = {!!}
helper2 k tr-pmr s = {!!}
helper2 k tr-pm s = {!!}
helper2 k tr-π₁ s = {!!}
helper2 k tr-π₂ s = {!!}
helper2 ._ tr-∧₁ s = {!!}
helper2 ._ tr-∧₂ s = {!!}
helper2 k tr-′ s = {!!}
helper2 ._ tr-ƛ s = {!!}
-- helper2 {k = k} tr-let t₁ = m⇓n⇓→mk⇓nk⇓ ev-let k t₁
-- helper2 tr-to t₁ = t₁
-- helper2 {k = k} tr-prod t₁ = m⇓n⇓→mk⇓nk⇓ {!ev-pro!} {!!} {!!}
-- helper2 tr-force t₁ = {!!}
-- helper2 tr-pml t₁ = {!!}
-- helper2 tr-pmr t₁ = {!!}
-- helper2 tr-pm t₁ = {!!}
-- helper2 tr-π₁ t₁ = {!!}
-- helper2 tr-π₂ t₁ = {!!}
-- helper2 tr-∧₁ t₁ = {!!}
-- helper2 tr-∧₂ t₁ = {!!}
-- helper2 tr-′ t₁ = {!!}
-- helper2 tr-ƛ t₁ = {!!}

foo : ∀ {∁ β : CType} {m t} {k : Outside ∅ ∁ β} → 
            Terminal (t , nil) → (m , k) ↝⋆ (t , nil) → (m ∙ k) ⇓ t
foo t ↝refl = helper t
foo t₁ (↝trans x s) = helper2 _ x (foo t₁ s)
