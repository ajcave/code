module atp where

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

-- Well-scoped, well-typed de Bruijn indices
data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ S T} -> var Γ T -> var (Γ , S) T

record unit : Set where
 constructor *

postulate
 atomic-type : Set

data type : Set where
 ▹ : (P : atomic-type) -> type 
 _∧_ _∨_ _⊃_ : (A B : type) -> type
 ⊤ ⊥ : type

mutual
 -- Well-scoped de Bruijn indices
 data neut (Γ : ctx unit) : Set where
  ▹ : (x : var Γ *) -> neut Γ -- variables are neutral
  _·_ : (E : neut Γ) (I : norm Γ) -> neut Γ -- application
  fst snd : (E : neut Γ) -> neut Γ
  [_∶_] : (I : norm Γ) (A : type) -> neut Γ -- coercion
 data norm (Γ : ctx unit) : Set where
  〈_,_〉 : (I₁ I₂ : norm Γ) -> norm Γ
  ƛ : (I : norm (Γ , *)) -> norm Γ -- A term in an extended context can be lambda abstracted
  inl inr : (I : norm Γ) -> norm Γ
  case_of-inl=>_|inr=>_ : (E : neut Γ) (I₁ I₂ : norm (Γ , *)) -> norm Γ
  〈〉 : norm Γ
  abort : (E : neut Γ) -> norm Γ
  ▸ : (E : neut Γ) -> norm Γ

-- The list length function
⌞_⌟ : ctx type -> ctx unit
⌞ ⊡ ⌟ = ⊡
⌞ Γ , T ⌟ = ⌞ Γ ⌟ , *

<_> : ∀ {Γ T} -> var Γ T -> var ⌞ Γ ⌟ *
<_> {Γ} x = {!!}

mutual
 data _⊢_∶_↓ (Γ : ctx type) : (E : neut ⌞ Γ ⌟) (A : type) -> Set where
  ▹ : ∀ {A} (x : var Γ A)
         -> ----------------
            Γ ⊢ ▹ < x > ∶ A ↓ 
  _·_ : ∀ {A B E I} -> Γ ⊢ E ∶ (A ⊃ B) ↓ -> Γ ⊢ I ∶ A ⇑
                    -> -------------------------------
                           Γ ⊢ (E · I) ∶ B ↓
  fst : ∀ {A B E} -> Γ ⊢ E ∶ (A ∧ B) ↓
                  -> -----------------
                     Γ ⊢ fst E ∶ A ↓
  snd : ∀ {A B E} -> Γ ⊢ E ∶ (A ∧ B) ↓
                  -> -----------------
                     Γ ⊢ snd E ∶ B ↓
  [_∶_] : ∀ {A I} -> Γ ⊢ I ∶ A ⇑
                 -> ---------------
                     Γ ⊢ [ I ∶ A ] ∶ A ↓
 data _⊢_∶_⇑ (Γ : ctx type) : (I : norm ⌞ Γ ⌟) (A : type) -> Set where 
  