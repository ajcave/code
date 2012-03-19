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

infix 40 _,_

mutual
 data _⊢_∶_↓ (Γ : ctx type) : (E : neut ⌞ Γ ⌟) (A : type) -> Set where
  ▹ : ∀ {A} (x : var Γ A)
         -> ----------------
            Γ ⊢ ▹ < x > ∶ A ↓ 
  ⊃E : ∀ {A B E I} -> Γ ⊢ E ∶ (A ⊃ B) ↓ -> Γ ⊢ I ∶ A ⇑
                   -> -------------------------------
                          Γ ⊢ (E · I) ∶ B ↓
  ∧E₁ : ∀ {A B E} -> Γ ⊢ E ∶ (A ∧ B) ↓
                  -> -----------------
                     Γ ⊢ fst E ∶ A ↓
  ∧E₂ : ∀ {A B E} -> Γ ⊢ E ∶ (A ∧ B) ↓
                  -> -----------------
                     Γ ⊢ snd E ∶ B ↓
  ⇑↓ : ∀ {A I} ->    Γ ⊢ I ∶ A ⇑
               -> ------------------
                  Γ ⊢ [ I ∶ A ] ∶ A ↓
 data _⊢_∶_⇑ (Γ : ctx type) : (I : norm ⌞ Γ ⌟) (A : type) -> Set where 
  ∧I : ∀ {A B I₁ I₂} -> Γ ⊢ I₁ ∶ A ⇑ -> Γ ⊢ I₂ ∶ B ⇑
                     -> ---------------------------
                         Γ ⊢ 〈 I₁ , I₂ 〉 ∶ (A ∧ B) ⇑
  ⊃I : ∀ {A B I} -> Γ , A ⊢ I ∶ B ⇑
                 -> ---------------
                    Γ ⊢ ƛ I ∶ A ⊃ B ⇑
  ∨I₁ : ∀ {A B I} ->      Γ ⊢ I ∶ A ⇑
                  -> ---------------------
                     Γ ⊢ inl I ∶ (A ∨ B) ⇑
  ∨I₂ : ∀ {A B I} ->      Γ ⊢ I ∶ B ⇑
                  -> ---------------------
                     Γ ⊢ inr I ∶ (A ∨ B) ⇑
  ∨E : ∀ {A B C E I₁ I₂} -> Γ ⊢ E ∶ (A ∨ B) ↓ -> Γ , A ⊢ I₁ ∶ C ⇑ -> Γ , B ⊢ I₂ ∶ C ⇑
                         -> --------------------------------------------------------
                                   Γ ⊢ case E of-inl=> I₁ |inr=> I₂ ∶ C ⇑
  ⊤I : Γ ⊢ 〈〉 ∶ ⊤ ⇑
  ⊥E : ∀ {E C} ->    Γ ⊢ E ∶ ⊥ ↓
               -> -----------------
                  Γ ⊢ abort E ∶ C ⇑
  ↓⇑ : ∀ {E A} ->    Γ ⊢ E ∶ A ↓
               -> -----------------
                   Γ ⊢ (▸ E) ∶ A ⇑