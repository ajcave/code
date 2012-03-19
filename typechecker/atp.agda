module atp where

-- Basic library stuff
record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  first : A
  second : B first

data empty : Set where

record unit : Set where
 constructor *

data eq-result {A : Set} (x : A) : (y : A) -> Set where
 is-equal : eq-result x x
 not-equal : ∀ {y} -> eq-result x y

-- Contexts are lists of types
data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

-- Well-scoped, well-typed de Bruijn indices
data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ S T} -> var Γ T -> var (Γ , S) T

-- We have some unspecified bunch of atomic types
-- We need to be able to test them for equality
postulate
 atomic-type : Set
 atomic-eq? : (P Q : atomic-type) -> eq-result P Q

data type : Set where
 ▹ : (P : atomic-type) -> type 
 _∧_ _∨_ _⊃_ : (A B : type) -> type
 ⊤ ⊥ : type

-- We can decide whether or not two types are equal
eq? : (A B : type) -> eq-result A B
eq? (▹ P) (▹ Q) with atomic-eq? P Q
eq? (▹ P) (▹ .P) | is-equal = is-equal
eq? (▹ P) (▹ Q) | not-equal = not-equal
eq? (A ∧ B) (A' ∧ B') with eq? A A' | eq? B B'
eq? (.A' ∧ .B') (A' ∧ B') | is-equal | is-equal = is-equal
eq? (A ∧ B) (A' ∧ B') | _ | _ = not-equal
eq? (A ∨ B) (A' ∨ B') with eq? A A' | eq? B B'
eq? (.A' ∨ .B') (A' ∨ B') | is-equal | is-equal = is-equal
eq? (A ∨ B) (A' ∨ B') | _ | _ = not-equal
eq? (A ⊃ B) (A' ⊃ B') with eq? A A' | eq? B B'
eq? (.A' ⊃ .B') (A' ⊃ B') | is-equal | is-equal = is-equal
eq? (A ⊃ B) (A' ⊃ B') | _ | _ = not-equal
eq? ⊤ ⊤ = is-equal
eq? ⊥ ⊥ = is-equal
eq? _ _ = not-equal

-- Our grammar. Maintains well-scopedness
mutual
 -- Well-scoped de Bruijn indices. ctx unit is essentially nat
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

-- We can look up a variable in a context to get a type
lookup : ∀ Γ -> var ⌞ Γ ⌟ * -> type
lookup ⊡ ()
lookup (Γ , T) top = T
lookup (Γ , T) (pop x) = lookup Γ x

infix 40 _,_

-- Let's produce typing derivations as output so I don't get it wrong
mutual
 data _⊢_∶_↓ (Γ : ctx type) : (E : neut ⌞ Γ ⌟) (A : type) -> Set where
  ▹ : ∀ {A} (x : var ⌞ Γ ⌟ A)
         -> ------------------------
            Γ ⊢ ▹ x ∶ (lookup Γ x) ↓ 
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

data infer-result Γ E : Set where
 yep : ∀ A -> Γ ⊢ E ∶ A ↓ -> infer-result Γ E
 nope : infer-result Γ E

data check-result Γ I A : Set where
 yep : Γ ⊢ I ∶ A ⇑ -> check-result Γ I A
 nope : check-result Γ I A

mutual
 infer : ∀ Γ E -> infer-result Γ E
 infer Γ (▹ x) = yep (lookup Γ x) (▹ x)
 infer Γ (E · I) with infer Γ E
 ... | yep (A ⊃ B) D with check Γ I A
 ... | yep F = yep B (⊃E D F)
 ... | nope  = nope
 infer Γ (E · I) | _ = nope
 infer Γ (fst E) with infer Γ E
 ... | yep (A ∧ B) D = yep A (∧E₁ D)
 ... | _             = nope
 infer Γ (snd E) with infer Γ E
 ... | yep (A ∧ B) D = yep B (∧E₂ D)
 ... | _             = nope
 infer Γ [ I ∶ A ] with check Γ I A
 ... | yep D = yep A (⇑↓ D)
 ... | nope  = nope

 check : ∀ Γ I A -> check-result Γ I A
 check Γ 〈 I₁ , I₂ 〉 (A ∧ B) with check Γ I₁ A | check Γ I₂ B
 ... | yep D₁ | yep D₂ = yep (∧I D₁ D₂)
 ... | _ | _           = nope
 check Γ 〈 I₁ , I₂ 〉 _ = nope
 check Γ (ƛ I) (A ⊃ B) with check (Γ , A) I B
 ... | yep D = yep (⊃I D)
 ... | nope  = nope 
 check Γ (ƛ I) _ = nope
 check Γ (inl I) (A ∨ B) with check Γ I A
 ... | yep D = yep (∨I₁ D)
 ... | nope  = nope
 check Γ (inl I) _ = nope
 check Γ (inr I) (A ∨ B) with check Γ I B
 ... | yep D = yep (∨I₂ D)
 ... | nope  = nope
 check Γ (inr I) _ = nope
 check Γ (case E of-inl=> I₁ |inr=> I₂) C with infer Γ E
 ... | yep (A ∨ B) D with check (Γ , A) I₁ C | check (Γ , B) I₂ C
 ... | yep D₁ | yep D₂ = yep (∨E D D₁ D₂)
 ... | _ | _           = nope
 check Γ (case E of-inl=> I₁ |inr=> I₂) C | _ = nope
 check Γ 〈〉 ⊤ = yep ⊤I
 check Γ 〈〉 _ = nope
 check Γ (abort E) C with infer Γ E
 ... | yep ⊥ D = yep (⊥E D)
 ... | _       = nope
 check Γ (▸ E) A with infer Γ E
 check Γ (▸ E) A | yep A' D with eq? A A'
 check Γ (▸ E) A | yep .A D | is-equal = yep (↓⇑ D)
 check Γ (▸ E) A | yep A' D | _ = nope
 check Γ (▸ E) A | _ = nope