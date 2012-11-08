module normal where
open import mu-ltl
open import FinMap
open import Product
open import Unit

mutual
 data _,_⊢_⇓ (θ : ctx prop) (Γ : ctx prop) : prop -> Set where
  ▹ : ∀ {A} -> (x : var Γ A)
            -> -------------------
                θ , Γ ⊢ A ⇓
  _·_ : ∀ {A B} -> (M : θ , Γ ⊢ (A ⊃ B) ⇓) (N : θ , Γ ⊢ A ↑)
                -> -----------------------------------------------------------
                                θ , Γ ⊢ B ⇓

  rec : ∀ F {C} -> (M : θ , Γ ⊢ μ F ⇓) -> (N : ⊡ , (⊡ , [ C /x]p F) ⊢ C ↑)
                -> -------------------------------------------------------------------
                                θ , Γ ⊢ C ⇓
  out : ∀ {F} -> (M : θ , Γ ⊢ ν F ⇓)
              -> -----------------------------------
                 θ , Γ ⊢ ([ ν F /x]p F) ⇓

  fst : ∀ {A B} -> (M : θ , Γ ⊢ (A ∧ B) ⇓)
                -> -----------------------------
                       θ , Γ ⊢ A ⇓
  snd : ∀ {A B} -> (M : θ , Γ ⊢ (A ∧ B) ⇓)
                -> -----------------------------
                       θ , Γ ⊢ B ⇓
  let-◦ : ∀ {A C} (M : θ , Γ ⊢ (○ A) ⇓) (N : (θ , A) , Γ ⊢ C ↑)
                   -> ---------------------------------------------------------------
                                          θ , Γ ⊢ C ⇓

  case : ∀ {A B C} -> (M : θ , Γ ⊢ (A ∨ B) ⇓) -> (N1 : θ , (Γ , A) ⊢ C ↑) (N2 : θ , (Γ , B) ⊢ C ↑)
                   -> θ , Γ ⊢ C ⇓
 data _,_⊢_↑ (θ : ctx prop) (Γ : ctx prop) : prop -> Set where
  ▸ : ∀ {A} -> (M : θ , Γ ⊢ A ⇓)
            -> -----------------
                 θ , Γ ⊢ A ↑
  ƛ : ∀ {A B} -> (M : θ , (Γ , A) ⊢ B ↑)
              -> ----------------------------------
                      θ , Γ ⊢ (A ⊃ B) ↑
  ◦ : ∀ {A} -> (M : ⊡ , θ ⊢ A ↑)
              -> --------------------------
                   θ , Γ ⊢ (○ A) ↑
  inj : ∀ {F} -> (M : θ , Γ ⊢ ([ μ F /x]p F) ↑)
              -> -----------------------------------------------------
                              θ , Γ ⊢ μ F ↑
  unfold : ∀ F {C} -> (M : θ , Γ ⊢ C ↑) -> (N : ⊡ , (⊡ , C) ⊢ ([ C /x]p F) ↑)
                   -> -------------------------------------------------------------
                       θ , Γ ⊢ ν F ↑
  <_,_> : ∀ {A B} -> (M : θ , Γ ⊢ A ↑) (N : θ , Γ ⊢ B ↑)
                  -> ---------------------------------------------
                                θ , Γ ⊢ (A ∧ B) ↑
  inl : ∀ {A B} -> (M : θ , Γ ⊢ A ↑)
                -> ------------------------
                      θ , Γ ⊢ (A ∨ B) ↑
  inr : ∀ {A B} -> (M : θ , Γ ⊢ B ↑)
                -> ------------------------
                      θ , Γ ⊢ (A ∨ B) ↑
  unit : θ , Γ ⊢ ⊤ ↑

mutual
 rinj : ∀ {θ Γ A} -> θ , Γ ⊢ A ⇓ -> θ , Γ ⊢ A - true
 rinj (▹ x) = ▹ x
 rinj (M · N) = rinj M · ninj N
 rinj (rec F M N) = rec F (rinj M) (ninj N)
 rinj (out M) = out (rinj M)
 rinj (fst M) = fst (rinj M)
 rinj (snd M) = snd (rinj M)
 rinj (let-◦ M N) = let-◦ (rinj M) (ninj N)
 rinj (case M N1 N2) = case (rinj M) (ninj N1) (ninj N2)
 ninj : ∀ {θ Γ A} -> θ , Γ ⊢ A ↑ -> θ , Γ ⊢ A - true
 ninj (▸ M) = rinj M
 ninj (ƛ M) = ƛ (ninj M)
 ninj (◦ M) = ◦ (ninj M)
 ninj (inj M) = inj (ninj M)
 ninj (unfold F M N) = unfold F (ninj M) (ninj N)
 ninj < M , N > = < (ninj M) , (ninj N) >
 ninj (inl M) = inl (ninj M)
 ninj (inr M) = inr (ninj M)
 ninj unit = unit