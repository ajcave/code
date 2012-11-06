module interpreter where
open import mu-ltl

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

eval : ∀ {θ Γ A} -> θ , Γ ⊢ A - true -> θ , Γ ⊢ A ↑
eval (▹ x) = ▸ (▹ x)
eval (ƛ M) = ƛ (eval M)
eval (M · N) with eval M
eval (M · N) | ▸ M' = ▸ (M' · (eval N))
eval (M · N) | ƛ M' = eval ([ truesub-id , ninj (eval N) ]t (ninj M'))
eval (let-◦ M N) with eval M
eval (let-◦ M N) | ▸ M' = ▸ (let-◦ M' (eval N))
eval (let-◦ M N) | ◦ M' = eval ([ validsub-id , ninj M' ]va ninj (eval N))
eval (◦ M) = ◦ (eval M)
eval (inj M) = inj (eval M)
eval (rec F M N) with eval M
eval (rec F M N) | ▸ M' = ▸ (rec F M' (eval N))
eval (rec F M N) | inj M' = eval ([ ⊡ , (map3 F (rec F (▹ top) N) (ninj M')) ]t ([ ⊡ ]va N))
eval (out M) with eval M
eval (out M) | ▸ M' = ▸ (out M')
eval (out M) | unfold F M' N = eval (map3 F (unfold F (▹ top) (ninj N)) ([ ⊡ , (ninj M') ]t ([ ⊡ ]va ninj N)))
eval (unfold F M N) = unfold F (eval M) (eval N)
eval < M , N > = < (eval M) , (eval N) >
eval (fst M) with eval M
eval (fst M) | ▸ M' = ▸ (fst M')
eval (fst M) | < M' , N > = M'
eval (snd M) with eval M
eval (snd M) | ▸ M' = ▸ (snd M')
eval (snd M) | < M' , N > = N
eval (inl M) = inl (eval M)
eval (inr M) = inr (eval M)
eval (case M N1 N2) with eval M
eval (case M N1 N2) | ▸ M' = ▸ (case M' (eval N1) (eval N2))
eval (case M N1 N2) | inl M' = eval ([ truesub-id , (ninj M') ]t N1)
eval (case M N1 N2) | inr M' = eval ([ truesub-id , ninj M' ]t N2)
eval unit = unit

nat : ∀ {ζ} -> functor ζ
nat = μ (⊤ ∨ ▹ top)
 
plus : ∀ {θ Γ} -> θ , Γ ⊢ (nat ⊃ (nat ⊃ nat)) - true
plus = ƛ (rec _ (▹ top) (case (▹ top) (ƛ (▹ top)) (ƛ (inj (inr ((▹ (pop top)) · (▹ top)))))))

two : ∀ {θ Γ} -> θ , Γ ⊢ nat - true
two = inj (inr (inj (inr (inj (inl unit)))))

infixl 9 _·_

test : ∀ {θ Γ} -> θ , Γ ⊢ nat - true
test = (plus · two) · two

□ : (∀ {ζ} -> functor ζ) -> prop
□ A = ν (A ∧ ○ (▹ top))

imp : ∀ {θ Γ} -> θ , Γ ⊢ (nat ⊃ ○ nat) - true
imp = ƛ (rec _ (▹ top) (case (▹ top) (◦ (inj (inl unit))) (let-◦ (▹ top) (◦ (inj (inr (▹ top)))))))

psum : ∀ {θ Γ} -> θ , Γ ⊢ (nat ⊃ (□ nat ⊃ □ nat)) - true
psum = ƛ (ƛ (unfold _ < ▹ top , ▹ (pop top) > < ((plus · snd (▹ top)) · fst (out (fst (▹ top)))) ,
  let-◦ (imp · ((plus · snd (▹ top)) · fst (out (fst (▹ top)))))
  (let-◦ (snd (out (fst (▹ top)))) (◦ < (▹ top) , (▹ (pop top)) >)) >))

take3 : ∀ {θ Γ} -> θ , Γ ⊢ (□ nat) ⊃ (nat ∧ (○ (nat ∧ (○ nat)))) - true
take3  = ƛ < (fst (out (▹ top))) , let-◦ (snd (out (▹ top))) (◦ < fst (out (▹ top)) , let-◦ (snd (out (▹ top))) (◦ (fst (out (▹ top)))) >) >

count : ∀ {θ Γ} -> θ , Γ ⊢ □ nat - true
count = unfold _ {nat} (inj (inr (inj (inl unit)))) < (▹ top) , (let-◦ (imp · ▹ top) (◦ (inj (inr (▹ top))))) >

test1 : ∀ {θ Γ} -> θ , Γ ⊢ (nat ∧ (○ (nat ∧ (○ nat)))) - true
test1 = take3 · count

test2 : ∀ {θ Γ} -> θ , Γ ⊢ (nat ∧ (○ (nat ∧ (○ nat)))) - true
test2 = take3 · ((psum · inj (inl unit)) · count)