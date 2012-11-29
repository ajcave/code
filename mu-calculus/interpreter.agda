module interpreter where
open import mu-ltl
open import normal
open import FinMap
open import Product
open import Unit



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
eval (rec F M N) | inj M' = eval ([ tt , (map3 F (rec F (▹ top) N) (ninj M')) ]t ([ tt ]va N))
eval (out M) with eval M
eval (out M) | ▸ M' = ▸ (out M')
eval (out M) | unfold F M' N = eval (map3 F (unfold F (▹ top) (ninj N)) ([ tt , (ninj M') ]t ([ tt ]va ninj N)))
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