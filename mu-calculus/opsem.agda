module opsem where
open import mu-ltl
open import normal
open import FinMap
open import Product
open import Unit

-- full reduction
data step {θ Γ} : ∀ {A J} -> θ , Γ ⊢ A - J -> θ , Γ ⊢ A - J -> Set where
 circ-red : ∀ {A C} (M : ⊡ , θ ⊢ A - true) (N : (θ , A) , Γ ⊢ C - true)
                -> step (let-◦ (◦ M) N) ([ validsub-id , M ]va N)
 rec-red : ∀ {F C} (M : θ , Γ ⊢ ([ μ F /x]p F) - true) (N : ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                -> step (rec F (inj M) N) ([ tt , (map3 F (rec F (▹ top) N) M) ]t ([ tt ]va N))
 out-red : ∀ {F C} (M : θ , Γ ⊢ C - true) (N : ⊡ , ⊡ , C ⊢ [ C /x]p F - true)
                -> step (out (unfold F M N)) (map3 F (unfold F (▹ top) N) ([ tt , M ]t ([ tt ]va N)))
 app-red : ∀ {A B} (M : θ , (Γ , A) ⊢ B - true) (N : θ , Γ ⊢ A - true)
                -> step ((ƛ M) · N) ([ truesub-id , N ]t M)
 fst-red : ∀ {A B} (M : θ , Γ ⊢ A - true) (N : θ , Γ ⊢ B - true)
                -> step (fst < M , N >) M
 snd-red : ∀ {A B} (M : θ , Γ ⊢ A - true) (N : θ , Γ ⊢ B - true)
                -> step (snd < M , N >) N

-- CBV reduction
data _⟶_ {θ Γ} : ∀ {A J} -> θ , Γ ⊢ A - J -> θ , Γ ⊢ A - J -> Set where
 app-red1 : ∀ {A B} (M M' : θ , Γ ⊢ (A ⊃ B) - true) (N : θ , Γ ⊢ A - true)
                ->       M ⟶ M'
                -> ------------------
                   (M · N) ⟶ (M' · N)
 app-red2 : ∀ {A B} (V : θ , Γ ⊢ (A ⊃ B) ↑) (N N' : θ , Γ ⊢ A - true)
                ->       N ⟶ N'
                -> ------------------
                   ((ninj V) · N) ⟶ ((ninj V) · N')
 app-red3 : ∀ {A B} (M : θ , (Γ , A) ⊢ B - true) (V : θ , Γ ⊢ A ↑)
                -> ((ƛ M) · (ninj V)) ⟶ ([ truesub-id , (ninj V) ]t M)
 pair-red1 : ∀ {A B} (M M' : θ , Γ ⊢ A - true) (N : θ , Γ ⊢ B - true)
                ->           M ⟶ M'
                -> ---------------------------
                     < M , N > ⟶ < M' , N >
 pair-red2 : ∀ {A B} (V : θ , Γ ⊢ A ↑) (N N' : θ , Γ ⊢ B - true)
                ->           N ⟶ N'
                -> ---------------------------
                     < (ninj V) , N > ⟶ < (ninj V) , N' >
 fst-red1 : ∀ {A B} (M M' : θ , Γ ⊢ (A ∧ B) - true)
                ->           M ⟶ M'
                -> --------------------------
                      (fst M) ⟶ (fst M')
 fst-red2 : ∀ {A B} (V1 : θ , Γ ⊢ A ↑) (V2 : θ , Γ ⊢ B ↑)
                -> (fst < (ninj V1) , (ninj V2) >) ⟶ (ninj V1)
 snd-red1 : ∀ {A B} (M M' : θ , Γ ⊢ (A ∧ B) - true)
                ->           M ⟶ M'
                -> --------------------------
                      (snd M) ⟶ (snd M')
 snd-red2 : ∀ {A B} (V1 : θ , Γ ⊢ A ↑) (V2 : θ , Γ ⊢ B ↑)
                -> (snd < (ninj V1) , (ninj V2) >) ⟶ (ninj V2)
 inl-red : ∀ {B A} (M M' : θ , Γ ⊢ A - true)
                ->                M ⟶ M'
                -> -------------------------
                    (inl {B = B} M) ⟶ (inl M')
 inr-red : ∀ {A B} (M M' : θ , Γ ⊢ B - true)
                ->                M ⟶ M'
                -> -------------------------
                    (inr {A = A} M) ⟶ (inr M')
 case-red1 : ∀ {A B C} (M M' : θ , Γ ⊢ (A ∨ B) - true) (N1 : θ , (Γ , A) ⊢ C - true) (N2 : θ , (Γ , B) ⊢ C - true)
                ->              M ⟶ M'
                -> --------------------------------
                   (case M N1 N2) ⟶ (case M' N1 N2)
 case-red2 : ∀ {A B C} (V : θ , Γ ⊢ A ↑) (N1 : θ , (Γ , A) ⊢ C - true) (N2 : θ , (Γ , B) ⊢ C - true)
                -> --------------------------------------------------------------
                   (case (inl (ninj V)) N1 N2) ⟶ ([ truesub-id , (ninj V) ]t N1)
 case-red3 : ∀ {A B C} (V : θ , Γ ⊢ B ↑) (N1 : θ , (Γ , A) ⊢ C - true) (N2 : θ , (Γ , B) ⊢ C - true)
                -> --------------------------------------------------------------
                   (case (inr (ninj V)) N1 N2) ⟶ ([ truesub-id , (ninj V) ]t N2)
 circ-red : ∀ {A} (M M' : ⊡ , θ ⊢ A - true)
                ->           M ⟶ M'
                -> -------------------------
                         (◦ M) ⟶ (◦ M')
 let◦-red1 : ∀ {A C} (M M' : θ , Γ ⊢ ○ A - true) (N : (θ , A) , Γ ⊢ C - true)
                ->           M ⟶ M'
                -> ---------------------------
                   (let-◦ M N) ⟶ (let-◦ M' N)
 let◦-red2 : ∀ {A C} (V : ⊡ , θ ⊢ A ↑) (N : (θ , A) , Γ ⊢ C - true)
                -> (let-◦ (◦ (ninj V)) N) ⟶ ([ validsub-id , (ninj V) ]va N)
 inj-red : ∀ {F} (M M' : θ , Γ ⊢ ([ μ F /x]p F) - true)
                ->              M ⟶ M'
                -> -----------------------------
                    inj {F = F} M ⟶ inj {F = F} M'
 rec-red1 : ∀ {F C} (N N' : θ , Γ ⊢ μ F - true) (M : ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                ->           N ⟶ N'
                -> ---------------------------
                   (rec F N M) ⟶ (rec F N' M)
 rec-red2 : ∀ {F C} (V : θ , Γ ⊢ ([ μ F /x]p F) ↑) (M : ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                -> (rec F (inj (ninj V)) M) ⟶ ([ tt , (map3 F (rec F (▹ top) M) (ninj V)) ]t ([ tt ]va M))
 out-red1 : ∀ {F} (M M' : θ , Γ ⊢ ν F - true)
                ->                 M ⟶ M'
                -> ------------------------------------
                     (out {F = F} M) ⟶ (out {F = F} M)
 unfold-red : ∀ {F C} (N N' : θ , Γ ⊢ C - true) (M : ⊡ , ⊡ , C ⊢ [ C /x]p F - true) 
                ->              N ⟶ N'
                -> ---------------------------------
                   (unfold F N M) ⟶ (unfold F N' M)
 out-red2 : ∀ {F C} (V : θ , Γ ⊢ C ↑) (M : ⊡ , ⊡ , C ⊢ [ C /x]p F - true)
                -> (out (unfold F (ninj V) M)) ⟶ (map3 F (unfold F (▹ top) M) ([ tt , (ninj V) ]t ([ tt ]va M)))
 
data _⟶*_ {θ Γ} {A} : θ , Γ ⊢ A - true -> θ , Γ ⊢ A - true -> Set where
 refl : ∀ {M} -> M ⟶* M
 trans1 : ∀ {M N P} -> M ⟶ N -> N ⟶* P -> M ⟶* P
