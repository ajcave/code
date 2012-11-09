module soundness where
open import mu-ltl
open import semantics-noirr
open import opsem
open import FinMap
open import Product
open import Unit
open import normal
open import Function
open import Relation.Binary.PropositionalEquality

compositional : ∀ {θ Γ1 Γ2 T} (M : θ , Γ1 ⊢ T - true) (σ : truesub θ Γ2 Γ1) -> eval θ Γ2 T ([ σ ]t M) ≡ (eval θ Γ1 T M) ∘⁺ {!!}
compositional M σ = {!!}

λ⁺β : ∀ {B Γ C} (m : (Γ ∧⁺ B) ⇒ C) (n : Γ ⇒ B) -> ((λ⁺ {B} m) ·⁺ n) ≡ m ∘⁺ < (id⁺ Γ) , n >⁺
λ⁺β (m , mf) (n , nf) = {!use heterogeneous equality and a dependent cong₂?!}

π₁β1 : ∀ {Γ A B} (m : Γ ⇒ A) (n : Γ ⇒ B) -> (π₁⁺ {B} ∘⁺ < m , n >⁺) ≡ m
π₁β1 (m , mf) n = cong (_,_ m) (funext-imp (λ x → funext-imp (λ x' → funext (λ x0 → funext (λ x1 → K _ _)))))

π₂β1 : ∀ {Γ A B} (m : Γ ⇒ A) (n : Γ ⇒ B) -> (π₂⁺ {A} ∘⁺ < m , n >⁺) ≡ n
π₂β1 m (n , nf) = cong (_,_ n) (funext-imp (λ x → funext-imp (λ x' → funext (λ x0 → funext (λ x1 → K _ _)))))

sound : ∀ T {N M : ⊡ , ⊡ ⊢ T - true} -> (N ⟶ M) -> eval ⊡ ⊡ T N ≡ eval ⊡ ⊡ T M
sound T (app-red1 M M' N y) = cong₂ _·⁺_ (sound _ y) refl
sound T (app-red2 V N N' y) = cong (_·⁺_ (eval ⊡ ⊡ _ (ninj V))) (sound _ y)
sound T (app-red3 M V) = {!!}
sound .(A ∧ B) (pair-red1 {A} {B} M M' N y) = cong (flip <_,_>⁺ (eval ⊡ ⊡ B N)) (sound A y)
sound .(A ∧ B) (pair-red2 {A} {B} V N N' y) = cong (<_,_>⁺ (eval ⊡ ⊡ A (ninj V))) (sound B y)
sound T (fst-red1 {.T} {B} M M' y) = cong (_∘⁺_ (π₁⁺ {⟦ B ⟧t})) (sound _ y)
sound T (fst-red2 V1 V2) = π₁β1 (eval ⊡ ⊡ _ (ninj V1)) (eval ⊡ ⊡ _ (ninj V2))
sound T (snd-red1 {A} M M' y) = cong (_∘⁺_ (π₂⁺ {⟦ A ⟧t})) (sound _ y)
sound T (snd-red2 V1 V2) = π₂β1 (eval ⊡ ⊡ _ (ninj V1)) (eval ⊡ ⊡ _ (ninj V2))
sound .(A ∨ B) (inl-red {B} {A} M M' y) = cong (_∘⁺_ (inj₁⁺ ⟦ B ⟧t)) (sound A y)
sound .(A ∨ B) (inr-red {A} {B} M M' y) = cong (_∘⁺_ (inj₂⁺ ⟦ A ⟧t)) (sound B y)
sound T (case-red1 {A} {B} M M' N1 N2 y) = {!!} --cong (λ α → case⁺' {⟦ ⊡ ⟧c} {⟦ ⊡ ⟧c} α (eval ⊡ (⊡ , A) T N1) (eval ⊡ (⊡ , B) T N2)) (sound (A ∨ B) y)
sound T (case-red2 V N1 N2) = {!!}
sound T (case-red3 V N1 N2) = {!!}
sound .(○ A) (circ-red {A} M M' y) = cong (◦⁺ ⟦ ⊡ ⟧c ⟦ ⊡ ⟧c ⟦ A ⟧t) (sound A y) 
sound T (let◦-red1 {S} M M' N y) = cong (flip (let-◦⁺ ⟦ ⊡ ⟧c ⟦ ⊡ ⟧c ⟦ T ⟧t ⟦ S ⟧t) (eval (⊡ , S) ⊡ T N)) (sound (○ S) y)
sound T (let◦-red2 V N) = {!!}
sound .(μ F) (inj-red {F} M M' y) = {!!}
sound T (rec-red1 N N' M y) = {!!}
sound T (rec-red2 V M) = {!!}
sound .([ tt , ν F ]p F) (out-red1 {F} M M' y) = {!!}
sound .(ν F) (unfold-red {F} N N' M y) = {!!}
sound .([ tt , ν F ]p F) (out-red2 {F} V M) = {!!}

