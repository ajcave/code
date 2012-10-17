module paths where
open import FinMap
open import Unit
open import lambda
open import Relation.Binary.PropositionalEquality

data path (Γ : ctx Unitz) : Set where
 ▹ : (x : var Γ *) -> path Γ
 ƛ : (P : path (Γ , *)) -> path Γ
 m·_ : (P : path Γ) -> path Γ
 _·n : (P : path Γ) -> path Γ
 ⊡ : path Γ

data is-path {Γ : ctx Unitz} : path Γ -> tm Γ -> Set where
 ▹ : (x : var Γ *) -> is-path (▹ x) (▹ x)
 ƛ : ∀ {P M} (p : is-path P M) -> is-path (ƛ P) (ƛ M)
 m·_ : ∀ {P M N} (p : is-path P M) -> is-path (m· P) (M · N)
 _·n : ∀ {P M N} (p : is-path P N) -> is-path (P ·n) (M · N)
 ⊡ : ∀ {M} -> is-path ⊡ M

yay : ∀ {Γ} (M : tm Γ) N -> (∀ {P} -> is-path P M -> is-path P N) -> M ≡ N
yay (▹ x) N f with f (▹ x)
yay (▹ x) .(▹ x) f | ▹ .x = refl
yay (ƛ M) N f = {!!}
yay (M · N) N' f with f (m· ⊡)
yay (M · N) .(M' · N') f | m·_ {.⊡} {M'} {N'} p = cong₂ _·_ (yay M M' g1) (yay N N' g2)
  where g1 : ∀ {Q} -> is-path Q M -> is-path Q M'
        g1 x with f (m· x)
        g1 x | m· p = p

        g2 : ∀ {Q} -> is-path Q N -> is-path Q N'
        g2 x with f (x ·n)
        g2 x | p' ·n = p'


-- yay (M · N) f with f (m· ⊡)
-- yay (M · N) f | m· ⊡ with yay M g
--  where g : ∀ {Q} -> is-path Q M -> is-path Q _
--        g x with f (m· x)
--        g x | m· p = p
-- yay (M · N) | m· ⊡ | refl = ?
