module paths-rdx where
open import FinMap
open import Unit
open import lambda-rdx
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])

data path (Γ : ctx Unitz) : Set where
 ▹ : (x : var Γ *) -> path Γ
 ƛ : (P : path (Γ , *)) -> path Γ
 m·_ : (P : path Γ) -> path Γ
 _·n : (P : path Γ) -> path Γ
 ⊡ : path Γ

[_]pr : ∀ {Γ Δ} (σ : vsubst Γ Δ) -> (M : path Γ) -> path Δ
[_]pr σ (▹ x) = ▹ (lookup σ x)
[_]pr σ (ƛ P) = ƛ ([ vsub-ext σ ]pr P)
[_]pr σ (m· P) = m· [ σ ]pr P
[_]pr σ (P ·n) = [ σ ]pr P ·n
[_]pr σ ⊡ = ⊡

mutual
 data dctx : Set where
  ⊡ : dctx
  _,_ : (Γ : dctx) -> (x : (Unitz ⊎ (tm ≪ Γ ≫))) -> dctx

 ≪_≫ : dctx -> ctx Unitz
 ≪ ⊡ ≫ = ⊡
 ≪ Γ , x ≫ = ≪ Γ ≫ , *

wknt : ∀ {Γ} -> Unitz ⊎ (tm Γ) -> Unitz ⊎ (tm (Γ , *))
wknt (inj₁ x) = inj₁ *
wknt (inj₂ y) = inj₂ ([ wkn-vsub ]r y)

data dvar : (Γ : dctx) (T : Unitz ⊎ (tm ≪ Γ ≫)) -> Set where
 top : ∀ {Γ T} -> dvar (Γ , T) (wknt T)
 pop : ∀ {Γ T S} -> (x : dvar Γ T) -> dvar (Γ , S) (wknt T)

≪_≫v : ∀ {Γ T} -> dvar Γ T -> var ≪ Γ ≫ *
≪ top ≫v = top
≪ pop x ≫v = pop ≪ x ≫v 

data is-path {Γ : dctx} : path ≪ Γ ≫ -> tm ≪ Γ ≫ -> Set where
 ▹ : (x : dvar Γ (inj₁ *)) -> is-path (▹ ≪ x ≫v) (▹ ≪ x ≫v)
 ▸ : ∀ {N} (xf : dvar Γ (inj₂ N)) -> ∀ Q -> (p1 : is-path Q N) -> is-path Q (▹ ≪ xf ≫v)
 ƛ : ∀ {P} {M} (p : is-path {Γ , inj₁ *} P M) -> is-path (ƛ P) (ƛ M)
 m·_ : ∀ {P M N} (p : is-path P M) -> is-path (m· P) (M · N)
 _·n : ∀ {P M N} (p : is-path P N) -> is-path (P ·n) (M · N)
 rdx : ∀ {P F M} (p : is-path {Γ , inj₂ M} ([ wkn-vsub ]pr P) F) -> is-path P (F [ M ])
 ⊡ : ∀ {M} -> is-path ⊡ M

data reduce {Γ : dctx} : tm ≪ Γ ≫ -> tm ≪ Γ ≫ -> Set where
 ▹ : (x : dvar Γ (inj₁ *)) -> reduce (▹ ≪ x ≫v) (▹ ≪ x ≫v)
 ▸ : ∀ {N} (xf : dvar Γ (inj₂ N)) -> ∀ M -> (r : reduce M N) -> reduce M (▹ ≪ xf ≫v)
 ƛ : ∀ {P} {M} (r : reduce {Γ , inj₁ *} P M) -> reduce (ƛ P) (ƛ M)
 _·_ : ∀ {M M' N N'} (r1 : reduce M M') (r2 : reduce N N') -> reduce (M · N) (M' · N')
 rdx : ∀ {P F M} (r : reduce {Γ , inj₂ M} F ([ wkn-vsub ]r P)) -> reduce (F [ M ]) P


path-preserved : ∀ {Γ : dctx} {M U : tm ≪ Γ ≫} {P} -> reduce M U -> is-path P M -> is-path P U
path-preserved (▹ x) p = p
path-preserved (▸ x M R) p = {!!}  --▸ x _ {!!} --▸ x _ (path-preserved R p)
path-preserved (ƛ r) (ƛ p) = ƛ (path-preserved r p)
path-preserved (ƛ r) ⊡ = ⊡
path-preserved (r1 · r2) (m· p) = m· path-preserved r1 p
path-preserved (r1 · r2) (p ·n) = path-preserved r2 p ·n
path-preserved (r1 · r2) ⊡ = ⊡
path-preserved (rdx p) (rdx p') with path-preserved p p'
... | q = {!!}
path-preserved (rdx p) ⊡ = ⊡


{-
yay : ∀ {Γ} (M : tm Γ) N -> (∀ {P} -> is-path P M -> is-path P N) -> M ≡ N
yay (▹ x) N f with f (▹ x)
yay (▹ x) .(▹ x) f | ▹ .x = refl
yay (ƛ M) N f with f (ƛ ⊡)
yay (ƛ M) .(ƛ M') f | ƛ {.⊡} {M'} p = cong ƛ (yay M M' g)
 where g : ∀ {Q} → is-path Q M → is-path Q M'
       g x with f (ƛ x)
       g x | ƛ p' = p'
yay (M · N) N' f with f (m· ⊡)
yay (M · N) .(M' · N') f | m·_ {.⊡} {M'} {N'} p = cong₂ _·_ (yay M M' g1) (yay N N' g2)
  where g1 : ∀ {Q} -> is-path Q M -> is-path Q M'
        g1 x with f (m· x)
        g1 x | m· p = p

        g2 : ∀ {Q} -> is-path Q N -> is-path Q N'
        g2 x with f (x ·n)
        g2 x | p' ·n = p'
-}


-- yay (M · N) f with f (m· ⊡)
-- yay (M · N) f | m· ⊡ with yay M g
--  where g : ∀ {Q} -> is-path Q M -> is-path Q _
--        g x with f (m· x)
--        g x | m· p = p
-- yay (M · N) | m· ⊡ | refl = ?
