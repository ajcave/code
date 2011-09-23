module cc where

postulate
 O : Set

data tp : Set where
 ▹ : O -> tp
 _×_ : tp -> tp -> tp

postulate
 var : tp -> tp -> Set

data exp : tp -> tp -> Set where
 ▹ : ∀ {t s} -> var t s -> exp t s
 _∘_ : ∀ {t u s} -> exp t u -> exp u s -> exp t s
 [_,_] : ∀ {t u s} -> exp t u -> exp t s -> exp t (u × s)
 π₁ : ∀ {t s} -> exp (t × s) t
 π₂ : ∀ {t s} -> exp (t × s) s
 id : ∀ {t} -> exp t t