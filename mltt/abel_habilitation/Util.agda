module Util where

PREL : Set -> Set₁
PREL α = α -> α -> Set

_→₂_ : ∀ {A : Set} (P Q : PREL A) -> Set
P →₂ Q = ∀ {a b} -> P a b -> Q a b