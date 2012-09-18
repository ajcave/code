module Unit where
open import Level

record Unit {a : Level} : Set a where
 constructor tt

Unitz = Unit {zero}
