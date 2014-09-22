module ModelProperties where
open import Syntax
open import SyntaxTm
open import Model
open import Sym
open import Cumulativity
open Syn Exp
open import Data.Product
open import Eval
open import Util

type-inv : ∀ {T S} -> T ≈ S ∈ App Type -> ∃ (λ n -> T ≈ S ∈ App (SetU n))
type-inv (inj b1 b2 red1 red2 (n , rel)) = , inj _ _ red1 red2 rel

hsymω :  ∀ {A A'} (pA : A ≈ A' ∈ App Type) (pA' : A' ≈ A ∈ App Type)
   -> ∀ {a b} -> ⟦ pA ⟧tp a b -> ⟦ pA' ⟧tp b a
hsymω pA pA' x = hsym* (proj₂ (type-inv pA)) (proj₂ (type-inv pA')) x

⟦,⟧ctx-sym : ∀ {Γ : Ctx} {p : ⊨ Γ ctx} -> SYM ⟦ Γ , p ⟧ctx
⟦,⟧ctx-sym {⊡} {tt} {⊡} {⊡} x = tt
⟦,⟧ctx-sym {Γ , S} {vΓ , vT} {a Syn., a₁} {b Syn., a₂} (r1 , r2) = (⟦,⟧ctx-sym r1) , hsymω (vT r1) (vT (⟦,⟧ctx-sym r1)) r2 
⟦,⟧ctx-sym {⊡} {tt} {Syn.⊡} {b Syn., a} ()
⟦,⟧ctx-sym {⊡} {tt} {a Syn., a₁} {Syn.⊡} ()
⟦,⟧ctx-sym {⊡} {tt} {a Syn., a₁} {b Syn., a₂} ()
⟦,⟧ctx-sym {Γ , S} {proj₁ , proj₂} {Syn.⊡} {Syn.⊡} ()
⟦,⟧ctx-sym {Γ , S} {proj₁ , proj₂} {Syn.⊡} {b Syn., a} ()
⟦,⟧ctx-sym {Γ , S} {proj₁ , proj₂} {a Syn., a₁} {Syn.⊡} ()