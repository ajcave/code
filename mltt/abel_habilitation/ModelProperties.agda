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

hsymω' :  ∀ {k A A'} (pA : A ≈ A' ∈ App (SetU k)) (pA' : A' ≈ A ∈ App (SetU k))
   -> ∀ {a b} -> ElU _ (App.rel pA) a b -> ElU _ (App.rel pA') b a
hsymω' pA pA' x = hsymElω' (App.rel pA') (AppDeter1 pA' pA) (AppDeter2 pA pA') (App.rel pA) x

type-inv : ∀ {T S} -> T ≈ S ∈ App Type -> ∃ (λ n -> T ≈ S ∈ App (SetU n))
type-inv (inj b1 b2 red1 red2 (n , rel)) = , inj _ _ red1 red2 rel

hsymω :  ∀ {A A'} (pA : A ≈ A' ∈ App Type) (pA' : A' ≈ A ∈ App Type)
   -> ∀ {a b} -> ⟦ pA ⟧tp a b -> ⟦ pA' ⟧tp b a
hsymω pA pA' x with hsymω' (proj₂ (type-inv pA)) {! (proj₂ (type-inv pA')) !} x
... | q = {!!}

⟦,⟧ctx-sym : ∀ {Γ : Ctx} {p : ⊨ Γ ctx} -> SYM ⟦ Γ , p ⟧ctx
⟦,⟧ctx-sym {⊡} {tt} {⊡} {⊡} x = tt
⟦,⟧ctx-sym {⊡} {tt} {Syn.⊡} {b Syn., a} ()
⟦,⟧ctx-sym {⊡} {tt} {a Syn., a₁} {Syn.⊡} ()
⟦,⟧ctx-sym {⊡} {tt} {a Syn., a₁} {b Syn., a₂} ()
⟦,⟧ctx-sym {Γ , S} {proj₁ , proj₂} {Syn.⊡} {Syn.⊡} ()
⟦,⟧ctx-sym {Γ , S} {proj₁ , proj₂} {Syn.⊡} {b Syn., a} ()
⟦,⟧ctx-sym {Γ , S} {proj₁ , proj₂} {a Syn., a₁} {Syn.⊡} ()
⟦,⟧ctx-sym {Γ , S} {vΓ , vT} {a Syn., a₁} {b Syn., a₂} (r1 , r2) = (⟦,⟧ctx-sym r1) , hsymω (vT r1) (vT (⟦,⟧ctx-sym r1)) r2 -- hsymω (App.rel (vT r1)) {!!} r2