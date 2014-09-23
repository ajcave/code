module ModelProperties where
open import Syntax
open import SyntaxTm
open import Model
open import Sym
open import Transitivity
open import Cumulativity
open Syn Exp
open import Data.Product
open import Eval
open import Util
open import Function
open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])

type-inv : ∀ {T S} -> T ≈ S ∈ App Type -> ∃ (λ n -> T ≈ S ∈ App (SetU n))
type-inv (inj red1 red2 (n , rel)) = , inj red1 red2 rel

hsymω :  HSYM (App Type) ⟦_⟧tp (App Type) ⟦_⟧tp
hsymω pA pA' x = hsym* (proj₂ (type-inv pA)) (proj₂ (type-inv pA')) x

htransω0 : HTRANS (App Type) ⟦_⟧tp
htransω0
 (inj (_ , red1) (_ , red2) rel)
 (inj (_ , red3) (_ , red4) rel')
 (inj (_ , red5) (_ , red6) rel0)
 r1 r2 with eval-deter red1 red5 | eval-deter red2 red3 | eval-deter red4 red6
htransω0 (inj (._ , red1) (._ , red2) rel) (inj (_ , red3) (._ , red4) rel') (inj (_ , red5) (_ , red6) rel0) r1 r2 | refl | refl | refl = htransω rel rel' rel0 r1 r2

htransω0' : ∀ {k n m} -> HTRANS' (App (SetU k)) (⟦_,_⟧tp' k) (App (SetU n)) (⟦_,_⟧tp' n) (App (SetU m)) (⟦_,_⟧tp' m)
htransω0'
 (inj (_ , red1) (_ , red2) rel)
 (inj (_ , red3) (_ , red4) rel')
 (inj (_ , red5) (_ , red6) rel0)
 r1 r2 with eval-deter red1 red5 | eval-deter red2 red3 | eval-deter red4 red6
htransω0' (inj (._ , red1) (._ , red2) rel) (inj (_ , red3) (._ , red4) rel') (inj (_ , red5) (_ , red6) rel0) r1 r2 | refl | refl | refl = htrans* rel rel' rel0 r1 r2

-- TODO: Is part of this shared with the def of transEl like 
-- it is for symEl? Factor it out?
htransω' : ∀ {k n m}
 -> HTRANS' (App (SetU k)) (App ∘ (⟦_,_⟧tp' k))
           (App (SetU n)) (App ∘ (⟦_,_⟧tp' n))
           (App (SetU m)) (App ∘ (⟦_,_⟧tp' m))
htransω' pAB pBC pAC (inj red1 (_ , red2) rel) (inj (_ , red3) red4 rel') with eval-deter red2 red3
htransω' pAB pBC pAC (inj red1 (.proj₁ , red2) rel) (inj (proj₁ , red3) red4 rel') | refl = inj red1 red4 (htransω0' pAB pBC pAC rel rel')

hsymωt : ∀ {k} -> HSYM (App (SetU k)) (App ∘ (⟦_,_⟧tp' k)) (App (SetU k)) (App ∘ (⟦_,_⟧tp' k))
hsymωt pA pA' (inj red1 red2 rel) = inj red2 red1 (hsym* pA pA' rel)

⟦,⟧ctx-sym : ∀ {Γ : Ctx} {p : ⊨ Γ ctx} -> SYM ⟦ Γ , p ⟧ctx
⟦,⟧ctx-sym {⊡} {tt} {⊡} {⊡} x = tt
⟦,⟧ctx-sym {Γ , S} {vΓ , vT} {a , a₁} {b , a₂} (r1 , r2) = (⟦,⟧ctx-sym r1) , hsymω (vT r1) (vT (⟦,⟧ctx-sym r1)) r2 
⟦,⟧ctx-sym {⊡} {tt} {⊡} {b , a} ()
⟦,⟧ctx-sym {⊡} {tt} {a , a₁} {⊡} ()
⟦,⟧ctx-sym {⊡} {tt} {a , a₁} {b , a₂} ()
⟦,⟧ctx-sym {Γ , S} {proj₁ , proj₂} {⊡} {⊡} ()
⟦,⟧ctx-sym {Γ , S} {proj₁ , proj₂} {⊡} {b , a} ()
⟦,⟧ctx-sym {Γ , S} {proj₁ , proj₂} {a , a₁} {Syn.⊡} ()

⟦,⟧ctx-trans : ∀ {Γ : Ctx} {p : ⊨ Γ ctx} -> TRANS ⟦ Γ , p ⟧ctx
⟦,⟧ctx-trans {⊡} {p} {Syn.⊡} {Syn.⊡} {Syn.⊡} x1 x2 = tt
⟦,⟧ctx-trans {⊡} {p} {Syn.⊡} {Syn.⊡} {Syn._,_ ρ a} x1 ()
⟦,⟧ctx-trans {⊡} {p} {Syn.⊡} {Syn._,_ ρ a} () x2
⟦,⟧ctx-trans {⊡} {p} {Syn._,_ ρ a} {Syn.⊡} () x2
⟦,⟧ctx-trans {⊡} {p} {Syn._,_ ρ a} {Syn._,_ ρ' a'} () x2
⟦,⟧ctx-trans {Γ , S} {vΓ , vT} {Syn.⊡} {Syn.⊡} () x2
⟦,⟧ctx-trans {Γ , S} {vΓ , vT} {Syn.⊡} {Syn._,_ ρ a} () x2
⟦,⟧ctx-trans {Γ , S} {vΓ , vT} {Syn._,_ ρ a} {Syn.⊡} () x2
⟦,⟧ctx-trans {Γ , S} {vΓ , vT} {Syn._,_ ρ a} {Syn._,_ ρ' a'} {Syn.⊡} x1 ()
⟦,⟧ctx-trans {Γ , S} {vΓ , vT} {Syn._,_ ρ a} {Syn._,_ ρ' a'} {Syn._,_ ρ0 a0} (x1 , y1) (x2 , y) = ⟦,⟧ctx-trans x1 x2 ,
 htransω0 (vT x1) (vT x2) (vT (⟦,⟧ctx-trans x1 x2)) y1 y

⟦,⟧ctx-irr : ∀ {Γ : Ctx} {p q : ⊨ Γ ctx} -> ⟦ Γ , p ⟧ctx →₂ ⟦ Γ , q ⟧ctx
⟦,⟧ctx-irr {⊡} {p} {q} {Syn.⊡} {Syn.⊡} x = tt
⟦,⟧ctx-irr {⊡} {p} {q} {Syn.⊡} {Syn._,_ ρ a} ()
⟦,⟧ctx-irr {⊡} {p} {q} {Syn._,_ ρ a} ()
⟦,⟧ctx-irr {Γ , S} {p} {q} {Syn.⊡} ()
⟦,⟧ctx-irr {Γ , S} {p} {q} {Syn._,_ ρ a} {Syn.⊡} ()
⟦,⟧ctx-irr {Γ , S} {p , r} {q , s} {Syn._,_ ρ a} {Syn._,_ ρ' a'} (x1 , x2) = ⟦,⟧ctx-irr x1 , ⟦⟧tp-irr (r x1) (s (⟦,⟧ctx-irr x1)) x2

⟦,⟧ctx-self : ∀ {Γ : Ctx} {p : ⊨ Γ ctx} -> SELFL (⟦ Γ , p ⟧ctx)
⟦,⟧ctx-self x = ⟦,⟧ctx-trans x (⟦,⟧ctx-sym x)
