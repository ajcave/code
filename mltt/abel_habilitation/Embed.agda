open import Syntax
open import SyntaxTm

open Syn Exp

mutual
 ⌈_⌉v : Val -> Exp
 ⌈ ƛ t ρ ⌉v = (ƛ t) [ ⌈ ρ ⌉e ]
 ⌈ ↑[_] v e ⌉v = ⌈ e ⌉dne
 ⌈ Π v v₁ ⌉v = Π ⌈ v ⌉v ⌈ v₁ ⌉v
 ⌈ Nat ⌉v = Nat
 ⌈ Set* x ⌉v = Set* x
 ⌈ natval x ⌉v = ⌈ x ⌉nat

 ⌈_⌉e : Env -> Subst
 ⌈ Syn.⊡ ⌉e = ⊡
 ⌈ ρ Syn., a ⌉e = ⌈ ρ ⌉e , ⌈ a ⌉v

 ⌈_⌉dne : Dne -> Exp
 ⌈ Syn.lvl x ⌉dne = idx 0
 ⌈ e Syn.· (↓[ A ] a) ⌉dne = ⌈ e ⌉dne · ⌈ a ⌉v
 ⌈ Syn.rec T tz ts e ⌉dne = rec T tz ts (⌈ e ⌉nn)

 ⌈_⌉nat : NatVal -> Exp
 ⌈ Syn.zero ⌉nat = zero
 ⌈ Syn.suc n ⌉nat = suc ⌈ n ⌉nat
 ⌈ Syn.natneu e ⌉nat = ⌈ e ⌉nn

 ⌈_⌉nn : NatNeu -> Exp
 ⌈ x Syn.⊕ x₁ ⌉nn = ⌈ x ⌉dne ⊕ ⌈ x₁ ⌉nat

open import Eval
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])


mutual
 -- TODO: There's also a converse of this to prove:
 vas : ∀ {t ρ v τ ρ' u} -> ⟦ t ⟧ ρ ↘ v -> ⟦ ⌈ ρ ⌉e ⟧ τ ↘s ρ' -> ⟦ t ⟧ ρ' ↘ u -> ⟦ ⌈ v ⌉v ⟧ τ ↘ u
 vas (idx x₁) p2 (idx x₂) = {!!}
 vas ƛ p2 ƛ = ƛ [ p2 ]
 vas (ap p1 p3 (ƛ· x)) p2 (ap p4 p5 (ƛ· x₁)) with vas p1 p2 p4
 vas (ap p1 p3 (ƛ· x₁)) p2 (ap p4 p5 (ƛ· x₂)) | ƛ [ x ] = vas x₁ (x , (vas p3 p2 p5)) x₂
 vas (ap p1 p3 (ƛ· x)) p2 (ap p4 p5 (↑ x₁)) with vas p1 p2 p4
 vas (ap p1 p3 (ƛ· x₁)) p2 (ap p4 p5 (↑ x₂)) | () [ x ]
 vas (ap p1 p3 (↑ x)) p2 (ap p4 p5 (ƛ· x₁)) with vas p1 p2 p4 | vas p3 p2 p5
 ... | q0 | q1 = ap q0 q1 (ƛ· x₁)
 vas (ap p1 p3 (↑ x)) p2 (ap p4 p5 (↑ x₁)) with vas p1 p2 p4 | vas p3 p2 p5
 ... | q0 | q1 = ap q0 q1 (↑ x₁)
 vas zero p2 zero = zero
 vas (suc p1 natval) p2 (suc p3 natval) = suc (vas p1 p2 p3) natval
 vas (suc p1 natval) p2 (suc p3 neu) with vas p1 p2 p3
 ... | q = suc q neu
 vas (suc p1 neu) p2 (suc {n = n} p3 natval) with vas p1 p2 p3 
 ... | q = suc (plus q zero natval natval) (subst (λ α → UnboxNat natval α ↘ n) (sym ⊕lem) natval)
 vas (suc p1 neu) p2 (suc p3 neu) = suc (plus (vas p1 p2 p3) zero neu natval) natval
 vas (rec p1 x x₁) p2 (rec p3 x₂ x₃) = {!!}
 vas Set* p2 Set* = Set*
 vas (Π p3 p1) p2 (Π p4 p5) = Π (vas p3 p2 p4) (vas p1 p2 p5)
 vas Nat p2 Nat = Nat
 vas (p1 [ x ]) p2 (p3 [ x₁ ]) = vas p1 (vas' x p2 x₁) p3
 vas (plus p1 p3 x x₁) p2 (plus p4 p5 x₂ x₃) = {!!}

 ⊕lem : ∀ {n} -> n ⊕̂ zero ≡ n
 ⊕lem {Syn.zero} = refl
 ⊕lem {Syn.suc n} = cong suc ⊕lem
 ⊕lem {Syn.natneu (x ⊕ v)} = cong natneu (cong (_⊕_ x) ⊕lem)

 vas' : ∀ {t ρ v τ ρ' u} -> ⟦ t ⟧ ρ ↘s v -> ⟦ ⌈ ρ ⌉e ⟧ τ ↘s ρ' -> ⟦ t ⟧ ρ' ↘s u -> ⟦ ⌈ v ⌉e ⟧ τ ↘s u
 vas' (p3 [ p1 ]) p2 (p4 [ p5 ]) = vas' p1 (vas' p3 p2 p4) p5
 vas' id p2 id = p2
 vas' ↑ (p2 , x) ↑ = p2
 vas' (p1 , x) p2 (p3 , x₁) = (vas' p1 p2 p3) , (vas x p2 x₁)
 vas' ⊡ p2 ⊡ = ⊡

mutual
 vas2 : ∀ {t ρ v τ ρ' u} -> ⟦ t ⟧ ρ ↘ v -> ⟦ ⌈ ρ ⌉e ⟧ τ ↘s ρ' -> ⟦ ⌈ v ⌉v ⟧ τ ↘ u  -> ⟦ t ⟧ ρ' ↘ u 
 vas2 d1 d2 d3 = {!d1!}


 