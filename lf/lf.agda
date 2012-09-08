-- By Induction-induction-recursion
module lf where
open import Data.Unit
open import Data.Product
open import Function
open import FinMap

mutual
 data rtm (Γ : ctx Unit) :  Set where
  ▹ : ∀ (x : var Γ unit) -> rtm Γ
  _·_ : ∀ (R : rtm Γ) (N : ntm Γ) -> rtm Γ
 data ntm (Γ : ctx Unit) : Set where
  ▸ : ∀ (R : rtm Γ) -> ntm Γ
  ƛ : ∀ (N : ntm (Γ , unit)) -> ntm Γ

{-mutual
 data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) -> (T : tp Γ) -> ctx
 
 data tp (Γ : ctx) : Set where
  Π : (T : tp Γ) (S : tp (Γ , T)) -> tp Γ
  nat : tp Γ
  vec : (n : ntm Γ nat) -> tp Γ

 _,,_ : (Γ : ctx) -> (T : tp Γ) -> ctx
 Γ ,, T = Γ , T

 data var : (Γ : ctx) -> tp Γ -> Set where
  top : ∀ {Γ T} -> var (Γ , T) ([ wkn-vsubst ]tv T)
  pop : ∀ {Γ T S} (x : var Γ T) -> var (Γ , S) ([ wkn-vsubst ]tv T)
 data rtm (Γ : ctx) : tp Γ -> Set where
  ▹ : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (Π T S) -> ntm Γ T -> rtm Γ {!!}
 data ntm (Γ : ctx) : tp Γ -> Set where
  ▸ : ∀ {T} -> rtm Γ T -> ntm Γ T
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (Π T S)

 vsubst : (Γ Δ : ctx) -> Set
 vsubst ⊡ Δ = Unit
 vsubst (Γ , T) Δ = Σ[ σ ∶ (vsubst Γ Δ) ] (var Δ ([ σ ]tv T))

 vmap : ∀ {Γ Δ Δ'} -> (σ : vsubst Γ Δ) -> (∀ T -> var Δ T -> var Δ' {!!}) -> vsubst Γ Δ'
 vmap {⊡} σ f = unit
 vmap {Γ , T} (σ , x) f = vmap σ f , {!!}

 id-vsubst : ∀ {Γ} -> vsubst Γ Γ
 id-vsubst {⊡} = unit
 id-vsubst {Γ , T} = (vmap id-vsubst {!!}) , {!!}

 wkn-vsubst : ∀ {Γ T} -> vsubst Γ (Γ ,, T)
 wkn-vsubst = vmap id-vsubst {!!}

 --vsubst-map : ∀ {Γ Δ} -> vsubst Γ Δ -> 

 [_]tv : ∀ {Γ Δ} -> vsubst Γ Δ -> tp Γ -> tp Δ
 [_]tv σ (Π T S) = Π ([ σ ]tv T) ([ {!!} , {!!} ]tv S)
 [_]tv σ nat = nat
 [_]tv σ (vec n) = vec {!!} 


 {-data vsubst (Δ : ctx) : ctx -> Set where
  ⊡ : vsubst Δ ⊡
  _,_ : ∀ {Γ T} -> (σ : vsubst Δ Γ) -> var Δ {!!} -> vsubst Δ (Γ , T) -}

 -}