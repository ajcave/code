{-# OPTIONS --no-positivity --no-termination #-} -- I think this is only necessary because I use trustMe?
module sysf-copy where
open import Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.PropositionalEquality.TrustMe


mutual
 data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) -> (d : decl Γ) -> ctx
 
 data decl (Γ : ctx) : Set where
  `tp : decl Γ
  `tm : (T : tp Γ) -> decl Γ

 _,'_ : (Γ : ctx) -> (d : decl Γ) -> ctx
 _,'_ = _,_

 data var : (Γ : ctx) -> decl Γ -> Set where
  top : ∀ {Γ d} -> var (Γ , d) ([ ↑ ]d d)
  pop : ∀ {Γ d d'} -> var Γ d -> var (Γ , d') ([ ↑ ]d d)

 data tp (Γ : ctx) : Set where
  _⇒_ : (T S : tp Γ) -> tp Γ
  Π : (T : tp (Γ , `tp)) -> tp Γ
  ▹ : (X : var Γ `tp) -> tp Γ
 
 tsub : (Δ Γ : ctx) -> Set
 tsub Δ ⊡ = Unit
 tsub Δ (Γ , d) = Σ (tsub Δ Γ) (λ σ → fam Δ ([ σ ]td d))
 
 [_]td : ∀ {Δ Γ} -> tsub Δ Γ -> decl Γ -> decl Δ
 [_]td σ `tp = `tp
 [_]td σ (`tm T) = `tm ([ σ ]t T)

 -- Ok this is interesting...
 -- Try to use this as an index to the datatype and see what it looks like.. need to compute index type
 fam : (Γ : ctx) -> (d : decl Γ) -> Set
 fam Γ `tp = tp Γ
 fam Γ (`tm T) = tm Γ T

 data tm (Γ : ctx) : tp Γ -> Set where
  ▹ : ∀ {T} (x : var Γ (`tm T)) -> tm Γ T
  ƛ : ∀ {T S} -> tm (Γ , `tm T) ([ ↑ ] S) -> tm Γ (T ⇒ S)
  _·_ : ∀ {T S} -> tm Γ (T ⇒ S) -> tm Γ T -> tm Γ S
  Λ : ∀ {T} -> tm (Γ , `tp) T -> tm Γ (Π T)
  _$_ : ∀ {T} -> tm Γ (Π T) -> (S : tp Γ) -> tm Γ ([ idtsub , S ]t T)

 vsub : (Δ Γ : ctx) -> Set
 vsub Δ ⊡ = Unit
 vsub Δ (Γ , d) = Σ (vsub Δ Γ) (λ π → var Δ ([ π ]d d))
 
 [_]d : ∀ {Δ Γ} -> vsub Δ Γ -> decl Γ -> decl Δ
 [_]d π `tp = `tp
 [_]d π (`tm T) = `tm ([ π ] T)

 -- TODO: Can we get rid of this?
 [_] : ∀ {Δ Γ} -> vsub Δ Γ -> tp Γ -> tp Δ
 [_] π (T ⇒ T₁) = ([ π ] T) ⇒ ([ π ] T₁)
 [_] π (Π T) = Π ([ extvsub π ] T)
 [_] π (▹ X) = ▹ ([ π ]v X)

 -- Then this will have weird behaviour where if I reorder the cases it won't check?
 [_]fam : ∀ {Δ Γ} -> (π : vsub Δ Γ) -> (d : _) -> fam Γ d -> fam Δ ([ π ]d d)
 [_]fam π `tp (t ⇒ t₁) = ([ π ]fam `tp t) ⇒ ([ π ]fam `tp t₁)
 [_]fam π `tp (Π t) = Π ([ extvsub π ]fam `tp t)
 [_]fam π `tp (▹ X) = ▹ ([ π ]v X)
 [_]fam π (`tm ._) (▹ x) = ▹ ([ π ]v x)
 [_]fam π (`tm ._) (ƛ t) = ƛ (subst (tm _) trustMe ([ extvsub π ]fam (`tm _) t))
 [_]fam π (`tm ._) (_·_ t t₁) = ([ π ]fam (`tm _) t) · ([ π ]fam (`tm _) t₁)
 [_]fam π (`tm ._) (Λ t) = Λ (subst (tm _) trustMe ([ extvsub π ]fam (`tm _) t))
 [_]fam π (`tm ._) (t $ S) = subst (tm _) trustMe ([ π ]fam (`tm _) t $ ([ π ]fam `tp S))
 
 [_]v : ∀ {Δ Γ d} -> (π : vsub Δ Γ) -> var Γ d -> var Δ ([ π ]d d)
 [_]v (π , y) top = subst (var _) trustMe y
 [_]v (π , y) (pop x) = subst (var _) trustMe ([ π ]v x)

 idvsub : ∀ {Γ} -> vsub Γ Γ
 idvsub {⊡} = tt
 idvsub {Γ , d} = wknvsubf idvsub , subst (var _) trustMe top

 extvsub : ∀ {Δ Γ d} -> (π : vsub Δ Γ) -> vsub (Δ ,' ([ π ]d d)) (Γ ,' d)
 extvsub π = (wknvsubf π) , subst (var _) trustMe top

 wknvsubf : ∀ {Δ Γ d} -> vsub Δ Γ -> vsub (Δ ,' d) Γ
 wknvsubf {Δ} {⊡} σ = tt
 wknvsubf {Δ} {Γ , d} (σ , x) = (wknvsubf σ) , subst (var _) trustMe (pop x)

 ↑ : ∀ {Γ d} -> vsub (Γ ,' d) Γ
 ↑ = wknvsubf idvsub

 [_]t : ∀ {Δ Γ} -> tsub Δ Γ -> tp Γ -> tp Δ
 [_]t σ (T ⇒ T₁) = ([ σ ]t T) ⇒ ([ σ ]t T₁)
 [_]t σ (Π T) = Π ([ exttsub σ ]t T)
 [_]t σ (▹ X) = [ σ ]tv X

 [_]tv : ∀ {Δ Γ d} -> (σ : tsub Δ Γ) -> var Γ d -> fam Δ ([ σ ]td d)
 [_]tv {Δ} {Γ , d} {._} (σ , t) top = subst (fam Δ) {[ σ ]td d} {[ σ , t ]td ([ ↑ ]d d)} trustMe t
 [_]tv {Δ} {Γ , d} {._} (σ , t) (pop {._} {d'} x) = subst (fam Δ) {[ σ ]td d'} {[ σ , t ]td ([ ↑ ]d d')} trustMe ([ σ ]tv x)

 ftop : ∀ {Γ} d -> fam (Γ ,' d) ([ ↑ ]d d)
 ftop `tp = ▹ top
 ftop (`tm T) = ▹ top

 idtsub : ∀ {Γ} -> tsub Γ Γ
 idtsub {⊡} = tt
 idtsub {Γ , d} = wkntsubf idtsub , subst (fam (Γ , d)) {[ ↑ ]d d} {[ wkntsubf idtsub ]td d} trustMe (ftop d)

 exttsub : ∀ {Δ Γ d} -> (σ : tsub Δ Γ) -> tsub (Δ ,' ([ σ ]td d)) (Γ ,' d)
 exttsub {Δ} {Γ} {d} σ = wkntsubf σ , subst (fam (Δ , [ σ ]td d)) {[ ↑ ]d ([ σ ]td d)} {[ wkntsubf σ ]td d} trustMe (ftop ([ σ ]td d))


 wkntsubf : ∀ {Δ Γ d} -> tsub Δ Γ -> tsub (Δ ,' d) Γ
 wkntsubf {Δ} {⊡} σ = tt
 wkntsubf {Δ} {Γ , d} {d'} (σ , t) = wkntsubf σ , subst (fam (Δ , d')) {[ wknvsubf idvsub ]d ([ σ ]td d)} {[ wkntsubf σ ]td d} trustMe ([ ↑ ]fam ([ σ ]td d) t)
-- TODO: Try the thing above!

data _≡'_ {A : Set} (x : A) : {B : Set} -> (b : B) -> Set where
 refl : x ≡' x

mutual
 copyctx : ctx -> ctx
 copyctx ⊡ = ⊡
 copyctx (Γ , d) = copyctx Γ , copydecl d

 copydecl : ∀ {Γ} -> decl Γ -> decl (copyctx Γ)
 copydecl `tp = `tp
 copydecl (`tm T) = `tm (copytp T)

 copyvar : ∀ {Γ d} -> var Γ d -> var (copyctx Γ) (copydecl d)
 copyvar (top) = {!!}
 copyvar (pop X) = {!!}

 copytp : ∀ {Γ} -> tp Γ -> tp (copyctx Γ)
 copytp (T ⇒ T₁) = copytp T ⇒ copytp T₁
 copytp (Π T) = Π (copytp T)
 copytp (▹ X) = ▹ (copyvar X)

 copyvsub : ∀ {Δ Γ} -> vsub Δ Γ -> vsub (copyctx Δ) (copyctx Γ)
 copyvsub {Δ} {⊡} tt = tt
 copyvsub {Δ} {Γ , d} (π , x) = (copyvsub π) , subst (var (copyctx Δ)) (lem π d) (copyvar x)
  
 lem : ∀ {Δ Γ} (π : vsub Δ Γ) d -> copydecl ([ π ]d d) ≡ [ copyvsub π ]d (copydecl d)
 lem π `tp = refl
 lem π (`tm T) = cong `tm (lemtp π T)

 lemtp : ∀ {Δ Γ} (π : vsub Δ Γ) T -> copytp ([ π ] T) ≡ [ copyvsub π ] (copytp T)
 lemtp π (T ⇒ T₁) = cong₂ _⇒_ (lemtp π T) (lemtp π T₁)
 lemtp π (Π T) = cong Π {!!}
 lemtp π (▹ X) = cong ▹ {!!}

copytm : ∀ {Γ} {T : tp Γ} -> tm Γ T -> tm (copyctx Γ) (copytp T)
copytm (▹ x) = ▹ (copyvar x)
copytm (ƛ t) with copytm t
... | q = ƛ {!!}
copytm (t · t₁) = (copytm t) · (copytm t₁)
copytm (Λ t) = Λ (copytm t)
copytm (t $ S) with copytm t | copytp S
... | q1 | q2 = {!!}



