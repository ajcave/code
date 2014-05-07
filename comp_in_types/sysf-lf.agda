{-# OPTIONS --no-positivity --no-termination #-} -- I think this is only necessary because I use trustMe?
module sysf-lf where
open import Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.PropositionalEquality.TrustMe


mutual
 data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) -> (d : decl Γ) -> ctx
 
 data decl (Γ : ctx) : Set where
  tp : decl Γ
  tm : (T : Γ ⊢ tp) -> decl Γ

 _,'_ : (Γ : ctx) -> (d : decl Γ) -> ctx
 _,'_ = _,_

 data var : (Γ : ctx) -> decl Γ -> Set where
  top : ∀ {Γ d} -> var (Γ , d) ([ ↑ ]d d)
  pop : ∀ {Γ d d'} -> var Γ d -> var (Γ , d') ([ ↑ ]d d)
 
 tsub : (Δ Γ : ctx) -> Set
 tsub Δ ⊡ = Unit
 tsub Δ (Γ , d) = Σ (tsub Δ Γ) (λ σ → Δ ⊢ ([ σ ]td d))
 
 [_]td : ∀ {Δ Γ} -> tsub Δ Γ -> decl Γ -> decl Δ
 [_]td σ tp = tp
 [_]td σ (tm T) = tm ([ σ ]t T)

 vsub : (Δ Γ : ctx) -> Set
 vsub Δ ⊡ = Unit
 vsub Δ (Γ , d) = Σ (vsub Δ Γ) (λ π → var Δ ([ π ]d d))

 [_]d : ∀ {Δ Γ} -> vsub Δ Γ -> decl Γ -> decl Δ
 [_]d π tp = tp
 [_]d π (tm T) = tm ([ π ] T)

 data _⊢_ (Γ : ctx) : (d : decl Γ) -> Set where 
  _⇒_ : (T S : Γ ⊢ tp) -> Γ ⊢ tp
  Π : (T : (Γ , tp) ⊢ tp) -> Γ ⊢ tp
  ▹ : ∀ {d} (X : var Γ d) -> Γ ⊢ d
  ƛ : ∀ {T S} -> (Γ , tm T) ⊢ (tm ([ ↑ ] S)) -> Γ ⊢ (tm (T ⇒ S))
  _·_ : ∀ {T S} -> Γ ⊢ (tm (T ⇒ S)) -> Γ ⊢ (tm T) -> Γ ⊢ (tm S)
  Λ : ∀ {T} -> (Γ , tp) ⊢ (tm T) -> Γ ⊢ (tm (Π T))
  _$_ : ∀ {T} -> Γ ⊢ (tm (Π T)) -> (S : Γ ⊢ tp) -> Γ ⊢ (tm ([ idtsub , S ]t T))

 [_] : ∀ {Δ Γ} -> (π : vsub Δ Γ) -> {d : _} -> Γ ⊢ d -> Δ ⊢([ π ]d d)
 [_] π (t ⇒ t₁) = ([ π ] t) ⇒ ([ π ] t₁)
 [_] π (Π t) = Π ([ extvsub π ] t)
 [_] π (▹ X) = ▹ ([ π ]v X)
 [_] {Δ} {Γ} π (ƛ {t} {t₁} t₂) = ƛ (subst (λ α → _ ⊢ (tm α)) trustMe ([ extvsub {Δ} {Γ} {tm t} π ] t₂))
 [_] π  (_·_ {t} {t₁} t₂ t₃) = ([ π ] t₂) · ([ π ] t₃)
 [_] π  (Λ {t} t₁) = Λ (subst (λ α → _ ⊢ (tm α)) trustMe ([ extvsub π ] t₁))
 [_] π  (_$_ {t} t₁ t₂) = subst (λ α → _ ⊢ (tm α)) trustMe ([ π ] t₁ $ [ π ] t₂)
 
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

 [_]t : ∀ {Δ Γ} -> (σ : tsub Δ Γ) -> {d : _} -> Γ ⊢ d -> Δ ⊢ ([ σ ]td d)
 [_]t σ (T ⇒ T₁) = ([ σ ]t T) ⇒ ([ σ ]t T₁)
 [_]t σ (Π T) = Π ([ exttsub σ ]t T)
 [_]t σ (▹ X) = [ σ ]tv X
 [_]t σ _ = {!!}

 [_]tv : ∀ {Δ Γ d} -> (σ : tsub Δ Γ) -> var Γ d -> Δ ⊢ ([ σ ]td d)
 [_]tv {Δ} {Γ , d} {._} (σ , t) top = subst (_⊢_ Δ) {[ σ ]td d} {[ σ , t ]td ([ ↑ ]d d)} trustMe t
 [_]tv {Δ} {Γ , d} {._} (σ , t) (pop {._} {d'} x) = subst (_⊢_ Δ) {[ σ ]td d'} {[ σ , t ]td ([ ↑ ]d d')} trustMe ([ σ ]tv x)

 ftop : ∀ {Γ} d -> (Γ ,' d) ⊢ ([ ↑ ]d d)
 ftop tp = ▹ top
 ftop (tm T) = ▹ top

 idtsub : ∀ {Γ} -> tsub Γ Γ
 idtsub {⊡} = tt
 idtsub {Γ , d} = wkntsubf idtsub , subst (_⊢_ (Γ , d)) {[ ↑ ]d d} {[ wkntsubf idtsub ]td d} trustMe (ftop d)

 exttsub : ∀ {Δ Γ d} -> (σ : tsub Δ Γ) -> tsub (Δ ,' ([ σ ]td d)) (Γ ,' d)
 exttsub {Δ} {Γ} {d} σ = wkntsubf σ , subst (_⊢_ (Δ , [ σ ]td d)) {[ ↑ ]d ([ σ ]td d)} {[ wkntsubf σ ]td d} trustMe (ftop ([ σ ]td d))


 wkntsubf : ∀ {Δ Γ d} -> tsub Δ Γ -> tsub (Δ ,' d) Γ
 wkntsubf {Δ} {⊡} σ = tt
 wkntsubf {Δ} {Γ , d} {d'} (σ , t) = wkntsubf σ , subst (_⊢_ (Δ , d')) {[ wknvsubf idvsub ]d ([ σ ]td d)} {[ wkntsubf σ ]td d} trustMe ([ ↑ ] t)

