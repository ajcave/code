{-# OPTIONS --no-positivity --no-termination #-} -- I think this is only necessary because I use trustMe?
module sysf-lf where
open import Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.PropositionalEquality.TrustMe


mutual
 data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) -> (J : judgment Γ) -> ctx
 
 data judgment (Γ : ctx) : Set where
  tp : judgment Γ
  tm : (T : Γ ⊢ tp) -> judgment Γ

 _,'_ : (Γ : ctx) -> (J : judgment Γ) -> ctx
 _,'_ = _,_

 data var : (Γ : ctx) -> judgment Γ -> Set where
  top : ∀ {Γ J} -> var (Γ , J) ([ ↑ ]j J)
  pop : ∀ {Γ J J'} -> var Γ J -> var (Γ , J') ([ ↑ ]j J)
 
 tsub : (Δ Γ : ctx) -> Set
 tsub Δ ⊡ = Unit
 tsub Δ (Γ , J) = Σ (tsub Δ Γ) (λ σ → Δ ⊢ ([ σ ]tj J))
 
 [_]tj : ∀ {Δ Γ} -> tsub Δ Γ -> judgment Γ -> judgment Δ
 [_]tj σ tp = tp
 [_]tj σ (tm T) = tm ([ σ ]t T)

 vsub : (Δ Γ : ctx) -> Set
 vsub Δ ⊡ = Unit
 vsub Δ (Γ , J) = Σ (vsub Δ Γ) (λ π → var Δ ([ π ]j J))

 [_]j : ∀ {Δ Γ} -> vsub Δ Γ -> judgment Γ -> judgment Δ
 [_]j π tp = tp
 [_]j π (tm T) = tm ([ π ] T)

 data _⊢_ (Γ : ctx) : (J : judgment Γ) -> Set where 
  _⇒_ : (T S : Γ ⊢ tp) -> Γ ⊢ tp
  Π : (T : (Γ , tp) ⊢ tp) -> Γ ⊢ tp
  ▹ : ∀ {J} (X : var Γ J) -> Γ ⊢ J
  ƛ : ∀ {T S} -> (Γ , tm T) ⊢ tm ([ ↑ ] S) -> Γ ⊢ tm (T ⇒ S)
  _·_ : ∀ {T S} -> Γ ⊢ tm (T ⇒ S) -> Γ ⊢ tm T -> Γ ⊢ tm S
  Λ : ∀ {T} -> (Γ , tp) ⊢ tm T -> Γ ⊢ tm (Π T)
  _$_ : ∀ {T} -> Γ ⊢ tm (Π T) -> (S : Γ ⊢ tp) -> Γ ⊢ tm ([ id , S ]t T)

 [_] : ∀ {Δ Γ} -> (π : vsub Δ Γ) -> {J : _} -> Γ ⊢ J -> Δ ⊢ ([ π ]j J)
 [_] π (t ⇒ t₁) = ([ π ] t) ⇒ ([ π ] t₁)
 [_] π (Π t) = Π ([ π ⊗ tp ] t)
 [_] π (▹ X) = ▹ ([ π ]v X)
 [_] π (ƛ {t} t₂) = ƛ (subst (λ α → _ ⊢ (tm α)) trustMe ([ π ⊗ tm t ] t₂))
 [_] π (_·_ t₂ t₃) = ([ π ] t₂) · ([ π ] t₃)
 [_] π (Λ t₁) = Λ (subst (λ α → _ ⊢ tm α) trustMe ([ π ⊗ tp ] t₁))
 [_] π (_$_ t₁ t₂) = subst (λ α → _ ⊢ tm α) trustMe ([ π ] t₁ $ [ π ] t₂)
 
 [_]v : ∀ {Δ Γ J} -> (π : vsub Δ Γ) -> var Γ J -> var Δ ([ π ]j J)
 [_]v (π , y) top = subst (var _) trustMe y
 [_]v (π , y) (pop x) = subst (var _) trustMe ([ π ]v x)

 idv : ∀ {Γ} -> vsub Γ Γ
 idv {⊡} = tt
 idv {Γ , J} = wknvsubf idv , subst (var _) trustMe top

 _⊗_ : ∀ {Δ Γ} -> (π : vsub Δ Γ) -> ∀ J -> vsub (Δ ,' ([ π ]j J)) (Γ ,' J)
 π ⊗ J = (wknvsubf π) , subst (var _) trustMe top

 wknvsubf : ∀ {Δ Γ J} -> vsub Δ Γ -> vsub (Δ ,' J) Γ
 wknvsubf {Δ} {⊡} σ = tt
 wknvsubf {Δ} {Γ , J} (σ , x) = (wknvsubf σ) , subst (var _) trustMe (pop x)

 ↑ : ∀ {Γ J} -> vsub (Γ ,' J) Γ
 ↑ = wknvsubf idv

 [_]t : ∀ {Δ Γ} -> (σ : tsub Δ Γ) -> {J : _} -> Γ ⊢ J -> Δ ⊢ ([ σ ]tj J)
 [_]t σ (T ⇒ T₁) = ([ σ ]t T) ⇒ ([ σ ]t T₁)
 [_]t σ (Π T) = Π ([ σ 〉 tp ]t T)
 [_]t σ (▹ X) = [ σ ]tv X
 [_]t σ (ƛ {t} t₂) = ƛ (subst (λ α → _ ⊢ tm α) trustMe ([ σ 〉 tm t ]t t₂))
 [_]t σ (t₂ · t₃) = ([ σ ]t t₂) · ([ σ ]t t₃)
 [_]t σ (Λ t₁) = Λ (subst (λ α → _ ⊢ tm α) trustMe ([ σ 〉 tp ]t t₁))
 [_]t σ (t₁ $ t₂) = subst (λ α → _ ⊢ tm α) trustMe (([ σ ]t t₁) $ ([ σ ]t t₂))

 [_]tv : ∀ {Δ Γ J} -> (σ : tsub Δ Γ) -> var Γ J -> Δ ⊢ ([ σ ]tj J)
 [_]tv {Δ} {Γ , J} {._} (σ , t) top = subst (_⊢_ Δ) {[ σ ]tj J} {[ σ , t ]tj ([ ↑ ]j J)} trustMe t
 [_]tv {Δ} {Γ , J} {._} (σ , t) (pop {._} {J'} x) = subst (_⊢_ Δ) {[ σ ]tj J'} {[ σ , t ]tj ([ ↑ ]j J')} trustMe ([ σ ]tv x)

 ftop : ∀ {Γ} J -> (Γ ,' J) ⊢ ([ ↑ ]j J)
 ftop tp = ▹ top
 ftop (tm T) = ▹ top

 id : ∀ {Γ} -> tsub Γ Γ
 id {⊡} = tt
 id {Γ , J} = wkntsubf id , subst (_⊢_ (Γ , J)) {[ ↑ ]j J} {[ wkntsubf id ]tj J} trustMe (ftop J)

 _〉_ : ∀ {Δ Γ} -> (σ : tsub Δ Γ) -> ∀ J -> tsub (Δ ,' ([ σ ]tj J)) (Γ ,' J)
 σ 〉 J = wkntsubf σ , subst (_⊢_ (_ , [ σ ]tj J)) {[ ↑ ]j ([ σ ]tj J)} {[ wkntsubf σ ]tj J} trustMe (ftop ([ σ ]tj J))


 wkntsubf : ∀ {Δ Γ J} -> tsub Δ Γ -> tsub (Δ ,' J) Γ
 wkntsubf {Δ} {⊡} σ = tt
 wkntsubf {Δ} {Γ , J} {J'} (σ , t) = wkntsubf σ , subst (_⊢_ (Δ , J')) {[ wknvsubf idv ]j ([ σ ]tj J)} {[ wkntsubf σ ]tj J} trustMe ([ ↑ ] t)

