-- By Induction-induction-recursion
module lf where
open import Level
open import Unit
open import Product
open import Function
open import FinMap

* : ∀ {a} -> Unit {a}
* = tt

mutual
 data rtm (Γ : ctx (Unit {zero})) :  Set where
  ▹ : ∀ (x : var Γ *) -> rtm Γ
  _·_ : ∀ (R : rtm Γ) (N : ntm Γ) -> rtm Γ
 data ntm (Γ : ctx Unit) : Set where
  ▸ : ∀ (R : rtm Γ) -> ntm Γ
  ƛ : ∀ (N : ntm (Γ , *)) -> ntm Γ

mutual
 [_]rv : ∀ {Γ Δ} -> vsubst Γ Δ -> rtm Γ -> rtm Δ
 [_]rv σ (▹ x) = ▹ (lookup σ x)
 [_]rv σ (R · N) = ([ σ ]rv R) · ([ σ ]nv N)

 [_]nv : ∀ {Γ Δ} -> vsubst Γ Δ -> ntm Γ -> ntm Δ
 [_]nv σ (▸ R) = ▸ ([ σ ]rv R)
 [_]nv σ (ƛ N) = ƛ ([ vsub-ext σ ]nv N)

id-n : ∀ {Γ} -> gksubst Γ (ntm Γ)
id-n = interp (▸ ∘ ▹)

mutual
 [_]r : ∀ {Γ Δ} -> gksubst Γ (ntm Δ) -> rtm Γ -> ntm Δ
 [_]r σ (▹ x) = lookup σ x
 [_]r σ (R · N) with [ σ ]r R | [ σ ]n N
 [_]r σ (R · N) | ▸ R' | N2 = ▸ (R' · N2)
 [_]r σ (R · N) | ƛ N' | N2 = [ id-n , N2 ]n N'
 [_]n : ∀ {Γ Δ} -> gksubst Γ (ntm Δ) -> ntm Γ -> ntm Δ
 [_]n σ (▸ R) = [ σ ]r R
 [_]n σ (ƛ N) = ƛ ([ (gmap [ wkn-vsub ]nv σ) , (▸ (▹ top)) ]n N)

data tp (Γ : ctx Unit) : Set where
 Π : (T : tp Γ) (S : tp (Γ , *)) -> tp Γ
 nat : tp Γ
 vec : (n : ntm Γ) -> tp Γ

[_]tv : ∀ {Γ Δ} -> vsubst Γ Δ -> tp Γ -> tp Δ
[_]tv σ (Π T S) = Π ([ σ ]tv T) ([ vsub-ext σ ]tv S)
[_]tv σ nat = nat
[_]tv σ (vec n) = vec ([ σ ]nv n)

[_]t : ∀ {Γ Δ} -> gksubst Γ (ntm Δ) -> tp Γ -> tp Δ
[_]t σ (Π T S) = Π ([ σ ]t T) ([ (gmap [ wkn-vsub ]nv σ) , (▸ (▹ top)) ]t S)
[_]t σ nat = nat
[_]t σ (vec n) = vec ([ σ ]n n)

mutual
 data dctx : Set where
  ⊡ : dctx
  _,_ : (Γ : dctx) -> (T : tp ⌊ Γ ⌋) -> dctx

 ⌊_⌋ : dctx -> ctx Unit
 ⌊ ⊡ ⌋ = ⊡
 ⌊ Γ , T ⌋ = ⌊ Γ ⌋ , *

mutual
 data _ok : (Γ : dctx) -> Set where
  ⊡ : ⊡ ok
  _,_ : ∀ {Γ T} -> (Γok : Γ ok) -> (T-type : Γ ⊢ T type) -> (Γ , T) ok

 data _⊢_type (Γ : dctx) : tp ⌊ Γ ⌋ -> Set where
  nat : Γ ⊢ nat type
  vec : ∀ {n : ntm ⌊ Γ ⌋} -> Γ ⊢ n ⇐ nat -> Γ ⊢ (vec n) type
  Π : ∀ {T S} -> (T-type : Γ ⊢ T type) -> (S-type : (Γ , T) ⊢ S type) -> Γ ⊢ (Π T S) type 

 data _∋_∶_ : (Γ : dctx) -> (x : var ⌊ Γ ⌋ *) -> (T : tp ⌊ Γ ⌋) -> Set where
  top : ∀ {Γ T} -> (Γ , T) ∋ top ∶ [ wkn-vsub ]tv T
  pop : ∀ {Γ T S x} -> Γ ∋ x ∶ T -> (Γ , S) ∋ (pop x) ∶ [ wkn-vsub ]tv T
 data _⊢_⇒_ (Γ : dctx) : rtm ⌊ Γ ⌋ -> tp ⌊ Γ ⌋ -> Set where
  ▹ : ∀ {T x} -> (y : Γ ∋ x ∶ T) -> Γ ⊢ (▹ x) ⇒ T
  _·_ : ∀ {T S R N} -> (r : Γ ⊢ R ⇒ (Π T S)) -> (n : Γ ⊢ N ⇐ T) -> Γ ⊢ (R · N) ⇒ [ id-n , N ]t S
 data _⊢_⇐_ (Γ : dctx) : ntm ⌊ Γ ⌋ -> tp ⌊ Γ ⌋ -> Set where
  ▸ : ∀ {T R} -> (r : Γ ⊢ R ⇒ T) -> Γ ⊢ (▸ R) ⇐ T
  ƛ : ∀ {T S N} -> (t : Γ ⊢ T type) -> (n : (Γ , T) ⊢ N ⇐ S) -> Γ ⊢ (ƛ N) ⇐ (Π T S)

vsubst-ok : ∀ Γ Δ (σ : vsubst ⌊ Γ ⌋ ⌊ Δ ⌋) -> Set
vsubst-ok Γ Δ σ = ∀ x {U} -> Γ ∋ x ∶ U -> Δ ∋ (lookup σ x) ∶ ([ σ ]tv U)

vsubst-ok-, : ∀ {Γ Δ T} {σ : vsubst ⌊ Γ ⌋ ⌊ Δ ⌋} -> vsubst-ok Γ Δ σ -> ∀ {x} (y : Δ ∋ x ∶ ([ σ ]tv T))
  -> vsubst-ok (Γ , T) Δ (σ , x)
vsubst-ok-, θ y top top = {!!}
vsubst-ok-, θ y (pop y') (pop y0) = {!!}

vsubst-ok-ext : ∀ {Γ Δ T} {σ : vsubst ⌊ Γ ⌋ ⌊ Δ ⌋} -> vsubst-ok Γ Δ σ
  -> vsubst-ok (Γ , T) (Δ , ([ σ ]tv T)) (vsub-ext σ)
vsubst-ok-ext θ y = {!!} --vsubst-ok-, {!!} {!!} top

mutual
 tv-ok : ∀ {Γ Δ T} {σ : vsubst ⌊ Γ ⌋ ⌊ Δ ⌋}
    -> vsubst-ok Γ Δ σ
   -> Γ ⊢ T type -> Δ ⊢ ([ σ ]tv T) type
 tv-ok f nat = nat
 tv-ok f (vec y) = vec (nv-ok f y)
 tv-ok f (Π T-type S-type) = Π (tv-ok f T-type) (tv-ok (vsubst-ok-ext f) S-type)
 
 rv-ok : ∀ {Γ Δ R T} {σ : vsubst ⌊ Γ ⌋ ⌊ Δ ⌋}
    -> vsubst-ok Γ Δ σ
   -> Γ ⊢ R ⇒ T -> Δ ⊢ ([ σ ]rv R) ⇒ ([ σ ]tv T)
 rv-ok f (▹ y) = ▹ (f _ y)
 rv-ok f (r · n) with (rv-ok f r) | (nv-ok f n)
 ... | q1 | q2 = {!!} · q2

 nv-ok : ∀ {Γ Δ N T} {σ : vsubst ⌊ Γ ⌋ ⌊ Δ ⌋}
   -> vsubst-ok Γ Δ σ
   -> Γ ⊢ N ⇐ T -> Δ ⊢ ([ σ ]nv N) ⇐ ([ σ ]tv T)
 nv-ok f (▸ r) = ▸ (rv-ok f r)
 nv-ok f (ƛ t n) = ƛ (tv-ok f t) (nv-ok (vsubst-ok-ext f) n)

mutual
 var-wf : ∀ {Γ x T} -> Γ ok -> Γ ∋ x ∶ T -> Γ ⊢ T type
 var-wf {⊡} γ ()
 var-wf (Γok , T-type) top = tv-ok {!!} T-type
 var-wf (Γok , T-type) (pop y) = tv-ok {!!} (var-wf Γok y)

 neut-wf : ∀ {Γ R T} -> Γ ok -> Γ ⊢ R ⇒ T -> Γ ⊢ T type
 neut-wf Γok (▹ y) = var-wf Γok y
 neut-wf Γok (r · n) with neut-wf Γok r
 neut-wf Γok (r · n) | Π T-type S-type = {! !}

 norm-wf : ∀ {Γ N T} -> Γ ok -> Γ ⊢ N ⇐ T -> Γ ⊢ T type
 norm-wf Γok (▸ r) = neut-wf Γok r
 norm-wf Γok (ƛ t n) = Π t (norm-wf (Γok , t) n)