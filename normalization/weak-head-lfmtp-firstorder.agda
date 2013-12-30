module weak-head-lfmtp-firstorder where
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Unit
open import Product
open import Function

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (ψ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

gsubst : ∀ {A : Set} -> ctx A -> (F : A -> Set) -> Set
gsubst ⊡ F = Unit
gsubst (ψ , T) F = (gsubst ψ F) × (F T)

gksubst : ∀ {A : Set} -> ctx A -> (F : Set) -> Set
gksubst ψ F = gsubst ψ (λ _ -> F)

lookup : ∀ {A : Set} {ψ : ctx A} {F : A -> Set} {T} -> gsubst ψ F -> var ψ T -> F T
lookup {A} {⊡} σ ()
lookup {A} {ψ , T} σ top = proj₂ σ
lookup {A} {ψ , T} σ (pop y) = lookup (proj₁ σ) y

gmap : ∀ {A : Set} {ψ : ctx A} {F : A -> Set} {G : A -> Set} -> (∀ {T} -> F T -> G T) -> gsubst ψ F -> gsubst ψ G
gmap {A} {⊡} f σ = tt
gmap {A} {ψ , T} f σ = (gmap f (proj₁ σ)) , (f (proj₂ σ))

gmap-id : ∀ {A : Set} {F : A -> Set} {ψ : ctx A} (σ : gsubst ψ F) -> gmap id σ ≡ σ
gmap-id {A} {F} {⊡} σ = refl
gmap-id {A} {F} {ψ , T} σ = cong₂ _,_ (gmap-id (proj₁ σ)) refl

gmap-funct : ∀ {A : Set} {ψ : ctx A} {F : A -> Set} {G : A -> Set} {H : A -> Set} {f : ∀ {T} -> F T -> G T} {g : ∀ {T} -> G T -> H T} (σ : gsubst ψ F)
 -> gmap g (gmap f σ) ≡ gmap (g ∘ f) σ
gmap-funct {A} {⊡} σ = refl
gmap-funct {A} {ψ , T} σ = cong₂ _,_ (gmap-funct (proj₁ σ)) refl

gmap-cong : ∀ {A : Set} {ψ : ctx A} {F : A -> Set} {G : A -> Set} {f g : ∀ {T} -> F T -> G T} {σ : gsubst ψ F} (p : ∀ {T} (x : F T) -> f x ≡ g x)
 -> gmap f σ ≡ gmap g σ
gmap-cong {A = A} {⊡} p = refl
gmap-cong {A = A} {ψ , T} p = cong₂ _,_ (gmap-cong p) (p _)

lookup-gmap : ∀ {A : Set} {ψ : ctx A} {F : A -> Set} {G : A -> Set} (f : ∀ {T} -> F T -> G T) (σ : gsubst ψ F) {T} (x : var ψ T)
 -> lookup (gmap f σ) x ≡ f (lookup σ x)
lookup-gmap {A = A} {⊡} f σ ()
lookup-gmap {A = A} {ψ , T} f σ top = refl
lookup-gmap {A = A} {ψ , T} f σ (pop y) = lookup-gmap f (proj₁ σ) y

vsubst : ∀ {A : Set} -> ctx A -> ctx A -> Set
vsubst Γ Δ = gsubst Γ (var Δ)

[_]v : ∀ {A : Set} {F : A -> Set} {Δ T} (σ : gsubst Δ F) -> var Δ T -> F T
[ σ ]v x = lookup σ x

wkn : ∀ {A : Set} {Γ1 Γ2} {T : A} -> vsubst Γ1 Γ2 -> vsubst Γ1 (Γ2 , T)
wkn σ = gmap pop σ

id-vsub : ∀ {A : Set} {Γ : ctx A} -> vsubst Γ Γ
id-vsub {A} {⊡} = tt
id-vsub {A} {Γ , T} = (wkn id-vsub) , top

wkn-vsub : ∀ {A : Set} {Γ : ctx A} {T} -> vsubst Γ (Γ , T)
wkn-vsub {A} {Γ} {T} = wkn id-vsub

vsub-ext : ∀ {A : Set} {T} {Γ1 Γ2 : ctx A} -> vsubst Γ1 Γ2 -> vsubst (Γ1 , T) (Γ2 , T)
vsub-ext σ = (gmap pop σ) , top

_∘v_ : ∀ {A : Set} {Δ Γ ψ : ctx A} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘v σ2) = gmap [ σ1 ]v σ2

{-ren-assoc : ∀ {A : Set} {n m k k' : ctx A} (w : vsubst n m) {w' : vsubst m k} {v : vsubst k k'}
 -> (v ∘v (w' ∘v w)) ≡ ((v ∘v w') ∘v w)
ren-assoc w {w'} {v} = trans (gmap-funct w) (gmap-cong (λ x → sym (lookup-gmap (lookup v) w' x))) -}

{-id-v-right : ∀ {a} {A : Set a} {n m : ctx A} {w : vsubst n m} -> w ≡ (w ∘v id-vsub)
id-v-right {a} {A} {⊡} = refl
id-v-right {a} {A} {ψ , T} = cong₂ _,_ (trans id-v-right (sym (gmap-funct id-vsub))) refl -}

{-lookup-id : ∀ {a} {A : Set a} {n : ctx A} {T} {x : var n T} -> x ≡ lookup id-vsub x
lookup-id {a} {A} {⊡} {x = ()}
lookup-id {a} {A} {ψ , .T} {T} {top} = refl
lookup-id {a} {A} {ψ , T} {T'} {pop y} = trans (cong pop lookup-id) (sym (lookup-gmap pop id-vsub y))

id-v-left : ∀ {a} {A : Set a} {n m : ctx A} {w : vsubst n m} -> w ≡ (id-vsub ∘v w)
id-v-left {a} {A} {⊡} = refl
id-v-left {a} {A} {ψ , T} = cong₂ _,_ id-v-left lookup-id -}

data tp : Set where
 atom : tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

vsub-ext-funct : ∀ {A : Set} {n m k : ctx A} {T : A} (w : vsubst n m) (w' : vsubst m k)
 -> vsub-ext {T = T} (w' ∘v w) ≡ (vsub-ext w') ∘v (vsub-ext w)
vsub-ext-funct w w' = cong (λ α → α , top) (trans (gmap-funct w) (trans (gmap-cong (λ x → sym (lookup-gmap pop w' x))) (sym (gmap-funct w))))

{-ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> ext id x ≡ x
ext-id z = refl
ext-id (s y) = refl 

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn = s -}

data tm (Γ : ctx tp) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)
 c : tm Γ atom

[_]r : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[ σ ]r (v y) = v ([ σ ]v y)
[ σ ]r (M · N) = [ σ ]r M · [ σ ]r N
[ σ ]r (ƛ M) = ƛ ([ vsub-ext σ ]r M)
[ σ ]r c = c

sub : (Γ1 Γ2 : ctx tp) -> Set
sub Γ1 Γ2 = gsubst Γ1 (tm Γ2)

sub-ext : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> sub (Γ1 , T) (Γ2 , T)
sub-ext σ = (gmap [ wkn-vsub ]r σ) , (v top)

[_] : ∀ {Γ1 Γ2 T} (σ : sub Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[ σ ] (v y) = [ σ ]v y
[ σ ] (M · N) = [ σ ] M · [ σ ] N
[ σ ] (ƛ M) = ƛ ([ sub-ext σ ] M)
[ σ ] c = c

[]v-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]r ([ σ2 ]r R) ≡ [ σ1 ∘v σ2 ]r R
[]v-funct σ1 σ2 (v y) = cong v (sym (lookup-gmap (lookup σ1) σ2 y))
[]v-funct σ1 σ2 (y · y') = cong₂ _·_ ([]v-funct σ1 σ2 y) ([]v-funct σ1 σ2 y')
[]v-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]v-funct (vsub-ext σ1) (vsub-ext σ2) y) (cong (λ α → [ α ]r y) (sym (vsub-ext-funct σ2 σ1))))
[]v-funct σ1 σ2 c = refl

vn-ext-funct : ∀ {n m k : ctx tp} {T : tp} (σ : sub n m) (w' : vsubst m k)
 -> sub-ext {T = T} (gmap [ w' ]r σ) ≡ gmap [ vsub-ext w' ]r (sub-ext σ)
vn-ext-funct σ w' = cong (λ α → α , v top) (trans (gmap-funct σ) (trans (gmap-cong (λ x → trans ([]v-funct _ _ x) (trans (cong (λ α → [ α ]r x) (trans {!!} (sym (gmap-funct id-vsub)))) (sym ([]v-funct _ _ x))))) (sym (gmap-funct σ)))) --cong (λ α → α , top) (trans (gmap-funct w) (trans (gmap-cong (λ x → sym (lookup-gmap pop w' x))) (sym (gmap-funct w))))

[]vn-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : vsubst Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ]r ([ σ2 ] R) ≡ [ gmap [ σ1 ]r σ2 ] R
[]vn-funct σ1 σ2 (v y) = sym (lookup-gmap [ σ1 ]r σ2 y)
[]vn-funct σ1 σ2 (y · y') = cong₂ _·_ ([]vn-funct σ1 σ2 y) ([]vn-funct σ1 σ2 y')
[]vn-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]vn-funct (vsub-ext σ1) (sub-ext σ2) y) (cong (λ α → [ α ] y) (sym (vn-ext-funct _ _))))
[]vn-funct σ1 σ2 c = refl

{-
[]nv-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : vsubst Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ]v R) ≡ [ σ1 ∘₁ σ2 ] R
[]nv-funct σ1 σ2 (v y) = refl
[]nv-funct σ1 σ2 (y · y') = cong2 _·_ ([]nv-funct σ1 σ2 y) ([]nv-funct σ1 σ2 y')
[]nv-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]nv-funct (sub-ext σ1) (ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → refl) refl)))
[]nv-funct σ1 σ2 c = refl

[]-funct : ∀ {Γ1 Γ2 Γ3 S} (σ1 : sub Γ2 Γ3) (σ2 : sub Γ1 Γ2) (R : tm Γ1 S)
  -> [ σ1 ] ([ σ2 ] R) ≡ [ [ σ1 ] ∘₁ σ2 ] R
[]-funct σ1 σ2 (v y) = refl
[]-funct σ1 σ2 (y · y') = cong2 _·_ ([]-funct σ1 σ2 y) ([]-funct σ1 σ2 y')
[]-funct σ1 σ2 (ƛ y) = cong ƛ (trans ([]-funct (sub-ext σ1) (sub-ext σ2) y) (cong (λ (α : sub _ _) → [ α ] y) (var-dom-eq (λ x → trans ([]nv-funct (sub-ext σ1) s (σ2 x)) (sym ([]vn-funct s σ1 (σ2 x)))) refl)))
[]-funct σ1 σ2 c = refl

sub-ext-idv : ∀ {Γ T U} (x : var (Γ , T) U) -> (ext id) x ≡ x
sub-ext-idv z = refl
sub-ext-idv (s y) = refl

[]v-id : ∀ {Γ T} {M : tm Γ T} -> [ id ]v M ≡ M
[]v-id {M = v y} = refl
[]v-id {M = M · N} = cong2 _·_ []v-id []v-id
[]v-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : vsubst _ _) → [ α ]v M) (funext-imp (λ x → funext (λ x' → sub-ext-idv x')))) []v-id)
[]v-id {M = c} = refl

sub-ext-id : ∀ {Γ T U} (x : var (Γ , T) U) -> (sub-ext v) x ≡ v x
sub-ext-id z = refl
sub-ext-id (s y) = refl

[]-id : ∀ {Γ T} {M : tm Γ T} -> [ v ] M ≡ M
[]-id {M = v y} = refl
[]-id {M = M · N} = cong2 _·_ []-id []-id
[]-id {M = ƛ M} = cong ƛ (trans (cong (λ (α : sub _ _) → [ α ] M) (funext-imp (λ x → funext (λ x' → sub-ext-id x')))) []-id)
[]-id {M = c} = refl

data _→*_ : ∀ {T} -> tm ⊡ T -> tm ⊡ T -> Set where
 →*-refl : ∀ {T} {M : tm ⊡ T} -> M →* M
 ap1 : ∀ {T S} {M1 M2 : tm ⊡ (T ⇝ S)} {N1 : tm _ T} -> M1 →* M2  -> (M1 · N1) →* (M2 · N1)
 β : ∀ {T S} (M : tm (⊡ , T) S) (N : tm ⊡ T) -> ((ƛ M) · N) →* [ v ,, N ] M
 →*-trans : ∀ {T} {M N P : tm _ T} -> M →* N -> N →* P -> M →* P

data isNormal : ∀ {T} (t : tm ⊡ T) -> Set where
 ƛ : ∀ {T S} (t : tm (_ , T) S) -> isNormal (ƛ t)
 c : isNormal c

halts : ∀ {T} (t : tm ⊡ T) -> Set
halts {T} t = ∃ (λ (n : tm _ T) → (t →* n) × isNormal n)

reduce : ∀ T -> tm ⊡ T -> Set
reduce atom t = halts t
reduce (T ⇝ S) t = halts t × (∀ (x : tm _ T) -> reduce T x -> reduce S (t · x))

reduce-closed : ∀ {T} {t t' : tm _ T} -> (t →* t') -> reduce T t' -> reduce T t
reduce-closed {atom} p (N , (q1 , q2)) = N , ((→*-trans p q1) , q2)
reduce-closed {T ⇝ S} p ((N , (q1 , q2)) , f) = (N , (→*-trans p q1 , q2)) , (λ x rx → reduce-closed (ap1 p) (f x rx))

reduce-ext : ∀ {Γ} {σ : ∀ {U} (x : var Γ U) -> tm _ U} (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) {T} {t : tm _ T} (w : reduce T t) ->
 ∀ {U} (x : var (Γ , T) U) -> reduce U ((σ ,, t) x)
reduce-ext θ w z = w
reduce-ext θ w (s y) = θ y

lemma : ∀ {Γ Δ T S} -> (σ : sub Γ Δ) -> ∀ (N : tm Δ T) (M : tm (Γ , T) S) -> [ σ ,, N ] M ≡ [ v ,, N ] ([ sub-ext σ ] M)
lemma σ N M = trans (cong (λ (α : sub _ _) → [ α ] M) (var-dom-eq (λ x → trans (sym []-id) (sym ([]nv-funct (v ,, N) s (σ x)))) refl)) (sym ([]-funct (v ,, N) (sub-ext σ) M))

thm : ∀ {Γ T} (σ : ∀ {U} (x : var Γ U) -> tm ⊡ U) (θ : ∀ {U} (x : var Γ U) -> reduce U (σ x)) (t : tm Γ T) -> reduce T ([ σ ] t)
thm σ θ c = c , (→*-refl , c)
thm σ θ (v y) = θ y
thm σ θ (M · N) = proj₂ (thm σ θ M) ([ σ ] N) (thm σ θ N)
thm σ θ (ƛ {T} {S} M) = (_ , (→*-refl , (ƛ _))) , (λ N redN → reduce-closed {S} (β _ _) (eq-ind (reduce _) (lemma σ N M) (thm (σ ,, N) (reduce-ext θ redN) M)))

reify : ∀ {T} (t : tm _ T) -> reduce T t -> halts t
reify {atom} t p = p
reify {T ⇝ S} t (h , _) = h

done' : ∀ {T} (t : tm ⊡ T) -> halts t
done' {T} t = reify _ (eq-ind (reduce T) []-id (thm v (λ ()) t))
-}