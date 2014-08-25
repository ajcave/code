module subj-red where
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality hiding ([_])

data tp : Set where
 i : tp
 _⇝_ : (T S : tp) -> tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

-- data var : (Γ : ctx) -> tp -> Set where
--  top : ∀ {Γ T} -> var (Γ , T) T
--  pop : ∀ {Γ S T} -> var Γ T -> var (Γ , S) T


data exp (Γ : ℕ) :  Set where
 ▹ : Fin Γ -> exp Γ
 _·_ : ∀ (M : exp Γ) (N : exp Γ) -> exp Γ
 ƛ : (M : exp (suc Γ)) -> exp Γ

⌞_⌟ : ctx -> ℕ
⌞ ⊡ ⌟ = 0
⌞ Γ , T ⌟ = suc ⌞ Γ ⌟

lookup : (Γ : ctx) -> Fin ⌞ Γ ⌟ -> tp
lookup ⊡ ()
lookup (Γ , T) zero = T
lookup (Γ , T) (suc n) = lookup Γ n

data oft (Γ : ctx) : exp ⌞ Γ ⌟ -> tp -> Set where
 ▹ : (x : Fin ⌞ Γ ⌟) -> oft Γ (▹ x) (lookup Γ x)
 _·_ : ∀ {T S} {M N} -> oft Γ M (T ⇝ S) -> oft Γ N T -> oft Γ (M · N) S
 ƛ : ∀ {T S} {M} -> oft (Γ , T) M S -> oft Γ (ƛ M) (T ⇝ S)

data sub : (Γ : ℕ) -> ℕ -> Set where
  ⊡ : ∀ {Γ} -> sub Γ zero
  _,_ : ∀ {Γ Δ } (σ : sub Γ Δ) (M : exp Γ) -> sub Γ (suc Δ)

--  where
 -- ⊡ : ∀ {Γ} -> tsub Γ ⊡ ⊡
 -- _,_ : ∀ {Γ Δ T} {σ} (θ : tsub Γ Δ σ) {M} -> oft Γ M T -> tsub Γ (Δ , T) (σ , M)

data vsub : (Γ : ℕ) -> ℕ -> Set where
 ⊡ : ∀ {Γ} -> vsub Γ zero
 _,_ : ∀ {Γ Δ} (σ : vsub Γ Δ) (x : Fin Γ) -> vsub Γ (suc Δ)

[_]v : ∀ {Γ Δ} (σ : vsub Γ Δ) (x : Fin Δ) -> Fin Γ
[ ⊡ ]v ()
[ σ , x ]v zero = x
[ σ , x ]v (suc y) = [ σ ]v y

tvsub : (Γ : ctx) -> (Δ : ctx) -> (σ : vsub ⌞ Γ ⌟ ⌞ Δ ⌟) -> Set
tvsub Γ Δ σ = ∀ x -> lookup Δ x ≡ lookup Γ ([ σ ]v x)

var = Fin

map : ∀ {Γ Δ θ} (f : var Γ -> var θ) (σ : vsub Γ Δ) -> vsub θ Δ
map f ⊡ = ⊡
map f (σ , x) = (map f σ) , (f x)

vext : ∀ {Γ Δ} (σ : vsub Γ Δ) -> vsub (suc Γ) (suc Δ)
vext σ = map suc σ , zero

id : ∀ {Γ} -> vsub Γ Γ
id {zero} = ⊡
id {suc Γ} = (map suc id) , zero

wkn : ∀ {Γ} -> vsub (suc Γ) Γ
wkn = map suc id

[_] : ∀ {Γ Δ} (σ : vsub Γ Δ) (M : exp Δ) -> exp Γ
[_] σ (▹ y) = ▹ ([ σ ]v y)
[_] σ (M · N) = ([ σ ] M) · ([ σ ] N)
[_] σ (ƛ M) = ƛ ([ vext σ ] M)

[_]tv : ∀ {Γ Δ} (σ : sub Γ Δ) (x : var Δ) -> exp Γ
[ ⊡ ]tv ()
[ σ , x ]tv zero = x
[ σ , x ]tv (suc y) = [ σ ]tv y

tmap : ∀ {Γ Δ θ} (f : exp Γ -> exp θ) (σ : sub Γ Δ) -> sub θ Δ
tmap f ⊡ = ⊡
tmap f (σ , x) = (tmap f σ) , (f x)

[_]t : ∀ {Γ Δ} (σ : sub Γ Δ) (M : exp Δ) -> exp Γ
[_]t σ (▹ y) = [ σ ]tv y
[_]t σ (M · N) = [ σ ]t M · [ σ ]t N
[_]t σ (ƛ M) = ƛ ([ tmap [ wkn ] σ , (▹ zero) ]t M)

tsub : (Γ : ctx) -> (Δ : ctx) -> (σ : sub ⌞ Γ ⌟ ⌞ Δ ⌟) -> Set
tsub Γ Δ σ = ∀ x -> oft Γ ([ σ ]tv x) (lookup Δ x)

tid : ∀ {Γ} -> sub Γ Γ
tid {zero} = ⊡
tid {suc Γ} = (tmap [ wkn ] tid) , (▹ zero)

[_/x] : ∀ {Γ} (N : exp Γ) (M : exp (suc Γ)) -> exp Γ
[ N /x] M = [ tid , N ]t M

map-lem : ∀ {Γ Δ θ} (f : var Γ -> var θ) (σ : vsub Γ Δ) x -> [ map f σ ]v x ≡ f ([ σ ]v x)
map-lem f (σ , x) zero = refl
map-lem f (σ , x) (suc x₁) = map-lem f σ x₁

tvsub-ext : ∀ {Γ : ctx} {Δ : ctx} {T} {σ : vsub ⌞ Γ ⌟ ⌞ Δ ⌟} -> tvsub Γ Δ σ -> tvsub (Γ , T) (Δ , T) (vext σ)
tvsub-ext θ zero = refl
tvsub-ext {σ = σ} θ (suc x) with θ x | cong (lookup _) (map-lem suc σ x)
... | q0 | q1 = trans q0 (sym q1)

[_]tpv : ∀ {Γ Δ T} {σ} (θ : tvsub Γ Δ σ) {M} -> oft Δ M T -> oft Γ ([ σ ] M) T
[_]tpv {σ = σ} θ (▹ x) = subst (oft _ (▹ ([ σ ]v x))) (sym (θ x)) (▹ ([ σ ]v x))
[_]tpv θ (m · m₁) = ([ θ ]tpv m) · ([ θ ]tpv m₁)
[_]tpv θ (ƛ m) = ƛ ([ tvsub-ext θ ]tpv m)

lem0 : ∀ {Γ Δ Δ'} (w : vsub Δ' Δ) (σ : sub Δ Γ) x -> [ tmap [ w ] σ ]tv x ≡ [ w ] ([ σ ]tv x)
lem0 w ⊡ ()
lem0 w (σ , M) zero = refl
lem0 w (σ , M) (suc x) = lem0 w σ x

lem1 : ∀ {Γ} (x : var Γ) -> x ≡ [ id ]v x
lem1 zero = refl
lem1 (suc x) = trans (cong suc (lem1 x)) (sym (map-lem suc id x))

tvsub-wkn : ∀ {Γ : ctx} {T} -> tvsub (Γ , T) Γ wkn
tvsub-wkn {Γ} {T} x with map-lem suc id x
... | q = trans (cong (lookup Γ) (lem1 x)) (cong (lookup (Γ , T)) (sym q))

tpsub-wkn : ∀ {Γ : ctx} {Δ : ctx} {T} {σ} -> tsub Γ Δ σ -> tsub (Γ , T) Δ (tmap [ wkn ] σ)
tpsub-wkn {Γ} {Δ} {T} {σ = σ} θ x = subst (λ α → oft (Γ , T) α (lookup Δ x)) (sym (lem0 wkn σ x)) ([ tvsub-wkn  ]tpv (θ x))

tpsub-ext : ∀ {Γ : ctx} {Δ : ctx} {T} {σ} -> tsub Γ Δ σ -> tsub (Γ , T) (Δ , T) (tmap [ wkn ] σ , ▹ zero)
tpsub-ext θ zero = ▹ zero
tpsub-ext {σ = σ} θ (suc x) = tpsub-wkn {σ = σ} θ x

[_]tp : ∀ {Γ Δ T} {σ} (θ : tsub Γ Δ σ) {M} -> oft Δ M T -> oft Γ ([ σ ]t M) T
[_]tp θ (▹ x) = θ x
[_]tp θ (m · m₁) = ([ θ ]tp m) · ([ θ ]tp m₁)
[_]tp θ (ƛ m) = ƛ ([ tpsub-ext θ ]tp m)





