module mu-ltl where
open import Relation.Binary.PropositionalEquality
--open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import FinMap
open import Product
open import Unit
open import Function

const1 : ∀ {A : Set} {B : Set₁} -> B -> A -> B
const1 b _ = b


swap : ∀ {A B C : Set} (f : A -> B -> C) -> B -> A -> C
swap f b a = f a b 

{-data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x
-}
subst2/3 : ∀ {A B C : Set} (P : A → B -> C → Set)
         {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → (z : C) -> P x₂ y₂ z → P x₁ y₁ z
subst2/3 P refl refl z p = p

--cong : ∀ {A B : Set} (f : A -> B) {x y} -> x ≡ y -> f x ≡ f y
--cong f refl = refl

cong1st : ∀ {A B C : Set} (f : A -> B -> C) {a1 a2} -> a1 ≡ a2 -> (b : B) -> f a1 b ≡ f a2 b 
cong1st f refl b = refl

cong2 : ∀ {A B C : Set} (f : A -> B -> C) {a1 a2} -> a1 ≡ a2 -> {b1 b2 : B} -> b1 ≡ b2 -> f a1 b1 ≡ f a2 b2
cong2 f refl refl = refl 

{-trans : ∀ {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

sym : ∀ {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl -}

_≈_ : ∀ {A B : Set} (f g : A -> B) -> Set
f ≈ g = ∀ x -> f x ≡ g x 

{-data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ S T} -> var Γ T -> var (Γ , S) T -}

sub : ∀ {A : Set} (exp : A -> Set) -> ctx A -> Set
sub exp Γ = gsubst Γ exp

{-[_]v : ∀ {A} {exp : A -> Set} {Δ T} (σ : sub exp Δ) -> var Δ T -> exp T
[ ⊡ ]v ()
[ σ , M ]v top = M
[ σ , M ]v (pop y) = [ σ ]v y -}

sub-map : ∀ {A} {exp1 exp2 : A -> Set} (f : ∀ {T} -> exp1 T -> exp2 T) {Δ} -> sub exp1 Δ -> sub exp2 Δ
sub-map f σ = gmap f σ

vsub : ∀ {A} (Γ1 Γ2 : ctx A) -> Set
vsub Γ1 Γ2 = sub (var Γ1) Γ2

{-wkn : ∀ {A} {Γ1 Γ2} {T : A} -> vsub Γ1 Γ2 -> vsub (Γ1 , T) Γ2
wkn σ = sub-map pop σ -}

{-id-vsub : ∀ {A} {Γ : ctx A} -> vsub Γ Γ
id-vsub {A} {⊡} = ⊡
id-vsub {A} {Γ , T} = (wkn id-vsub) , top 

wkn-vsub : ∀ {A} {Γ : ctx A} {T} -> vsub (Γ , T) Γ
wkn-vsub {A} {Γ} {T} = wkn id-vsub 

vsub-ext : ∀ {A T} {Γ1 Γ2 : ctx A} -> vsub Γ1 Γ2 -> vsub (Γ1 , T) (Γ2 , T)
vsub-ext σ = (sub-map pop σ) , top -}

record type : Set where
 constructor #prop

mutual
 data functor (ζ : ctx type) : Set where
  ▹ : (A : var ζ #prop) -> functor ζ
  μ ν : (F : functor (ζ , #prop)) -> functor ζ
  ○ : (A : functor ζ) -> functor ζ
  _⊃_ : (A : prop) (B : functor ζ) -> functor ζ
  _∧_ _∨_ : (A B : functor ζ) -> functor ζ
  ⊤ : functor ζ

 prop : Set
 prop = functor ⊡

psub : ∀ (ζ1 ζ2 : ctx type) -> Set
psub ζ1 ζ2 = sub (const1 (functor ζ1)) ζ2

[_]pv : ∀ {ζ1 ζ2} -> vsub ζ2 ζ1 -> functor ζ1 -> functor ζ2
[ σ ]pv (▹ A) = ▹ ([ σ ]v A)
[ σ ]pv (μ F) = μ ([ vsub-ext σ ]pv F)
[ σ ]pv (ν F) = ν ([ vsub-ext σ ]pv F)
[ σ ]pv (○ A) = ○ ([ σ ]pv A)
[ σ ]pv (A ⊃ B) = A ⊃ ([ σ ]pv B)
[ σ ]pv (A ∧ B) = ([ σ ]pv A) ∧ ([ σ ]pv B)
[ σ ]pv (A ∨ B) = ([ σ ]pv A) ∨ ([ σ ]pv B)
[ σ ]pv ⊤ = ⊤

id-psub : ∀ {ζ} -> psub ζ ζ
id-psub {⊡} = _
id-psub {ζ , #prop} = (sub-map [ wkn-vsub ]pv id-psub) , (▹ top)

psub-wkn : ∀ {ζ1 ζ2} (σ : psub ζ1 ζ2) -> psub (ζ1 , #prop) ζ2
psub-wkn σ = sub-map [ wkn-vsub ]pv σ

psub-ext : ∀ {ζ1 ζ2} -> psub ζ1 ζ2 -> psub (ζ1 , #prop) (ζ2 , #prop)
psub-ext σ = (psub-wkn σ) , ▹ top

[_]p : ∀ {ζ1 ζ2} -> psub ζ2 ζ1 -> functor ζ1 -> functor ζ2
[ σ ]p (▹ A) = [ σ ]v A
[ σ ]p (μ F) = μ ([ psub-ext σ ]p F)
[ σ ]p (ν F) = ν ([ psub-ext σ ]p F)
[ σ ]p (○ A) = ○ ([ σ ]p A)
[ σ ]p (A ⊃ B) = A ⊃ ([ σ ]p B)
[ σ ]p (A ∧ B) = ([ σ ]p A) ∧ ([ σ ]p B)
[ σ ]p (A ∨ B) = ([ σ ]p A) ∨ ([ σ ]p B)
[ σ ]p ⊤ = ⊤

_•_ : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> psub ζ1 ζ3
σ1 • σ2 = sub-map [ σ1 ]p σ2

_◦_ : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : vsub ζ2 ζ3) -> psub ζ1 ζ3
σ1 ◦ σ2 = sub-map [ σ1 ]v σ2

_⁌_ : ∀ {a b} {A : Set a} {ζ2 ζ3} {exp : A -> Set b} (σ1 : gsubst ζ2 exp) (σ2 : vsubst {a} {A} ζ3 ζ2) -> gsubst ζ3 exp
σ1 ⁌ σ2 = gmap [ σ1 ]v σ2

_◆_ :  ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> psub ζ1 ζ3
σ1 ◆ σ2 = sub-map [ σ1 ]pv σ2


sub-vsub-funct : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]p ∘ [ σ2 ]v) ≈ [ σ1 • σ2 ]v
sub-vsub-funct σ1 σ2 top = refl
sub-vsub-funct σ1 σ2 (pop y) = sym (lookup-gmap [ σ1 ]p σ2 (pop y))



pvsub-vsub-funct :  ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]pv ∘ [ σ2 ]v) ≈ [ σ1 ◆ σ2 ]v
pvsub-vsub-funct σ1 σ2 top = refl
pvsub-vsub-funct σ1 σ2 (pop y) = sym (lookup-gmap [ σ1 ]pv σ2 (pop y))



sub-map-funct : ∀ {A : Set} {exp1 exp2 exp3 : A -> Set} (g : ∀ {T} -> exp2 T -> exp3 T) (f : ∀ {T} -> exp1 T -> exp2 T)
 -> ∀ {Δ} (σ : sub exp1 Δ) -> (((sub-map g) ∘ (sub-map f)) σ) ≡ (sub-map (g ∘ f) σ)
sub-map-funct g f σ = gmap-funct σ

sub-map-resp-≈ :  ∀ {a} {A : Set a} {exp1 exp2 : A -> Set} {f g : ∀ {T} -> exp1 T -> exp2 T} {Δ}
 -> (∀ {T} -> f {T} ≈ g {T}) -> (σ : gsubst Δ exp1) -> gmap f σ ≡ gmap g σ
sub-map-resp-≈ H σ = gmap-cong H

-- TODO: Move into FinMap
id-v-right : ∀ {a b} {A : Set a} {F : A -> Set b} {ζ} (σ : gsubst ζ F) -> (σ ⁌ id-vsub) ≡ σ
id-v-right {a} {b} {A} {F} {⊡} σ = refl
id-v-right {a} {b} {A} {F} {ψ , T} (σ , M) = cong (λ α → α , M) (trans (gmap-funct id-vsub) (id-v-right σ))


ext-wkn : ∀ {ζ1 ζ2} (σ1 : psub ζ1 ζ2) -> ((psub-ext σ1) ◦ wkn-vsub) ≡ (wkn-vsub ◆ σ1)
ext-wkn σ1 = trans (sub-map-funct _ _ _) (id-v-right _)

comma-wkn : ∀ {ζ1 ζ2} (σ1 : psub ζ1 ζ2) A -> ((σ1 , A) ◦ wkn-vsub) ≡ σ1
comma-wkn σ1 A = trans (sub-map-funct _ _ _) (id-v-right _)

map-lookup : ∀ {A} {ζ1 ζ2 ζ3} (f : ∀ {U : A} -> var ζ2 U -> var ζ3 U) (σ : vsub {A} ζ2 ζ1) {T} (y : var ζ1 T) -> [ sub-map f σ ]v y ≡ f ([ σ ]v y)
map-lookup f σ = lookup-gmap f σ

vsub-v-id : ∀ {a} {A : Set a} {ζ T} (x : var ζ T) -> [ id-vsub {a} {A} ]v x ≡ x
vsub-v-id top = refl
vsub-v-id (pop y) = trans (lookup-gmap pop id-vsub y) (cong pop (vsub-v-id y))

ext-wkn2 : ∀ {a} {A : Set a} {ζ1 ζ2} (σ1 : vsubst {a} {A} ζ2 ζ1) {T} -> ((vsub-ext {a} {A} {T} σ1) ⁌ wkn-vsub) ≡ (wkn-vsub ⁌ σ1)
ext-wkn2 {a} σ1 =  begin
                (vsub-ext σ1 ⁌ wkn-vsub) ≡⟨ (gmap-funct id-vsub) ⟩
                (wkn σ1 ⁌ id-vsub) ≡⟨ id-v-right (wkn σ1) ⟩
                (wkn σ1) ≡⟨ (gmap-cong (λ x → cong pop (sym (vsub-v-id x)))) ⟩
                (gmap (λ z → pop (lookup id-vsub z)) σ1 ≡⟨ (gmap-cong {σ = σ1} (λ x → sym (lookup-gmap pop id-vsub x))) ⟩
                (wkn-vsub ⁌ σ1)
               ∎)

-- TODO: Move into FinMap
vsub-vsub-funct :  ∀ {A} {ζ2 ζ3} {exp : A -> Set} (σ1 : sub exp ζ2) (σ2 : vsub {A} ζ2 ζ3) {T} (x : var ζ3 T) -> ([ σ1 ]v ∘ [ σ2 ]v) x ≡ [ σ1 ⁌ σ2 ]v x
vsub-vsub-funct σ1 σ x = sym (lookup-gmap [ σ1 ]v σ x)

assocvvv : ∀ {A} {ζ1 ζ2 ζ3 ζ4} (σ1 : vsub {A} ζ1 ζ2) (σ2 : vsub ζ2 ζ3) (σ3 : vsub ζ3 ζ4) -> (σ1 ⁌ (σ2 ⁌ σ3)) ≡ ((σ1 ⁌ σ2) ⁌ σ3)
assocvvv σ1 σ2 σ3 = trans (sub-map-funct _ _ _) (sub-map-resp-≈ (vsub-vsub-funct σ1 σ2) σ3)

ext-funct-vv : ∀ {a} {A : Set a} {ζ1 ζ2 ζ3} {T} (σ1 : vsubst {a} {A} ζ2 ζ1) (σ2 : vsubst ζ3 ζ2) -> ((vsub-ext {a} {A} {T} σ1) ⁌ (vsub-ext σ2)) ≡ vsub-ext (σ1 ⁌ σ2)
ext-funct-vv σ1 σ2 = cong (λ α -> α , top) (trans (trans (gmap-funct σ2) (gmap-cong (lookup-gmap pop σ1))) (sym (gmap-funct σ2)))

pvsub-pvsub-funct :  ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : vsub ζ2 ζ3) -> ([ σ1 ]pv ∘ [ σ2 ]pv) ≈ [ σ1 ⁌ σ2 ]pv
pvsub-pvsub-funct σ1 σ2 (▹ A) = cong ▹ (vsub-vsub-funct σ1 σ2 A)
pvsub-pvsub-funct σ1 σ2 (μ F) = cong μ (trans (pvsub-pvsub-funct (vsub-ext σ1) (vsub-ext σ2) F) (cong1st [_]pv (ext-funct-vv _ _) F))
pvsub-pvsub-funct σ1 σ2 (ν F) = cong ν (trans (pvsub-pvsub-funct (vsub-ext σ1) (vsub-ext σ2) F) (cong1st [_]pv (ext-funct-vv _ _) F))
pvsub-pvsub-funct σ1 σ2 (○ A) = cong ○ (pvsub-pvsub-funct σ1 σ2 A)
pvsub-pvsub-funct σ1 σ2 (A ⊃ B) = cong (_⊃_ A) (pvsub-pvsub-funct σ1 σ2 B)
pvsub-pvsub-funct σ1 σ2 (A ∧ B) = cong2 _∧_ (pvsub-pvsub-funct σ1 σ2 A) (pvsub-pvsub-funct σ1 σ2 B)
pvsub-pvsub-funct σ1 σ2 (A ∨ B) = cong2 _∨_ (pvsub-pvsub-funct σ1 σ2 A) (pvsub-pvsub-funct σ1 σ2 B)
pvsub-pvsub-funct σ1 σ2 ⊤ = refl

ext-funct-pv : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : vsub ζ2 ζ3) -> ((psub-ext σ1) ◦ (vsub-ext σ2)) ≡ psub-ext (σ1 ◦ σ2)
ext-funct-pv σ1 σ2 = cong1st _,_ (trans (trans (sub-map-funct _ pop σ2) (sub-map-resp-≈ (λ x → sym (pvsub-vsub-funct _ σ1 x)) σ2)) (sym (sub-map-funct _ _ σ2))) (▹ top)

sub-pvsub-funct :  ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : vsub ζ2 ζ3) -> ([ σ1 ]p ∘ [ σ2 ]pv) ≈ [ σ1 ◦ σ2 ]p
sub-pvsub-funct σ1 σ2 (▹ A) = vsub-vsub-funct σ1 σ2 A
sub-pvsub-funct σ1 σ2 (μ F) = cong μ (trans (sub-pvsub-funct (psub-ext σ1) (vsub-ext σ2) F) (cong1st [_]p (ext-funct-pv _ _) F))
sub-pvsub-funct σ1 σ2 (ν F) = cong ν (trans (sub-pvsub-funct (psub-ext σ1) (vsub-ext σ2) F) (cong1st [_]p (ext-funct-pv _ _) F))
sub-pvsub-funct σ1 σ2 (○ A) = cong ○ (sub-pvsub-funct σ1 σ2 A)
sub-pvsub-funct σ1 σ2 (A ⊃ B) = cong (_⊃_ A) (sub-pvsub-funct σ1 σ2 B)
sub-pvsub-funct σ1 σ2 (A ∧ B) = cong2 _∧_ (sub-pvsub-funct σ1 σ2 A) (sub-pvsub-funct σ1 σ2 B)
sub-pvsub-funct σ1 σ2 (A ∨ B) = cong2 _∨_ (sub-pvsub-funct σ1 σ2 A) (sub-pvsub-funct σ1 σ2 B)
sub-pvsub-funct σ1 σ2 ⊤ = refl

assocvv : ∀ {ζ1 ζ2 ζ3 ζ4} (σ1 : vsub ζ1 ζ2) (σ2 : vsub ζ2 ζ3) (σ3 : psub ζ3 ζ4) -> (σ1 ◆ (σ2 ◆ σ3)) ≡ ((σ1 ⁌ σ2) ◆ σ3)
assocvv σ1 σ2 σ3 = trans (sub-map-funct _ _ _) (sub-map-resp-≈ (pvsub-pvsub-funct σ1 σ2) σ3)

ext-funct-vp : ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ((vsub-ext σ1) ◆ (psub-ext σ2)) ≡ psub-ext (σ1 ◆ σ2)
ext-funct-vp σ1 σ2 = cong1st _,_ (trans (assocvv _ _ _) (trans (sub-map-resp-≈ (λ x → trans (cong1st [_]pv (ext-wkn2 σ1) x) (sym (pvsub-pvsub-funct _ _ x))) σ2) (sym (sub-map-funct _ _ σ2)))) (▹ top)

pvsub-sub-funct :  ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]pv ∘ [ σ2 ]p) ≈ [ σ1 ◆ σ2 ]p
pvsub-sub-funct σ1 σ2 (▹ A) = pvsub-vsub-funct σ1 σ2 A
pvsub-sub-funct σ1 σ2 (μ F) = cong μ (trans (pvsub-sub-funct (vsub-ext σ1) (psub-ext σ2) F) (cong1st [_]p (ext-funct-vp σ1 σ2) F))
pvsub-sub-funct σ1 σ2 (ν F) = cong ν (trans (pvsub-sub-funct (vsub-ext σ1) (psub-ext σ2) F) (cong1st [_]p (ext-funct-vp σ1 σ2) F))
pvsub-sub-funct σ1 σ2 (○ A) = cong ○ (pvsub-sub-funct σ1 σ2 A)
pvsub-sub-funct σ1 σ2 (A ⊃ B) = cong (_⊃_ A) (pvsub-sub-funct σ1 σ2 B)
pvsub-sub-funct σ1 σ2 (A ∧ B) = cong2 _∧_ (pvsub-sub-funct σ1 σ2 A) (pvsub-sub-funct σ1 σ2 B)
pvsub-sub-funct σ1 σ2 (A ∨ B) = cong2 _∨_ (pvsub-sub-funct σ1 σ2 A) (pvsub-sub-funct σ1 σ2 B)
pvsub-sub-funct σ1 σ2 ⊤ = refl

assocv : ∀ {ζ1 ζ2 ζ3 ζ4} (σ1 : psub ζ1 ζ2) (σ2 : vsub ζ2 ζ3) (σ3 : psub ζ3 ζ4) -> (σ1 • (σ2 ◆ σ3)) ≡ ((σ1 ◦ σ2) • σ3)
assocv σ1 σ2 σ3 = trans (sub-map-funct _ _ _) (sub-map-resp-≈ (sub-pvsub-funct σ1 σ2) σ3) 

ext-funct : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ((psub-ext σ1) • (psub-ext σ2)) ≡ psub-ext (σ1 • σ2)
ext-funct σ1 σ2 = cong1st _,_ (trans (assocv _ _ _) (trans (sub-map-resp-≈ (λ x → trans (cong1st [_]p (ext-wkn σ1) x) (sym (pvsub-sub-funct _ _ x))) σ2) (sym (sub-map-funct _ _ σ2)))) (▹ top)

-- TODO: Take advantage of generic traversal to get functorality
sub-funct : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]p ∘ [ σ2 ]p) ≈ [ σ1 • σ2 ]p
sub-funct σ1 σ2 (▹ A) = sub-vsub-funct σ1 σ2 A
sub-funct σ1 σ2 (μ F) = cong μ (trans (sub-funct (psub-ext σ1) (psub-ext σ2) F) (cong1st [_]p (ext-funct σ1 σ2) F))
sub-funct σ1 σ2 (ν F) = cong ν (trans (sub-funct (psub-ext σ1) (psub-ext σ2) F) (cong1st [_]p (ext-funct σ1 σ2) F))
sub-funct σ1 σ2 (○ A) = cong ○ (sub-funct σ1 σ2 A)
sub-funct σ1 σ2 (A ⊃ B) = cong (_⊃_ A) (sub-funct σ1 σ2 B)
sub-funct σ1 σ2 (A ∧ B) = cong2 _∧_ (sub-funct σ1 σ2 A) (sub-funct σ1 σ2 B)
sub-funct σ1 σ2 (A ∨ B) = cong2 _∨_ (sub-funct σ1 σ2 A) (sub-funct σ1 σ2 B)
sub-funct σ1 σ2 ⊤ = refl



sub-v-id : ∀ {ζ1} (A : var ζ1 #prop) -> [ id-psub ]v A ≡ ▹ A
sub-v-id top = refl
sub-v-id (pop y) = trans (sym (pvsub-vsub-funct wkn-vsub id-psub y)) (trans (cong [ wkn-vsub ]pv (sub-v-id y)) (cong ▹ (trans (map-lookup pop id-vsub y) (cong pop (vsub-v-id y)))))

sub-id : ∀ {ζ1} (M : functor ζ1) -> [ id-psub ]p M ≡ M
sub-id (▹ A) = sub-v-id A
sub-id (μ F) = cong μ (sub-id F)
sub-id (ν F) = cong ν (sub-id F)
sub-id (○ A) = cong ○ (sub-id A)
sub-id (A ⊃ B) = cong (_⊃_ A) (sub-id B)
sub-id (A ∧ B) = cong2 _∧_ (sub-id A) (sub-id B)
sub-id (A ∨ B) = cong2 _∨_ (sub-id A) (sub-id B)
sub-id ⊤ = refl

sub-map-id : ∀ {ζ1 ζ2} (σ : psub ζ1 ζ2) -> (id-psub • σ) ≡ σ
sub-map-id {ζ1} {⊡} σ = refl
sub-map-id {ζ1} {ψ , T} (σ , M) = cong₂ _,_ (sub-map-id σ) (sub-id M)

assoc : ∀ {ζ1 ζ2 ζ3 ζ4} (σ1 : psub ζ1 ζ2) (σ2 : psub ζ2 ζ3) (σ3 : psub ζ3 ζ4) -> (σ1 • (σ2 • σ3)) ≡ ((σ1 • σ2) • σ3)
assoc σ1 σ2 σ3 = trans (sub-map-funct _ _ _) (sub-map-resp-≈ (sub-funct σ1 σ2) σ3)


[_/x]p : ∀ {ζ} -> functor ζ -> functor (ζ , #prop) -> functor ζ
[ M /x]p A = [ id-psub , M ]p A

record judgement : Set where
 constructor true

mutual
 data _,_⊢_-_ (θ : ctx prop) (Γ : ctx prop) : prop -> judgement -> Set where
  ▹ : ∀ {A} -> (x : var Γ A)
            -> -------------------
                θ , Γ ⊢ A - true
  ƛ : ∀ {A B} -> (M : θ , (Γ , A) ⊢ B - true)
              -> ----------------------------------
                      θ , Γ ⊢ (A ⊃ B) - true
  _·_ : ∀ {A B} -> (M : θ , Γ ⊢ (A ⊃ B) - true) (N : θ , Γ ⊢ A - true)
                -> -----------------------------------------------------------
                                θ , Γ ⊢ B - true
  let-◦ : ∀ {A C J} (M : θ , Γ ⊢ (○ A) - true) (N : (θ , A) , Γ ⊢ C - J)
                   -> ---------------------------------------------------------------
                                          θ , Γ ⊢ C - J
  ◦ : ∀ {A} -> (M : ⊡ , θ ⊢ A - true)
              -> --------------------------
                   θ , Γ ⊢ (○ A) - true
  inj : ∀ {F} -> (M : θ , Γ ⊢ ([ μ F /x]p F) - true)
              -> -----------------------------------------------------
                              θ , Γ ⊢ μ F - true
  rec : ∀ F {C} -> (M : θ , Γ ⊢ μ F - true) -> (N : ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                -> -------------------------------------------------------------------
                                θ , Γ ⊢ C - true
  out : ∀ {F} -> (M : θ , Γ ⊢ ν F - true)
              -> -----------------------------------
                 θ , Γ ⊢ ([ ν F /x]p F) - true
  unfold : ∀ F {C} -> (M : θ , Γ ⊢ C - true) -> (N : ⊡ , ⊡ , C ⊢ [ C /x]p F - true)
                   -> -------------------------------------------------------------
                       θ , Γ ⊢ ν F - true
  <_,_> : ∀ {A B} -> (M : θ , Γ ⊢ A - true) (N : θ , Γ ⊢ B - true)
                  -> ---------------------------------------------
                                θ , Γ ⊢ (A ∧ B) - true
  fst : ∀ {A B} -> (M : θ , Γ ⊢ (A ∧ B) - true)
                -> -----------------------------
                       θ , Γ ⊢ A - true
  snd : ∀ {A B} -> (M : θ , Γ ⊢ (A ∧ B) - true)
                -> -----------------------------
                       θ , Γ ⊢ B - true
  inl : ∀ {B A} -> (M : θ , Γ ⊢ A - true)
                -> ------------------------
                      θ , Γ ⊢ (A ∨ B) - true
  inr : ∀ {A B} -> (M : θ , Γ ⊢ B - true)
                -> ------------------------
                      θ , Γ ⊢ (A ∨ B) - true
  case : ∀ {A B C} -> (M : θ , Γ ⊢ (A ∨ B) - true) -> (N1 : θ , Γ , A ⊢ C - true) (N2 : θ , Γ , B ⊢ C - true)
                   -> θ , Γ ⊢ C - true
  unit : θ , Γ ⊢ ⊤ - true

[_]tv : ∀ {θ Γ1 Γ2 A J} -> vsub Γ2 Γ1 -> θ , Γ1 ⊢ A - J -> θ , Γ2 ⊢ A - J
[_]tv σ (▹ x) = ▹ ([ σ ]v x)
[_]tv σ (ƛ M) = ƛ ([ vsub-ext σ ]tv M)
[_]tv σ (M · N) = [ σ ]tv M · [ σ ]tv N
[_]tv σ (let-◦ M N) = let-◦ ([ σ ]tv M) ([ σ ]tv N)
[_]tv σ (◦ M) = ◦ M
[_]tv σ (inj M) = inj ([ σ ]tv M)
[_]tv σ (rec F M N) = rec F ([ σ ]tv M) N
[_]tv σ (out M) = out ([ σ ]tv M)
[_]tv σ (unfold F M N) = unfold F ([ σ ]tv M) N
[_]tv σ < M , N > = < [ σ ]tv M , [ σ ]tv N >
[_]tv σ (fst M) = fst ([ σ ]tv M)
[_]tv σ (snd M) = snd ([ σ ]tv M)
[_]tv σ (inl M) = inl ([ σ ]tv M)
[_]tv σ (inr M) = inr ([ σ ]tv M)
[_]tv σ (case M N1 N2) = case ([ σ ]tv M) ([ vsub-ext σ ]tv N1) ([ vsub-ext σ ]tv N2)
[_]tv σ unit = unit

[_]vav : ∀ {θ1 θ2 Γ A J} -> vsub θ2 θ1 -> θ1 , Γ ⊢ A - J -> θ2 , Γ ⊢ A - J
[_]vav σ (▹ x) = ▹ x
[_]vav σ (ƛ M) = ƛ ([ σ ]vav M)
[_]vav σ (M · N) = [ σ ]vav M · [ σ ]vav N
[_]vav σ (let-◦ M N) = let-◦ ([ σ ]vav M) ([ vsub-ext σ ]vav N)
[_]vav σ (◦ M) = ◦ ([ σ ]tv M)
[_]vav σ (inj M) = inj ([ σ ]vav M)
[_]vav σ (rec F M N) = rec F ([ σ ]vav M) N
[_]vav σ (out M) = out ([ σ ]vav M)
[_]vav σ (unfold F M N) = unfold F ([ σ ]vav M) N
[_]vav σ < M , N > = < [ σ ]vav M , [ σ ]vav N >
[_]vav σ (fst M) = fst ([ σ ]vav M)
[_]vav σ (snd M) = snd ([ σ ]vav M)
[_]vav σ (inl M) = inl ([ σ ]vav M)
[_]vav σ (inr M) = inr ([ σ ]vav M)
[_]vav σ (case M N1 N2) = case ([ σ ]vav M) ([ σ ]vav N1) ([ σ ]vav N2)
[_]vav σ unit = unit

truesub : ∀ θ (Γ1 Γ2 : ctx (prop)) -> Set
truesub θ Γ1 Γ2 = sub (λ A -> θ , Γ1 ⊢ A - true) Γ2

truesub-id : ∀ {θ Γ} -> truesub θ Γ Γ
truesub-id {θ} {⊡} = _
truesub-id {θ} {Γ , T} = (sub-map [ wkn-vsub ]tv truesub-id) , (▹ top)

truesub-ext : ∀ {θ Γ1 Γ2 T} -> truesub θ Γ1 Γ2 -> truesub θ (Γ1 , T) (Γ2 , T)
truesub-ext σ = (sub-map [ wkn-vsub ]tv σ) , (▹ top)

[_]t : ∀ {θ Γ1 Γ2 A J} -> truesub θ Γ2 Γ1 -> θ , Γ1 ⊢ A - J -> θ , Γ2 ⊢ A - J
[_]t σ (▹ x) = [ σ ]v x
[_]t σ (ƛ M) = ƛ ([ truesub-ext σ ]t M)
[_]t σ (M · N) = [ σ ]t M · [ σ ]t N
[_]t σ (let-◦ M N) = let-◦ ([ σ ]t M) ([ sub-map [ wkn-vsub ]vav σ ]t N)
[_]t σ (◦ M) = ◦ M
[_]t σ (inj M) = inj ([ σ ]t M)
[_]t σ (rec F M N) = rec F ([ σ ]t M) N
[_]t σ (out M) = out ([ σ ]t M)
[_]t σ (unfold F M N) = unfold F ([ σ ]t M) N
[_]t σ < M , N > = < [ σ ]t M , [ σ ]t N >
[_]t σ (fst M) = fst ([ σ ]t M)
[_]t σ (snd M) = snd ([ σ ]t M)
[_]t σ (inl M) = inl ([ σ ]t M)
[_]t σ (inr M) = inr ([ σ ]t M)
[_]t σ (case M N1 N2) = case ([ σ ]t M) ([ truesub-ext σ ]t N1) ([ truesub-ext σ ]t N2)
[_]t σ unit = unit

validsub : ∀ (θ1 θ2 : ctx prop) -> Set
validsub θ1 θ2 = truesub ⊡ θ1 θ2

validsub-ext : ∀ {θ1 θ2 T} -> validsub θ1 θ2 -> validsub (θ1 , T) (θ2 , T)
validsub-ext σ = truesub-ext σ

validsub-id : ∀ {θ} -> validsub θ θ
validsub-id = truesub-id

[_]va_ : ∀ {θ1 θ2 Γ C J} (θ : validsub θ2 θ1) (M : θ1 , Γ ⊢ C - J) ->  θ2 , Γ ⊢ C - J
[ θ ]va ▹ x = ▹ x
[ θ ]va ƛ M = ƛ ([ θ ]va M)
[ θ ]va (M · N) = ([ θ ]va M) · ([ θ ]va N)
[ θ ]va let-◦ M N = let-◦ ([ θ ]va M) ([ validsub-ext θ ]va N)
[ θ ]va ◦ M = ◦ ([ θ ]t M)
[ θ ]va inj M = inj ([ θ ]va M)
[ θ ]va rec F M N = rec F ([ θ ]va M) N
[ σ ]va out M = out ([ σ ]va M)
[ σ ]va unfold F M N = unfold F ([ σ ]va M) N
[ σ ]va < M , N > = < [ σ ]va M , [ σ ]va N >
[ σ ]va (fst M) = fst ([ σ ]va M)
[ σ ]va (snd M) = snd ([ σ ]va M)
[ σ ]va (inl M) = inl ([ σ ]va M)
[ σ ]va (inr M) = inr ([ σ ]va M)
[ σ ]va (case M N1 N2) = case ([ σ ]va M) ([ σ ]va N1) ([ σ ]va N2)
[ σ ]va unit = unit

-- generalize?
data arrow : ∀ {ζ} -> psub ⊡ ζ -> psub ⊡ ζ -> Set where
 ⊡ : arrow tt tt
 _,_ : ∀ {ζ} {σ1 σ2 : psub ⊡ ζ} (θ : arrow σ1 σ2) {A B} (N : ⊡ , (⊡ , A) ⊢ B - true) -> arrow {ζ , #prop} (σ1 , A) (σ2 , B)

arrow-lookup : ∀ {ζ} {σ1 σ2 : psub ⊡ ζ} (θ : arrow σ1 σ2) (A : var ζ #prop) -> ⊡ , ⊡ , ([ σ1 ]v A) ⊢ [ σ2 ]v A - true
arrow-lookup ⊡ ()
arrow-lookup (θ , N) top = N
arrow-lookup (θ , N) (pop y) = arrow-lookup θ y

{-
map : ∀ {ζ} F {σ1 σ2 : psub ⊡ ζ} (θ : arrow σ1 σ2) -> ⊡ , (⊡ , [ σ1 ]p F) ⊢ [ σ2 ]p F - true
map (▹ A) θ = arrow-lookup θ A
map (μ F) {σ1} {σ2} θ = rec ([ psub-ext σ1 ]p F) (▹ top) (inj {F = [ psub-ext σ2 ]p F } (subst2/3 (_,_⊢_-_ ⊡)
  (cong (_,_ ⊡) (trans (sub-funct _ _ F) (cong1st [_]p (cong1st _,_ (trans (assocv _ _ σ1) (sub-map-id σ1)) _) F)))
                (trans (sub-funct _ _ F) (cong1st [_]p (cong1st _,_ (trans (assocv _ _ σ2) (sub-map-id σ2)) _) F))
  true (map F (θ , ▹ top))))
map (ν F) {σ1} {σ2} θ = unfold ([ psub-ext σ2 ]p F) (out (▹ top)) (subst2/3 (_,_⊢_-_ ⊡)
   (cong (_,_ ⊡) (trans (sub-funct _ _ F) (cong1st [_]p (cong1st _,_ (trans (assocv _ _ σ1) (sub-map-id σ1)) _) F)))
                 (trans (sub-funct _ _ F) (cong1st [_]p (cong1st _,_ (trans (assocv _ _ σ2) (sub-map-id σ2)) _) F))
   true (map F (θ , out (▹ top))))
map (○ A) θ = let-◦ (▹ top) (◦ (map A θ))
map (A ⊃ B) θ = ƛ ([ _ , (▹ (pop top) · ▹ top) ]t (map B θ))
map (A ∧ B) θ = < [ _ , (fst (▹ top)) ]t (map A θ) , [ _ , (snd (▹ top)) ]t (map B θ) >
map (A ∨ B) θ = case (▹ top) (inl ([ _ , (▹ top) ]t (map A θ))) (inr ([ _ , (▹ top) ]t (map B θ)))
map ⊤ θ = ▹ top

map1 : ∀ F {A B} -> ⊡ , ⊡ , A ⊢ B - true -> ⊡ , (⊡ , [ A /x]p F) ⊢ [ B /x]p F - true
map1 F H = map F (⊡ , H)

map2 : ∀ {ζ θ Γ} F {σ1 σ2 : psub ⊡ ζ} (ρ : arrow σ1 σ2) -> θ , Γ ⊢ [ σ1 ]p F - true -> θ , Γ ⊢ [ σ2 ]p F - true
map2 F ρ t = [ _ , t ]t ([ _ ]va map F ρ)

map3 : ∀ {θ Γ A B} F -> (ρ : ⊡ , ⊡ , A ⊢ B - true) -> θ , Γ ⊢ [ A /x]p F - true -> θ , Γ ⊢ [ B /x]p F - true
map3 F ρ t = map2 F (⊡ , ρ) t -}

lem : ∀ {ζ1 ζ2 ζ3} F (σ1 : psub ζ2 ζ1) (σ2 : psub ζ3 ζ2) A -> ([ σ2 , A ]p ([ psub-ext σ1 ]p F)) ≡ ([ (σ2 • σ1) , A ]p F)
lem F σ1 σ2 A = begin
  [ σ2 , A ]p ([ psub-ext σ1 ]p F)             ≡⟨ sub-funct (σ2 , A) (psub-ext σ1) F ⟩
  [ ((σ2 , A) • (wkn-vsub ◆ σ1)) , A ]p F      ≡⟨ cong (λ α → [ α , A ]p F) (assocv (σ2 , A) (wkn-vsub) σ1) ⟩
  [ (((σ2 , A) ⁌ wkn-vsub) • σ1) , A ]p F      ≡⟨ cong (λ α → [ α , A ]p F) (sub-map-resp-≈ (λ x → cong (λ α → [ α ]p x) (comma-wkn σ2 A)) σ1) ⟩
  [ (σ2 • σ1) , A ]p F
  ∎

lem2 : ∀ {ζ1} F (σ1 : psub ⊡ ζ1) A -> ([ _ , A ]p ([ psub-ext σ1 ]p F)) ≡ ([ σ1 , A ]p F)
lem2 F σ1 A = begin
  [ tt , A ]p ([ psub-ext σ1 ]p F)           ≡⟨ lem F σ1 tt A ⟩
  [ (tt • σ1) , A ]p F                       ≡⟨ cong (λ α → [ α , A ]p F) (sub-map-id σ1) ⟩
  [ σ1 , A ]p F
  ∎


map2' : ∀ {ζ θ Γ} F {σ1 σ2 : psub ⊡ ζ} (ρ : arrow σ1 σ2) -> θ , Γ ⊢ [ σ1 ]p F - true -> θ , Γ ⊢ [ σ2 ]p F - true
map2' (▹ A) ρ t = [ tt , t ]t ([ tt ]va (arrow-lookup ρ A))
map2' (μ F) {σ1} {σ2} ρ t = rec ([ psub-ext σ1 ]p F) t (inj (subst2/3 (_,_⊢_-_ ⊡)
  (cong (_,_ ⊡) (lem2 F σ1 (μ ([ psub-ext σ2 ]p F))))
                (lem2 F σ2 (μ ([ psub-ext σ2 ]p F))) true
  (map2' F (ρ , ▹ top) (▹ top))) )
map2' (ν F) {σ1} {σ2} ρ t = unfold ([ psub-ext σ2 ]p F) t
       (subst2/3 (_,_⊢_-_ ⊡) refl (lem2 F σ2 (ν ([ psub-ext σ1 ]p F))) true
    (map2' F (ρ , ▹ top)
       (subst2/3 (_,_⊢_-_ ⊡) refl (sym (lem2 F σ1 (ν ([ psub-ext σ1 ]p F)))) true
    (out (▹ top)))))
map2' (○ A) ρ t = let-◦ t (◦ (map2' A ρ (▹ top)))
map2' (A ⊃ B) ρ t = ƛ (map2' B ρ (([ wkn-vsub ]tv t) · ▹ top))
map2' (A ∧ B) ρ t = < (map2' A ρ (fst t)) , map2' B ρ (snd t) >
map2' (A ∨ B) ρ t = case t (inl (map2' A ρ (▹ top))) (inr (map2' B ρ (▹ top)))
map2' ⊤ ρ t = t

map3 : ∀ {θ Γ A B} F -> (ρ : ⊡ , ⊡ , A ⊢ B - true) -> θ , Γ ⊢ [ A /x]p F - true -> θ , Γ ⊢ [ B /x]p F - true
map3 F ρ t = map2' F (⊡ , ρ) t

{-data step {θ Γ} : ∀ {A J} -> θ , Γ ⊢ A - J -> θ , Γ ⊢ A - J -> Set where
 box-red : ∀ {A C} (M : ⊡ , θ ⊢ A - true) (N : (θ , A) , Γ ⊢ C - true)
                -> step (let-◦ (◦ M) N) ([ validsub-id , M ]va N)
 rec-red : ∀ {F C} (M : θ , Γ ⊢ ([ μ F /x]p F) - true) (N : ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                -> step (rec F (inj M) N) ([ tt , (map3 F (rec F (▹ top) N) M) ]t ([ tt ]va N))
 out-red : ∀ {F C} (M : θ , Γ ⊢ C - true) (N : ⊡ , ⊡ , C ⊢ [ C /x]p F - true)
                -> step (out (unfold F M N)) (map3 F (unfold F (▹ top) N) ([ tt , M ]t ([ tt ]va N)))
 app-red : ∀ {A B} (M : θ , (Γ , A) ⊢ B - true) (N : θ , Γ ⊢ A - true)
                -> step ((ƛ M) · N) ([ truesub-id , N ]t M)
 fst-red : ∀ {A B} (M : θ , Γ ⊢ A - true) (N : θ , Γ ⊢ B - true)
                -> step (fst < M , N >) M
 snd-red : ∀ {A B} (M : θ , Γ ⊢ A - true) (N : θ , Γ ⊢ B - true)
                -> step (snd < M , N >) N
-}

stream : functor (⊡ , #prop)
stream = ν ((▹ (pop top)) ∧ (○ (▹ top)))

□ : prop -> prop
□ A = [ A /x]p stream

□map : ∀ {A B θ Γ} -> ⊡ , ⊡ , A ⊢ B - true -> θ , Γ ⊢ □ A - true -> θ , Γ ⊢ □ B - true
□map f x = map3 stream f x

Nat : ∀ {ζ} -> functor ζ
Nat = μ (⊤ ∨ ▹ top)

fcons : ∀ {θ Γ} -> θ , Γ ⊢ (Nat ⊃ (□ (○ Nat) ⊃ □ Nat)) - true
fcons = ƛ (ƛ (unfold (Nat ∧ ○ (▹ top)) < (▹ (pop top)) , (▹ top) >
                < (fst (▹ top)) ,
                  (let-◦ (fst (out (snd (▹ top))))
                  (let-◦ (snd (out (snd (▹ top))))
                         (◦ < ▹ (pop top) , ▹ top >))) >))

sflip : ∀ {θ Γ} -> θ , Γ ⊢ (□ (○ Nat) ⊃ ○ (□ Nat)) - true
sflip = ƛ (let-◦ (fst (out (▹ top)))
          (let-◦ (snd (out (▹ top)))
          (◦ ((fcons · (▹ (pop top))) · (▹ top)))))

nimport : ∀ {θ Γ} -> θ , Γ ⊢ (Nat ⊃ ○ Nat) - true
nimport = ƛ (rec (⊤ ∨ ▹ top) (▹ top)
               (case (▹ top)
                (◦ (inj (inl unit)))
                (let-◦ (▹ top) (◦ (inj (inr (▹ top)))))))

simport : ∀ {θ Γ} -> θ , Γ ⊢ (□ Nat ⊃ ○ (□ Nat)) - true
simport = ƛ (sflip · (□map (nimport · (▹ top)) (▹ top)))

