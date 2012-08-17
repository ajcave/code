module mu-ltl where

const1 : ∀ {A : Set} {B : Set₁} -> B -> A -> B
const1 b _ = b

_∘_ : ∀ {A B C : Set} (g : B -> C) (f : A -> B) -> A -> C
(g ∘ f) x = g (f x)

swap : ∀ {A B C : Set} (f : A -> B -> C) -> B -> A -> C
swap f b a = f a b 

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

subst2/3 : ∀ {A B C : Set} (P : A → B -> C → Set)
         {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → (z : C) -> P x₂ y₂ z → P x₁ y₁ z
subst2/3 P refl refl z p = p

cong : ∀ {A B : Set} (f : A -> B) {x y} -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong1st : ∀ {A B C : Set} (f : A -> B -> C) {a1 a2} -> a1 ≡ a2 -> (b : B) -> f a1 b ≡ f a2 b 
cong1st f refl b = refl

cong2 : ∀ {A B C : Set} (f : A -> B -> C) {a1 a2} -> a1 ≡ a2 -> {b1 b2 : B} -> b1 ≡ b2 -> f a1 b1 ≡ f a2 b2
cong2 f refl refl = refl 

trans : ∀ {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

sym : ∀ {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

_≈_ : ∀ {A B : Set} (f g : A -> B) -> Set
f ≈ g = ∀ x -> f x ≡ g x 

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ S T} -> var Γ T -> var (Γ , S) T

data sub {A} (exp : A -> Set) : ctx A -> Set where
 ⊡ : sub exp ⊡
 _,_ : ∀ {Δ T} (σ : sub exp Δ) (M : exp T) -> sub exp (Δ , T) 

[_]v : ∀ {A} {exp : A -> Set} {Δ T} (σ : sub exp Δ) -> var Δ T -> exp T
[ ⊡ ]v ()
[ σ , M ]v top = M
[ σ , M ]v (pop y) = [ σ ]v y

sub-map : ∀ {A} {exp1 exp2 : A -> Set} (f : ∀ {T} -> exp1 T -> exp2 T) {Δ} -> sub exp1 Δ -> sub exp2 Δ
sub-map f ⊡ = ⊡
sub-map f (σ , M) = (sub-map f σ) , (f M)

vsub : ∀ {A} (Γ1 Γ2 : ctx A) -> Set
vsub Γ1 Γ2 = sub (var Γ1) Γ2

wkn : ∀ {A} {Γ1 Γ2} {T : A} -> vsub Γ1 Γ2 -> vsub (Γ1 , T) Γ2
wkn σ = sub-map pop σ

id-vsub : ∀ {A} {Γ : ctx A} -> vsub Γ Γ
id-vsub {A} {⊡} = ⊡
id-vsub {A} {Γ , T} = (wkn id-vsub) , top

wkn-vsub : ∀ {A} {Γ : ctx A} {T} -> vsub (Γ , T) Γ
wkn-vsub {A} {Γ} {T} = wkn id-vsub

vsub-ext : ∀ {A T} {Γ1 Γ2 : ctx A} -> vsub Γ1 Γ2 -> vsub (Γ1 , T) (Γ2 , T)
vsub-ext σ = (sub-map pop σ) , top

record type : Set where
 constructor #prop

postulate
 atomic-prop : Set

mutual
 data functor (ζ : ctx type) : Set where
  ▸ : (P : atomic-prop) -> functor ζ
  ▹ : (A : var ζ #prop) -> functor ζ
  μ ν : (F : functor (ζ , #prop)) -> functor ζ
  ○ : (A : functor ζ) -> functor ζ
  _⊃_ : (A : prop) (B : functor ζ) -> functor ζ
  _∧_ : (A B : functor ζ) -> functor ζ

 prop : Set
 prop = functor ⊡

psub : ∀ (ζ1 ζ2 : ctx type) -> Set
psub ζ1 ζ2 = sub (const1 (functor ζ1)) ζ2

[_]pv : ∀ {ζ1 ζ2} -> vsub ζ2 ζ1 -> functor ζ1 -> functor ζ2
[ σ ]pv (▸ P) = ▸ P
[ σ ]pv (▹ A) = ▹ ([ σ ]v A)
[ σ ]pv (μ F) = μ ([ vsub-ext σ ]pv F)
[ σ ]pv (ν F) = ν ([ vsub-ext σ ]pv F)
[ σ ]pv (○ A) = ○ ([ σ ]pv A)
[ σ ]pv (A ⊃ B) = A ⊃ ([ σ ]pv B)
[ σ ]pv (A ∧ B) = ([ σ ]pv A) ∧ ([ σ ]pv B)

id-psub : ∀ {ζ} -> psub ζ ζ
id-psub {⊡} = ⊡
id-psub {ζ , #prop} = (sub-map [ wkn-vsub ]pv id-psub) , (▹ top)

psub-wkn : ∀ {ζ1 ζ2} (σ : psub ζ1 ζ2) -> psub (ζ1 , #prop) ζ2
psub-wkn σ = sub-map [ wkn-vsub ]pv σ

psub-ext : ∀ {ζ1 ζ2} -> psub ζ1 ζ2 -> psub (ζ1 , #prop) (ζ2 , #prop)
psub-ext σ = (psub-wkn σ) , ▹ top

[_]p : ∀ {ζ1 ζ2} -> psub ζ2 ζ1 -> functor ζ1 -> functor ζ2
[ σ ]p (▸ P) = ▸ P
[ σ ]p (▹ A) = [ σ ]v A
[ σ ]p (μ F) = μ ([ psub-ext σ ]p F)
[ σ ]p (ν F) = ν ([ psub-ext σ ]p F)
[ σ ]p (○ A) = ○ ([ σ ]p A)
[ σ ]p (A ⊃ B) = A ⊃ ([ σ ]p B)
[ σ ]p (A ∧ B) = ([ σ ]p A) ∧ ([ σ ]p B)

_•_ : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> psub ζ1 ζ3
σ1 • σ2 = sub-map [ σ1 ]p σ2

_◦_ : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : vsub ζ2 ζ3) -> psub ζ1 ζ3
σ1 ◦ σ2 = sub-map [ σ1 ]v σ2

_◆_ :  ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> psub ζ1 ζ3
σ1 ◆ σ2 = sub-map [ σ1 ]pv σ2


sub-vsub-funct : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]p ∘ [ σ2 ]v) ≈ [ σ1 • σ2 ]v
sub-vsub-funct σ1 ⊡ ()
sub-vsub-funct σ1 (σ , M) top = refl
sub-vsub-funct σ1 (σ , M) (pop y) = sub-vsub-funct σ1 σ y

sub-pvsub-funct :  ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : vsub ζ2 ζ3) -> ([ σ1 ]p ∘ [ σ2 ]pv) ≈ [ σ1 ◦ σ2 ]p
sub-pvsub-funct σ1 σ2 P = {!!}


pvsub-vsub-funct :  ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]pv ∘ [ σ2 ]v) ≈ [ σ1 ◆ σ2 ]v
pvsub-vsub-funct σ1 ⊡ ()
pvsub-vsub-funct σ1 (σ , M) top = refl
pvsub-vsub-funct σ1 (σ , M) (pop y) = pvsub-vsub-funct σ1 σ y

pvsub-sub-funct :  ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]pv ∘ [ σ2 ]p) ≈ [ σ1 ◆ σ2 ]p
pvsub-sub-funct σ1 σ2 P = {!!}

sub-map-funct : ∀ {A : Set} {exp1 exp2 exp3 : A -> Set} (g : ∀ {T} -> exp2 T -> exp3 T) (f : ∀ {T} -> exp1 T -> exp2 T)
 -> ∀ {Δ} (σ : sub exp1 Δ) -> (((sub-map g) ∘ (sub-map f)) σ) ≡ (sub-map (g ∘ f) σ)
sub-map-funct g f ⊡ = refl
sub-map-funct g f (σ , M) = cong1st _,_ (sub-map-funct g f σ) (g (f M)) 

sub-map-resp-≈ :  ∀ {A : Set} {exp1 exp2 : A -> Set} {f g : ∀ {T} -> exp1 T -> exp2 T} {Δ}
 -> (∀ {T} -> f {T} ≈ g {T}) -> (σ : sub exp1 Δ) -> sub-map f σ ≡ sub-map g σ
sub-map-resp-≈ H ⊡ = refl
sub-map-resp-≈ H (σ , M) = cong2 _,_ (sub-map-resp-≈ H σ) (H M) 

id-v-right : ∀ {ζ2 ζ1} (σ : psub ζ1 ζ2) -> (σ ◦ id-vsub) ≡ σ
id-v-right ⊡ = refl
id-v-right (σ , M) = cong1st _,_ (trans (sub-map-funct _ _ _) (id-v-right σ)) M

assocv : ∀ {ζ1 ζ2 ζ3 ζ4} (σ1 : psub ζ1 ζ2) (σ2 : vsub ζ2 ζ3) (σ3 : psub ζ3 ζ4) -> (σ1 • (σ2 ◆ σ3)) ≡ ((σ1 ◦ σ2) • σ3)
assocv σ1 σ2 σ3 = trans (sub-map-funct _ _ _) (sub-map-resp-≈ (sub-pvsub-funct σ1 σ2) σ3) 

ext-wkn : ∀ {ζ1 ζ2} (σ1 : psub ζ1 ζ2) -> ((psub-ext σ1) ◦ wkn-vsub) ≡ (wkn-vsub ◆ σ1)
ext-wkn σ1 = trans (sub-map-funct _ _ _) (id-v-right _)

ext-funct : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ((psub-ext σ1) • (psub-ext σ2)) ≡ psub-ext (σ1 • σ2)
ext-funct σ1 σ2 = cong1st _,_ (trans (assocv _ _ _) (trans (sub-map-resp-≈ (λ x → trans (cong1st [_]p (ext-wkn σ1) x) (sym (pvsub-sub-funct _ _ x))) σ2) (sym (sub-map-funct _ _ σ2)))) (▹ top)

-- TODO: Take advantage of generic traversal to get functorality
sub-funct : ∀ {ζ1 ζ2 ζ3} (σ1 : psub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]p ∘ [ σ2 ]p) ≈ [ σ1 • σ2 ]p
sub-funct σ1 σ2 (▸ P) = refl
sub-funct σ1 σ2 (▹ A) = sub-vsub-funct σ1 σ2 A
sub-funct σ1 σ2 (μ F) = cong μ (trans (sub-funct (psub-ext σ1) (psub-ext σ2) F) (cong1st [_]p (ext-funct σ1 σ2) F))
sub-funct σ1 σ2 (ν F) = cong ν (trans (sub-funct (psub-ext σ1) (psub-ext σ2) F) (cong1st [_]p (ext-funct σ1 σ2) F))
sub-funct σ1 σ2 (○ A) = cong ○ (sub-funct σ1 σ2 A)
sub-funct σ1 σ2 (A ⊃ B) = cong (_⊃_ A) (sub-funct σ1 σ2 B)
sub-funct σ1 σ2 (A ∧ B) = cong2 _∧_ (sub-funct σ1 σ2 A) (sub-funct σ1 σ2 B)


vsub-v-id : ∀ {ζ} (A : var ζ #prop) -> [ id-vsub ]v A ≡ A
vsub-v-id top = refl
vsub-v-id (pop y) = {!!}

sub-v-id : ∀ {ζ1} (A : var ζ1 #prop) -> [ id-psub ]v A ≡ ▹ A
sub-v-id top = refl
sub-v-id (pop y) = trans (sym (pvsub-vsub-funct wkn-vsub id-psub y)) (trans (cong [ wkn-vsub ]pv (sub-v-id y)) (cong ▹ {!!}))

sub-id : ∀ {ζ1} (M : functor ζ1) -> [ id-psub ]p M ≡ M
sub-id (▸ P) = refl
sub-id (▹ A) = sub-v-id A
sub-id (μ F) = cong μ (sub-id F)
sub-id (ν F) = cong ν (sub-id F)
sub-id (○ A) = cong ○ (sub-id A)
sub-id (A ⊃ B) = cong (_⊃_ A) (sub-id B)
sub-id (A ∧ B) = cong2 _∧_ (sub-id A) (sub-id B)

sub-map-id : ∀ {ζ1 ζ2} (σ : psub ζ1 ζ2) -> (id-psub • σ) ≡ σ
sub-map-id ⊡ = refl
sub-map-id (σ , M) = cong2 _,_ (sub-map-id σ) (sub-id M)

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

truesub : ∀ θ (Γ1 Γ2 : ctx (prop)) -> Set
truesub θ Γ1 Γ2 = sub (λ A -> θ , Γ1 ⊢ A - true) Γ2

truesub-id : ∀ {θ Γ} -> truesub θ Γ Γ
truesub-id {θ} {⊡} = ⊡
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

-- generalize?
data arrow : ∀ {ζ} -> psub ⊡ ζ -> psub ⊡ ζ -> Set where
 ⊡ : arrow ⊡ ⊡
 _,_ : ∀ {ζ} {σ1 σ2 : psub ⊡ ζ} (θ : arrow σ1 σ2) {A B} (N : ⊡ , (⊡ , A) ⊢ B - true) -> arrow (σ1 , A) (σ2 , B)

arrow-lookup : ∀ {ζ} {σ1 σ2 : psub ⊡ ζ} (θ : arrow σ1 σ2) (A : var ζ #prop) -> ⊡ , ⊡ , ([ σ1 ]v A) ⊢ [ σ2 ]v A - true
arrow-lookup ⊡ ()
arrow-lookup (θ , N) top = N
arrow-lookup (θ , N) (pop y) = arrow-lookup θ y

map : ∀ {ζ} F {σ1 σ2 : psub ⊡ ζ} (θ : arrow σ1 σ2) -> ⊡ , (⊡ , [ σ1 ]p F) ⊢ [ σ2 ]p F - true
map (▸ P) θ = ▹ top
map (▹ A) θ = arrow-lookup θ A
map (μ F) {σ1} {σ2} θ = rec ([ psub-ext σ1 ]p F) (▹ top) (inj {F = [ psub-ext σ2 ]p F } (subst2/3 (_,_⊢_-_ ⊡) (cong (_,_ ⊡)
  (trans (sub-funct _ _ F) (cong1st [_]p (cong1st _,_ (trans (assocv _ _ σ1) (sub-map-id σ1)) _) F)))
  (trans (sub-funct _ _ F) (cong1st [_]p (cong1st _,_ (trans (assocv _ _ σ2) (sub-map-id σ2)) _) F))
  true (map F (θ , ▹ top))))
map (ν F) {σ1} {σ2} θ = {!!} {-rec ([ psub-ext σ1 ]p F) (▹ top) (inj {F = [ psub-ext σ2 ]p F } (subst2/3 (_,_⊢_-_ ⊡) (cong (_,_ ⊡)
  (trans (sub-funct _ _ F) (cong1st [_]p (cong1st _,_ (trans (assocv _ _ σ1) (sub-map-id σ1)) _) F)))
  (trans (sub-funct _ _ F) (cong1st [_]p (cong1st _,_ (trans (assocv _ _ σ2) (sub-map-id σ2)) _) F))
  true (map F (θ , ▹ top)))) -}
map (○ A) θ = let-◦ (▹ top) (◦ (map A θ))
map (A ⊃ B) θ = ƛ ([ ⊡ , (▹ (pop top) · ▹ top) ]t (map B θ))
map (A ∧ B) θ = < [ ⊡ , (fst (▹ top)) ]t (map A θ) , [ ⊡ , (snd (▹ top)) ]t (map B θ) >

map1 : ∀ F {A B} -> ⊡ , ⊡ , A ⊢ B - true -> ⊡ , (⊡ , [ A /x]p F) ⊢ [ B /x]p F - true
map1 F H = map F (⊡ , H)

map2 : ∀ {ζ θ Γ} F {σ1 σ2 : psub ⊡ ζ} (ρ : arrow σ1 σ2) -> θ , Γ ⊢ [ σ1 ]p F - true -> θ , Γ ⊢ [ σ2 ]p F - true
map2 F ρ t = [ ⊡ , t ]t ([ ⊡ ]va map F ρ)

map3 : ∀ {θ Γ A B} F -> (ρ : ⊡ , ⊡ , A ⊢ B - true) -> θ , Γ ⊢ [ A /x]p F - true -> θ , Γ ⊢ [ B /x]p F - true
map3 F ρ t = map2 F (⊡ , ρ) t

-- Other way to write it maybe concludes θ;Γ ⊢ F(A) -> θ;Γ ⊢ F(B) ?

-- Double check that this is the same way Baelde treats fixed points
-- Is there a slightly nicer way?
data step {θ Γ} : ∀ {A J} -> θ , Γ ⊢ A - J -> θ , Γ ⊢ A - J -> Set where
 box-red : ∀ {A C} (M : ⊡ , θ ⊢ A - true) (N : (θ , A) , Γ ⊢ C - true)
                -> step (let-◦ (◦ M) N) ([ validsub-id , M ]va N)
 rec-red : ∀ {F C} (M : θ , Γ ⊢ ([ μ F /x]p F) - true) (N : ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                -> step (rec F (inj M) N) ([ ⊡ , (map3 F (rec F (▹ top) N) M) ]t ([ ⊡ ]va N))
 app-red : ∀ {A B} (M : θ , (Γ , A) ⊢ B - true) (N : θ , Γ ⊢ A - true)
                -> step ((ƛ M) · N) ([ truesub-id , N ]t M)
 fst-red : ∀ {A B} (M : θ , Γ ⊢ A - true) (N : θ , Γ ⊢ B - true)
                -> step (fst < M , N >) M
 snd-red : ∀ {A B} (M : θ , Γ ⊢ A - true) (N : θ , Γ ⊢ B - true)
                -> step (snd < M , N >) N 