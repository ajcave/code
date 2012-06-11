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
  μ : (F : functor (ζ , #prop)) -> functor ζ
  □ : (A : functor ζ) -> functor ζ
  ◇ : (A : functor ζ) -> functor ζ
  _⊃_ : (A : prop) (B : functor ζ) -> functor ζ

 prop : Set
 prop = functor ⊡

psub : ∀ (ζ1 ζ2 : ctx type) -> Set
psub ζ1 ζ2 = sub (const1 (functor ζ1)) ζ2

[_]pv : ∀ {ζ1 ζ2} -> vsub ζ2 ζ1 -> functor ζ1 -> functor ζ2
[ σ ]pv (▸ P) = ▸ P
[ σ ]pv (▹ A) = ▹ ([ σ ]v A)
[ σ ]pv (μ F) = μ ([ vsub-ext σ ]pv F)
[ σ ]pv (□ A) = □ ([ σ ]pv A)
[ σ ]pv (◇ A) = ◇ ([ σ ]pv A)
[ σ ]pv (A ⊃ B) = A ⊃ ([ σ ]pv B)

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
[ σ ]p (□ A) = □ ([ σ ]p A)
[ σ ]p (◇ A) = ◇ ([ σ ]p A)
[ σ ]p (A ⊃ B) = A ⊃ ([ σ ]p B)

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
sub-pvsub-funct σ1 σ2 (▸ P) = refl
sub-pvsub-funct σ1 σ2 (▹ A) = {!!}
sub-pvsub-funct σ1 σ2 (μ F) = {!!}
sub-pvsub-funct σ1 σ2 (□ A) = {!!}
sub-pvsub-funct σ1 σ2 (◇ A) = {!!}
sub-pvsub-funct σ1 σ2 (A ⊃ B) = {!!}

pvsub-vsub-funct :  ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]pv ∘ [ σ2 ]v) ≈ [ σ1 ◆ σ2 ]v
pvsub-vsub-funct σ1 ⊡ ()
pvsub-vsub-funct σ1 (σ , M) top = refl
pvsub-vsub-funct σ1 (σ , M) (pop y) = pvsub-vsub-funct σ1 σ y

pvsub-sub-funct :  ∀ {ζ1 ζ2 ζ3} (σ1 : vsub ζ1 ζ2) (σ2 : psub ζ2 ζ3) -> ([ σ1 ]pv ∘ [ σ2 ]p) ≈ [ σ1 ◆ σ2 ]p
pvsub-sub-funct σ1 σ2 (▸ P) = {!!}
pvsub-sub-funct σ1 σ2 (▹ A) = {!!}
pvsub-sub-funct σ1 σ2 (μ F) = {!!}
pvsub-sub-funct σ1 σ2 (□ A) = {!!}
pvsub-sub-funct σ1 σ2 (◇ A) = {!!}
pvsub-sub-funct σ1 σ2 (A ⊃ B) = {!!}

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
sub-funct σ1 σ2 (□ A) = cong □ (sub-funct σ1 σ2 A)
sub-funct σ1 σ2 (◇ A) = cong ◇ (sub-funct σ1 σ2 A)
sub-funct σ1 σ2 (A ⊃ B) = cong (_⊃_ A) (sub-funct σ1 σ2 B)


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
sub-id (□ A) = cong □ (sub-id A)
sub-id (◇ A) = cong ◇ (sub-id A)
sub-id (A ⊃ B) = cong (_⊃_ A) (sub-id B)

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
 data _,_⊢_-_ (Δ : ctx prop) (Γ : ctx prop) : prop -> judgement -> Set where
  ▹ : ∀ {A} -> (x : var Γ A)
            -> -------------------
                Δ , Γ ⊢ A - true
  ƛ : ∀ {A B} -> (M : Δ , (Γ , A) ⊢ B - true)
              -> ----------------------------------
                      Δ , Γ ⊢ (A ⊃ B) - true
  _·_ : ∀ {A B} -> (M : Δ , Γ ⊢ (A ⊃ B) - true) (N : Δ , Γ ⊢ A - true)
                -> -----------------------------------------------------------
                                Δ , Γ ⊢ B - true
  let-box : ∀ {A C J} (M : Δ , Γ ⊢ (□ A) - true) (N : (Δ , A) , Γ ⊢ C - J)
                   -> ---------------------------------------------------------------
                                          Δ , Γ ⊢ C - J
  box : ∀ {A} -> (M : ⊡ , Δ ⊢ A - true)
              -> --------------------------
                   Δ , Γ ⊢ (□ A) - true
-- Read this as saying that when proving a possibility we're allowed to take one possibility along with us, and all necessities.
  let-dia : ∀ {A C} -> (M : Δ , Γ ⊢ ◇ A - true) -> (N : ⊡ , (Δ , A) ⊢ C - true)
                    -> --------------------------------------------------------
                                      Δ , Γ ⊢ ◇ C - true
  inj : ∀ {F} -> (M : Δ , Γ ⊢ ([ μ F /x]p F) - true)
              -> -----------------------------------------------------
                              Δ , Γ ⊢ μ F - true
  rec : ∀ F {C} -> (M : Δ , Γ ⊢ μ F - true) -> (N : ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                -> -------------------------------------------------------------------
                                Δ , Γ ⊢ C - true

[_]tv : ∀ {Δ Γ1 Γ2 A J} -> vsub Γ2 Γ1 -> Δ , Γ1 ⊢ A - J -> Δ , Γ2 ⊢ A - J
[_]tv σ (▹ x) = ▹ ([ σ ]v x)
[_]tv σ (ƛ M) = ƛ ([ vsub-ext σ ]tv M)
[_]tv σ (M · N) = [ σ ]tv M · [ σ ]tv N
[_]tv σ (let-box M N) = let-box ([ σ ]tv M) ([ σ ]tv N)
[_]tv σ (box M) = box M
[_]tv σ (let-dia M N) = let-dia ([ σ ]tv M) N
[_]tv σ (inj M) = inj ([ σ ]tv M)
[_]tv σ (rec F M N) = rec F ([ σ ]tv M) N

[_]vav : ∀ {Δ1 Δ2 Γ A J} -> vsub Δ2 Δ1 -> Δ1 , Γ ⊢ A - J -> Δ2 , Γ ⊢ A - J
[_]vav σ (▹ x) = ▹ x
[_]vav σ (ƛ M) = ƛ ([ σ ]vav M)
[_]vav σ (M · N) = [ σ ]vav M · [ σ ]vav N
[_]vav σ (let-box M N) = let-box ([ σ ]vav M) ([ vsub-ext σ ]vav N)
[_]vav σ (box M) = box ([ σ ]tv M)
[_]vav σ (let-dia M N) = let-dia ([ σ ]vav M) ([ vsub-ext σ ]tv N)
[_]vav σ (inj M) = inj ([ σ ]vav M)
[_]vav σ (rec F M N) = rec F ([ σ ]vav M) N

truesub : ∀ Δ (Γ1 Γ2 : ctx (prop)) -> Set
truesub Δ Γ1 Γ2 = sub (λ A -> Δ , Γ1 ⊢ A - true) Γ2

truesub-id : ∀ {Δ Γ} -> truesub Δ Γ Γ
truesub-id {Δ} {⊡} = ⊡
truesub-id {Δ} {Γ , T} = (sub-map [ wkn-vsub ]tv truesub-id) , (▹ top)

truesub-ext : ∀ {Δ Γ1 Γ2 T} -> truesub Δ Γ1 Γ2 -> truesub Δ (Γ1 , T) (Γ2 , T)
truesub-ext σ = (sub-map [ wkn-vsub ]tv σ) , (▹ top)

[_]t : ∀ {Δ Γ1 Γ2 A J} -> truesub Δ Γ2 Γ1 -> Δ , Γ1 ⊢ A - J -> Δ , Γ2 ⊢ A - J
[_]t σ (▹ x) = [ σ ]v x
[_]t σ (ƛ M) = ƛ ([ truesub-ext σ ]t M)
[_]t σ (M · N) = [ σ ]t M · [ σ ]t N
[_]t σ (let-box M N) = let-box ([ σ ]t M) ([ sub-map [ wkn-vsub ]vav σ ]t N)
[_]t σ (box M) = box M
[_]t σ (let-dia M N) = let-dia ([ σ ]t M) N
[_]t σ (inj M) = inj ([ σ ]t M)
[_]t σ (rec F M N) = rec F ([ σ ]t M) N

validsub : ∀ (Δ1 Δ2 : ctx prop) -> Set
validsub Δ1 Δ2 = truesub ⊡ Δ1 Δ2

validsub-ext : ∀ {Δ1 Δ2 T} -> validsub Δ1 Δ2 -> validsub (Δ1 , T) (Δ2 , T)
validsub-ext σ = truesub-ext σ

validsub-id : ∀ {Δ} -> validsub Δ Δ
validsub-id = truesub-id

[_]va_ : ∀ {Δ1 Δ2 Γ C J} (θ : validsub Δ2 Δ1) (M : Δ1 , Γ ⊢ C - J) ->  Δ2 , Γ ⊢ C - J
[ θ ]va ▹ x = ▹ x
[ θ ]va ƛ M = ƛ ([ θ ]va M)
[ θ ]va (M · N) = ([ θ ]va M) · ([ θ ]va N)
[ θ ]va let-box M N = let-box ([ θ ]va M) ([ validsub-ext θ ]va N)
[ θ ]va box M = box ([ θ ]t M)
[ θ ]va let-dia M N = let-dia ([ θ ]va M) ([ truesub-ext θ ]t N)
[ θ ]va inj M = inj ([ θ ]va M)
[ θ ]va rec F M N = rec F ([ θ ]va M) N

--〈_/x〉 : ∀ {Δ Γ A C} (M : Δ , Γ ⊢ A - poss) (N : ⊡ , (Δ , A) ⊢ C - true) -> Δ , Γ ⊢ C - poss
--〈_/x〉 (let-box M N) N' = let-box M (〈 N /x〉 ([ wkn wkn-vsub , top ]tv N'))
--〈_/x〉 (▸ M) N = ▸ ([ truesub-id , M ]t N)
--〈_/x〉 (let-dia M N) N' = let-dia M ([ (sub-map [ wkn-vsub ]tv truesub-id) , N ]t N')  

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
map (□ A) θ = let-box (▹ top) (box (map A θ))
map (◇ A) θ = let-dia (▹ top) (map A θ)
map (A ⊃ B) θ = ƛ ([ ⊡ , (▹ (pop top) · ▹ top) ]t (map B θ))

map1 : ∀ F {A B} -> ⊡ , ⊡ , A ⊢ B - true -> ⊡ , (⊡ , [ A /x]p F) ⊢ [ B /x]p F - true
map1 F H = map F (⊡ , H)

-- Other way to write it maybe concludes Δ;Γ ⊢ F(A) -> Δ;Γ ⊢ F(B) ?

data step {Δ Γ} : ∀ {A J} -> Δ , Γ ⊢ A - J -> Δ , Γ ⊢ A - J -> Set where
 box-red : ∀ {A C} (M : ⊡ , Δ ⊢ A - true) (N : (Δ , A) , Γ ⊢ C - true)
                -> step (let-box (box M) N) ([ validsub-id , M ]va N)
-- No local soundness/completeness for ◇? Because its introduction and elimination rules are the same thing!
-- dia-red : ∀ {A B C} (M : Δ , Γ ⊢ ◇ A - true) (N1 : ⊡ , (Δ , A) ⊢ B - true) (N2 : ⊡ , (Δ , B) ⊢ C - true)
--                -> step (let-dia (let-dia M N1) N2) (let-dia {!!} {!!})
 rec-red : ∀ {F C} (M : Δ , Γ ⊢ ([ μ F /x]p F) - true) (N : ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                -> step (rec F (inj M) N) ([ ⊡ , [ ⊡ , M ]t ([ ⊡ ]va map1 F (rec F (▹ top) N)) ]t ([ ⊡ ]va N))
 app-red : ∀ {A B}  (M : Δ , (Γ , A) ⊢ B - true) (N : Δ , Γ ⊢ A - true)
                -> step ((ƛ M) · N) ([ truesub-id , N ]t M)