module mu where

const1 : ∀ {A : Set} {B : Set₁} -> B -> A -> B
const1 b _ = b

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

data var {A : Set} : (Γ : ctx A) -> A -> Set where
 top : ∀ {Γ T} -> var (Γ , T) T
 pop : ∀ {Γ S T} -> var Γ T -> var (Γ , S) T

data sub {A} (exp : A -> Set) : ctx A -> Set where
 ⊡ : sub exp ⊡
 _,_ : ∀ {Δ T} (σ : sub exp Δ) (M : exp T) -> sub exp (Δ , T) 

[_]v_ : ∀ {A} {exp : A -> Set} {Δ T} (σ : sub exp Δ) -> var Δ T -> exp T
[ ⊡ ]v ()
[ σ , M ]v top = M
[ σ , M ]v (pop y) = [ σ ]v y

sub-map : ∀ {A} {exp1 exp2 : A -> Set} (f : ∀ {T} -> exp1 T -> exp2 T) {Δ} -> sub exp1 Δ -> sub exp2 Δ
sub-map f ⊡ = ⊡
sub-map f (σ , M) = (sub-map f σ) , (f M)

vsub : ∀ {A} (Γ1 Γ2 : ctx A) -> Set
vsub Γ1 Γ2 = sub (var Γ1) Γ2

id-vsub : ∀ {A} (Γ : ctx A) -> vsub Γ Γ
id-vsub ⊡ = ⊡
id-vsub (Γ , T) = (sub-map pop (id-vsub Γ)) , top

wkn-vsub : ∀ {A} {Γ : ctx A} {T} -> vsub (Γ , T) Γ
wkn-vsub {A} {Γ} {T} = sub-map pop (id-vsub Γ)

vsub-ext : ∀ {A T} {Γ1 Γ2 : ctx A} -> vsub Γ1 Γ2 -> vsub (Γ1 , T) (Γ2 , T)
vsub-ext σ = (sub-map pop σ) , top

record type : Set where
 constructor #prop

postulate
 atomic-prop : Set

data prop (ζ : ctx type) : Set where
 ▸ : (P : atomic-prop) -> prop ζ
 ▹ : (A : var ζ #prop) -> prop ζ
 μ : (F : prop (ζ , #prop)) -> prop ζ
 □ : (A : prop ζ) -> prop ζ
 ◇ : (A : prop ζ) -> prop ζ
 _⊃_ : (A B : prop ζ) -> prop ζ

psub : ∀ (ζ1 ζ2 : ctx type) -> Set
psub ζ1 ζ2 = sub (const1 (prop ζ1)) ζ2

[_]pv : ∀ {ζ1 ζ2} -> vsub ζ2 ζ1 -> prop ζ1 -> prop ζ2
[ σ ]pv (▸ P) = ▸ P
[ σ ]pv (▹ A) = ▹ ([ σ ]v A)
[ σ ]pv (μ F) = μ ([ vsub-ext σ ]pv F)
[ σ ]pv (□ A) = □ ([ σ ]pv A)
[ σ ]pv (◇ A) = ◇ ([ σ ]pv A)
[ σ ]pv (A ⊃ B) = ([ σ ]pv A) ⊃ ([ σ ]pv B)

id-psub : ∀ {ζ} -> psub ζ ζ
id-psub {⊡} = ⊡
id-psub {ζ , #prop} = (sub-map [ wkn-vsub ]pv id-psub) , (▹ top)

psub-ext : ∀ {ζ1 ζ2} -> psub ζ1 ζ2 -> psub (ζ1 , #prop) (ζ2 , #prop)
psub-ext σ = (sub-map [ wkn-vsub ]pv σ) , ▹ top

[_]p : ∀ {ζ1 ζ2} -> psub ζ2 ζ1 -> prop ζ1 -> prop ζ2
[ σ ]p (▸ P) = ▸ P
[ σ ]p (▹ A) = [ σ ]v A
[ σ ]p (μ F) = μ ([ psub-ext σ ]p F)
[ σ ]p (□ A) = □ ([ σ ]p A)
[ σ ]p (◇ A) = ◇ ([ σ ]p A)
[ σ ]p (A ⊃ B) = ([ σ ]p A) ⊃ ([ σ ]p B)

[_/x]p : ∀ {ζ} -> prop ζ -> prop (ζ , #prop) -> prop ζ
[ M /x]p A = [ id-psub , M ]p A

data judgement : Set where
 true : judgement
 poss : judgement

mutual
 data _,_⊢_-_ (Δ : ctx (prop ⊡)) (Γ : ctx (prop ⊡)) : prop ⊡ -> judgement -> Set where
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
  ▸ : ∀ {A} -> (M : ⊡ , Δ ⊢ A - true)
            -> --------------------------
                    Δ , Γ ⊢ A - poss
  dia : ∀ {A} -> (M : Δ , Γ ⊢ A - poss)
              -> --------------------------
                     Δ , Γ ⊢ ◇ A - true
  let-dia : ∀ {A C} -> (M : Δ , Γ ⊢ ◇ A - true) -> (N : ⊡ , (Δ , A) ⊢ C - true)
                    -> ----------------------------------------------------------------
                                      Δ , Γ ⊢ C - poss
  fold : ∀ {F} -> (M : Δ , Γ ⊢ ([ μ F /x]p F) - true)
               -> -----------------------------------------------------
                                Δ , Γ ⊢ μ F - true
  rec : ∀ {F C} -> (M : Δ , Γ ⊢ μ F - true) -> (N : ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                -> -------------------------------------------------------------------
                                Δ , Γ ⊢ C - true -- What about poss?

[_]tv : ∀ {Δ Γ1 Γ2 A J} -> vsub Γ2 Γ1 -> Δ , Γ1 ⊢ A - J -> Δ , Γ2 ⊢ A - J
[_]tv σ (▹ x) = ▹ ([ σ ]v x)
[_]tv σ (ƛ M) = ƛ ([ vsub-ext σ ]tv M)
[_]tv σ (M · N) = [ σ ]tv M · [ σ ]tv N
[_]tv σ (let-box M N) = let-box ([ σ ]tv M) ([ σ ]tv N)
[_]tv σ (box M) = box M
[_]tv σ (▸ M) = ▸ M
[_]tv σ (dia M) = dia ([ σ ]tv M)
[_]tv σ (let-dia M N) = let-dia ([ σ ]tv M) N
[_]tv σ (fold M) = fold ([ σ ]tv M)
[_]tv σ (rec M N) = rec ([ σ ]tv M) N

[_]vav : ∀ {Δ1 Δ2 Γ A J} -> vsub Δ2 Δ1 -> Δ1 , Γ ⊢ A - J -> Δ2 , Γ ⊢ A - J
[_]vav σ (▹ x) = ▹ x
[_]vav σ (ƛ M) = ƛ ([ σ ]vav M)
[_]vav σ (M · N) = [ σ ]vav M · [ σ ]vav N
[_]vav σ (let-box M N) = let-box ([ σ ]vav M) ([ vsub-ext σ ]vav N)
[_]vav σ (box M) = box ([ σ ]tv M)
[_]vav σ (▸ M) = ▸ ([ σ ]tv M)
[_]vav σ (dia M) = dia ([ σ ]vav M)
[_]vav σ (let-dia M N) = let-dia ([ σ ]vav M) ([ vsub-ext σ ]tv N)
[_]vav σ (fold M) = fold ([ σ ]vav M)
[_]vav σ (rec M N) = rec ([ σ ]vav M) N

truesub : ∀ Δ (Γ1 Γ2 : ctx (prop ⊡)) -> Set
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
[_]t σ (▸ M) = ▸ M
[_]t σ (dia M) = dia ([ σ ]t M)
[_]t σ (let-dia M N) = let-dia ([ σ ]t M) N
[_]t σ (fold M) = fold ([ σ ]t M)
[_]t σ (rec M N) = rec ([ σ ]t M) N

validsub : ∀ (Δ1 Δ2 : ctx (prop ⊡)) -> Set
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
[ θ ]va ▸ M = ▸ ([ θ ]t M)
[ θ ]va dia M = dia ([ θ ]va M)
[ θ ]va let-dia M N = let-dia ([ θ ]va M) ([ truesub-ext θ ]t N)
[ θ ]va fold M = fold ([ θ ]va M)
[ θ ]va rec M N = rec ([ θ ]va M) N

〈_/x〉 : ∀ {Δ Γ A C} (M : Δ , Γ ⊢ A - poss) (N : ⊡ , (Δ , A) ⊢ C - true) -> Δ , Γ ⊢ C - poss
〈_/x〉 (let-box M N) N' = let-box M (〈 N /x〉 ([ (sub-map pop wkn-vsub) , top ]tv N'))
〈_/x〉 (▸ M) N = ▸ ([ truesub-id , M ]t N)
〈_/x〉 (let-dia M N) N' = let-dia M ([ (sub-map [ wkn-vsub ]tv truesub-id) , N ]t N')  

data step {Δ Γ} : ∀ {A J} -> Δ , Γ ⊢ A - J -> Δ , Γ ⊢ A - J -> Set where
 box-red : ∀ {A C} (M : ⊡ , Δ ⊢ A - true) (N : (Δ , A) , Γ ⊢ C - true)
                -> step (let-box (box M) N) ([ validsub-id , M ]va N)
 dia-red : ∀ {A C} (M : Δ , Γ ⊢ A - poss) (N : ⊡ , (Δ , A) ⊢ C - true)
                -> step (let-dia (dia M) N) {!!}