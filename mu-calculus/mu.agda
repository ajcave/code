module mu where

const1 : ∀ {A : Set} {B : Set₁} -> B -> A -> B
const1 b _ = b

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : ctx A -> A -> ctx A

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

wkn-vsub : ∀ {A} (Γ : ctx A) T -> vsub (Γ , T) Γ
wkn-vsub Γ T = sub-map pop (id-vsub Γ)

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

app-pvsub : ∀ {ζ1 ζ2} -> vsub ζ2 ζ1 -> prop ζ1 -> prop ζ2
app-pvsub σ (▸ P) = ▸ P
app-pvsub σ (▹ A) = ▹ ([ σ ]v A)
app-pvsub σ (μ F) = μ (app-pvsub (vsub-ext σ) F)
app-pvsub σ (□ A) = □ (app-pvsub σ A)
app-pvsub σ (◇ A) = ◇ (app-pvsub σ A)
app-pvsub σ (A ⊃ B) = (app-pvsub σ A) ⊃ app-pvsub σ B

id-psub : ∀ {ζ} -> psub ζ ζ
id-psub {⊡} = ⊡
id-psub {ζ , #prop} = (sub-map (app-pvsub (wkn-vsub ζ #prop)) id-psub) , (▹ top)

psub-ext : ∀ {ζ1 ζ2} -> psub ζ1 ζ2 -> psub (ζ1 , #prop) (ζ2 , #prop)
psub-ext σ = (sub-map (app-pvsub (wkn-vsub _ _)) σ) , ▹ top

[_]p_ : ∀ {ζ1 ζ2} -> psub ζ2 ζ1 -> prop ζ1 -> prop ζ2
[ σ ]p (▸ P) = ▸ P
[ σ ]p (▹ A) = [ σ ]v A
[ σ ]p (μ F) = μ ([ psub-ext σ ]p F)
[ σ ]p (□ A) = □ ([ σ ]p A)
[ σ ]p (◇ A) = ◇ ([ σ ]p A)
[ σ ]p (A ⊃ B) = ([ σ ]p A) ⊃ ([ σ ]p B)

[_/x]p_ : ∀ {ζ} -> prop ζ -> prop (ζ , #prop) -> prop ζ
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
  

validsub : ∀ (Δ1 Δ2 : ctx (prop ⊡)) -> Set
validsub Δ1 Δ2 = sub (λ A -> ⊡ , Δ1 ⊢ A - true) Δ2

[_]va_ : ∀ {Δ1 Δ2 Γ C J} (θ : validsub Δ2 Δ1) (M : Δ1 , Γ ⊢ C - J)
 ->  Δ2 , Γ ⊢ C - J
[ θ ]va ▸ M = ▸ {!!}
[ θ ]va ▹ x = ▹ x
[ θ ]va ƛ M = ƛ ([ θ ]va M)
[ θ ]va (M · N) = ([ θ ]va M) · ([ θ ]va N)
[ θ ]va let-box M N = let-box ([ θ ]va M) ([ {!!} ]va N)
[ θ ]va box M = box {!!}
[ θ ]va dia M = dia ([ θ ]va M)
[ θ ]va let-dia M N = let-dia ([ θ ]va M) {!!}
[ θ ]va fold M = fold ([ θ ]va M)
[ θ ]va rec M N = rec ([ θ ]va M) N

--data step {Δ Γ} : ∀ {A} -> Δ , Γ ⊢ A - true -> Δ , Γ ⊢ A - true -> Set where
-- box-red : ∀ {A C} (D : ⊡ , Δ ⊢ A - true) (E : (Δ , A) , Γ ⊢ C - true)
--                -> step (let-box (box D) E) (sub-valid D E)