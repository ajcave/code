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
 data _,_,_⊢_-_ (ζ : ctx type) (Δ : ctx (prop ζ)) (Γ : ctx (prop ζ)) : prop ζ -> judgement -> Set where
  ▹ : {A : prop ζ} (x : var Γ A)
                -> -------------------
                    ζ , Δ , Γ ⊢ A - true
  ƛ : {A B : prop ζ} -> (M : ζ , Δ , (Γ , A) ⊢ B - true)
                     -> -----------------------------------
                             ζ , Δ , Γ ⊢ (A ⊃ B) - true
  _·_ : {A B : prop ζ}    (M : ζ , Δ , Γ ⊢ (A ⊃ B) - true) (N : ζ , Δ , Γ ⊢ A - true)
                       -> -----------------------------------------------------------
                                            ζ , Δ , Γ ⊢ B - true
  let-box : ∀ {A C J} (M : ζ , Δ , Γ ⊢ (□ A) - true) (N : ζ , (Δ , A) , Γ ⊢ C - J)
                   -> ---------------------------------------------------------------
                                          ζ , Δ , Γ ⊢ C - J
  box : ∀ {A} -> (M : ζ , ⊡ , Δ ⊢ A - true)
              -> --------------------------
                   ζ , Δ , Γ ⊢ (□ A) - true
  ▸ : ∀ {A} -> (M : ζ , ⊡ , Δ ⊢ A - true)
            -> --------------------------
                    ζ , Δ , Γ ⊢ A - poss
  dia : ∀ {A} -> (M : ζ , Δ , Γ ⊢ A - poss)
              -> --------------------------
                     ζ , Δ , Γ ⊢ ◇ A - true
  let-dia : ∀ {A C} -> (M : ζ , Δ , Γ ⊢ ◇ A - true) -> (N : ζ , ⊡ , (Δ , A) ⊢ C - poss)
                    -> ----------------------------------------------------------------
                                      ζ , Δ , Γ ⊢ C - poss
  fold : ∀ {F} -> (M : ζ , Δ , Γ ⊢ ([ μ F /x]p F) - true)
               -> -----------------------------------------------------
                                ζ , Δ , Γ ⊢ μ F - true
  rec : ∀ {F C} -> (M : ζ , Δ , Γ ⊢ μ F - true) -> (N : ζ , ⊡ , (⊡ , [ C /x]p F) ⊢ C - true)
                -> -------------------------------------------------------------------
                                ζ , Δ , Γ ⊢ C - true -- What about poss?
  

sub-valid : ∀ {ζ Δ Γ A C} (D : ζ , ⊡ , Δ ⊢ A - true) (E : ζ , (Δ , A) , Γ ⊢ C - true)
 ->  ζ , Δ , Γ ⊢ C - true
sub-valid D M = {!!}

data step {ζ Δ Γ} : {A : prop ζ} -> ζ , Δ , Γ ⊢ A - true -> ζ , Δ , Γ ⊢ A - true -> Set where
 box-red : ∀ {A C} (D : ζ , ⊡ , Δ ⊢ A - true) (E : ζ , (Δ , A) , Γ ⊢ C - true)
                -> step (let-box (box D) E) (sub-valid D E)