module ltl where

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

postulate
 atomic_type : Set

data type : Set where
 ▸ : (P : atomic_type) -> type
 _▹_ : (A B : type) -> type
 □ ◇ ○ : (A : type) -> type
 _∧_ _⊃_ _∨_ : (A B : type) -> type
 ⊤ ⊥ : type

data judgement : Set where
 true next : judgement

mutual
 data _,_,_⊢_-_ (Δ : ctx type) (θ : ctx type) (Γ : ctx type) : type -> judgement -> Set where
  ▹ : ∀ {A} -> (x : var Γ A)
            -> -------------------
               Δ , θ , Γ ⊢ A - true
  ▻ : ∀ {A} -> (u : var Δ A)
            -> --------------------
               Δ , θ , Γ ⊢ A - true
  let-next : ∀ {A C J} (M : Δ , θ , Γ ⊢ (○ A) - true) (N : Δ , (θ , A) , Γ ⊢ C - J)
                   -> ---------------------------------------------------------------
                                          Δ , θ , Γ ⊢ C - J
  next : ∀ {A} -> (M : Δ , θ , Γ ⊢ A - next)
               -> --------------------------
                     Δ , θ , Γ ⊢ (○ A) - true
  shift : ∀ {A} -> (M : Δ , ⊡ , θ ⊢ A - true)
                -> --------------------------
                     Δ , θ , Γ ⊢ A - next
  -- I suspect we only need this for true, not next. Show admissibility for next using true?
  let-box : ∀ {A C J} (M : Δ , θ , Γ ⊢ (□ A) - true) (N : (Δ , A) , θ , Γ ⊢ C - J)
                   -> ---------------------------------------------------------------
                                           Δ , θ , Γ ⊢ C - J
  box : ∀ {A Γ'} (M : Δ , θ , Γ ⊩ Γ' - true) (N : Δ , ⊡ , Γ' ⊢ A - true) (P : Δ , ⊡ , Γ' ⊩ Γ' - next)
              -> -------------------------------------------------------------------------------------
                                           Δ , θ , Γ ⊢ (□ A) - true
  dia-rec : ∀ {A C} (M : Δ , θ , Γ ⊢ (◇ A) - true) (N : Δ , ⊡ , (⊡ , A) ⊢ C - true) (P : Δ , (⊡ , C) , ⊡ ⊢ C - true)
                 -> ------------------------------------------------------------------------------------------------
                                           Δ , θ , Γ ⊢ C - true
  dia-now : ∀ {A} (M : Δ , θ , Γ ⊢ A - true)
               -> --------------------------
                    Δ , θ , Γ ⊢ (◇ A) - true
  dia-next : ∀ {A} (M : Δ , ⊡ , θ ⊢ (◇ A) - true)
               -> -------------------------------
                    Δ , θ , Γ ⊢ (◇ A) - true
  
 _,_,_⊩_-_ : (Δ : ctx type) (θ : ctx type) (Γ : ctx type) (Γ' : ctx type) -> judgement -> Set
 Δ , θ , Γ ⊩ Γ' - J = sub (λ A → Δ , θ , Γ ⊢ A - J) Γ'

mutual
 [_]tv : ∀ {Δ θ Γ1 Γ2 A J} -> vsub Γ2 Γ1 -> Δ , θ , Γ1 ⊢ A - J -> Δ , θ , Γ2 ⊢ A - J
 [_]tv σ (▹ x) = ▹ ([ σ ]v x)
 [_]tv σ (▻ u) = ▻ u
 [_]tv σ (let-next M N) = let-next ([ σ ]tv M) ([ σ ]tv N)
 [_]tv σ (next M) = next ([ σ ]tv M)
 [_]tv σ (shift M) = shift M
 [_]tv σ (let-box M N) = let-box ([ σ ]tv M) ([ σ ]tv N)
 [_]tv σ (box M N P) = box ([ σ ]tvs M) N P
 [_]tv σ (dia-rec M N P) = dia-rec ([ σ ]tv M) N P
 [_]tv σ (dia-now M) = dia-now ([ σ ]tv M)
 [_]tv σ (dia-next M) = dia-next M

 [_]tvs : ∀ {Δ θ Γ1 Γ2 Γ' J} -> vsub Γ2 Γ1 -> Δ , θ , Γ1 ⊩ Γ' - J -> Δ , θ , Γ2 ⊩ Γ' - J
 [_]tvs σ ⊡ = ⊡
 [_]tvs σ (σ' , M) = ([ σ ]tvs σ') , ([ σ ]tv M)

mutual
 [_]nv : ∀ {Δ θ1 θ2 Γ A J} -> vsub θ2 θ1 -> Δ , θ1 , Γ ⊢ A - J -> Δ , θ2 , Γ ⊢ A - J
 [_]nv σ (▹ x) = ▹ x
 [_]nv σ (▻ u) = ▻ u
 [_]nv σ (let-next M N) = let-next ([ σ ]nv M) ([ vsub-ext σ ]nv N)
 [_]nv σ (next M) = next ([ σ ]nv M)
 [_]nv σ (shift M) = shift ([ σ ]tv M)
 [_]nv σ (let-box M N) = let-box ([ σ ]nv M) ([ σ ]nv N)
 [_]nv σ (box M N P) = box ([ σ ]nvs M) N P
 [_]nv σ (dia-rec M N P) = dia-rec ([ σ ]nv M) N P
 [_]nv σ (dia-now M) = dia-now ([ σ ]nv M)
 [_]nv σ (dia-next M) = dia-next ([ σ ]tv M)

 [_]nvs : ∀ {Δ θ1 θ2 Γ A J} -> vsub θ2 θ1 -> Δ , θ1 , Γ ⊩ A - J -> Δ , θ2 , Γ ⊩ A - J
 [_]nvs σ ⊡ = ⊡
 [_]nvs σ (σ' , M) = ([ σ ]nvs σ') , ([ σ ]nv M)

mutual
 [_]vav : ∀ {Δ1 Δ2 θ Γ A J} -> vsub Δ2 Δ1 -> Δ1 , θ , Γ ⊢ A - J -> Δ2 , θ , Γ ⊢ A - J
 [_]vav σ (▹ x) = ▹ x
 [_]vav σ (▻ u) = ▻ ([ σ ]v u)
 [_]vav σ (let-next M N) = let-next ([ σ ]vav M) ([ σ ]vav N)
 [_]vav σ (next M) = next ([ σ ]vav M)
 [_]vav σ (shift M) = shift ([ σ ]vav M)
 [_]vav σ (let-box M N) = let-box ([ σ ]vav M) ([ vsub-ext σ ]vav N)
 [_]vav σ (box M N P) = box ([ σ ]vavs M) ([ σ ]vav N) ([ σ ]vavs P)
 [_]vav σ (dia-rec M N P) = dia-rec ([ σ ]vav M) ([ σ ]vav N) ([ σ ]vav P)
 [_]vav σ (dia-now M) = dia-now ([ σ ]vav M)
 [_]vav σ (dia-next M) = dia-next ([ σ ]vav M)

 [_]vavs : ∀ {Δ1 Δ2 θ Γ A J} -> vsub Δ2 Δ1 -> Δ1 , θ , Γ ⊩ A - J -> Δ2 , θ , Γ ⊩ A - J
 [_]vavs σ ⊡ = ⊡
 [_]vavs σ (σ' , M) = ([ σ ]vavs σ') , ([ σ ]vav M)

truesub-id : ∀ {Δ θ Γ} -> Δ , θ , Γ ⊩ Γ - true
truesub-id {Δ} {θ} {⊡} = ⊡
truesub-id {Δ} {θ} {Γ , T} = (sub-map [ wkn-vsub ]tv truesub-id) , (▹ top)

truesub-ext : ∀ {Δ θ Γ1 Γ2 T} -> Δ , θ , Γ1 ⊩ Γ2 - true -> Δ , θ , (Γ1 , T) ⊩ (Γ2 , T) - true
truesub-ext σ = (sub-map [ wkn-vsub ]tv σ) , (▹ top)

mutual
 [_]t : ∀ {Δ θ Γ1 Γ2 A J} -> Δ , θ , Γ2 ⊩ Γ1 - true -> Δ , θ , Γ1 ⊢ A - J -> Δ , θ , Γ2 ⊢ A - J
 [_]t σ (▹ x) = [ σ ]v x
 [_]t σ (▻ u) = ▻ u
 [_]t σ (let-next M N) = let-next ([ σ ]t M) ([ sub-map [ wkn-vsub ]nv σ ]t N)
 [_]t σ (next M) = next ([ σ ]t M)
 [_]t σ (shift M) = shift M
 [_]t σ (let-box M N) = let-box ([ σ ]t M) ([ sub-map [ wkn-vsub ]vav σ ]t N)
 [_]t σ (box M N P) = box ([ σ ]ts M) N P
 [_]t σ (dia-rec M N P) = dia-rec ([ σ ]t M) N P
 [_]t σ (dia-now M) = dia-now ([ σ ]t M)
 [_]t σ (dia-next M) = dia-next M

 [_]ts : ∀ {Δ θ Γ1 Γ2 Γ' J} -> Δ , θ , Γ2 ⊩ Γ1 - true -> Δ , θ , Γ1 ⊩ Γ' - J -> Δ , θ , Γ2 ⊩ Γ' - J
 [_]ts σ ⊡ = ⊡
 [_]ts σ (σ' , M) = ([ σ ]ts σ') , ([ σ ]t M)