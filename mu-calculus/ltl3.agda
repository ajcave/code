module ltl3 where

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A

_++_ : ∀ {A : Set} -> ctx A -> ctx A -> ctx A
Γ1 ++ ⊡ = Γ1
Γ1 ++ (Γ , T) = (Γ1 ++ Γ) , T

_<<_ : ∀ {A : Set} -> ctx A -> ctx A -> ctx A
Γ1 << ⊡ = Γ1
Γ1 << (Γ , T) = (Γ1 , T) << Γ

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

trans : ∀ {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

sym : ∀ {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong : ∀ {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

subst : ∀ {A : Set} (B : A -> Set) {x y : A} -> x ≡ y -> B x -> B y
subst B refl t = t

assoc : ∀ {A} (Γ1 Γ2 Γ3 : ctx A) -> ((Γ1 ++ Γ2) << Γ3) ≡ (Γ1 ++ (Γ2 << Γ3))
assoc Γ1 Γ2 ⊡ = refl
assoc Γ1 Γ2 (Γ , T) = assoc Γ1 (Γ2 , T) Γ

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
 true next poss : judgement

-- Try the system without Δ, so the other elim rule.
-- I think we can have atomic init rule for this system, but not for the one without Δ
-- This stems from the direct treatment of □ as a fixpoint: fixpoints must be considered atomic
-- for purposes of the init rule
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
  box : ∀ {A Γ'} (ρ : Δ , θ , Γ ⊢ Γ' - true) (M : Δ , ⊡ , (⊡ , Γ') ⊢ A - true) (ρ' : Δ , ⊡ , (⊡ , Γ') ⊢ Γ' - next)
              -> -------------------------------------------------------------------------------------
                                           Δ , θ , Γ ⊢ (□ A) - true
  dia-rec : ∀ {A C} (M : Δ , θ , Γ ⊢ (◇ A) - true) (N : Δ , ⊡ , (⊡ , A) ⊢ C - true) (P : Δ , (⊡ , C) , ⊡ ⊢ C - true)
                 -> ------------------------------------------------------------------------------------------------
                                           Δ , θ , Γ ⊢ C - true
  dia : ∀ {A} (M : Δ , θ , Γ ⊢ A - poss)
               -> --------------------------
                   Δ , θ , Γ ⊢ (◇ A) - true
  poss-now : ∀ {A} (M : Δ , θ , Γ ⊢ A - true)
               -> --------------------------
                        Δ , θ , Γ ⊢ A - poss
  poss-next : ∀ {A} (M : Δ , ⊡ , θ ⊢ A - poss)
               -> -------------------------------
                    Δ , θ , Γ ⊢ A - poss
  
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
 [_]tv σ (box M N P) = box ([ σ ]tv M) N P
 [_]tv σ (dia-rec M N P) = dia-rec ([ σ ]tv M) N P
 [_]tv σ (dia M) = dia ([ σ ]tv M)
 [_]tv σ (poss-now M) = poss-now ([ σ ]tv M)
 [_]tv σ (poss-next M) = poss-next M

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
 [_]nv σ (box ρ M ρ') = box ([ σ ]nv ρ) M ρ'
 [_]nv σ (dia-rec M N P) = dia-rec ([ σ ]nv M) N P
 [_]nv σ (dia M) = dia ([ σ ]nv M)
 [_]nv σ (poss-now M) = poss-now ([ σ ]nv M)
 [_]nv σ (poss-next M) = poss-next ([ σ ]tv M)
 
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
 [_]vav σ (box ρ M ρ') = box ([ σ ]vav ρ) ([ σ ]vav M) ([ σ ]vav ρ')
 [_]vav σ (dia-rec M N P) = dia-rec ([ σ ]vav M) ([ σ ]vav N) ([ σ ]vav P)
 [_]vav σ (dia M) = dia ([ σ ]vav M)
 [_]vav σ (poss-now M) = poss-now ([ σ ]vav M)
 [_]vav σ (poss-next M) = poss-next ([ σ ]vav M)

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
 [_]t σ (box M N P) = box ([ σ ]t M) N P
 [_]t σ (dia-rec M N P) = dia-rec ([ σ ]t M) N P
 [_]t σ (dia M) = dia ([ σ ]t M)
 [_]t σ (poss-now M) = poss-now ([ σ ]t M)
 [_]t σ (poss-next M) = poss-next M

 [_]ts : ∀ {Δ θ Γ1 Γ2 Γ' J} -> Δ , θ , Γ2 ⊩ Γ1 - true -> Δ , θ , Γ1 ⊩ Γ' - J -> Δ , θ , Γ2 ⊩ Γ' - J
 [_]ts σ ⊡ = ⊡
 [_]ts σ (σ' , M) = ([ σ ]ts σ') , ([ σ ]t M)


mutual
 [_]n : ∀ {Δ θ1 θ2 Γ A J} -> Δ , ⊡ , θ2 ⊩ θ1 - true -> Δ , θ1 , Γ ⊢ A - J -> Δ , θ2 , Γ ⊢ A - J
 [_]n σ (▹ x) = ▹ x
 [_]n σ (▻ u) = ▻ u
 [_]n σ (let-next M N) = let-next ([ σ ]n M) ([ truesub-ext σ ]n N)
 [_]n σ (next M) = next ([ σ ]n M)
 [_]n σ (shift M) = shift ([ σ ]t M) --!
 [_]n σ (let-box M N) = let-box ([ σ ]n M) ([ sub-map [ wkn-vsub ]vav σ ]n N)
 [_]n σ (box M N P) = box ([ σ ]n M) N P
 [_]n σ (dia-rec M N P) = dia-rec ([ σ ]n M) N P
 [_]n σ (dia M) = dia ([ σ ]n M)
 [_]n σ (poss-now M) = poss-now ([ σ ]n M)
 [_]n σ (poss-next M) = poss-next ([ σ ]t M) --!

 [_]ns : ∀ {Δ θ1 θ2 Γ A J} -> Δ , ⊡ , θ2 ⊩ θ1 - true -> Δ , θ1 , Γ ⊩ A - J -> Δ , θ2 , Γ ⊩ A - J
 [_]ns σ ⊡ = ⊡
 [_]ns σ (σ' , M) = ([ σ ]ns σ') , ([ σ ]n M)


〈_/x〉 : ∀ {Δ θ Γ A B J} -> Δ , θ , Γ ⊢ A - next ->  Δ , (θ , A) , Γ ⊢ B - J -> Δ , θ , Γ ⊢ B - J
〈_/x〉 (let-next M N) N' = let-next M (〈 N /x〉 ([ (wkn (wkn-vsub)) , top ]nv N'))
〈_/x〉 (shift M) N = [ truesub-id , M ]n N
〈_/x〉 (let-box M N) N' = let-box M (〈 N /x〉 ([ wkn-vsub ]vav N'))

lem : ∀ {Δ θ Γ Γ' C} -> Δ , θ , Γ ⊢ Γ' - next
  -> (∀ Δ' θ' -> (Δ << Δ') , ⊡ , (θ << θ') ⊢ Γ' - true -> (Δ << Δ') , ⊡ , (θ << θ') ⊢ C - true)
  -> Δ , θ , Γ ⊢ C - next
lem (let-next M N) f = let-next M (lem N (λ Δ' θ' x → f Δ' (θ' , _) x))
lem (shift M) f = shift (f ⊡ ⊡ M)
lem (let-box M N) f = let-box M (lem N (λ Δ' θ' x → f (Δ' , _) θ' x ))

lem2 : ∀ {Δ θ Γ Γ' C} -> Δ , θ , Γ ⊢ Γ' - next
  -> (∀ Δ' θ' -> (Δ << Δ') , ⊡ , (θ << θ') ⊢ Γ' - true -> (Δ << Δ') , ⊡ , (θ << θ') ⊢ C - poss)
  -> Δ , θ , Γ ⊢ C - poss
lem2 (let-next M N) f = let-next M (lem2 N (λ Δ' θ' x → f Δ' (θ' , _) x))
lem2 (shift M) f = poss-next (f ⊡ ⊡ M)
lem2 (let-box M N) f = let-box M (lem2 N (λ Δ' θ' x → f (Δ' , _) θ' x))

imp<< : ∀ {A : Set} (Γ Γ' : ctx A) -> vsub (Γ << Γ') Γ
imp<< Γ ⊡ = id-vsub
imp<< Γ (Γ' , T) with imp<< (Γ , T) Γ'
imp<< Γ (Γ' , T) | σ , M = σ

importv : ∀ {Δ1 Δ2 θ Γ C J} Δ' -> (Δ1 ++ Δ2) , θ , Γ ⊢ C - J -> (Δ1 ++ (Δ2 << Δ')) , θ , Γ ⊢ C - J
importv {Δ1} {Δ2} Δ' M = [ subst (λ x → sub (var x) (Δ1 ++ Δ2)) (assoc Δ1 Δ2 Δ') (imp<< (Δ1 ++ Δ2) Δ') ]vav M

importvn : ∀ {Δ1 Δ2 θ Γ C J} Δ' θ' -> (Δ1 ++ Δ2) , θ , Γ ⊢ C - J -> (Δ1 ++ (Δ2 << Δ')) , (θ << θ') , Γ ⊢ C - J
importvn Δ' θ' M = importv Δ' ([ imp<< _ θ' ]nv M)

importvt : ∀ {Δ1 Δ2 θ Γ C J} Δ' Γ' -> (Δ1 ++ Δ2) , θ , Γ ⊢ C - J -> (Δ1 ++ (Δ2 << Δ')) , θ , (Γ << Γ') ⊢ C - J
importvt Δ' Γ' M = importv Δ' ([ imp<< _ Γ' ]tv M)

reassoc1 : ∀ {θ Γ C J} Δ1 Δ2 Δ3 -> (Δ1 ++ (Δ2 << Δ3)) , θ , Γ ⊢ C - J -> ((Δ1 ++ Δ2) << Δ3) , θ , Γ ⊢ C - J
reassoc1 {θ} {Γ} {C} {J} Δ1 Δ2 Δ3 M = subst (λ x → x , θ , Γ ⊢ C - J) (sym (assoc Δ1 Δ2 Δ3)) M 

reassoc2 : ∀ {θ Γ C J} Δ1 Δ2 Δ3 -> ((Δ1 ++ Δ2) << Δ3) , θ , Γ ⊢ C - J -> (Δ1 ++ (Δ2 << Δ3)) , θ , Γ ⊢ C - J
reassoc2 {θ} {Γ} {C} {J} Δ1 Δ2 Δ3 M = subst (λ x → x , θ , Γ ⊢ C - J) (assoc Δ1 Δ2 Δ3) M

-- Doesn't termination check because we make recursive calls on weakenings of terms
-- Should terminate, but I don't want to try to convince Agda at the moment
vsub1 : ∀ {Δ A θ Γ Γ' C J} Δ'
  -> (Δ ++ Δ') , θ , Γ ⊢ Γ' - true
  -> (Δ ++ Δ') , ⊡ , (⊡ , Γ') ⊢ A - true
  -> (Δ ++ Δ') , ⊡ , (⊡ , Γ') ⊢ Γ' - next
  -> ((Δ , A) ++ Δ') , θ , Γ ⊢ C - J
  -> (Δ ++ Δ') , θ , Γ ⊢ C - J
vsub1 Δ1 M N P (▹ x) = ▹ x
vsub1 Δ1 M N P (▻ u) = {!!} -- case u is pointing to the A or not
vsub1 Δ1 M N P (let-next M' N') = let-next (vsub1 Δ1 M N P M') (vsub1 Δ1 ([ wkn-vsub ]nv M) N P N')
vsub1 Δ1 M N P (next M') = next (vsub1 Δ1 M N P M')
vsub1 Δ1 M N P (shift M') = lem ([ ⊡ , M ]t ([ ⊡ ]n P)) (λ Δ' θ' x → reassoc1 _ Δ1 Δ' (vsub1 (Δ1 << Δ') (reassoc2 _ Δ1 Δ' x) (importvn Δ' ⊡ N) (importvn Δ' ⊡ P) (importvt Δ' θ' M')))
vsub1 Δ1 M N P (let-box M' N') = let-box (vsub1 Δ1 M N P M') (vsub1 (Δ1 , _) ([ wkn-vsub ]vav M) ([ wkn-vsub ]vav N) ([ wkn-vsub ]vav P) N')
vsub1 Δ1 M N P (box ρ M' ρ') = box {!!} {!!} {!!} -- Need to take conjuction of invariants or both invariants here
vsub1 Δ1 M N P (dia-rec M' N' P') = {!!} --dia-rec (vsub1 Δ1 M N P M') {!!} {!!} -- ???? This is tough!
vsub1 Δ1 M N P (dia M') = dia (vsub1 Δ1 M N P M')
vsub1 Δ1 M N P (poss-now M') = poss-now (vsub1 Δ1 M N P M')
vsub1 Δ1 M N P (poss-next M') = lem2 ([ ⊡ , M ]t ([ ⊡ ]n P)) (λ Δ' θ' x → reassoc1 _ Δ1 Δ' (vsub1 (Δ1 << Δ') (reassoc2 _ Δ1 Δ' x) (importvn Δ' ⊡ N) (importvn Δ' ⊡ P) (importvt Δ' θ' M')))

{-record unfold (Δ θ Γ : ctx type) (A : type) : Set where
 constructor rule
 field
  Γ' : ctx type
  start : Δ , θ , Γ ⊩ Γ' - true
  conseq : Δ , ⊡ , Γ' ⊢ A - true
  preserve : Δ , ⊡ , Γ' ⊩ Γ' - next

validsub : ∀ (Δ1 Δ2 θ Γ : ctx type) -> Set
validsub Δ1 Δ2 θ Γ = sub (unfold Δ2 θ Γ) Δ1

wkn-validsub1 : ∀ {Δ1 Δ2 θ T Γ} -> validsub Δ1 Δ2 θ Γ -> validsub Δ1 Δ2 (θ , T) Γ
wkn-validsub1 M = sub-map (λ x → rule (unfold.Γ' x) (sub-map [ wkn-vsub ]nv (unfold.start x)) (unfold.conseq x) (unfold.preserve x)) M 

unfold-top : ∀ {Δ θ Γ A} -> unfold (Δ , A) θ Γ A
unfold-top = rule (⊡ , _) (⊡ , ▻ top) (▻ top) (⊡ , shift (▻ top))

wkn-unfold : ∀ {Δ θ Γ A T} -> unfold Δ θ Γ A -> unfold (Δ , T) θ Γ A
wkn-unfold (rule Γ' ρ M ρ') = rule Γ' (sub-map [ wkn-vsub ]vav ρ) ([ wkn-vsub ]vav M) (sub-map [ wkn-vsub ]vav ρ')

wkn-validsub2 : ∀ {Δ1 Δ2 θ Γ A} -> validsub Δ1 Δ2 θ Γ -> validsub Δ1 (Δ2 , A) θ Γ
wkn-validsub2 σ = sub-map wkn-unfold σ

validsub-ext : ∀ {Δ1 Δ2 θ Γ A} -> validsub Δ1 Δ2 θ Γ -> validsub (Δ1 , A) (Δ2 , A) θ Γ
validsub-ext σ = wkn-validsub2 σ , unfold-top 

mutual
 [_]va : ∀ {Δ1 Δ2 θ Γ A J} -> validsub Δ1 Δ2 θ Γ -> Δ1 , θ , Γ ⊢ A - J -> Δ2 , θ , Γ ⊢ A - J
 [_]va σ (▹ x) = ▹ x
 [_]va σ (▻ u) with [ σ ]v u
 [_]va σ (▻ u) | rule Γ' σ' M _ = [ σ' ]t ([ ⊡ ]n M)
 [_]va σ (let-next M N) = let-next ([ σ ]va M) ([ wkn-validsub1 σ ]va N)
 [_]va σ (next M) = next ([ σ ]va M)
 [_]va σ (shift M) = {!!} -- This is pretty much precisely the lemma we want
 [_]va σ (let-box M N) = let-box ([ σ ]va M) ([ validsub-ext σ ]va N)
 [_]va σ (box M N P) = box {!!} {!!} {!!}
 [_]va σ (dia-rec M N P) = {!!}
 [_]va σ (dia M) = dia ([ σ ]va M)
 [_]va σ (poss-now M) = poss-now ([ σ ]va M)
 [_]va σ (poss-next M) = {!!} -- This is precisely the lemma we want. Hmm if we did it in the original dia next implies dia now
-- style (but didn't force the shift to be early) then we could save ourselves work, actually. Just need the "next" lemma,
-- not the "poss" one. I think this is just because it's part way towards "just use fixpoints", which saves a lot of work

 [_]vas : ∀ {Δ1 Δ2 θ Γ A J} -> validsub Δ1 Δ2 θ Γ -> Δ1 , θ , Γ ⊩ A - J -> Δ2 , θ , Γ ⊩ A - J
 [_]vas σ ⊡ = ⊡
 [_]vas σ (σ' , M) = ([ σ ]vas σ') , ([ σ ]va M) -}