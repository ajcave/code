module cc2 where

data tp : Set where
 i : tp
 _⇝_ : tp -> tp -> tp

data ctx (Tp : Set) : Set where
 ⊡ : ctx Tp
 _,_ : (Γ : ctx Tp) -> (T : Tp) -> ctx Tp
infixl 14 _,_

data var {A : Set} : ctx A -> A -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

data exp (Γ : ctx tp) : tp -> Set where
 v : ∀ {T} -> (x : var Γ T) -> exp Γ T
 _·_ : ∀ {T S} -> (M : exp Γ (T ⇝ S)) -> (N : exp Γ T) -> exp Γ S
 ƛ : ∀ {T S} -> (M : exp (Γ , T) S) -> exp Γ (T ⇝ S)
 let1 : ∀ {T S} -> (M : exp Γ T) -> (N : exp (Γ , T) S) -> exp Γ S 

mutual
 data ctp : Set where
  i : ctp
  _⇝_ : ctp -> ctp -> ctp
  ∧_ : (Lbls : labelSet) -> ctp -- Type of records with label set Lbls
  clos : ctp -> ctp -> ctp

 labelSet = ctx ctp -- They're both just lists of ctps

infixr 13 _⇝_

label : labelSet -> ctp -> Set
label Lbls T = var Lbls T

mutual
 data cexp (Γ : ctx ctp) : ctp -> Set where
  v : ∀ {T} -> var Γ T -> cexp Γ T
  _·_ : ∀ {T S} -> cexp Γ (T ⇝ S) -> cexp Γ T -> cexp Γ S
  ƛ : ∀ {T S} -> cexp (⊡ , T) S -> cexp Γ (T ⇝ S)
  letx : ∀ {Δ S} -> subst Δ Γ -> cexp Δ S -> cexp Γ S -- aka explicit substitution
  let1 : ∀ {T S} -> cexp Γ T -> cexp (Γ , T) S -> cexp Γ S -- Can be defined in terms of letx
  clos : ∀ {T Env S} -> cexp Γ (∧ (Env , T) ⇝ S) -> cexp Γ (∧ Env) -> cexp Γ (clos T S) 
  copen : ∀ {T S U} -> cexp Γ (clos T S) -> (∀ {Env} -> cexp (Γ , (∧ (Env , T) ⇝ S), (∧ Env)) U) -> cexp Γ U
  create : ∀ {Lbls} -> labelAssignment Lbls Γ -> cexp Γ (∧ Lbls)
  proj : ∀ {Lbls T} -> cexp Γ (∧ Lbls) -> label Lbls T -> cexp Γ T

 subst : ctx ctp -> ctx ctp -> Set
 subst Δ Γ = ∀ {T} -> var Δ T -> cexp Γ T
 labelAssignment : labelSet -> ctx ctp -> Set
 labelAssignment Lbls Γ = ∀ {T} -> label Lbls T -> cexp Γ T

data tpRel : tp -> ctp -> Set where
 i : tpRel i i
 _⇝_ : ∀ {T T' S S'} -> tpRel T T' -> tpRel S S' -> tpRel (T ⇝ S) (clos T' S')

〚_〛 : tp -> ctp
〚 i 〛 = i
〚 T ⇝ S 〛 = clos 〚 T 〛 〚 S 〛

data ctxRel : ctx tp -> ctx ctp -> Set where
 ⊡ : ctxRel ⊡ ⊡
 _,_ : ∀ {Γ Γ' T T'} -> ctxRel Γ Γ' -> tpRel T T' -> ctxRel (Γ , T) (Γ' , T')

<_> : ctx tp -> ctx ctp
< ⊡ > = ⊡
< Γ , T > = < Γ > , 〚 T 〛

wkn : ∀ {Γ T S} -> cexp Γ S -> cexp (Γ , T) S
wkn M = letx (λ x → v (s x)) M

_,,_ : ∀ {Γ Env T} -> cexp Γ (∧ Env) -> cexp Γ T -> labelAssignment (Env , T) Γ
(recrd ,, M) z = M
(recrd ,, M) (s y) = proj recrd y

data Σ_ {A : Set} (B : A -> Set) : Set where
 ex : ∀ (x : A) (y : B x) -> Σ B

tpRelTotal : (T : tp) -> Σ (tpRel T)
tpRelTotal i = ex i i
tpRelTotal (T ⇝ S) with tpRelTotal T | tpRelTotal S
tpRelTotal (T ⇝ S) | ex T' RT'  | ex S' RS' = ex (clos T' S') (RT' ⇝ RS')

data _==_ {A : Set} (x : A) : A -> Set where
 refl : x == x

tpRelDeter : ∀ {T T1 T2} -> tpRel T T1 -> tpRel T T2 -> T1 == T2
tpRelDeter i i = refl
tpRelDeter (RT1 ⇝ RS1) (RT2 ⇝ RS2) with tpRelDeter RT1 RT2 | tpRelDeter RS1 RS2
tpRelDeter (RT1 ⇝ RS1) (RT2 ⇝ RS2) | refl | refl = refl

vconv : ∀ {Γ Γ' T T'} -> ctxRel Γ Γ' -> tpRel T T' -> var Γ T -> var Γ' T'
vconv ⊡ Tr () 
vconv (_ , Tr1) Tr2 z with tpRelDeter Tr1 Tr2
vconv (_ , _) _ z | refl = z
vconv (R , _) TR (s y) = s (vconv R TR y)

conv : ∀ {Γ Γ' T T'} -> ctxRel Γ Γ' -> tpRel T T' -> exp Γ T -> cexp Γ' T'
conv R Tr (v x) = v (vconv R Tr x)
conv R Tr (_·_ {S} M N) with tpRelTotal S
... | ex _ TrS = copen (conv R (TrS ⇝ Tr) M) ((v (s z)) · (create ((v z) ,, (wkn (wkn (conv R TrS N))))))
conv R (TrS ⇝ TrT) (ƛ M) = clos (ƛ (letx (proj (v z)) (conv (R , TrS) TrT M))) (create v)
conv R Tr (let1 {S} M N) with tpRelTotal S
... | ex _ TrS = let1 (conv R TrS M) (conv (R , TrS) Tr N)

-- If you're concerned about the efficiency of building up complex record access functions
-- then "force" them at every stage.
-- Or if you *really* insist, use a first-order representation