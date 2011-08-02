module cc where

data tp : Set where
 i : tp
 _⇝_ : tp -> tp -> tp

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (T : A) -> ctx A
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

 labelSet = ctx ctp

infixr 13 _⇝_

label : labelSet -> ctp -> Set
label Lbls T = var Lbls T

mutual
 data cexp (Γ : ctx ctp) : ctp -> Set where
  v : ∀ {T} -> var Γ T -> cexp Γ T
  _·_ : ∀ {T S} -> cexp Γ (T ⇝ S) -> cexp Γ T -> cexp Γ S
  ƛ : ∀ {T S} -> cexp (⊡ , T) S -> cexp Γ (T ⇝ S)
  let* : ∀ {Δ S} -> subst Δ Γ -> cexp Δ S -> cexp Γ S -- aka explicit substitution
  let1 : ∀ {T S} -> cexp Γ T -> cexp (Γ , T) S -> cexp Γ S -- Can be defined in terms of letx
  clos : ∀ {T Env S} -> cexp Γ (∧ (Env , T) ⇝ S) -> cexp Γ (∧ Env) -> cexp Γ (clos T S) 
  copen : ∀ {T S U} -> cexp Γ (clos T S) -> (∀ {Env} -> cexp (Γ , (∧ (Env , T) ⇝ S), (∧ Env)) U) -> cexp Γ U
  create : ∀ {Lbls} -> labelAssignment Lbls Γ -> cexp Γ (∧ Lbls)
  proj : ∀ {Lbls T} -> cexp Γ (∧ Lbls) -> label Lbls T -> cexp Γ T

 subst : ctx ctp -> ctx ctp -> Set
 subst Δ Γ = ∀ {T} -> var Δ T -> cexp Γ T
 labelAssignment : labelSet -> ctx ctp -> Set
 labelAssignment Lbls Γ = ∀ {T} -> label Lbls T -> cexp Γ T

〚_〛 : tp -> ctp
〚 i 〛 = i
〚 T ⇝ S 〛 = clos 〚 T 〛 〚 S 〛

<_> : ctx tp -> ctx ctp
< ⊡ > = ⊡
< Γ , T > = < Γ > , 〚 T 〛

wkn : ∀ {Γ T S} -> cexp Γ S -> cexp (Γ , T) S
wkn M = let* (λ x → v (s x)) M

_,,_ : ∀ {Γ Env T} -> cexp Γ (∧ Env) -> cexp Γ T -> labelAssignment (Env , T) Γ
(recrd ,, M) z = M
(recrd ,, M) (s y) = proj recrd y

vconv : ∀ {Γ T} -> var Γ T -> var < Γ > 〚 T 〛
vconv z = z
vconv (s y) = s (vconv y)

conv : ∀ {Γ T} -> exp Γ T -> cexp < Γ > 〚 T 〛
conv (v x) = v (vconv x)
conv (M · N) = copen (conv M) ((v (s z)) · create ((v z) ,, (wkn (wkn (conv N)))))
conv (ƛ M) = clos (ƛ (let* (proj (v z)) (conv M))) (create v)
conv (let1 M N) = let1 (conv M) (conv N) 

-- If you're concerned about the efficiency of building up complex record access functions
-- then "force" them at every stage.
-- Or if you *really* insist, use a first-order representation