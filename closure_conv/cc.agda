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
 letx : ∀ {T S} -> (M : exp Γ T) -> (N : exp (Γ , T) S) -> exp Γ S 

data ctp : Set where
 i : ctp
 _⇝_ : ctp -> ctp -> ctp
 ∧_ : (Γ : ctx ctp) -> ctp -- Type of records
 clos : ctp -> ctp -> ctp
infixr 13 _⇝_

mutual
 data cexp (Γ : ctx ctp) : ctp -> Set where
  v : ∀ {T} -> var Γ T -> cexp Γ T
  _·_ : ∀ {T S} -> cexp Γ (T ⇝ S) -> cexp Γ T -> cexp Γ S
  ƛ : ∀ {T S} -> cexp (⊡ , T) S -> cexp Γ (T ⇝ S)
  letx : ∀ {Δ S} -> subst Δ Γ -> cexp Δ S -> cexp Γ S -- aka explicit substitution
  let1 : ∀ {T S} -> cexp Γ T -> cexp (Γ , T) S -> cexp Γ S -- Can be defined in terms of letx
  clos : ∀ {T Env S} -> cexp Γ ((∧ (Env , T)) ⇝ S) -> cexp Γ (∧ Env) -> cexp Γ (clos T S) 
  copen : ∀ {T S U} -> cexp Γ (clos T S) -> (∀ {Env} -> cexp (Γ , ((∧ (Env , T)) ⇝ S), (∧ Env)) U) -> cexp Γ U
  create : ∀ {Δ} -> (∀ {T} -> var Δ T -> cexp Γ T) -> cexp Γ (∧ Δ)
  proj : ∀ {Δ T} -> cexp Γ (∧ Δ) -> var Δ T -> cexp Γ T

 subst : ctx ctp -> ctx ctp -> Set
 subst Δ Γ = ∀ {T} -> var Δ T -> cexp Γ T

〚_〛 : tp -> ctp
〚 i 〛 = i
〚 T ⇝ S 〛 = clos 〚 T 〛 〚 S 〛

<_> : ctx tp -> ctx ctp
< ⊡ > = ⊡
< Γ , T > = < Γ > , 〚 T 〛 

wkn : ∀ {Γ T S} -> cexp Γ S -> cexp (Γ , T) S
wkn M = {!!}

_,,_ : ∀ {Γ Env T} -> cexp Γ (∧ Env) -> cexp Γ T -> ∀ {S} -> var (Env , T) S -> cexp Γ S
(recrd ,, M) z = M
(recrd ,, M) (s y) = proj recrd y

conv : ∀ {Γ T} -> exp Γ T -> cexp < Γ > 〚 T 〛
conv (v x) = v {!!}
conv (M · N) = copen (conv M) ((v (s z)) · create ((v z) ,, (wkn (wkn (conv N)))))
conv {Γ} (ƛ M) = clos (ƛ (letx (proj (v z)) (conv M))) (create v)
conv (letx M N) = let1 (conv M) (conv N) 