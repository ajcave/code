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
 _×_ : ctp -> ctp -> ctp
 clos : ctp -> ctp -> ctp
infixr 14 _×_
infixr 13 _⇝_

data cexp (Γ : ctx ctp) : ctp -> Set where
 v : ∀ {T} -> var Γ T -> cexp Γ T
 _·_ : ∀ {T S} -> cexp Γ (T ⇝ S) -> cexp Γ T -> cexp Γ S
 ƛ : ∀ {T S} -> cexp (⊡ , T) S -> cexp Γ (T ⇝ S)
 letx : ∀ {T S} -> cexp Γ T -> cexp (Γ , T) S -> cexp Γ S
 clos : ∀ {T Env S} -> cexp Γ (T × Env ⇝ S) -> cexp Γ Env -> cexp Γ (clos T S) 
 copen : ∀ {T S U} -> cexp Γ (clos T S) -> (∀ {Env} -> cexp (Γ , (T × Env ⇝ S), Env) U) -> cexp Γ U
 fst : ∀ {T S} -> cexp Γ (T × S) -> cexp Γ T
 snd : ∀ {T S} -> cexp Γ (T × S) -> cexp Γ S
 pair : ∀ {T S} -> cexp Γ T -> cexp Γ S -> cexp Γ (T × S)

〚_〛 : tp -> ctp
〚 i 〛 = i
〚 T ⇝ S 〛 = clos 〚 T 〛 〚 S 〛

<_> : ctx tp -> ctx ctp
< ⊡ > = ⊡
< Γ , T > = < Γ > , 〚 T 〛 

wkn : ∀ {Γ T S} -> cexp Γ S -> cexp (Γ , T) S
wkn M = {!!}

conv : ∀ {Γ T} -> exp Γ T -> cexp < Γ > 〚 T 〛
conv (v x) = v {!!}
conv (M · N) = copen (conv M) (v (s z) · (pair (wkn (wkn (conv N))) (v z)))
conv (ƛ M) = clos (ƛ {!!}) {!!}
conv (letx M N) = letx (conv M) (conv N)