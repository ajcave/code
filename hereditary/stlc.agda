module stlc where

postulate
 atype : Set

data type : Set where
 ▹ : atype -> type
 _⇒_ : type -> type -> type

data ctx : Set where
 ⊡ : ctx
 _,_ : ctx -> type -> ctx

data var : ctx -> type -> Set where
 z : ∀ {Γ τ} -> var (Γ , τ) τ
 s : ∀ {Γ τ σ} -> var Γ τ -> var (Γ , σ) τ

mutual
 data nf (Γ : ctx) : type -> Set where
  ▹ : ∀ {σ τ} -> (x : var Γ σ) -> (S : spine Γ σ (▹ τ)) -> nf Γ (▹ τ) 
  ƛ : ∀ {σ τ} -> (N : nf (Γ , σ) τ) -> nf Γ (σ ⇒ τ)
 data spine (Γ : ctx) : type -> type -> Set where
  ε : ∀ {ρ} -> spine Γ ρ ρ
  _,_ : ∀ {τ σ ρ} -> (N : nf Γ τ) -> (S : spine Γ σ ρ) -> spine Γ (τ ⇒ σ) ρ

subst : ctx -> ctx -> Set
subst Γ1 Γ2 = ∀ {τ} -> var Γ1 τ -> nf Γ2 τ

vsubst : ctx -> ctx -> Set
vsubst Γ1 Γ2 = ∀ {τ} -> var Γ1 τ -> var Γ2 τ

_,,,_ : ∀ {Γ1 Γ2 τ} -> vsubst Γ1 Γ2 -> var Γ2 τ -> vsubst (Γ1 , τ) Γ2
(σ ,,, y) z = y
(σ ,,, y) (s x) = σ x

_,,_ : ∀ {Γ1 Γ2 τ} -> subst Γ1 Γ2 -> nf Γ2 τ -> subst (Γ1 , τ) Γ2
(σ ,, N) z = N
(σ ,, N) (s x) = σ x

_∘_ : ∀ {A B C : Set} -> (f : B -> C) -> (g : A -> B) -> (A -> C)
(f ∘ g) x = f (g x)

mutual
 〚_〛n : ∀ {Γ1 Γ2 τ} -> (∀ {σ} -> var Γ1 σ -> var Γ2 σ) -> nf Γ1 τ -> nf Γ2 τ
 〚_〛n σ (▹ x S) = ▹ (σ x) (〚 σ 〛s S)
 〚_〛n σ (ƛ N) = ƛ (〚 (s ∘ σ) ,,, z 〛n N)
 〚_〛s : ∀ {Γ1 Γ2 τ ρ} -> (∀ {σ} -> var Γ1 σ -> var Γ2 σ) -> spine Γ1 τ ρ -> spine Γ2 τ ρ
 〚_〛s σ ε = ε
 〚_〛s σ (N , S) = (〚 σ 〛n N) , (〚 σ 〛s S)

-- Should spines go the other way?
appSp : ∀ {ρ Γ τ σ} -> spine Γ ρ (σ ⇒ τ) -> nf Γ σ -> spine Γ ρ τ
appSp ε N = N , ε
appSp (N , S) N' = N , appSp S N'


mutual 
 nvar : ∀ {Γ τ} -> var Γ τ -> nf Γ τ
 nvar x = η-exp x ε

 η-exp : ∀ {ρ Γ τ} -> var Γ τ -> spine Γ τ ρ -> nf Γ ρ
 η-exp {▹ α} x S = ▹ x S
 η-exp {τ ⇒ σ} x S = ƛ (η-exp (s x) (appSp (〚 s 〛s S) (nvar z)))

… : ∀ {Γ} -> subst Γ Γ
… x = nvar x

_×_ : ∀ {Γ1 Γ2 τ ρ} -> subst Γ1 Γ2 -> nf (Γ2 , τ) ρ -> subst (Γ1 , ρ) (Γ2 , τ)
σ × N = (〚 s 〛n ∘ σ) ,, N

mutual
 [_] : ∀ {Γ1 Γ2 τ} -> subst Γ1 Γ2 -> nf Γ1 τ -> nf Γ2 τ
 [ σ ] (▹ x S) = σ x ◆ < σ > S
 [ σ ] (ƛ N) = ƛ ([ σ × (nvar z) ] N)

 <_> : ∀ {Γ1 Γ2 τ σ} -> subst Γ1 Γ2 -> spine Γ1 τ σ -> spine Γ2 τ σ
 < σ > ε = ε
 < σ > (N , S) = ([ σ ] N) , (< σ > S) 

 _◆_ : ∀ {Γ σ τ} -> nf Γ σ -> spine Γ σ τ -> nf Γ τ
 N ◆ ε = N
 ƛ N ◆ (N' , S) = ([ … ,, N' ] N) ◆ S

-- What follows is the implementation straight out of Keller's paper

_-_ : ∀ {τ} -> (Γ : ctx) -> var Γ τ -> ctx
⊡ - ()
(Γ , τ) - z = Γ
(Γ , τ) - (s x) = (Γ - x) , τ

wkv : ∀ {Γ σ τ} (x : var Γ σ) -> var (Γ - x) τ -> var Γ τ
wkv z y = s y
wkv (s y) z = z
wkv (s y) (s y') = s (wkv y y')

data eqV {Γ} : ∀ {τ σ} -> var Γ τ -> var Γ σ -> Set where
 same : ∀ {τ} {x : var Γ τ} -> eqV x x
 diff : ∀ {τ σ} (x : var Γ τ) (y : var (Γ - x) σ) -> eqV x (wkv x y)

eq : ∀ {Γ τ σ} -> (x : var Γ τ) -> (y : var Γ σ) -> eqV x y
eq z z = same
eq z (s y) = diff z y
eq (s y) z = diff (s y) z
eq (s y) (s y') with eq y y'
eq (s .y) (s .y) | same {τ} {y} = same
eq (s y) (s .(wkv y y')) | diff .y y' = diff (s y) (wkv z y')

mutual
 _[[_:=_]] : ∀ {Γ τ σ} -> nf Γ τ -> (x : var Γ σ) -> nf (Γ - x) σ -> nf (Γ - x) τ
 ▹ x S [[ y := N' ]] with eq y x
 ▹ .x S [[ .x := N' ]] | same {τ} {x} = N' ◇ (S << x := N' >>)
 ▹ .(wkv x y) S [[ .x := N' ]] | diff x y = ▹ y (S << x := N' >>)
 ƛ N [[ x := N' ]] = ƛ (N [[ s x := 〚 s 〛n N' ]])

 _<<_:=_>> : ∀ {Γ τ σ ρ} -> spine Γ τ ρ -> (x : var Γ σ) -> nf (Γ - x) σ -> spine (Γ - x) τ ρ
 ε << x := N >> = ε
 (N , S) << x := N' >> = (N [[ x := N' ]]) , (S << x := N' >>)

 _◇_ : ∀ {Γ τ σ} -> nf Γ σ -> spine Γ σ τ -> nf Γ τ
 N ◇ ε = N
 ƛ N ◇ (N' , S) = (N [[ z := N' ]]) ◇ S