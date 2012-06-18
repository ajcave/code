module large-elim where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Σ {A : Set} (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

record Unit : Set where
 constructor tt

data Bool : Set where
 true false : Bool

postulate
 atomic_tp : Set

mutual
 data U : Set where
  unit bool : U
  Π : (S : U) -> (T : El S -> U) -> U

 El : U -> Set
 El unit = Unit
 El bool = Bool
 El (Π S T) = (s : El S) -> El (T s)

mutual
 data ctx : Set where
  ⊡ : ctx
  _,_ : (Γ : ctx) -> (T : 〚 Γ 〛c -> U) -> ctx

 〚_〛c : ctx -> Set
 〚 ⊡ 〛c = Unit
 〚 Γ , T 〛c = Σ (λ (x : 〚 Γ 〛c) → El (T x))

_∘_ : ∀ {R : Set} {S : R -> Set} {T : (r : R) -> S r -> Set}
 -> (∀ {r} (s : S r) -> T r s)
 -> (g : (r : R) -> S r)
 -> (r : R) -> T r (g r)
f ∘ g = λ x -> f (g x)

data var : (Γ : ctx) -> (T : 〚 Γ 〛c -> U) -> Set where
 top : ∀ {Γ T} -> var (Γ , T) (T ∘ Σ.fst)
 pop : ∀ {Γ T S} -> var Γ T -> var (Γ , S) (T ∘ Σ.fst)

〚_〛v : ∀ {Γ T} -> var Γ T -> (γ : 〚 Γ 〛c) -> El (T γ)
〚_〛v {⊡} () tt
〚_〛v {Γ , T} top (γ , t) = t
〚_〛v {Γ , T} (pop y) (γ , s) = 〚 y 〛v γ

{-data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp
 unit : tp


data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

vsubst : ctx -> ctx -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U

mutual 
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
  π₁ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ T
  π₂ : ∀ {T S} -> rtm Γ (T × S) -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)
  <_,_> : ∀ {T S} -> (M : ntm Γ T) -> (N : ntm Γ S) -> ntm Γ (T × S)
  tt : ntm Γ unit -}
