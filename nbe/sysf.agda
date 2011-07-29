{-# OPTIONS --type-in-type #-}
module sysf where
data nat : Set where
 z : nat
 s : nat -> nat

data Fin : nat -> Set where
 z : ∀ {n} -> Fin (s n)
 s : ∀ {n} -> Fin n -> Fin (s n)

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

record Σ {A : Set}(B : A -> Set) : Set where
  constructor _,_ 
  field
    fst : A
    snd : B fst

record _*_ (A : Set) (B : Set) : Set where
  constructor _,_ 
  field
    fst : A
    snd : B

data ctx (A : Set) : Set where
 ⊡ : ctx A
 _,_ : (Γ : ctx A) -> (x : A) -> ctx A

data tvar {A : Set} : ∀ (Δ : ctx A) (x : A) -> Set where
 z : ∀ {Δ T} -> tvar (Δ , T) T
 s : ∀ {Δ T S} -> tvar Δ T -> tvar (Δ , S) T

record unit : Set where
 constructor tt

lctx = ctx unit

data tp (Δ : lctx) : Set where
 v : tvar Δ _ -> tp Δ 
 _⇒_ : ∀ (T : tp Δ) -> (S : tp Δ) -> tp Δ
 Π : ∀ (T : tp (Δ , _)) -> tp Δ

data tctx (Δ : lctx) : Set where
 ⊡ : tctx Δ
 _,_ : ∀ (Γ : tctx Δ) -> (T : tp Δ) -> tctx Δ

data var {Δ : lctx} : ∀ (Γ : tctx Δ) (T : tp Δ) -> Set where
 z : ∀ {Γ} {T : tp Δ} -> var (Γ , T) T
 s : ∀ {Γ} {T : tp Δ} {S : tp Δ} -> var Γ T -> var (Γ , S) T

tctxM : ∀ {Δ1 Δ2} (f : tp Δ1 -> tp Δ2) -> tctx Δ1 -> tctx Δ2
tctxM f ⊡ = ⊡
tctxM f (Γ , x) = tctxM f Γ , f x 
 
tvsubst : ∀ Δ1 Δ2 -> Set
tvsubst Δ1 Δ2 = ∀ {x : _ } (T : tvar Δ1 x) -> tvar Δ2 x

data tsubst : ∀ Δ1 Δ2 -> Set where
 ⊡ : ∀ {Δ2} -> tsubst ⊡ Δ2
 _,_ : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp Δ2 -> tsubst (Δ1 , tt) Δ2

_∘_ : ∀ {A : Set} {B : Set} {C : Set} (g : B -> C) (f : A -> B) -> A -> C
(g ∘ f) x = g (f x)

_,,_ : ∀ {Δ1 Δ2 l} -> tvsubst Δ1 Δ2 -> tvar Δ2 l -> tvsubst (Δ1 , l) Δ2
_,,_ σ x z = x
_,,_ σ x (s y) = σ y

_×_ : ∀ {Δ1 Δ2 l m} -> tvsubst Δ1 Δ2 -> tvar (Δ2 , l) m -> tvsubst (Δ1 , m) (Δ2 , l)
(σ × y) = (s ∘ σ) ,, y

[_] : ∀ {Δ1 Δ2} -> tvsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[ σ ] (v y) = v (σ y)
[ σ ] (T ⇒ S) = [ σ ] T ⇒ [ σ ] S
[ σ ] (Π T) = Π ([ σ × z ] T)

tsubstMap : ∀ {Δ1 Δ2 Δ3} -> tsubst Δ1 Δ2 -> (tp Δ2 -> tp Δ3) -> tsubst Δ1 Δ3
tsubstMap ⊡ f = ⊡
tsubstMap (θ , T) f = (tsubstMap θ f) , (f T)

tsubstLookup : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tvar Δ1 tt -> tp Δ2
tsubstLookup ⊡ ()
tsubstLookup (Θ , T) z = T
tsubstLookup (θ , T) (s x) = tsubstLookup θ x

_××_ : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp (Δ2 , _) -> tsubst (Δ1 , _) (Δ2 , _)
(θ ×× T) = (tsubstMap θ [ s ]) , T

[[_]] : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[[ θ ]] (v y) = tsubstLookup θ y
[[ θ ]] (T ⇒ S) = [[ θ ]] T ⇒ [[ θ ]] S
[[ θ ]] (Π T) = Π ([[ θ ×× v z ]] T)

… : ∀ {A : Set} -> A -> A
… x = x

id-tsubst : ∀ {Δ1} -> tsubst Δ1 Δ1
id-tsubst {⊡} = ⊡
id-tsubst {Δ , T} = (tsubstMap (id-tsubst {Δ}) [ s ]) , v z

mutual
 data rtm (Δ : lctx) (Γ : tctx Δ) : tp Δ -> Set where
  v : ∀ {T : tp Δ} -> var Γ T -> rtm Δ Γ T
  _·_ : ∀ {T : tp Δ} {S : tp Δ} -> rtm Δ Γ (T ⇒ S) -> ntm Δ Γ T -> rtm Δ Γ S
  _$_ : ∀ {T : tp (Δ , _)} -> rtm Δ Γ (Π T) -> (S : tp Δ)
         -> rtm Δ Γ ([[ id-tsubst , S ]] T)
 data ntm (Δ : lctx) (Γ : tctx Δ) : tp Δ -> Set where 
  ƛ : ∀ {T S : tp Δ} -> ntm Δ (Γ , T) S -> ntm Δ Γ (T ⇒ S)
  Λ : ∀ {T : tp (Δ , _)} -> ntm (Δ , _) (tctxM [ s ] Γ) T -> ntm Δ Γ (Π T)
  ▹ : ∀ {A} -> rtm Δ Γ (v A) -> ntm Δ Γ (v A)

{-
data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S) -}

record candidate T : Set₁ where
 field
  sem : (Γ : tctx ⊡) -> Set
  reflect : ∀ {Γ} -> rtm ⊡ Γ T -> sem Γ
  reify : ∀ {Γ} -> sem Γ -> ntm ⊡ Γ T

〚_〛 : (Δ : lctx) (θ : tsubst Δ ⊡) -> Set
〚 ⊡ 〛 θ = unit
〚 Δ , l 〛 (θ , U) = (〚 Δ 〛 θ) * (candidate U)

vari : ∀ {Δ : lctx} {θ : tsubst Δ ⊡} (Δ' : 〚 Δ 〛 θ) (α : tvar Δ _) -> candidate (tsubstLookup θ α)
vari {θ = ⊡} _ ()
vari {θ = θ , T} (Δ' , α) z = α
vari {θ = θ , T} (Δ' , α) (s y) = vari Δ' y

vsubst : ∀ {Δ : lctx} (Γ Γ' : tctx Δ) -> Set
vsubst Γ Γ' = ∀ {T} -> var Γ T -> var Γ' T

sem : ∀ {Δ} {θ : tsubst Δ ⊡} (Δ' : 〚 Δ 〛 θ) (T : tp Δ) -> (Γ : tctx ⊡) -> Set
sem Δ' (v y) Γ = candidate.sem (vari Δ' y) Γ
sem Δ' (T ⇒ S) Γ = ∀ Γ' -> vsubst Γ Γ' -> sem Δ' T Γ' → sem Δ' S Γ'
sem Δ' (Π T) Γ = ∀ U R  → sem {θ = _ , U} (Δ' , R) T Γ

_∘₁_ : ∀ {Δ : lctx} {Γ Γ' ψ : tctx Δ} -> vsubst Γ' Γ -> vsubst ψ Γ' -> vsubst ψ Γ
(σ1 ∘₁ σ2) x = σ1 (σ2 x)

ext : ∀ {Δ : lctx} {Γ Γ' : tctx Δ} {T} -> vsubst Γ Γ' -> vsubst (Γ , T) (Γ' , T)
ext σ z = z
ext σ (s y) = s (σ y)


mutual
 rappSubst : ∀ {Δ Γ Γ' S} -> vsubst Γ Γ' -> rtm Δ Γ S -> rtm Δ Γ' S
 rappSubst σ (v y) = v (σ y)
 rappSubst σ (R · N) = (rappSubst σ R) · nappSubst σ N
 rappSubst σ (R $ S) = (rappSubst σ R) $ S
 nappSubst : ∀ {Δ Γ Γ' S} -> vsubst Γ Γ' -> ntm Δ Γ S -> ntm Δ Γ' S 
 nappSubst σ (ƛ N) = ƛ (nappSubst {!_,,_!} N)
 nappSubst σ (Λ N) = Λ (nappSubst {!!} N)
 nappSubst σ (▹ R) = ▹ (rappSubst σ R)

wkn : ∀ {Δ : lctx} {Γ : tctx Δ} {T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {Δ} {θ : tsubst Δ ⊡} (Δ' : 〚 Δ 〛 θ) T {Γ} -> rtm ⊡ Γ ([[ θ ]] T) -> sem Δ' T Γ
 reflect Δ' (v α) r = candidate.reflect (vari Δ' α) r
 reflect Δ' (T ⇒ S) r = λ Γ' σ x → reflect Δ' S (rappSubst σ r · reify Δ' T x)
 reflect Δ' (Π T) r = λ U R' → reflect (Δ' , R') T ({!!} $ {!!})

 reify : ∀ {Δ} {θ : tsubst Δ ⊡} (Δ' : 〚 Δ 〛 θ) T {Γ} -> sem Δ' T Γ -> ntm ⊡ Γ ([[ θ ]] T)
 reify Δ' (v α) M = candidate.reify (vari Δ' α) M
 reify {θ = θ} Δ' (T ⇒ S) M = ƛ (reify Δ' S (M (_ , [[ θ ]] T) wkn (reflect Δ' T (v z))))
 reify Δ' (Π T) M = Λ {!!}
