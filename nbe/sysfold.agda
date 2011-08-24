{-# OPTIONS --type-in-type #-}
module sysfold where
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

tsubstMap : ∀ {Δ1 Δ2 Δ3} -> (tp Δ2 -> tp Δ3) -> tsubst Δ1 Δ2 -> tsubst Δ1 Δ3
tsubstMap f ⊡ = ⊡
tsubstMap f (θ , T) = (tsubstMap f θ) , (f T)

tsubstLookup : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tvar Δ1 tt -> tp Δ2
tsubstLookup ⊡ ()
tsubstLookup (Θ , T) z = T
tsubstLookup (θ , T) (s x) = tsubstLookup θ x

_××_ : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp (Δ2 , _) -> tsubst (Δ1 , _) (Δ2 , _)
(θ ×× T) = (tsubstMap [ s ] θ) , T

[[_]] : ∀ {Δ1 Δ2} -> tsubst Δ1 Δ2 -> tp Δ1 -> tp Δ2
[[ θ ]] (v y) = tsubstLookup θ y
[[ θ ]] (T ⇒ S) = [[ θ ]] T ⇒ [[ θ ]] S
[[ θ ]] (Π T) = Π ([[ θ ×× v z ]] T)

… : ∀ {A : Set} -> A -> A
… x = x

id-tsubst : ∀ {Δ1} -> tsubst Δ1 Δ1
id-tsubst {⊡} = ⊡
id-tsubst {Δ , T} = (tsubstMap [ s ] (id-tsubst {Δ})) , v z

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

vsubst : ∀ {Δ : lctx} (Γ Γ' : tctx Δ) -> Set
vsubst Γ Γ' = ∀ {T} -> var Γ T -> var Γ' T

record candidate Δ T : Set₁ where
 field
  sem : (Γ : tctx Δ) -> Set
  funct : ∀ {Γ1 Γ2} -> vsubst Γ1 Γ2 -> sem Γ1 -> sem Γ2
  reflect : ∀ {Γ} -> rtm Δ Γ T -> sem Γ
  reify : ∀ {Γ} -> sem Γ -> ntm Δ Γ T

〚_〛 : (Δ1 : lctx) {Δ2 : lctx} (θ : tsubst Δ1 Δ2) -> Set
〚 ⊡ 〛 θ = unit
〚 Δ , l 〛 (θ , U) = (〚 Δ 〛 θ) * (candidate _ U)

vari : ∀ {Δ1 Δ2 : lctx} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) (α : tvar Δ1 _) -> candidate Δ2 (tsubstLookup θ α)
vari {θ = ⊡} _ ()
vari {θ = θ , T} (Δ' , α) z = α
vari {θ = θ , T} (Δ' , α) (s y) = vari Δ' y


sem : ∀ {Δ1 Δ2} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) (T : tp Δ1) -> (Γ : tctx Δ2) -> Set
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
 nappSubst σ (ƛ N) = ƛ (nappSubst (ext σ) N)
 nappSubst σ (Λ N) = Λ (nappSubst {!!} N)
 nappSubst σ (▹ R) = ▹ (rappSubst σ R)

appSubst : ∀ {Δ1 Δ2} {Γ1 Γ2 : tctx Δ2} {θ : tsubst Δ1 Δ2} {Δ' : 〚 Δ1 〛 θ} S -> vsubst Γ1 Γ2 -> sem Δ' S Γ1 -> sem Δ' S Γ2
appSubst {Δ' = Δ'} (v α) θ M = candidate.funct (vari Δ' α) θ M
appSubst (T ⇒ S) θ M = λ Γ' σ x → M Γ' (σ ∘ θ) x
appSubst (Π T) θ M = λ U R → appSubst T θ (M U R)

wkn : ∀ {Δ : lctx} {Γ : tctx Δ} {T} -> vsubst Γ (Γ , T)
wkn x = s x

lem : ∀ {Δ1 Δ2 Δ3} (θ1 : tsubst Δ1 Δ2) (θ2 : tsubst Δ2 Δ3) T -> [[ θ2 ]] ([[ θ1 ]] T) ≡ [[ tsubstMap [[ θ2 ]] θ1 ]] T
lem θ1 θ2 T = {!!}

lem2 : ∀ {Δ1 Δ2 Δ3 Δ4} (f : tp Δ1 -> tp Δ2) (g : tp Δ2 -> tp Δ3) (θ : tsubst Δ4 Δ1)
  -> tsubstMap g (tsubstMap f θ) ≡ tsubstMap (λ x -> g (f x)) θ
lem2 f g ⊡ = refl
lem2 f g (θ , T) rewrite lem2 f g θ = refl

neut-candidate : ∀ {Δ} -> candidate (Δ , tt) (v z)
neut-candidate {Δ} = record { sem = λ Γ → rtm _ Γ (v z); reflect = λ x → x; reify = ▹; funct = rappSubst}

mutual
 reflect : ∀ {Δ1 Δ2} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) T {Γ} -> rtm Δ2 Γ ([[ θ ]] T) -> sem Δ' T Γ
 reflect Δ' (v α) r = candidate.reflect (vari Δ' α) r
 reflect Δ' (T ⇒ S) r = λ Γ' σ x → reflect Δ' S (rappSubst σ r · reify Δ' T x)
 reflect {Δ2 = Δ2} {θ = θ} Δ' (Π T) {Γ} r = foo
   where foo : (U : tp Δ2) (R : candidate Δ2 U) -> sem (Δ' , R) T Γ
         foo U R with r $ U
         ... | w = reflect (Δ' , R) {!!} {!!}
         --... | w rewrite lem (tsubstMap [ s ] θ , v z) (? , U) T | lem2 [ s ] [[ ⊡ , U ]] θ = reflect {θ = θ , U} (Δ' , R) T {Γ = Γ} {!!}

 reify : ∀ {Δ1 Δ2} {θ : tsubst Δ1 Δ2} (Δ' : 〚 Δ1 〛 θ) T {Γ} -> sem Δ' T Γ -> ntm Δ2 Γ ([[ θ ]] T)
 reify Δ' (v α) M = candidate.reify (vari Δ' α) M
 reify {θ = θ} Δ' (T ⇒ S) M = ƛ (reify Δ' S (M (_ , [[ θ ]] T) wkn (reflect Δ' T (v z))))
 reify {θ = θ} Δ' (Π T) M = Λ (reify ({!!} , neut-candidate) T {!!}) -- Yep, M needs to allow all larger thingies
