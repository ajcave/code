module nbe-correctness-sigma where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

record Σ (A : Set) (B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

postulate
 funext : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g
 funext-imp : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> _≡_ { {x : A} -> B x} (λ {x} -> f x) (λ {x} -> g x)

cong-app1 : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> f ≡ g -> (x : A) -> f x ≡ g x
cong-app1 refl x = refl

cong-app : ∀ {A B : Set} {f g : A -> B} -> f ≡ g -> {x y : A} -> x ≡ y -> f x ≡ g y
cong-app refl refl = refl 

cong : ∀ {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl


cong1/2 : ∀ {A B C : Set} (f : A -> B -> C) -> {x y : A} -> x ≡ y -> (z : B) -> f x z ≡ f y z
cong1/2 f refl z = refl 

cong2 : ∀ {A B C : Set} (f : A -> B -> C) -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> f x z ≡ f y w
cong2 f refl refl = refl 

eq-ind : ∀ {A} (P : A -> Set) -> {x y : A} -> x ≡ y -> P x -> P y
eq-ind P refl t = t 

eq-indr : ∀ {A} (P : A -> Set) -> {x y : A} -> x ≡ y -> P y -> P x
eq-indr P refl t = t 

eq-ind2 : ∀ {A B} (P : A -> B -> Set) -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> P x z -> P y w
eq-ind2 P refl refl t = t

eq-sub1 : ∀ {A C} (P : A -> C) {t} -> {x y : A} -> x ≡ y -> P y ≡ t -> P x ≡ t
eq-sub1 P refl p = p 

eq-sub2 : ∀ {A B C} (P : A -> B -> C) {t} -> {x y : A} -> x ≡ y -> {z w : B} -> z ≡ w -> P y w ≡ t -> P x z ≡ t
eq-sub2 P refl refl p = p

trans : ∀ {A} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

sym : ∀ {A} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

cong2dep : ∀ {A : Set} {B : A -> Set} {C : Set} (f : (x : A) -> B x -> C) {x y} (p : x ≡ y) -> {z : B x} {w : B y} -> z ≡ eq-indr B p w -> f x z ≡ f y w 
cong2dep f refl refl = refl

uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) -> p ≡ q
uip refl refl = refl

record Unit : Set where
 constructor tt

postulate
 atomic_tp : Set

data tp : Set where
 atom : (A : atomic_tp) -> tp
 _⇝_ : (T : tp) -> (S : tp) -> tp

data ctx : Set where
 ⊡ : ctx
 _,_ : (Γ : ctx) -> (T : tp) -> ctx

data var : (Γ : ctx) -> (T : tp) -> Set where
 z : ∀ {Γ T} -> var (Γ , T) T
 s : ∀ {Γ T S} -> var Γ T -> var (Γ , S) T

vsubst : ctx -> ctx -> Set 
vsubst Δ Γ = ∀ {U} -> var Δ U -> var Γ U

mutual 
 data rtm (Γ : ctx) : (T : tp) -> Set where
  v : ∀ {T} -> var Γ T -> rtm Γ T
  _·_ : ∀ {T S} -> rtm Γ (T ⇝ S) -> ntm Γ T -> rtm Γ S
 data ntm (Γ : ctx) : (T : tp) -> Set where
  ƛ : ∀ {T S} -> ntm (Γ , T) S -> ntm Γ (T ⇝ S)
  neut : ∀ {A} -> rtm Γ (atom A) -> ntm Γ (atom A)

_∘_ : ∀ {Δ Γ ψ} -> vsubst Δ Γ -> vsubst ψ Δ -> vsubst ψ Γ
(σ1 ∘ σ2) x = σ1 (σ2 x)

ext : ∀ {Γ Δ T} -> vsubst Γ Δ -> vsubst (Γ , T) (Δ , T)
ext σ z = z
ext σ (s y) = s (σ y)

mutual
 rappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> rtm Δ S -> rtm Γ S
 rappSubst σ (v y) = v (σ y)
 rappSubst σ (R · N) = rappSubst σ R · nappSubst σ N
 nappSubst : ∀ {Γ Δ S} -> vsubst Δ Γ -> ntm Δ S -> ntm Γ S 
 nappSubst σ (ƛ M) = ƛ (nappSubst (ext σ) M)
 nappSubst σ (neut R) = neut (rappSubst σ R)

id : ∀ {Γ} -> vsubst Γ Γ
id x = x

mutual
 sem : (Γ : ctx) -> (T : tp) -> Set
 sem Γ (atom A) = rtm Γ (atom A)
 sem Γ (T ⇝ S) = Σ (∀ Δ -> (σ : vsubst Γ Δ) -> sem Δ T → sem Δ S)
   (λ f -> ∀ Δ (σ : vsubst Γ Δ) (x : sem Δ T) Δ' (σ' : vsubst Δ Δ') -> appSubst S σ' (f Δ σ x) ≡ f Δ' (σ' ∘ σ) (appSubst T σ' x))

 appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
 appSubst (atom A) σ M = rappSubst σ M
 appSubst (T ⇝ S) σ M = (λ Δ σ' x → Σ.fst M _ (σ' ∘ σ) x) ,
   λ Δ σ' x Δ' σ0 → Σ.snd M Δ (σ' ∘ σ) x Δ' σ0

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

{-mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = N
 reflect {T ⇝ S} N = (λ Δ σ x → reflect ((rappSubst σ N) · (reify x))) , (λ Δ σ x Δ' σ' → {!!})

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = neut M
 reify {T ⇝ S} (M , pf) = ƛ (reify (M _ wkn (reflect (v z)))) -}

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)

_◦_ : ∀ {Γ1 Γ2 Γ3} -> vsubst Γ2 Γ3 -> subst Γ1 Γ2 -> subst Γ1 Γ3
(σ ◦ θ) = λ x ->  appSubst _ σ (θ x)

blah : ∀ {Γ1 Γ2 Γ3 T} (σ : vsubst Γ2 Γ3) (θ : subst Γ1 Γ2) (t : sem Γ2 T) {U} (x : var (Γ1 , T) U) -> (σ ◦ (extend θ t)) x ≡ (extend (σ ◦ θ) (appSubst _ σ t)) x
blah σ θ t z = refl
blah σ θ t (s y) = refl

extend-blagh : ∀ {Γ1 Γ2 T} {θ1 θ2 : subst Γ1 Γ2} -> _≡_ {subst Γ1 Γ2} θ1 θ2 -> ∀ (t : sem Γ2 T) {U} (x : var (Γ1 , T) U) -> extend θ1 t x ≡ extend θ2 t x
extend-blagh refl t x = refl

appFunct : ∀ {T Γ1 Γ2 Γ3} (σ' : vsubst Γ2 Γ3) (σ : vsubst Γ1 Γ2) (t : sem Γ1 T) -> appSubst T σ' (appSubst T σ t) ≡ appSubst T (σ' ∘ σ) t
appFunct {atom A} σ' σ t = {!!}
appFunct {T ⇝ S} σ' σ t = refl

appFunct2 : ∀ {Γ0 Γ1 Γ2 Γ3} (σ' : vsubst Γ2 Γ3) (σ : vsubst Γ1 Γ2) (θ : subst Γ0 Γ1) -> _≡_ {subst Γ0 Γ3} (σ' ◦ (σ ◦ θ)) ((σ' ∘ σ) ◦ θ)
appFunct2 σ' σ θ = funext-imp (λ x → funext (λ x' → appFunct σ' σ (θ x')))


-- Traditional nbe
-- This is taking tm Γ T into a Yoneda-like Hom space
mutual
 eval : ∀ {Γ Δ T} -> tm Γ T -> subst Γ Δ -> sem Δ T
 eval (v y) θ = θ y
 eval (M · N) θ = Σ.fst (eval M θ) _ id (eval N θ)
 eval (ƛ M) θ = (λ Δ σ x → eval M (extend (σ ◦ θ) x)) , (λ Δ σ x Δ' σ' → trans (grar M (extend (σ ◦ θ) x) σ') (cong (eval M) (funext-imp (λ U → funext (λ x' → trans (blah σ' _ x x') (extend-blagh (appFunct2 σ' σ θ) _ x'))))))
 
 grar : ∀ {Γ T} (M : tm Γ T) {Δ} (θ : subst Γ Δ) {Δ'} (σ : vsubst Δ Δ') -> appSubst T σ (eval M θ) ≡ eval M (σ ◦ θ)
 grar (v y) θ σ = refl
 grar (M · N) θ σ = trans (Σ.snd (eval M θ) _ id (eval N θ) _ σ) (trans (cong-app1 (cong-app1 (cong-app1 (cong Σ.fst (grar M θ σ)) _) id) (appSubst _ σ (eval N θ))) (cong (λ α → Σ.fst (eval M (σ ◦ θ)) _ id α) (grar N θ σ)))
 grar (ƛ M) θ σ = cong2dep _,_ (funext (λ Δ → funext (λ σ' → funext (λ x → cong (eval M) (funext-imp (λ x' → funext (λ x0 → extend-blagh (sym (appFunct2 _ _ _)) x x0))))))) (funext (λ x → funext (λ x' → funext (λ x0 → funext (λ x1 → funext (λ x2 → uip _ _))))))

{-nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval (λ x → reflect (v x)) M) -}

{-
[_]v : ∀ {Γ1 Γ2 T} (σ : vsubst Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_]v σ (v y) = v (σ y)
[_]v σ (M · N) = [ σ ]v M · [ σ ]v N
[_]v σ (ƛ M) = ƛ ([ ext σ ]v M)

sub : (Γ1 Γ2 : ctx) -> Set
sub Γ1 Γ2 = ∀ {T} -> var Γ1 T -> tm Γ2 T

sub-ext : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> sub (Γ1 , T) (Γ2 , T)
sub-ext σ z = v z
sub-ext σ (s y) = [ s ]v (σ y)

[_] : ∀ {Γ1 Γ2 T} (σ : sub Γ1 Γ2) -> (M : tm Γ1 T) -> tm Γ2 T
[_] σ (v y) = σ y
[_] σ (M · N) = [ σ ] M · [ σ ] N
[_] σ (ƛ M) = ƛ ([ sub-ext σ ] M)

_,,_ : ∀ {Γ1 Γ2 T} -> sub Γ1 Γ2 -> tm Γ2 T -> sub (Γ1 , T) Γ2
(σ ,, M) z = M
(σ ,, M) (s y) = σ y

-- Why not just use an explicit substitution calculus?
data _≈_ {Γ} : ∀ {T} -> tm Γ T -> tm Γ T -> Set where
 v : ∀ {T} (x : var Γ T) -> (v x) ≈ (v x)
 _·_ : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} {N1 N2 : tm Γ T} -> M1 ≈ M2 -> N1 ≈ N2 -> (M1 · N1) ≈ (M2 · N2)
 ƛ : ∀ {T S} {M1 M2 : tm (Γ , T) S} -> M1 ≈ M2 -> (ƛ M1) ≈ (ƛ M2)
 β : ∀ {T S} (M : tm (Γ , T) S) (N : tm Γ T) -> ((ƛ M) · N) ≈ [ v ,, N ] M
 η : ∀ {T S} (M : tm Γ (T ⇝ S)) -> M ≈ (ƛ ([ (λ x -> (v (s x))) ] M · (v z)))
-- η2 : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} -> ([ (λ x -> v (s x)) ] M1 · (v z)) ≈ ([ (λ x -> v (s x)) ] M2 · (v z)) -> M1 ≈ M2

_•_ : ∀ {Γ1 Γ2 Γ3} (σ1 : subst Γ2 Γ3) (σ2 : sub Γ1 Γ2) -> subst Γ1 Γ3
(σ1 • σ2) x = eval σ1 (σ2 x) 

blah : ∀ {Γ1 Γ2 Γ3 T} (σ : subst Γ2 Γ3) (s : sem Γ3 T) (σ' : sub Γ1 Γ2) {U} (x : var (Γ1 , T) U)
 -> (((extend σ s) • (sub-ext σ')) x) ≡ (extend (σ • σ') s x)
blah σ s' σ' z = refl
blah σ s' σ' (s y) = {!!} --need to do comp for [_]v :(

blah' : ∀ {Γ1 Γ2 Γ3 T} (σ : subst Γ2 Γ3) (s : sem Γ3 T) (σ' : sub Γ1 Γ2)
 -> _≡_ {subst (Γ1 , T) Γ3} ((extend σ s) • (sub-ext σ')) (extend (σ • σ') s)
blah' σ s' σ' = funext-imp (λ U → funext (λ x → blah σ s' σ' x))

-- this is functoriality (wrap the M up in extensionality/an equivalence relation)
comp : ∀ {Γ3 T Γ1 Γ2} (σ1 : sub Γ1 Γ2) (σ2 : subst Γ2 Γ3) (M : tm Γ1 T) -> (eval σ2 ([ σ1 ] M)) ≡ (eval (σ2 • σ1) M)
comp σ1 σ2 (v y) = refl
comp {Γ3} σ1 σ2 (M · N) = eq-sub2 (λ x y → x Γ3 id y) (comp σ1 σ2 M) (comp σ1 σ2 N) refl
comp {Γ3} {.(T ⇝ S)} σ1 σ2 (ƛ {T} {S} M) = funext (λ Δ' → funext (λ σ → funext (λ s' → trans (f (λ {U} -> σ {U}) s') (cong1/2 eval (trans (g (λ {U} -> σ {U}) s') {!just need to reassociate here!}) M))))
 where f : ∀ {Δ'} (σ : vsubst Γ3 Δ') (s' : sem Δ' T) -> eval (extend (σ ◦ σ2) s') ([ sub-ext σ1 ] M)
                                                      ≡ eval (extend (σ ◦ σ2) s' • sub-ext σ1) M
       f σ s' = comp (sub-ext σ1) (extend (σ ◦ σ2) s') M
       g :  ∀ {Δ'} (σ : vsubst Γ3 Δ') (s' : sem Δ' T) -> _≡_ {subst (_ , T) Δ'} ((extend (σ ◦ σ2) s') • (sub-ext σ1)) (extend ((σ ◦ σ2) • σ1) s')
       g σ s' = blah' ((λ {U} -> σ) ◦ σ2) s' σ1

Pr : ∀ {Γ} T (t : sem Γ T) -> Set 
Pr (atom A) t = Unit
Pr (T ⇝ S) f = (Δ : _) (σ : vsubst _ Δ) (t : sem Δ T) -> Pr T t -> Pr S (f Δ σ t) *
 ((Δ' : _) (ρ : vsubst Δ Δ') → appSubst _ ρ (f Δ σ t) ≡ f Δ' (ρ ∘ σ) (appSubst _ ρ t))

niceSubst : (Γ Δ : ctx) (θ : subst Γ Δ) -> Set
niceSubst Γ Δ θ = ∀ {U} x -> Pr U (θ x)

niceExtend : ∀ {Γ Δ T} {θ : subst Γ Δ} (ρ : niceSubst Γ Δ θ) {M : sem Δ T} -> Pr T M -> niceSubst (Γ , T) Δ (extend θ M)
niceExtend ρ t z = t
niceExtend ρ t (s y) = ρ y

PrClosed : ∀ {Γ Δ} U (σ : vsubst Γ Δ) {M : sem Γ U} -> Pr U M -> Pr U (appSubst U σ M)
PrClosed (atom A) σ t = tt
PrClosed {Γ} {Δ} (T ⇝ S) σ f = λ Δ' σ' t' x → _*_.fst (f _ _ _ x) , (λ Δ'' ρ → _*_.snd (f _ _ _ x) Δ'' ρ)

_◦n_ : ∀ {Γ1 Γ2 Γ3} (σ : vsubst Γ2 Γ3) {θ : subst Γ1 Γ2} -> niceSubst Γ1 Γ2 θ -> niceSubst Γ1 Γ3 (σ ◦ θ)
(σ ◦n ρ) x = PrClosed _ σ (ρ x)

grar1 : ∀ {Γ1 Γ2 Γ3} T (M : tm Γ1 T) (θ : subst Γ1 Γ2) (θnice : niceSubst Γ1 Γ2 θ) (σ' : vsubst Γ2 Γ3)
 -> Pr T (eval θ M) -> (appSubst T σ' (eval θ M)) ≡ (eval (σ' ◦ θ) M)
grar1 (atom A) M θ ρ σ' t = {!!}
grar1 (T ⇝ S) M θ ρ σ' t = funext (λ Δ → funext (λ σ'' → funext (λ x → {!!})))

mutual
 nice : ∀ {Γ Δ T} (M : tm Γ T) (θ : subst Γ Δ) (θnice : niceSubst Γ Δ θ) -> Pr T (eval θ M)
 nice (v y) θ θnice = θnice y
 nice (M · N) θ θnice = _*_.fst (nice M θ θnice _ _ _ (nice N θ θnice))
 nice {Γ} {Δ1} {T ⇝ S} (ƛ M) θ θnice = λ Δ σ t x → (nice M (extend (σ ◦ θ) t) (niceExtend (σ ◦n θnice) x))
  , λ Δ' ρ → {!nice M (extend (σ ◦ θ) t)!}
  where f : ∀ Δ (σ : vsubst Δ1 Δ) (t : sem Δ T) (x : Pr T t) Δ' (ρ : vsubst Δ Δ') -> {!!}
        f Δ σ t x Δ' ρ with (nice M (extend (σ ◦ θ) t) (niceExtend (σ ◦n θnice) x))
        ... | q = {!!}


-- pretty sure this is false because σ can have all kinds of crazy functions in it
-- [σ'] (f id a1) != f σ' ([σ']a1) for arbitrary f!
grar : ∀ {Γ1 Γ2 Γ3} T (M : tm Γ1 T) (θ : subst Γ1 Γ2) (σ' : vsubst Γ2 Γ3)
 -> (appSubst T σ' (eval θ M)) ≡ (eval (σ' ◦ θ) M)
grar T (v y) θ σ' = refl
grar T (M · N) θ σ' with grar _ M θ σ' | grar _ N θ σ'
... | q1 | q2 = {!!} --trans {!!} (cong-app (cong-app1 (cong-app1 (grar _ M θ σ') _) id) (grar _ N θ σ'))
grar .(T ⇝ S) (ƛ {T} {S} M) θ σ' = {!easy!}

sem-η : ∀ {Γ Δ T S} (M1 : tm Γ (T ⇝ S)) (σ : subst Γ Δ) Δ' (σ' : vsubst Δ Δ') (s' : sem Δ' T)
  -> (eval σ M1 Δ' σ' s') ≡ (eval (extend (σ' ◦ σ) s') ([ (λ x -> v (s x)) ] M1) Δ' id s')
sem-η M1 σ Δ' σ' s' = trans (cong-app1 (cong-app1 (cong-app1 (grar _ M1 σ σ') _) id) s') (sym (eq-sub1 (λ x' → x' Δ' id s') (comp (λ y → v (s y)) (extend (_ ◦ σ) s') M1) refl))

sem-β : ∀ {Γ Δ T S} (M : tm (Γ , T) S) (N : tm Γ T) (σ : subst Γ Δ) -> (eval (extend (id ◦ σ) (eval σ N)) M) ≡ (eval σ ([ v ,, N ] M))
sem-β M N σ = trans (cong1/2 eval (funext-imp (λ T → funext (λ x → {!easy(?)!}))) M) (sym (comp (v ,, N) σ M))

-- If we're feeling ambitious we could try to do this without functional extensionality by defining an equivalence
-- relation by induction on the type
soundness : ∀ {Γ Δ T} {M1 M2 : tm Γ T} (σ : subst Γ Δ) -> M1 ≈ M2 -> (eval σ M1) ≡ (eval σ M2)
soundness σ (v x) = refl
soundness {Γ} {Δ} σ (M · N) = cong-app (cong-app1 (cong-app1 (soundness σ M) Δ) id) (soundness σ N)
soundness σ (ƛ M) = funext (λ Δ → funext (λ wkn → funext (λ x → soundness _ M)))
soundness σ (β M N) = sem-β M N σ
soundness {Γ} {Δ} {T ⇝ S} {M1} σ (η .M1) = funext (λ Δ' → funext (λ σ' → funext (λ s' → sem-η M1 σ Δ' _ s')))

soundness' : ∀ {Γ T} {M1 M2 : tm Γ T} -> M1 ≈ M2 -> (nbe M1) ≡ (nbe M2)
soundness' H = cong reify (soundness _ H)

GL : (Γ : ctx) (T : tp) (t : sem Γ T) -> Set
GL Γ (atom A) t = Unit
GL Γ (T ⇝ S) t = (p : sem Γ T) → GL Γ T p → (GL Γ S (t _ id p) * ((napp (reify t) (reify p)) ≡ (reify (t _ id p))))

-}