module nbe-correctness where

record _*_ (A B : Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

postulate
 funext : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> f ≡ g

funext-imp : ∀ {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (∀ x -> f x ≡ g x) -> _≡_ { {x : A} -> B x} (λ {x} -> f x) (λ {x} -> g x)
funext-imp H = {!!}

cong-app1 : ∀ {A} {B : A -> Set} {f g : (x : A) -> B x} -> f ≡ g -> (x : A) -> f x ≡ g x
cong-app1 refl x = refl

cong-app : ∀ {A B : Set} {f g : A -> B} -> f ≡ g -> {x y : A} -> x ≡ y -> f x ≡ g y
cong-app refl refl = refl 

cong : ∀ {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong1/2 : ∀ {A B C : Set} (f : A -> B -> C) -> {x y : A} -> x ≡ y -> (z : B) -> f x z ≡ f y z
cong1/2 f refl z = refl 

eq-ind : ∀ {A} (P : A -> Set) -> {x y : A} -> x ≡ y -> P x -> P y
eq-ind P refl t = t 

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


sem : (Γ : ctx) -> (T : tp) -> Set
sem Γ (atom A) = rtm Γ (atom A)
sem Γ (T ⇝ S) = ∀ Δ -> vsubst Γ Δ -> sem Δ T → sem Δ S

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

appSubst : ∀ {Γ Δ} S -> vsubst Δ Γ -> sem Δ S -> sem Γ S
appSubst (atom A) σ M = rappSubst σ M
appSubst (T ⇝ S) σ M = λ _ σ' s → M _ (σ' ∘ σ) s

wkn : ∀ {Γ T} -> vsubst Γ (Γ , T)
wkn x = s x

mutual
 reflect : ∀ {T Γ} -> rtm Γ T -> sem Γ T
 reflect {atom A} N = N
 reflect {T ⇝ S} N = λ _ σ s → reflect (rappSubst σ N · reify s)

 reify : ∀ {T Γ} -> sem Γ T -> ntm Γ T
 reify {atom A} M = neut M
 reify {T ⇝ S} M = ƛ (reify (M _ wkn (reflect (v z))))

subst : ctx -> ctx -> Set
subst Γ Δ = ∀ {T} -> var Γ T -> sem Δ T

extend : ∀ {Γ Δ T} -> subst Γ Δ -> sem Δ T -> subst (Γ , T) Δ
extend θ M z = M
extend θ M (s y) = θ y

-- Here we have "hereditary substitution"
mutual
 srSubst : ∀ {Γ Δ T} -> subst Γ Δ -> rtm Γ T -> sem Δ T
 srSubst θ (v y) = θ y
 srSubst θ (R · N) = srSubst θ R _ id (sSubst θ N)

 sSubst : ∀ {Γ Δ T} -> subst Γ Δ -> ntm Γ T -> sem Δ T
 sSubst θ (ƛ M) = λ Δ σ s → sSubst (extend (λ x → appSubst _ σ (θ x)) s) M
 sSubst θ (neut y) = srSubst θ y

nSubst : ctx -> ctx -> Set
nSubst Γ Δ = ∀ {S} -> var Γ S -> ntm Δ S
cut : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Γ T -> ntm Δ T
cut θ t = reify (sSubst (λ x → sSubst (λ x' → reflect (v x')) (θ x)) t)

nv : ∀ {Γ T} -> var Γ T -> ntm Γ T
nv x = reify (reflect (v x))

nExtend : ∀ {Γ Δ T} -> nSubst Γ Δ -> ntm Δ T -> nSubst (Γ , T) Δ
nExtend θ N z = N
nExtend θ N (s y) = θ y

nId : ∀ {Γ} -> nSubst Γ Γ
nId x = nv x

napp : ∀ {Γ T S} -> ntm Γ (T ⇝ S) -> ntm Γ T -> ntm Γ S
napp (ƛ N) M = cut (nExtend nId M) N

data tm (Γ : ctx) : (T : tp) -> Set where
 v : ∀ {T} -> var Γ T -> tm Γ T
 _·_ : ∀ {T S} -> tm Γ (T ⇝ S) -> tm Γ T -> tm Γ S
 ƛ : ∀ {T S} -> tm (Γ , T) S -> tm Γ (T ⇝ S)

complete : ∀ {Γ T} -> tm Γ T -> ntm Γ T
complete (v y) = nv y
complete (M · N) = napp (complete M) (complete N)
complete (ƛ M) = ƛ (complete M)

_◦_ : ∀ {Γ1 Γ2 Γ3} -> vsubst Γ2 Γ3 -> subst Γ1 Γ2 -> subst Γ1 Γ3
(σ ◦ θ) = λ x ->  appSubst _ σ (θ x)

-- Traditional nbe
eval : ∀ {Γ Δ T} -> subst Γ Δ -> tm Γ T -> sem Δ T
eval θ (v y) = θ y
eval θ (M · N) = eval θ M _ id (eval θ N)
eval θ (ƛ M) = λ _ σ s -> eval (extend (σ ◦ θ) s) M

nbe : ∀ {Γ T} -> tm Γ T -> ntm Γ T
nbe M = reify (eval (λ x → reflect (v x)) M)

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
 η2 : ∀ {T S} {M1 M2 : tm Γ (T ⇝ S)} -> ([ (λ x -> v (s x)) ] M1 · (v z)) ≈ ([ (λ x -> v (s x)) ] M2 · (v z)) -> M1 ≈ M2

_•_ : ∀ {Γ1 Γ2 Γ3} (σ1 : subst Γ2 Γ3) (σ2 : sub Γ1 Γ2) -> subst Γ1 Γ3
(σ1 • σ2) x = eval σ1 (σ2 x) 

-- this is functoriality (wrap the M up in extensionality/an equivalence relation)
comp : ∀ {Γ3 Γ1 Γ2 T} (σ1 : sub Γ1 Γ2) (σ2 : subst Γ2 Γ3) (M : tm Γ1 T) -> (eval σ2 ([ σ1 ] M)) ≡ (eval (λ x -> eval σ2 (σ1 x)) M)
comp σ1 σ2 (v y) = refl
comp {Γ3} σ1 σ2 (M · N) = eq-sub2 (λ x y → x Γ3 id y) (comp σ1 σ2 M) (comp σ1 σ2 N) refl
comp σ1 σ2 (ƛ M) with comp (sub-ext σ1) {!!} M
... | q = funext (λ Δ → funext (λ wkn → funext (λ x → {!!})))

appSubstApp : ∀ {Γ1 Γ2 Γ3 T S} (M : tm Γ1 (T ⇝ S)) (N : tm Γ1 T) (σ : subst Γ1 Γ2) (σ' : vsubst Γ2 Γ3)
 -> (appSubst S σ' (eval σ (M · N))) ≡ ((appSubst (T ⇝ S) σ' (eval σ M)) _ id (appSubst T σ' (eval σ N)))
appSubstApp (v y) N σ σ' = {!crap. the ones in sigma are unconstrained!}
appSubstApp (M · N1) N2 σ σ' = {!!}
appSubstApp (ƛ M) N σ σ' = {!!}

grar : ∀ {Γ1 Γ2 Γ3} T (M : tm Γ1 T) (σ : subst Γ1 Γ2) (σ' : vsubst Γ2 Γ3)
 -> (appSubst T σ' (eval σ M)) ≡ (eval (σ' ◦ σ) M)
grar T (v y) σ σ' = refl
grar T (M · N) σ σ' = trans (appSubstApp M N σ σ') (cong-app (cong-app1 (cong-app1 (grar _ M σ σ') _) id) (grar _ N σ σ'))
grar .(T ⇝ S) (ƛ {T} {S} M) σ σ' = {!easy!}

sem-funct : ∀ {Γ3 Γ1 Γ2 T S} (M : tm Γ1 (T ⇝ S)) (σ : subst Γ1 Γ2) (σ' : vsubst Γ2 Γ3) (s' : sem Γ3 T)
 -> (eval σ M Γ3 σ' s') ≡ (eval (σ' ◦ σ) M Γ3 id s')
sem-funct (v y) σ σ' s' = refl 
sem-funct {Γ3} (M · N) σ σ' s' = trans {!!} (cong-app1 (cong-app1 (cong-app1 (sem-funct M σ σ' (eval (σ' ◦ σ) N)) Γ3) id) s')
sem-funct (ƛ y) σ σ' s' = {!easy!}

sem-η : ∀ {Γ Δ T S} (M1 : tm Γ (T ⇝ S)) (σ : subst Γ Δ) Δ' (σ' : vsubst Δ Δ') (s' : sem Δ' T)
  -> (eval σ M1 Δ' σ' s') ≡ (eval (extend (σ' ◦ σ) s') ([ (λ x -> v (s x)) ] M1) Δ' id s')
sem-η M1 σ Δ' σ' s' = trans (sem-funct M1 σ σ' s') (sym (eq-sub1 (λ x' → x' Δ' id s') (comp (λ y → v (s y)) (extend (_ ◦ σ) s') M1) refl))

sem-β : ∀ {Γ Δ T S} (M : tm (Γ , T) S) (N : tm Γ T) (σ : subst Γ Δ) -> (eval (extend (id ◦ σ) (eval σ N)) M) ≡ (eval σ ([ v ,, N ] M))
sem-β M N σ = trans (cong1/2 eval (funext-imp (λ T → funext (λ x → {!easy(?)!}))) M) (sym (comp (v ,, N) σ M))

-- If we're feeling ambitious we could try to do this without functional extensionality by defining an equivalence
-- relation by induction on the type
soundness : ∀ {Γ Δ T} {M1 M2 : tm Γ T} (σ : subst Γ Δ) -> M1 ≈ M2 -> (eval σ M1) ≡ (eval σ M2)
soundness σ (v x) = refl
soundness σ (M · N) = eq-sub2 (λ x y → x _ _ y) (soundness σ M) (soundness σ N) refl
soundness σ (ƛ M) = funext (λ Δ → funext (λ wkn → funext (λ x → soundness _ M)))
soundness σ (β M N) = sem-β M N σ
soundness {Γ} {Δ} {T ⇝ S} {M1} σ (η .M1) = funext (λ Δ' → funext (λ σ' → funext (λ s' → sem-η M1 σ Δ' _ s')))
soundness {Γ} {Δ} {T ⇝ S} {M1} {M2} σ (η2 {.T} {.S} {.M1} {.M2} H) = funext (λ Δ' → funext (λ σ' → funext (λ s' → {!!})))
 where f : ∀ {Δ'} (σ' : vsubst Δ Δ') (s' : sem Δ' T) -> eval (extend (σ' ◦ σ) s')
                                                          ([ (λ {T'} x → v (s x)) ] M1) Δ' id s'
                                                          ≡
                                                          eval (extend (σ' ◦ σ) s')
                                                          ([ (λ {T'} x → v (s x)) ] M2) Δ' id s'
       f σ' s' = soundness (extend (σ' ◦ σ) s') H

soundness' : ∀ {Γ T} {M1 M2 : tm Γ T} -> M1 ≈ M2 -> (nbe M1) ≡ (nbe M2)
soundness' H = cong reify (soundness _ H)

GL : (Γ : ctx) (T : tp) (t : sem Γ T) -> Set
GL Γ (atom A) t = Unit
GL Γ (T ⇝ S) t = (p : sem Γ T) → GL Γ T p → (GL Γ S (t _ id p) * ((napp (reify t) (reify p)) ≡ (reify (t _ id p))))

