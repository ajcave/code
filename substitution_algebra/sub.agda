module sub where

postulate
 bO : Set

data O : Set where
 zero : O
 _⊕_ : bO -> O -> O

_+_ : O -> O -> O
zero + B = B
(A ⊕ As) + B = A ⊕ (As + B)

postulate
 var : O -> O -> Set

mutual
 data _⟹_ : O -> O -> Set where
  v : ∀ {A B} -> var A B -> A ⟹ B
  [_,_] : ∀ {A B C} -> A ⟶ C -> B ⟶ C -> (A + B) ⟹ C
  inl : ∀ {A} {B} -> A ⟹ (A + B)
  inr : ∀ {B} {A} -> B ⟹ (A + B)
  ! : ∀ {A} -> zero ⟹ A
 data _⟶_ : O -> O -> Set where
  id : ∀ {A} -> A ⟶ A
  _∘_ : ∀ {A B C} -> (B ⟹ C) -> (A ⟶ B) -> (A ⟶ C) 

infixr 40 _∘_
infixr 40 _◇_

_◇_ : ∀ {A B C} -> (B ⟶ C) -> (A ⟶ B) -> (A ⟶ C)
id ◇ g = g
(f ∘ fs) ◇ g = f ∘ (fs ◇ g)

<_> : ∀ {A B} -> (A ⟹ B) -> (A ⟶ B)
< f > = f ∘ id

data _≡_ {A : Set} (x : A) : A -> Set where
 refl : x ≡ x

data _≡₁_ {A : Set₁} (x : A) : A -> Set where
 refl : x ≡₁ x

data _≡'_ {A : Set} (x : A) : {B : Set} -> B -> Set where
 refl : x ≡' x

≅⇒≡ : ∀ {A B} {x : A} {y : B} → x ≡' y → A ≡₁ B
≅⇒≡ refl = refl

data ⊥ : Set where

¬ : Set -> Set
¬ A = A -> ⊥

-- Oh, right, we need to say that you can only η expand where it doesn't introduce a beta redex...
mutual
 data _↝_ : ∀ {A B} -> A ⟶ B -> A ⟶ B -> Set where
  βl : ∀ {A B C} (f : A ⟶ C) (g : B ⟶ C) -> < [ f , g ] > ◇ < inl {A} {B} > ↝ f
  βr : ∀ {A B C} (f : A ⟶ C) (g : B ⟶ C) -> < [ f , g ] > ◇ < inr {B} {A} > ↝ g
  !init : ∀ {A} (f : zero ⟶ A) -> ¬ (A ≡ zero) -> ¬ (f ≡ < ! >) -> f ↝ < ! >
  !zero : ∀ (f : zero ⟶ zero) -> ¬ (f ≡ id) -> f ↝ id
  η : ∀ {A B C} (f : (A + B) ⟶ C) -> f ↝ < [ f ◇ < inl {A} {B} > , f ◇ < inr {B} {A} > ] >
 
data ctx : O -> O -> O -> O -> Set where
 concat : ∀ {A B C D E F} (i : C ⟶ D) (C : ctx B C E F) (h : A ⟶ B) -> ctx A D E F
 caseL : ∀ {A B C E F} -> (Cf : ctx A C E F) -> (g : B ⟶ C) -> ctx (A + B) C E F
 caseR : ∀ {A B C E F} -> (f : A ⟶ C) -> (Cg : ctx B C E F) -> ctx (A + B) C E F
 here : ∀ {A B} -> ctx A B A B

plug : ∀ {A B C D} -> ctx A B C D -> (C ⟶ D) -> (A ⟶ B)
plug (concat i C h) j = i ◇ plug C j ◇ h
plug (caseL Cf g) j = < [ plug Cf j , g ] >
plug (caseR f Cg) j = < [ f , plug Cg j ] >
plug here j = j

composeIdL : ∀ {A B} {f : B ⟶ A} {g : A ⟶ B} -> f ◇ g ≡ id -> f ≡' (id {A})
composeIdL {f = id} r = refl
composeIdL {f = f ∘ fs} ()

plugId : ∀ {A C D} (Ct : ctx A A C D) {f : C ⟶ D} -> plug Ct f ≡ id -> f ≡' id {D}
plugId (concat i C0 h) r = {!!}
plugId (caseL Cf g) ()
plugId (caseR f Cg) ()
plugId here refl = {!refl!}

data _⇾_ : ∀ {A B} -> A ⟶ B -> A ⟶ B -> Set where
 context : ∀ {A B C D} {Ct : ctx A D B C} {f g : B ⟶ C} -> (f ↝ g) -> plug Ct f ⇾ plug Ct g

-- Strongly normalizing
data sn : ∀ {A B} -> A ⟶ B -> Set where
 sni : ∀ {A B} {f : A ⟶ B} -> (∀ {g} -> f ⇾ g -> sn g) -> sn f

{-
idDoesntStep : ∀ {A} {C : Set} {f g : A ⟶ A} -> f ↝ g -> f ≡ id -> C
idDoesntStep (βl f g) ()
idDoesntStep (βr f g) ()
idDoesntStep (!init .id y _) refl with y refl
... | ()
idDoesntStep (!zero f y) x with y x
... | ()
idDoesntStep (η f) ()

idDoesntStep' : ∀ {A} {C : Set} {f g : A ⟶ A} -> f ⇾ g -> f ≡ id -> C
idDoesntStep' {C = C} (context y) eq = {!!} -}


-- Oh, use an eq_dep, not a heterogeneous equality. Specific to ⟶.

-- Need some sort of contextual recursion pattern
-- Maybe weak normalization is easier?
{-allSn : ∀ {A B} {f g : A ⟶ B} -> (f ⇾ g) -> sn g
allSn (context (βl g g')) = {!!}
allSn (context (βr f g)) = {!!}
allSn (context (!init f y q)) = {!!}
allSn (context (!zero f y)) = {!!}
allSn (context (η f)) = {!!} -}
 
  

 
