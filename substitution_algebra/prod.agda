module prod where

postulate
 bO : Set

data O : Set where
 ⊤ : O
 _⊗_ : O -> O -> O
 ▹ : bO -> O

postulate
 var : O -> O -> Set

data Zero : Set where

record One : Set where

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

mutual
 data neut : O -> O -> Set where
  v∘ : ∀ {Γ T S} -> var Γ T -> neut S Γ -> neut S T
  id : ∀ {Γ} -> neut Γ Γ
  π1∘ : ∀ {Γ T S} -> neut Γ (T ⊗ S) -> neut Γ T
  π2∘ : ∀ {Γ T S} -> neut Γ (T ⊗ S) -> neut Γ S
 data norm : O -> O -> Set where
  ▹ : ∀ {Γ B} -> neut Γ (▹ B) -> norm Γ (▹ B)
  <_,_> : ∀ {Γ T S} -> norm Γ T -> norm Γ S -> norm Γ (T ⊗ S)
  ! : ∀ {Γ} -> norm Γ ⊤

mutual
 data _⟹_ : O -> O -> Set where
  v : ∀ {A B} -> var A B -> A ⟹ B
  <_,_> : ∀ {Γ T S} -> Γ ⟶ T -> Γ ⟶ S -> Γ ⟹ (T ⊗ S)
  πl : ∀ {T S} -> (T ⊗ S) ⟹ T
  πr : ∀ {T S} -> (T ⊗ S) ⟹ S
  ! : ∀ {T} -> T ⟹ ⊤
 data _⟶_ : O -> O -> Set where
  id : ∀ {A} -> A ⟶ A
  _·_ : ∀ {A B C} -> (f : B ⟹ C) -> (fs : A ⟶ B) -> (A ⟶ C)

[_] : ∀ {A B} -> A ⟹ B -> A ⟶ B
[ t ] = t · id

_∘_ : ∀ {A B C} -> (B ⟶ C) -> (A ⟶ B) -> (A ⟶ C)
id ∘ f = f
(g · gs) ∘ f = g · (gs ∘ f) 
{-  _·_ : ∀ {A B C} -> (B ⟶ C) -> (A ⟹ B) -> (A ⟶ C)

[_] : ∀ {A B} -> A ⟹ B -> A ⟶ B
[ t ] = id · t

_∘_ : ∀ {A B C} -> (B ⟶ C) -> (A ⟶ B) -> (A ⟶ C)
f ∘ id = f
f ∘ (gs · g) = (f ∘ gs) · g -}

comp : ∀ {A B C} -> neut B C -> neut A B -> neut A C
comp (v∘ u f) g = v∘ u (comp f g)
comp id g = g
comp (π1∘ f) g = π1∘ (comp f g)
comp (π2∘ f) g = π2∘ (comp f g)

{-
foo : ∀ {Γ B} -> Γ ⟶ ▹ B -> neut Γ (▹ B)
foo id = id
foo (f · g) with foo f
foo (f · (v y)) | w = comp w (v∘ y id)
foo (f · < y , y' >) | w = {!!}
foo (f · πl) | w = comp w (π1∘ id)
foo (f · πr) | w = comp w (π2∘ id)
foo (f · !) | w = {!!}

sub : ∀ {A B C} -> neut B C -> A ⟶ B -> neut A C
sub (v∘ u f) s = v∘ u (sub f s)
sub id s = {!!}
sub (π1∘ f) s = π1∘ (sub f s)
sub (π2∘ f) s = π2∘ (sub f s)

cp : ∀ A B C -> B ⟶ C -> norm A B -> norm A C
cp A B ⊤ t s = !
cp A B (C1 ⊗ C2) t s = < cp A B C1 ([ πl ] ∘ t) s , cp A B C2 ([ πr ] ∘ t) s >
cp A B (▹ y) t s = ▹ {!!}

mutual
 cp2 : ∀ A B C -> norm B C -> A ⟶ B -> norm A C
 cp2 A B ⊤ t s = !
 cp2 A B (C1 ⊗ C2) < f , g > s = < (cp2 A B C1 f s) , (cp2 A B C2 g s) >
 cp2 A B (▹ y) (▹ y') s = ▹ {!!}

 sub2 : ∀ {A B C} -> neut (▹ B) C -> A ⟶ ▹ B -> neut A C
 sub2 (v∘ y y') s = {!!}
 sub2 {A} {B} {.(▹ B)} id s with cp2 A (▹ B) (▹ B) (▹ id) s
 sub2 {A} {B} {.(▹ B)} id s | ▹ y = y
 sub2 (π1∘ y) s = {!!}
 sub2 (π2∘ y) s = {!!}

sub1 : ∀ A B C -> neut B C -> A ⟹ B -> norm A C
sub1 A B C (v∘ y y') s = {!!}
sub1 A .C C id (v y) = {!!}
sub1 A .(T ⊗ S) .(T ⊗ S) id (<_,_> {.A} {T} {S} y y') = < {!!} , {!!} >
sub1 .(C ⊗ S) .C C id (πl {.C} {S}) = {!!}
sub1 .(T ⊗ C) .C C id (πr {T}) = {!!}
sub1 A .⊤ .⊤ id ! = {!!}
sub1 A B C (π1∘ y) s = {!!}
sub1 A B C (π2∘ y) s = {!!}

cp3 : ∀ A B C -> norm B C -> A ⟹ B -> norm A C
cp3 A B ⊤ t s = !
cp3 A B (y ⊗ y') < f , g > s = < (cp3 A B y f s) , cp3 A B y' g s >
cp3 A B (▹ y) (▹ y') s = ▹ {!!}

nb : ∀ Γ T -> Γ ⟶ T -> norm Γ T
nb .T T id = {!!}
nb Γ T (y · y') with nb _ _ y
... | w = {!!}

nbe : ∀ Γ T -> Γ ⟶ T -> norm Γ T
nbe Γ ⊤ t = !
nbe Γ (T ⊗ S) t = < (nbe Γ T ([ πl ] ∘ t)) , (nbe Γ S ([ πr ] ∘ t)) >
nbe .(▹ B) (▹ B) id = ▹ id
nbe Γ (▹ B) f = {!!}

cp4 : ∀ A B C -> norm B C -> norm A B -> norm A C
cp4 A B ⊤ t s = !
cp4 A B (y ⊗ y') < y0 , y1 > s = < (cp4 A B y y0 s) , (cp4 A B y' y1 s) >
cp4 A B (▹ y) (▹ y') s = {!!}

cp5 : ∀ A B C -> neut B C -> norm A B -> neut A C
cp5 A B C (v∘ y y') s = {!!}
cp5 A .C C id s = {!!}
cp5 A B C (π1∘ y) s = {!!}
cp5 A B C (π2∘ y) s = {!!} -}

-- hereditary substition? neut in spine form?

η-exp : ∀ {A} B -> neut A B -> norm A B
η-exp ⊤ t = !
η-exp (y ⊗ y') t = < η-exp y (π1∘ t) , η-exp y' (π2∘ t) >
η-exp (▹ y) t = ▹ t

cp3 : ∀ A B C -> neut B C -> norm A B -> neut A C
cp3 A B C (v∘ y y') s = {!!}
cp3 A .C C id s = {!!}
cp3 A B C (π1∘ y) s = {!!}
cp3 A B C (π2∘ y) s = {!!}

cp4 : ∀ A B C -> norm B C -> norm A B -> norm A C
cp4 A B .(▹ B') (▹ {.B} {B'} y) s = {!!} -- cp3 A B (▹ B') y s
cp4 A B .(T ⊗ S) (<_,_> {.B} {T} {S} y y') s = < (cp4 A B T y s) , (cp4 A B S y' s) >
cp4 A B .⊤ ! s = !

ev : ∀ {A B C} -> B ⟶ C -> norm A B -> norm A C
ev id s = s
ev (v y · fs) s with ev fs s
... | w = {!!}
ev (< y , y' > · fs) s = < (ev (y ∘ fs) s) , ev (y' ∘ fs) s >
ev (πl · fs) s with ev fs s
ev (πl · fs) s | < y , y' > = y
ev (πr · fs) s with ev fs s
ev (πr · fs) s | < y , y' > = y'
ev (! · fs) s = !


ev2 : ∀ {A B C} -> B ⟹ C -> norm A B -> norm A C
ev2 (v y) s = {!!}
ev2 < y , y' > s = < {!!} , {!!} >
ev2 πl < y , y' > = y
ev2 πr < y , y' > = y'
ev2 ! s = !