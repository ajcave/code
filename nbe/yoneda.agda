{-# OPTIONS --type-in-type #-}
module yoneda where

data _≡_ {A : Set}(a : A) : {A' : Set} → A' → Set where
 refl : a ≡ a

sym : ∀{A A' : Set}{a : A}{a' : A'} → a ≡ a' → a' ≡ a
sym refl = refl

trans : ∀{A A' A'' : Set}{a : A}{a' : A'}{a'' : A''} →
       a ≡ a' → a' ≡ a'' → a ≡ a''
trans refl p = p

funnycong : ∀{A}{B : A → Set}{C : Set}{a a' : A} → a ≡ a' →
           {b : B a} → {b' : B a'} →
           (f : (a : A) → .(B a) → C) → f a b ≡ f a' b'
funnycong refl f = refl

cong : {A B : Set}(f : A → B){a a' : A} → a ≡ a' → f a ≡ f a'
cong f refl = refl

fcong : ∀{A}{B : A → Set}{f f' : (x : A) → B x}(a : A) → f ≡ f' → f a ≡ f' a
fcong a refl = refl

ifcong : ∀{A}{B : A → Set}{f f' : {x : A} → B x}(a : A) →
        _≡_ { {x : A} → B x} f { {x : A} → B x} f' → f {a} ≡ f' {a}
ifcong a refl = refl

ir : ∀{A A'}{a : A}{a' : A'}{p q : a ≡ a'} → p ≡ q
ir {p = refl} {q = refl} = refl

fixtypes : ∀{A A' : Set}{a a' : A}{a'' a''' : A'}
          {p : a ≡ a'}{q : a'' ≡ a'''} → a ≡ a'' → a' ≡ a''' → p ≡ q
fixtypes refl refl = ir

postulate ext : {X Y : Set}{f g : X → Y} → (∀ x → f x ≡ g x) → f ≡ g

postulate iext : {A : Set}{B B' : A → Set}{f : ∀ {a} → B a}{g : ∀{a} → B' a} →
                (∀ a → f {a} ≡ g {a}) →
                _≡_ { {a : A} → B a} f { {a : A} → B' a} g

id : {X : Set} → X → X
id = λ x → x

_◦_ : {X Y Z : Set} → (Y → Z) → (X → Y) → X → Z
f ◦ g = λ x → f (g x)

--Ok, now we define a category as follows:

record Cat : Set where
 field Obj  : Set
       Hom  : Obj → Obj → Set
       iden : ∀{X} → Hom X X
       comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
       idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≡ f
       idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≡ f
       ass  : ∀{W X Y Z}{f : Hom Y Z}{g : Hom X Y}{h : Hom W X} →
              comp (comp f g) h ≡ comp f (comp g h)
open Cat

--Now, Yoneda's embedding says that we can view morphism in C as the following polymorphic function:

Y : ∀{C A B} → Hom C A B → (∀ Z → Hom C B Z → Hom C A Z)
Y {C} f = λ Z g → comp C g f

--and we can convert back again:

Y-1 : ∀{C A B} → (∀ Z → Hom C B Z → Hom C A Z) → Hom C A B
Y-1 {C}{A}{B} α = α B (iden C)

--Given any category we can transform it like so:

CatY : Cat → Cat
CatY C = record {
 Obj  = Obj C;
 Hom  = λ X Y → ∀ Z → Hom C Y Z → Hom C X Z;
 iden = λ X → id;
 comp = λ α β Z → β Z ◦ α Z;
 idl  = refl;
 idr  = refl;
 ass  = refl}

{-Notice we get the identities, and associativity for free.

We're sort of done unless we'd like to actually prove the isomorphism between the homsets in these categories (Yoneda's lemma).

If we actually want to prove Yoneda's lemma we need to consider natural transformations instead of just polymorphic functions and some more machinery:

Functors: -}

{-record Fun (C D : Cat) : Set where
 field OMap  : Obj C → Obj D
       HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
       fid   : ∀{X} → HMap (iden C {X}) ≡ iden D {OMap X}
       fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} →
               HMap (comp C f g) ≡ comp D (HMap f) (HMap g)
open Fun

--The category of sets:

Sets : Cat
Sets = record{
 Obj  = Set;
 Hom  = λ X Y → X → Y;
 iden = id;
 comp = λ f g → f ◦ g;
 idl  = refl;
 idr  = refl;
 ass  = refl}

--Notice the laws come from free in Sets.

--Hom functors:

HomF : {C : Cat} → (A : Obj C) → Fun C Sets
HomF {C} A = record {
 OMap  = Hom C A;
 HMap  = comp C;
 fid   = ext λ _ → idl C;
 fcomp = ext λ _ → ass C}

--Natural transformations:

record NatT {C D}(F G : Fun C D) : Set where
 field cmp : ∀ {X} → Hom D (OMap F X) (OMap G X)
       nat : ∀{X Y}{f : Hom C X Y} →
             comp D (HMap G f) cmp ≡ comp D cmp (HMap F f)

open NatT

--we also define this handy principle which says that two NatTs are equal if their components are equal:

NatTEq : {C D : Cat}{F G : Fun C D}{α β : NatT F G} →
        (λ {X : Obj C} → cmp α {X}) ≡ (λ {X : Obj C} → cmp β {X}) → α ≡ β
NatTEq {C}{D}{F}{G} {α} {β} p = funnycong
 {∀ {X} → Hom D (OMap F X) (OMap G X)}
 {λ cmp → ∀{X Y}{f : Hom C X Y} →
   comp D (HMap G f) cmp ≡ comp D cmp (HMap F f)}
 {NatT F G}
 p
 {λ{X}{Y}{f} → nat α {X}{Y}{f}}{λ{X}{Y}{f} → nat β {X}{Y}{f}}
 λ x y → record{cmp = x;nat = y}

--Now we can redefine Y and Y-1 properly:

Y : ∀{C A B} → Hom C A B → NatT {C} (HomF B) (HomF A)
Y {C} f = record {
 cmp = λ g → comp C g f;
 nat = ext λ h → sym (ass C)}

Y-1 : ∀{C A B} → (NatT {C} (HomF B) (HomF A)) → Hom C A B
Y-1 {C} α = cmp α (iden C)

--and prove Yoneda's lemma:

Yoneda : ∀ C A B → Iso (Hom C A B) (NatT {C} (HomF B) (HomF A))
Yoneda C A B = record {
 fun = Y {C};
 inv = Y-1 {C};
 left = ext λ α → NatTEq (iext λ Z → ext λ g → trans (fcong (iden C) (nat α))
                                                     (cong (cmp α) (idr C)));
 right = ext λ x → idl C}

{-Ok, I'm cheating a little, we should also prove that it is natural in A and B. Here we just proved it is an isomorphism.

I would like to get associativity and the identities for free for composition of natural transformations, I can't have this in general as it composition uses composition in the target category of the functors which may not come for free. But, if the target category is Sets (if we have natural transformations between pre sheaves, which hom functors are, then it is) then we do get this stuff for free:
-}

idNat : ∀{C}{F : Fun C Sets} → NatT F F
idNat {C}{F} = record {
 cmp = id;
 nat = refl}

compNat : ∀{C}{F G H : Fun C Sets} → NatT G H → NatT F G → NatT F H
compNat {C}{F}{G}{H} α β = record {
 cmp = cmp α ◦ cmp β;
 nat = λ{X}{Y}{f} → ext λ Z → trans (fcong (cmp β Z) (nat α {f = f}))
                                    (cong (cmp α) (fcong Z (nat β {f = f})))}

idlNat : ∀{C}{F G : Fun C Sets}{α : NatT F G} → compNat idNat α ≡ α
idlNat {C} = refl

idrNat : ∀{C}{F G : Fun C Sets}{α : NatT F G} → compNat α idNat ≡ α
idrNat {C}{D} = refl

assNat : ∀{C}{E F G H : Fun C Sets}{α : NatT G H}{β : NatT F G}{η : NatT E F}
        → compNat (compNat α β) η ≡ compNat α (compNat β η)
assNat {C}{D} = refl

--I can fold this all up into a category CatY where the laws hold definitionally:

CatY : Cat → Cat
CatY C = record {
 Obj  = Obj C;
 Hom  = λ A B → NatT {C} (HomF B) (HomF A);
 iden = idNat;
 comp = λ α β → compNat β α;
 idl  = refl;
 idr  = refl;
 ass  = refl} -}