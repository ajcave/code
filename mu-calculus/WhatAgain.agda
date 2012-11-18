module WhatAgain where

record One : Set where
  constructor <>
open One public

record Sig (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sig public

uc : {S : Set}{T : S -> Set}{P : Sig S T -> Set} ->
     ((s : S)(t : T s) -> P (s , t)) ->
     (x : Sig S T) -> P x
uc p (s , t) = p s t

Uc : {S : Set}{T : S -> Set}{P : Sig S T -> Set1} ->
     ((s : S)(t : T s) -> P (s , t)) ->
     (x : Sig S T) -> P x
Uc p (s , t) = p s t

data Zero : Set where

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

_/_ : {S T : Set}{P : S + T -> Set} ->
      ((s : S) -> P (inl s)) ->
      ((t : T) -> P (inr t)) ->
      (x : S + T) -> P x
(f / g) (inl s) = f s
(f / g) (inr t) = g t

_/1_ : {S T : Set}{P : S + T -> Set1} ->
      ((s : S) -> P (inl s)) ->
      ((t : T) -> P (inr t)) ->
      (x : S + T) -> P x
(f /1 g) (inl s) = f s
(f /1 g) (inr t) = g t


{- FIRST ATTEMPT -}
{-
data Desc (I : Set) : Set1 where
  var : (i : I) -> Desc I
  sig pi : (S : Set)(T : S -> Desc I) -> Desc I
  one : Desc I
  mu : (O : Set)(F : O -> Desc (I + O))(o : O) -> Desc I

[_] : {I : Set} -> Desc I -> (I -> Set) -> Set
data Mu {I O : Set}(F : O -> Desc (I + O))(X : I -> Set)(o : O) : Set

[ var i ] X = X i
[ sig S T ] X = Sig S \ s -> [ T s ] X
[ pi S T ] X = (s : S) -> [ T s ] X
[ one ] X = One
[ mu O F o ] X = Mu F X o

data Mu {I} {O} F X where
  <_> : [ F o ] (X /1 Mu F X) -> Mu F X o

All : {I : Set}(D : Desc I)(X : I -> Set) -> [ D ] X -> Desc (Sig I X)
All (var i) X x = var (i , x)
All (sig S T) X (s , xs) = All (T s) X xs
All (pi S T) X f = pi S \ s -> All (T s) X (f s)
All one X xs = one
All {I} (mu O F o) X < xrs > =
  mu (Sig O \ o -> [ F o ] (X /1 Mu F X))
    \ { (o , xrs) -> {!!} } (o , xrs) 
-}

{-
Goal: Desc (Sig I X + Sig O (λ o' → [ F o' ] (X /1 Mu F X)))

xrs : [ F o ] (X /1 Mu F X)
o   : O
xrs : [ F o ] (X /1 Mu F X)
X   : I → Set
o   : O
F   : O → Desc (I + O)
O   : Set
I   : Set
-}

{- ABORT MISSION: can get Sig (I + O) blah, but not (Sig I bl) + (Sig O ah)
-}

data Cx : Set1 where
  [] : Cx
  _,_ : Cx -> Set -> Cx

data Env : Cx -> Set1 where
  [] : Env []
  _,_ : {G : Cx}{I : Set}(g : Env G)(X : I -> Set) -> Env (G , I)

data _<:_ (I : Set) : Cx -> Set1 where
  top : {G : Cx} -> I <: (G , I)
  pop : {G : Cx}{J : Set}(n : I <: G) -> I <: (G , J)

Var : {G : Cx}{I : Set} -> Env G -> I <: G -> I -> Set
Var [] () _
Var (g , X) top i = X i
Var (g , X) (pop n) i = Var g n i

data Desc (G : Cx) : Set1 where
  var : {I : Set}(n : I <: G)(i : I) -> Desc G
  sig pi : (S : Set)(T : S -> Desc G) -> Desc G
  one : Desc G
  mu : (O : Set)(F : O -> Desc (G , O))(o : O) -> Desc G

[_] : {G : Cx} -> Desc G -> Env G -> Set
data Mu {G : Cx}{O : Set}(F : O -> Desc (G , O))(g : Env G)(o : O) : Set

[ var n i ] g = Var g n i
[ sig S T ] g = Sig S \ s -> [ T s ] g
[ pi S T ] g = (s : S) -> [ T s ] g
[ one ] g = One
[ mu O F o ] g = Mu F g o

data Mu {G} {O} F g o where
  <_> : [ F o ] (g , Mu F g) -> Mu F g o

out : {G : Cx}{O : Set}{F : O -> Desc (G , O)}{g : Env G}{o : O} ->
      Mu F g o -> [ F o ] (g , Mu F g)
out < t > = t

CxS : (G : Cx)(g : Env G) -> Cx
CxS [] [] = []
CxS (G , I) (g , X) = CxS G g , Sig I X

varg : {G : Cx}{I : Set}(g : Env G)(n : I <: G) -> Sig I (Var g n) <: CxS G g
varg [] ()
varg (g , X) top = top
varg (g , X) (pop n) = pop (varg g n)

All : {G : Cx}(D : Desc G)(g : Env G) -> [ D ] g -> Desc (CxS G g)
All (var n i) g x = var (varg g n) (i , x)
All (sig S T) g (s , xs) = All (T s) g xs
All (pi S T) g f = pi S \ s -> All (T s) g (f s)
All one g xs = one
All {I} (mu O F o) g xs =
  mu (Sig O (Mu F g))
     (\ ox -> All (F (fst ox)) (g , Mu F g) (out (snd ox)))
     (o , xs)

{- SECOND ATTEMPT -}

_=>1_ : {G : Cx}(g : Env G)(h : Env (CxS G g)) -> Set
[] =>1 [] = One
(g , X) =>1 (h , Y) = Sig (g =>1 h) \ _ -> forall i (x : X i) -> Y (i , x)

apply1 : {G : Cx}(g : Env G)(h : Env (CxS G g))(m : g =>1 h)
        {I : Set}(n : I <: G)(i : I)(x : Var g n i) ->
        Var h (varg g n) (i , x)
apply1 [] h ms () i x
apply1 (g , X) (h , Y) (ms , m) top i x = m i x
apply1 (g , X) (h , Y) (ms , m) (pop n) i x = apply1 g h ms n i x

all1 : {G : Cx}(D : Desc G)(g : Env G) ->
      (h : Env (CxS G g)) -> g =>1 h ->
      (xs : [ D ] g) -> [ All D g xs ] h
all1 (var n i) g h ms x = apply1 g h ms n i x
all1 (sig S T) g h ms (s , xs) = all1 (T s) g h ms xs
all1 (pi S T) g h ms f = \ s -> all1 (T s) g h ms (f s)
all1 one g h ms _ = _
all1 (mu O F o) g h ms < xrs > =
  < all1 (F o) (g , Mu F g)
     (h , Mu (\ ox -> All (F (fst ox)) (g , Mu F g) (out (snd ox))) h)
     (ms , (\ o -> all1 (mu O F o) g h ms))
     xrs  >
{- Termination checker doesn't know that the recursive call to all
   will only be used on smaller things. -}

{- ABORT MISSION -}

{- What's an induction method? -}

IMeth : {G : Cx}{O : Set}(F : O -> Desc (G , O))(g : Env G)
        (h : Env (CxS G g))
        (P : Sig O (Mu F g) -> Set) -> O -> Set
IMeth F g h P o = (xrs : [ F o ] (g , Mu F g)) ->
                [ All (F o) (g , Mu F g) xrs ] (h , P) ->
                P (o , < xrs >)

{-
induction : {G : Cx}{O : Set}{F : O -> Desc (G , O)}
            {g : Env G}{h : Env (CxS G g)}(ms : g => h)
            (P : Sig O (Mu F g) -> Set)
            (m : (o : O) -> IMeth F g h P o).
            (o : O)(x : Mu F g o) -> P (o , x)
-}


data _=>_ : {G : Cx}(g : Env G)(h : Env (CxS G g)) -> Set1 where
  [] : [] => []
  _,_ : {G : Cx}{g : Env G}{h : Env (CxS G g)}
        {I : Set}{X : I -> Set}{Y : Sig I X -> Set}
        (ms : g => h)
        (m :  (ix : Sig I X) -> Y ix) ->
        (g , X) => (h , Y)
  alg : {G : Cx}{g : Env G}{h : Env (CxS G g)}{O : Set}
         (ms : g => h)
         (F : O -> Desc (G , O)) ->
         {P : Sig O (Mu F g) -> Set}  ->
         (m : (o : O) -> IMeth F g h P o) ->
         (g , Mu F g) => (h , P)
  _!_ : {G : Cx}{g : Env G}{h : Env (CxS G g)}{O : Set}
       (ms : g => h)
       (F : O -> Desc (G , O)) ->
       (g , Mu F g) => (h , Mu (\ ox -> All (F (fst ox)) (g , Mu F g) (out (snd ox))) h)


apply : {G : Cx}(g : Env G)(h : Env (CxS G g))(m : g => h)
        {I : Set}(n : I <: G)(i : I)(x : Var g n i) ->
        Var h (varg g n) (i , x)
all : {G : Cx}(D : Desc G)(g : Env G) ->
      (h : Env (CxS G g)) -> g => h ->
      (xs : [ D ] g) -> [ All D g xs ] h

apply [] h ms () i x
apply (g , X) (h , Y) (ms , m) top i x = m (i , x)
apply (g , X) (h , Y) (ms , m) (pop n) i x = apply g h ms n i x
apply (g , .(Mu F g)) (h , P) (alg ms F m) top o < xrs >
  = m o xrs (all (F o) (g , _) (h , _) (alg ms F m) xrs)
apply (g , .(Mu F g)) (h , P) (alg ms F m) (pop n) i x = apply g h ms n i x
apply (g , ._) (h , ._) (ms ! F) top o x = all (mu _ F o) g h ms x 
apply (g , ._) (h , ._) (ms ! F) (pop n) i x = apply g h ms n i x

all (var n i) g h ms x = apply g h ms n i x
all (sig S T) g h ms (s , xs) = all (T s) g h ms xs
all (pi S T) g h ms f = \ s -> all (T s) g h ms (f s)
all one g h ms _ = _
all (mu O F o) g h ms < xrs > =
  < all (F o) (g , _) (h , _) (ms ! F) xrs > 

induction : {G : Cx}{O : Set}{F : O -> Desc (G , O)}
            {g : Env G}{h : Env (CxS G g)}(ms : g => h)
            (P : Sig O (Mu F g) -> Set)
            (m : (o : O) -> IMeth F g h P o)
            (o : O)(x : Mu F g o) -> P (o , x)
induction {F = F} ms P m = apply _ _ (alg ms F m) top

Two : Set
Two = One + One


k : {S : Set}{T : Set} -> T -> S -> T
k t s = t

k1 : {S : Set}{T : Set1} -> T -> S -> T
k1 t s = t

Nat : {G : Cx} -> One -> Desc (G , One)
Nat _ = sig Two (k1 one /1 k1 (var top _))

zero : {G : Cx}{g : Env G} -> Mu Nat g _
zero = < inl _ , _ >

suc : {G : Cx}{g : Env G} -> Mu Nat g _ -> Mu Nat g _
suc n = < inr _ , n >

Dull : {G : Cx}(g : Env G) -> Env (CxS G g)
Dull [] = []
Dull (g , X) = Dull g , k1 One

dull : {G : Cx}{g : Env G} -> g => Dull g
dull {._} {[]} = []
dull {._} {g , X} = dull , _

natElim : {G : Cx}{g : Env G}
          (P : Mu Nat g _ -> Set)
          (mz : P zero)
          (ms : (m : Mu Nat g _) -> P m -> P (suc m))
          (n : Mu Nat g _) -> P n
natElim P mz ms = induction dull (\ { (_ , m) -> P m })
   ((k (uc ((\ _ _ _ -> mz) / (\ _ -> ms))))) _

plus : {G : Cx}{g : Env G} -> Mu Nat g _ -> Mu Nat g _ -> Mu Nat g _
plus {g = g} x y = natElim (\ _ -> Mu Nat g _) y (\ _ -> suc) x

four : {G : Cx}{g : Env G} -> Mu Nat g _
four = plus (suc (suc zero)) (suc (suc zero))
