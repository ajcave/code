Set Implicit Arguments.
Inductive Ctx (A : Set) : Set :=
 | nil : Ctx A
 | snoc : Ctx A -> A -> Ctx A.

Inductive Var {A : Set} : Ctx A -> A -> Set :=
 | top : forall {G T}, Var (snoc G T) T
 | pop : forall {G T S}, Var G T -> Var (snoc G S) T
 .

Inductive Tp : Set :=
 | Nat : Tp
 | Prod : Tp -> Tp -> Tp
 | Arr : Tp -> Tp -> Tp
.

Inductive Tm (G : Ctx Tp) : Tp -> Set :=
 | var : forall {T}, Var G T -> Tm G T
 | pair : forall {T S}, Tm G T -> Tm G S -> Tm G (Prod T S)
 | fst : forall {T S}, Tm G (Prod T S) -> Tm G T
 | snd : forall {T S}, Tm G (Prod T S) -> Tm G S
 | zero : Tm G Nat
 | succ : Tm G Nat -> Tm G Nat
 | iter : forall {C}, Tm (snoc G C) C -> Tm G C -> Tm G Nat -> Tm G C
.