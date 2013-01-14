Set Implicit Arguments.

Open Scope type_scope.
Inductive Ctx (A : Set) : Set :=
 | nil : Ctx A
 | snoc : Ctx A -> A -> Ctx A.
Implicit Arguments nil [A].

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
 | pair' : forall {T S}, Tm G T -> Tm G S -> Tm G (Prod T S)
 | fst' : forall {T S}, Tm G (Prod T S) -> Tm G T
 | snd' : forall {T S}, Tm G (Prod T S) -> Tm G S
 | zero : Tm G Nat
 | succ : Tm G Nat -> Tm G Nat
 | iter : forall {C}, Tm (snoc G C) C -> Tm G C -> Tm G Nat -> Tm G C
 | lam : forall {T S}, Tm (snoc G T) S -> Tm G (Arr T S)
 | app : forall {T S}, Tm G (Arr T S) -> Tm G T -> Tm G S
.
Implicit Arguments zero [G].

Fixpoint Gsubst (R : Tp -> Set) (G : Ctx Tp) : Set := match G with
 | nil => unit
 | snoc G' T => (Gsubst R G') * (R T)
end.

Fixpoint gmap (R1 R2 : Tp -> Set) (f : forall T, R1 T -> R2 T) {G : Ctx Tp} : Gsubst R1 G -> Gsubst R2 G :=
match G as G return Gsubst R1 G -> Gsubst R2 G with
 | nil => fun s => tt
 | snoc G' T => fun s => pair (gmap _ _ f (fst s)) (f T (snd s))
end.

Fixpoint lookup {G R T} (x : Var G T) : Gsubst R G -> R T :=
match x in Var G T return Gsubst R G -> R T with
 | top G T  => fun s => snd s
 | pop G T U y => fun s => lookup y (fst s)
end.

Definition VSubst (D G : Ctx Tp) : Set := Gsubst (Var D) G.

Definition SVextend {D G} T (s : VSubst D G) : VSubst (snoc D T) (snoc G T) :=
pair (gmap (Var D) (Var (snoc D T)) (fun _ => pop) s) top.

Fixpoint idvsubst (G : Ctx Tp) : VSubst G G :=
match G as G return VSubst G G with
| nil => tt
| snoc G' T => SVextend T (idvsubst G')
end.

Definition wknvsubst (G : Ctx Tp) (T : Tp) : VSubst (snoc G T) G :=
gmap (Var G) (Var (snoc G T)) (fun _ => pop) (idvsubst G).

Fixpoint vsubst {G D T} (t : Tm G T) (s : VSubst D G) : Tm D T :=
match t in Tm _ T return Tm D T with
 | var _ x => var (lookup x s)
 | pair' _ _ t1 t2 => pair' (vsubst t1 s) (vsubst t2 s)
 | fst' _ _ t1 => fst' (vsubst t1 s)
 | snd' _ _ t1 => snd' (vsubst t1 s)
 | zero => zero
 | succ t1 => succ (vsubst t1 s)
 | iter C f i n => iter (vsubst f (SVextend C s)) (vsubst i s) (vsubst n s)
 | lam _ _ t1 => lam (vsubst t1 (SVextend _ s))
 | app _ _ t1 t2 => app (vsubst t1 s) (vsubst t2 s)
end.

Definition Subst (D G : Ctx Tp) : Set := Gsubst (Tm D) G.

Definition Sextend {D G} T (s : Subst D G) : Subst (snoc D T) (snoc G T) :=
pair (gmap (Tm D) (Tm (snoc D T)) (fun _ t => vsubst t (wknvsubst D T)) s) (var top).

Fixpoint idsubst (G : Ctx Tp) : Subst G G :=
match G as G return Subst G G with
| nil => tt
| snoc G' T => Sextend T (idsubst G')
end.

Fixpoint subst {G D T} (t : Tm G T) (s : Subst D G) : Tm D T :=
match t in Tm _ T return Tm D T with
 | var _ x => lookup x s
 | pair' _ _ t1 t2 => pair' (subst t1 s) (subst t2 s)
 | fst' _ _ t1 => fst' (subst t1 s)
 | snd' _ _ t1 => snd' (subst t1 s)
 | zero => zero
 | succ t1 => succ (subst t1 s)
 | iter C f i n => iter (subst f (Sextend C s)) (subst i s) (subst n s)
 | lam _ _ t1 => lam (subst t1 (Sextend _ s))
 | app _ _ t1 t2 => app (subst t1 s) (subst t2 s)
end.

Definition topsubst {G T S} (t : Tm (snoc G S) T) (u : Tm G S) : Tm G T :=
subst t (pair (idsubst G) u).

Inductive Mstep {G} : forall {T}, Tm G T -> Tm G T -> Set :=
 | srefl : forall {T} {t : Tm G T}, Mstep t t
 | strans : forall {T} {t u v : Tm G T}, Mstep t u -> Mstep u v -> Mstep t v
 | spair : forall {T S} {t t' : Tm G T} {u u' : Tm G S},
           Mstep t t' -> Mstep u u' -> Mstep (pair' t u) (pair' t' u')
 | sfst : forall {T S} {t t' : Tm G (Prod T S)}, Mstep t t' -> Mstep (fst' t) (fst' t')
 | ssnd : forall {T S} {t t' : Tm G (Prod T S)}, Mstep t t' -> Mstep (snd' t) (snd' t')
 | ssucc : forall {t t'}, Mstep t t' -> Mstep (succ t) (succ t')
 | siter : forall {C} {t t' : Tm (snoc G C) C} {i i'} {n n'},
           @Mstep (snoc G C) C t t' -> Mstep i i' -> Mstep n n' -> Mstep (iter t i n) (iter t' i' n')
 | slam : forall {T S} {t t' : Tm (snoc G T) S}, @Mstep (snoc G T) S t t' -> Mstep (lam t) (lam t')
 | sapp : forall {T S} {t t' : Tm G (Arr T S)} {u u'}, Mstep t t' -> Mstep u u' -> Mstep (app t u) (app t' u')
 | beta_arr : forall {T S} {t : Tm (snoc G T) S} {u}, Mstep (app (lam t) u) (topsubst t u)
 | beta_prod1 : forall {T S} {t : Tm G T} {u : Tm G S}, Mstep (fst' (pair' t u)) t
 | beta_prod2 : forall {T S} {t : Tm G T} {u : Tm G S}, Mstep (snd' (pair' t u)) u
 | beta_nat1 : forall {C} {t : Tm (snoc G C) C} (i : Tm G C), Mstep (iter t i zero) i
 | beta_nat2 : forall {C} {t : Tm (snoc G C) C} (i : Tm G C) (n : Tm G Nat), Mstep (iter t i (succ n)) (topsubst t (iter t i n))
.


Definition inat : Set := forall (C : Set), (C -> C) -> C -> C.

Definition isucc (n : inat) : inat := fun C f i => f (n C f i).
Definition izero : inat := fun C f i => i.
Definition iiter {C : Set} (f : C -> C) (i : C) (n : inat) := n C f i.

Fixpoint SemT (T : Tp) : Set := match T with
 | Nat => inat
 | Prod U V => (SemT U) * (SemT V)
 | Arr U V => SemT U -> SemT V
end.

Fixpoint SemC (G : Ctx Tp) : Set := match G with
 | nil => unit
 | snoc G' U => (SemC G') * (SemT U)
end.

Fixpoint SemV {G T} (x : Var G T) : SemC G -> SemT T :=
match x in Var G T return SemC G -> SemT T with
 | top G T  => fun s => snd s
 | pop G T U y => fun s => SemV y (fst s)
end.

Fixpoint Sem {G T} (t : Tm G T) (s : SemC G) : SemT T :=
match t in Tm _ T return SemT T with
 | var _ x => SemV x s
 | pair' _ _ t1 t2 => pair (Sem t1 s) (Sem t2 s)
 | fst' _ _ t1 => fst (Sem t1 s)
 | snd' _ _ t1 => snd (Sem t1 s)
 | zero => izero
 | succ t1 => isucc (Sem t1 s)
 | iter C f i n => iiter (fun x => Sem f (pair s x)) (Sem i s) (Sem n s)
 | lam _ _ t1 => fun x => Sem t1 (pair s x)
 | app _ _ t1 t2 => Sem t1 s (Sem t2 s)
end.

Inductive Val : forall T, Tm nil T -> Set :=
 | vzero : Val zero
 | vsucc : forall n, Val n -> Val (succ n)
.

Fixpoint Red (T : Tp) : Tm nil T -> Set :=
match T as T return Tm nil T -> Set with
| Nat => fun t => { v : Tm nil Nat & (Mstep t v * Val v) }
| Arr U V => fun t => forall x, Red x -> Red (app t x)
| Prod U V => fun t => Red (fst' t) * Red (snd' t)
end.




