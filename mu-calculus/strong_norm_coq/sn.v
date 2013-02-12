Set Implicit Arguments.
Inductive ctx (A : Type) : Type :=
 | nil : ctx A
 | snoc : ctx A -> A -> ctx A.
Implicit Arguments nil [A].

Inductive var (A : Type) : ctx A -> A -> Type :=
 | top : forall G T, var (snoc G T) T
 | pop : forall G T S, var G T -> var (snoc G S) T.
Implicit Arguments top [A G T].
Implicit Arguments pop [A G T S].

Open Scope type_scope.
Fixpoint gsub (A : Type) (G : ctx A) (F : A -> Type) : Type :=
match G with
| nil => unit
| snoc G' T => (gsub G' F) * (F T)
end.

Fixpoint glookup (A : Type) (G : ctx A) (F : A -> Type) T (x : var G T) : gsub G F -> F T :=
match x in var G T return gsub G F -> F T with
| top G' T' => fun s => snd s
| pop G' T' S' y => fun s => glookup F y (fst s)
end.

Fixpoint gmap (A : Type) (G : ctx A) (F1 F2 : A -> Type) (f : forall T, F1 T -> F2 T) : gsub G F1 -> gsub G F2 :=
match G return gsub G F1 -> gsub G F2 with
| nil => fun s => s
| snoc G' T => fun s => pair (gmap G' F1 F2 f (fst s)) (f T (snd s))
end.

Definition vsub (A : Type) (G G' : ctx A) := gsub G (var G').

Definition wknvsub (A : Type) (G G' : ctx A) T (s : vsub G G') : vsub G (snoc G' T) :=
gmap G (var G') (var (snoc G' T)) (fun T x => pop x) s.

Definition extvsub (A : Type) (G G' : ctx A) T (s : vsub G G') : vsub (snoc G T) (snoc G' T) :=
pair (wknvsub G G' T s) top.

Fixpoint idvsub (A : Type) (G : ctx A) : vsub G G :=
match G return vsub G G with
| nil => tt
| snoc G' T => extvsub G' G' T (idvsub G')
end.

Definition weakening_vsub (A : Type) (G : ctx A) T : vsub G (snoc G T) :=
wknvsub G G T (idvsub G).

Inductive sort : Type :=
 | type : sort.

Inductive functor (D : ctx sort) : Set :=
 | fv : forall T, var D T -> functor D
 | arrow : functor nil -> functor D -> functor D
 | times : functor D -> functor D -> functor D
 | plus : functor D -> functor D -> functor D
 | mu : functor (snoc D type) -> functor D
 | nu : functor (snoc D type) -> functor D.

Fixpoint app_vsub D D' (F : functor D) (s : vsub D D') : functor D' :=
match F with
| fv _ x => fv (glookup (var _) x s)
| arrow A F' => arrow A (app_vsub D' F' s)
| times F G => times (app_vsub D' F s) (app_vsub D' G s)
| plus F G => plus (app_vsub D' F s) (app_vsub D' G s)
| mu F => mu (app_vsub _ F (extvsub D D' type s))
| nu F => nu (app_vsub _ F (extvsub D D' type s))
end.

Definition fsub (D D' : ctx sort) := gsub D (fun _ => functor D').

Definition wknfsub (G G' : ctx sort) T (s : fsub G G') : fsub G (snoc G' T) :=
gmap G (fun _ => functor G') (fun _ => functor (snoc G' T)) (fun _ F => app_vsub _ F (weakening_vsub G' T)) s.

Definition extfsub (G G' : ctx sort) T (s : fsub G G') : fsub (snoc G T) (snoc G' T) :=
pair (wknfsub G G' T s) (fv (@top sort G' T)).

Fixpoint idfsub (G : ctx sort) : fsub G G :=
match G return fsub G G with
| nil => tt
| snoc G' T => extfsub G' G' T (idfsub G')
end.

Fixpoint app_fsub D D' (F : functor D) (s : fsub D D') : functor D' :=
match F with
| fv _ x => glookup _ x s
| arrow A F' => arrow A (app_fsub D' F' s)
| times F G => times (app_fsub D' F s) (app_fsub D' G s)
| plus F G => plus (app_fsub D' F s) (app_fsub D' G s)
| mu F => mu (app_fsub _ F (extfsub D D' type s))
| nu F => nu (app_fsub _ F (extfsub D D' type s))
end.

Definition single_fsub D T F : fsub (snoc D T) D := pair (idfsub D) F.

Definition app_fsub1 D T (F : functor (snoc D T)) (G : functor D) : functor D :=
app_fsub D F (single_fsub T G).

Definition tp := functor nil.

Inductive tm (G : ctx tp) : tp -> Set :=
 | v : forall T, var G T -> tm G T
 | lam : forall T S, tm (snoc G T) S -> tm G (arrow T S)
 | app : forall T S, tm G (arrow T S) -> tm G T -> tm G S
 | pair : forall T S, tm G T -> tm G S -> tm G (times T S)
 | fst : forall T S, tm G (times T S) -> tm G T
 | snd : forall T S, tm G (times T S) -> tm G S
 | inl : forall S T, tm G T -> tm G (plus T S)
 | inr : forall T S, tm G S -> tm G (plus T S)
 | case : forall T S C, tm G (plus T S) -> tm (snoc G T) C -> tm (snoc G S) C -> tm G C
 | inj : forall F, tm G (app_fsub1 F (mu F)) -> tm G (mu F)
 | rec : forall F C, tm G (mu F) -> tm (snoc nil (app_fsub1 F C)) C -> tm G C
 | out : forall F, tm G (nu F) -> tm G (app_fsub1 F (nu F))
 | corec : forall F C, tm G C -> tm (snoc nil C) (app_fsub1 F C) -> tm G (nu F)
.

(* Gotta define map... *)

Inductive step (G : ctx tp) : forall (T : tp), tm G T -> tm G T -> Prop :=
| step_lam : forall T S (t1 t2 : tm (snoc G T) S), @step (snoc G T) S t1 t2 -> step (lam t1) (lam t2)
| step_appl : forall T S (t1 t2 : tm G (arrow T S)) t3, step t1 t2 -> step (app t1 t3) (app t2 t3)
| step_appr : forall T S (t1 : tm G (arrow T S)) (t2 t3 : tm G T), step t2 t3 -> step (app t1 t2) (app t1 t3)
| step_pairl : forall T S (t1 t1' : tm G T) (t2 : tm G S), step t1 t1' -> step (pair t1 t2) (pair t1' t2)
| step_pairr : forall T S (t1 : tm G T) (t2 t2' : tm G S), step t2 t2' -> step (pair t1 t2) (pair t1 t2')
| step_fst : forall T S (t t' : tm G (times T S)), step t t' -> step (fst t) (fst t')
| step_snd : forall T S (t t' : tm G (times T S)), step t t' -> step (snd t) (snd t')
| step_inl : forall T S (t t' : tm G T), step t t' -> step (inl S t) (inl S t')
| step_inr : forall T S (t t' : tm G S), step t t' -> step (inr T t) (inr T t')
| step_case : forall T S C (t t' : tm G (plus T S)) (t1 : tm (snoc G T) C) t2, step t t' -> step (case t t1 t2) (case t' t1 t2)
| step_case1 : forall T S C (t : tm G (plus T S)) (t1 t1' : tm (snoc G T) C) t2, @step _ _ t1 t1' -> step (case t t1 t2) (case t t1' t2)
| step_case2 : forall T S C (t : tm G (plus T S)) (t1 : tm (snoc G T) C) t2 t2', @step _ _ t2 t2' -> step (case t t1 t2) (case t t1 t2')
| step_inj : forall F (t t' : tm G (app_fsub1 F (mu F))), step t t' -> step (inj F t) (inj F t')
| step_rec1 : forall F C (t1 t1' : tm G (mu F)) (t2 : tm (snoc nil (app_fsub1 F C)) C), step t1 t1' -> step (rec t1 t2) (rec t1' t2)
| step_rec2 : forall F C (t1 : tm G (mu F)) (t2 t2' : tm (snoc nil (app_fsub1 F C)) C), @step _ _ t2 t2' -> step (rec t1 t2) (rec t1 t2')
| step_out : forall F (t t' : tm G (nu F)), step t t' -> step (out t) (out t')
| step_corec1 : forall F C (t1 t1' : tm G C) (t2 : tm (snoc nil C) (app_fsub1 F C)), step t1 t1' -> step (corec F t1 t2) (corec F t1' t2)
| step_corec2 : forall F C (t1 : tm G C) (t2 t2' : tm (snoc nil C) (app_fsub1 F C)), @step _ _ t2 t2' -> step (corec F t1 t2) (corec F t1 t2')

.
