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
Implicit Arguments extvsub [ A G G' T ].

Fixpoint idvsub (A : Type) (G : ctx A) : vsub G G :=
match G return vsub G G with
| nil => tt
| snoc G' T => extvsub (idvsub G')
end.
Implicit Arguments idvsub [A G].

Definition weakening_vsub (A : Type) (G : ctx A) T : vsub G (snoc G T) :=
wknvsub G G T idvsub.

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
| mu F => mu (app_vsub _ F (extvsub s))
| nu F => nu (app_vsub _ F (extvsub s))
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
 | tv : forall T, var G T -> tm G T
 | tlam : forall T S, tm (snoc G T) S -> tm G (arrow T S)
 | tapp : forall T S, tm G (arrow T S) -> tm G T -> tm G S
 | tpair : forall T S, tm G T -> tm G S -> tm G (times T S)
 | tfst : forall T S, tm G (times T S) -> tm G T
 | tsnd : forall T S, tm G (times T S) -> tm G S
 | tinl : forall S T, tm G T -> tm G (plus T S)
 | tinr : forall T S, tm G S -> tm G (plus T S)
 | tcase : forall T S C, tm G (plus T S) -> tm (snoc G T) C -> tm (snoc G S) C -> tm G C
 | tinj : forall F, tm G (app_fsub1 F (mu F)) -> tm G (mu F)
 | trec : forall F C, tm G (mu F) -> tm (snoc nil (app_fsub1 F C)) C -> tm G C
 | tout : forall F, tm G (nu F) -> tm G (app_fsub1 F (nu F))
 | tcorec : forall F C, tm G C -> tm (snoc nil C) (app_fsub1 F C) -> tm G (nu F)
.

Fixpoint app_vsub_tm G G' T (t : tm G T) (s : vsub G G') : tm G' T :=
match t with
| tv T' x => tv (glookup (var G') x s)
| tlam T1 T2 t' => tlam (app_vsub_tm _ t' (extvsub s))
| tapp T1 T2 t1 t2 => tapp (app_vsub_tm _ t1 s) (app_vsub_tm _ t2 s)
| tpair T1 T2 t1 t2 => tpair (app_vsub_tm _ t1 s) (app_vsub_tm _ t2 s)
| tfst T1 T2 t1 => tfst (app_vsub_tm _ t1 s)
| tsnd T1 T2 t2 => tsnd (app_vsub_tm _ t2 s)
| tinl T1 T2 t1 => tinl T1 (app_vsub_tm _ t1 s)
| tinr T1 T2 t1 => tinr T1 (app_vsub_tm _ t1 s)
| tcase T1 T2 C t1 t2 t3 => tcase (app_vsub_tm _ t1 s) (app_vsub_tm _ t2 (extvsub s)) (app_vsub_tm _ t3 (extvsub s))
| tinj F t1 => tinj F (app_vsub_tm _ t1 s)
| trec F C t1 t2 => trec (app_vsub_tm _ t1 s) t2
| tout F t1 => tout (app_vsub_tm _ t1 s)
| tcorec F C t1 t2 => tcorec F (app_vsub_tm _ t1 s) t2
end.

Definition tsub (D D' : ctx tp) := gsub D (tm D').

Definition wkntsub (G G' : ctx tp) T (s : tsub G G') : tsub G (snoc G' T) :=
gmap G (tm G') (tm (snoc G' T)) (fun _ t => app_vsub_tm _ t (weakening_vsub G' T)) s.

Definition exttsub (G G' : ctx tp) T (s : tsub G G') : tsub (snoc G T) (snoc G' T) :=
pair (wkntsub G G' T s) (tv (@top _ G' T)).
Implicit Arguments exttsub [G G' T].

Fixpoint idtsub (G : ctx tp) : tsub G G :=
match G return tsub G G with
| nil => tt
| snoc G' T => exttsub (idtsub G')
end.
Implicit Arguments idtsub [G].

Fixpoint app_tsub D D' T (t : tm D T) (s : tsub D D') : tm D' T :=
match t with
| tv T' x => glookup _ x s
| tlam T1 T2 t' => tlam (app_tsub _ t' (exttsub s))
| tapp T1 T2 t1 t2 => tapp (app_tsub _ t1 s) (app_tsub _ t2 s)
| tpair T1 T2 t1 t2 => tpair (app_tsub _ t1 s) (app_tsub _ t2 s)
| tfst T1 T2 t1 => tfst (app_tsub _ t1 s)
| tsnd T1 T2 t2 => tsnd (app_tsub _ t2 s)
| tinl T1 T2 t1 => tinl T1 (app_tsub _ t1 s)
| tinr T1 T2 t1 => tinr T1 (app_tsub _ t1 s)
| tcase T1 T2 C t1 t2 t3 => tcase (app_tsub _ t1 s) (app_tsub _ t2 (exttsub s)) (app_tsub _ t3 (exttsub s))
| tinj F t1 => tinj F (app_tsub _ t1 s)
| trec F C t1 t2 => trec (app_tsub _ t1 s) t2
| tout F t1 => tout (app_tsub _ t1 s)
| tcorec F C t1 t2 => tcorec F (app_tsub _ t1 s) t2
end.

Definition single_tsub D T (t : tm D T)  : tsub (snoc D T) D := pair idtsub t.

Definition app_tsub1 D T S (t : tm (snoc D T) S) (t2 : tm D T) : tm D S :=
app_tsub _ t (single_tsub t2).
Implicit Arguments app_tsub1 [ D T S ].

(* Gotta define map... *)

Inductive step (G : ctx tp) : forall (T : tp), tm G T -> tm G T -> Prop :=
| step_lam : forall T S (t1 t2 : tm (snoc G T) S), @step (snoc G T) S t1 t2 -> step (tlam t1) (tlam t2)
| step_appl : forall T S (t1 t2 : tm G (arrow T S)) t3, step t1 t2 -> step (tapp t1 t3) (tapp t2 t3)
| step_appr : forall T S (t1 : tm G (arrow T S)) (t2 t3 : tm G T), step t2 t3 -> step (tapp t1 t2) (tapp t1 t3)
| step_pairl : forall T S (t1 t1' : tm G T) (t2 : tm G S), step t1 t1' -> step (tpair t1 t2) (tpair t1' t2)
| step_pairr : forall T S (t1 : tm G T) (t2 t2' : tm G S), step t2 t2' -> step (tpair t1 t2) (tpair t1 t2')
| step_fst : forall T S (t t' : tm G (times T S)), step t t' -> step (tfst t) (tfst t')
| step_snd : forall T S (t t' : tm G (times T S)), step t t' -> step (tsnd t) (tsnd t')
| step_inl : forall T S (t t' : tm G T), step t t' -> step (tinl S t) (tinl S t')
| step_inr : forall T S (t t' : tm G S), step t t' -> step (tinr T t) (tinr T t')
| step_case : forall T S C (t t' : tm G (plus T S)) (t1 : tm (snoc G T) C) t2, step t t' -> step (tcase t t1 t2) (tcase t' t1 t2)
| step_case1 : forall T S C (t : tm G (plus T S)) (t1 t1' : tm (snoc G T) C) t2, @step _ _ t1 t1' -> step (tcase t t1 t2) (tcase t t1' t2)
| step_case2 : forall T S C (t : tm G (plus T S)) (t1 : tm (snoc G T) C) t2 t2', @step _ _ t2 t2' -> step (tcase t t1 t2) (tcase t t1 t2')
| step_inj : forall F (t t' : tm G (app_fsub1 F (mu F))), step t t' -> step (tinj F t) (tinj F t')
| step_rec1 : forall F C (t1 t1' : tm G (mu F)) (t2 : tm (snoc nil (app_fsub1 F C)) C), step t1 t1' -> step (trec t1 t2) (trec t1' t2)
| step_rec2 : forall F C (t1 : tm G (mu F)) (t2 t2' : tm (snoc nil (app_fsub1 F C)) C), @step _ _ t2 t2' -> step (trec t1 t2) (trec t1 t2')
| step_out : forall F (t t' : tm G (nu F)), step t t' -> step (tout t) (tout t')
| step_corec1 : forall F C (t1 t1' : tm G C) (t2 : tm (snoc nil C) (app_fsub1 F C)), step t1 t1' -> step (tcorec F t1 t2) (tcorec F t1' t2)
| step_corec2 : forall F C (t1 : tm G C) (t2 t2' : tm (snoc nil C) (app_fsub1 F C)), @step _ _ t2 t2' -> step (tcorec F t1 t2) (tcorec F t1 t2')

| step_arrow : forall T S (t1 : tm (snoc G T) S) (t2 : tm G T), step (tapp (tlam t1) t2) (app_tsub1 t1 t2)
.
