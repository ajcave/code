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
| step_times1 : forall T S (t1 : tm G T) (t2 : tm G S), step (tfst (tpair t1 t2)) t1
| step_times2 : forall T S (t1 : tm G T) (t2 : tm G S), step (tsnd (tpair t1 t2)) t2
| step_plus1 : forall T S C (t1 : tm G T) (t2 : tm (snoc G T) C) (t3 : tm (snoc G S) C), step (tcase (tinl S t1) t2 t3) (app_tsub1 t2 t1)
| step_plus2 : forall T S C (t1 : tm G S) (t2 : tm (snoc G T) C) (t3 : tm (snoc G S) C), step (tcase (tinr T t1) t2 t3) (app_tsub1 t3 t1)
(* TODO: cases for nu and mu: map *)
.

Inductive sn G T : tm G T -> Prop :=
| con_sn : forall t, (forall t', step t t' -> sn t') -> sn t.

Inductive SNe G : forall T, tm G T -> Prop :=
| sne_var : forall T (x : var G T), SNe (tv x)
| sne_app : forall T S (t1 : tm G (arrow T S)) t2, SNe t1 -> SN t2 -> SNe (tapp t1 t2)
| sne_fst : forall T S (t1 : tm G (times T S)), SNe t1 -> SNe (tfst t1)
| sne_snd : forall T S (t1 : tm G (times T S)), SNe t1 -> SNe (tsnd t1)
| sne_case : forall T S C (t1 : tm G (plus T S)) (t2 : tm (snoc G T) C) t3, SNe t1 -> @SN _ _ t2 -> @SN _ _ t3 -> SNe (tcase t1 t2 t3)
| sne_rec : forall F C (t1 : tm G (mu F)) (t2 : tm (snoc nil (app_fsub1 F C)) C), SNe t1 -> @SN _ _ t2 -> SNe (trec t1 t2)
| sne_out : forall F (t1 : tm G (nu F)), SNe t1 -> SNe (tout t1)
with SN G : forall T, tm G T -> Prop :=
| sn_sne : forall T (t : tm G T), SNe t -> SN t
| sn_lam : forall T S (t : tm (snoc G T) S), @SN _ _ t -> SN (tlam t)
| sn_pair : forall T S (t1 : tm G T) (t2 : tm G S), SN t1 -> SN t2 -> SN (tpair t1 t2)
| sn_inl : forall T S (t1 : tm G T), SN t1 -> SN (tinl S t1)
| sn_inr : forall T S (t1 : tm G S), SN t1 -> SN (tinr T t1)
| sn_inj : forall F (t : tm G (app_fsub1 F (mu F))), SN t -> SN (tinj F t)
| sn_corec : forall F C (t1 : tm G C) (t2 : tm (snoc nil C) (app_fsub1 F C)), SN t1 -> @SN _ _ t2 -> SN (tcorec F t1 t2)
| sn_closed : forall T (t t' : tm G T), step_SN t t' -> SN t' -> SN t'
with step_SN G : forall T, tm G T -> tm G T -> Prop :=
| step_SN_app : forall T S (t t' : tm G (arrow T S)) (u : tm G T), step_SN t t' -> step_SN (tapp t u) (tapp t' u)
| step_SN_arrow : forall T S (t : tm (snoc G T) S) (u : tm G T), SN u -> step_SN (tapp (tlam t) u) (app_tsub1 t u)
| step_SN_fst : forall T S (t t' : tm G (times T S)), step_SN t t' -> step_SN (tfst t) (tfst t')
| step_SN_snd : forall T S (t t' : tm G (times T S)), step_SN t t' -> step_SN (tsnd t) (tsnd t')
| step_SN_times1 : forall T S (t1 : tm G T) (t2 : tm G S), SN t2 -> step_SN (tfst (tpair t1 t2)) t1
| step_SN_times2 : forall T S (t1 : tm G T) (t2 : tm G S), SN t2 -> step_SN (tsnd (tpair t1 t2)) t2
| step_SN_case : forall T S C (t t' : tm G (plus T S)) (t1 : tm (snoc G T) C) t2, step_SN t t' -> step_SN (tcase t t1 t2) (tcase t' t1 t2)
| step_SN_plus1 : forall T S C (t1 : tm G T) (t2 : tm (snoc G T) C) (t3 : tm (snoc G S) C),
                  SN t1 -> @SN _ _ t3 -> step_SN (tcase (tinl S t1) t2 t3) (app_tsub1 t2 t1)
| step_SN_plus2 : forall T S C (t1 : tm G S) (t2 : tm (snoc G T) C) (t3 : tm (snoc G S) C),
                  SN t1 -> @SN _ _ t2 -> step_SN (tcase (tinr T t1) t2 t3) (app_tsub1 t3 t1)
| step_SN_rec1 : forall F C (t1 t1' : tm G (mu F)) (t2 : tm (snoc nil (app_fsub1 F C)) C), step_SN t1 t1' -> step_SN (trec t1 t2) (trec t1' t2)
| step_SN_out : forall F (t t' : tm G (nu F)), step_SN t t' -> step_SN (tout t) (tout t')
(* TODO: Cases for nu and mu: map *)
.

Definition Rel T := forall (G : ctx tp), tm G T -> Prop.

(* Definition lfp F (FR : forall X, Rel X -> Rel (app_fsub1 F X)) : Rel (mu F) :=
 fun G t => forall C f CR, (forall G' u, FR C CR G' u -> CR G' (f u)) *)

Fixpoint Rsub D : fsub D nil -> Type :=
match D return fsub D nil -> Type with
| nil => fun s => unit
| snoc D' _ => fun s => (Rsub D' (fst s)) * (Rel (snd s))
end.

Fixpoint Rlookup D T (x : var D T) : forall (s : fsub D nil), Rsub D s -> Rel (glookup _ x s) :=
match x in var D T return forall (s : fsub D nil), Rsub D s -> Rel (glookup _ x s) with
| top D' T' => fun s r => snd r
| pop D' T' S' y => fun s r => Rlookup y (fst s) (fst r) 
end.


Fixpoint RedF D (F : functor D) (s : fsub D nil) (r : Rsub D s) : Rel (app_fsub _ F s) :=
match F return Rel (app_fsub _ F s) with
| fv D' X => fun G t => Rlookup X s r t
| arrow A F' => fun G t => True (* forall G' (w : vsub G G') u, RedF A tt tt u -> RedF F' s r (tapp (app_vsub_tm _ t w) u) *)
| times F1 F2 => fun G t => RedF F1 s r (tfst t) /\ RedF F2 s r (tsnd t)
| plus F1 F2 => fun G t =>    (exists t', step_SN t (tinl _ t') /\ RedF F1 s r t')
                           \/ (exists t', step_SN t (tinr _ t') /\ RedF F2 s r t')
                           \/ (exists t', step_SN t t' /\ SNe t')
| mu F => fun G t => True
| nu F => fun G t => True
end.



Definition Red (T : tp) : Rel T := fun G t => RedF T tt tt t.

Lemma main_lemma G T (t : tm G T)