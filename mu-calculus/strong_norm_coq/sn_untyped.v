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
Implicit Arguments extfsub [G G' T].

Fixpoint idfsub (G : ctx sort) : fsub G G :=
match G return fsub G G with
| nil => tt
| snoc G' T => extfsub (idfsub G')
end.

Fixpoint app_fsub D D' (F : functor D) (s : fsub D D') : functor D' :=
match F with
| fv _ x => glookup _ x s
| arrow A F' => arrow A (app_fsub D' F' s)
| times F G => times (app_fsub D' F s) (app_fsub D' G s)
| plus F G => plus (app_fsub D' F s) (app_fsub D' G s)
| mu F => mu (app_fsub _ F (extfsub s))
| nu F => nu (app_fsub _ F (extfsub s))
end.

Definition single_fsub D T F : fsub (snoc D T) D := pair (idfsub D) F.

Definition app_fsub1 D T (F : functor (snoc D T)) (G : functor D) : functor D :=
app_fsub D F (single_fsub T G).

Definition tp := functor nil.

Definition scope := unit.

Inductive tm (G : ctx scope) : Set :=
 | tv : forall T, var G T -> tm G
 | tlam : tm (snoc G tt) -> tm G
 | tapp : tm G -> tm G -> tm G
 | tpair : tm G -> tm G -> tm G
 | tfst : tm G -> tm G
 | tsnd : tm G -> tm G
 | tinl : tm G -> tm G
 | tinr : tm G -> tm G
 | tcase : tm G -> tm (snoc G tt) -> tm (snoc G tt) -> tm G
 | tinj : tm G -> tm G
 | trec : tm G -> tm (snoc nil tt) -> tm G
 | tout : tm G -> tm G
 | tcorec : tm G -> tm (snoc nil tt) -> tm G
.

Fixpoint forget (G : ctx tp) : ctx scope :=
match G with
| nil => nil
| snoc G' T => snoc (forget G') tt
end.

Inductive mem : forall (G : ctx tp) (x : var (forget G) tt), tp -> Prop :=
| mtop : forall G T, mem (snoc G T) top T
| mpop : forall G T S x, mem G x T -> mem (snoc G S) (pop x) T.

Inductive oft (G : ctx tp) : tm (forget G) -> tp -> Prop :=
 | tpv : forall T x, mem G x T -> oft G (tv x) T
 | tplam : forall T S t, oft (snoc G T) t S -> oft G (tlam t) (arrow T S)
 | tpapp : forall T S t1 t2, oft G t1 (arrow T S) -> oft G t2 T -> oft G (tapp t1 t2) S
 | tppair : forall T S t1 t2, oft G t1 T -> oft G t2 S -> oft G (tpair t1 t2) (times T S)
 | tpfst : forall T S t, oft G t (times T S) -> oft G (tfst t) T
 | tpsnd : forall T S t, oft G t (times T S) -> oft G (tsnd t) S
 | tpinl : forall S T t, oft G t T -> oft G (tinl t) (plus T S)
 | tpinr : forall T S t, oft G t S -> oft G (tinr t) (plus T S)
 | tpcase : forall T S C t1 t2 t3, oft G t1 (plus T S) -> oft (snoc G T) t2 C -> oft (snoc G S) t3 C -> oft G (tcase t1 t2 t3) C
 | tpinj : forall F t, oft G t (app_fsub1 F (mu F)) -> oft G (tinj t) (mu F)
 | tprec : forall F C t1 t2, oft G t1 (mu F) -> oft (snoc nil (app_fsub1 F C)) t2 C -> oft G (trec t1 t2) C
 | tpout : forall F t, oft G t (nu F) -> oft G (tout t) (app_fsub1 F (nu F))
 | tpcorec : forall F C t1 t2, oft G t1 C -> oft (snoc nil C) t2 (app_fsub1 F C) -> oft G (tcorec t1 t2) (nu F)
.

Fixpoint app_vsub_tm G G' (t : tm G) (s : vsub G G') : tm G' :=
match t with
| tv T' x => tv (glookup (var G') x s)
| tlam t' => tlam (app_vsub_tm _ t' (extvsub s))
| tapp t1 t2 => tapp (app_vsub_tm _ t1 s) (app_vsub_tm _ t2 s)
| tpair t1 t2 => tpair (app_vsub_tm _ t1 s) (app_vsub_tm _ t2 s)
| tfst t1 => tfst (app_vsub_tm _ t1 s)
| tsnd t2 => tsnd (app_vsub_tm _ t2 s)
| tinl t1 => tinl (app_vsub_tm _ t1 s)
| tinr t1 => tinr (app_vsub_tm _ t1 s)
| tcase t1 t2 t3 => tcase (app_vsub_tm _ t1 s) (app_vsub_tm _ t2 (extvsub s)) (app_vsub_tm _ t3 (extvsub s))
| tinj t1 => tinj (app_vsub_tm _ t1 s)
| trec t1 t2 => trec (app_vsub_tm _ t1 s) t2
| tout t1 => tout (app_vsub_tm _ t1 s)
| tcorec t1 t2 => tcorec (app_vsub_tm _ t1 s) t2
end.

Definition tsub (D D' : ctx scope) := gsub D (fun _ => tm D').

Definition wkntsub (G G' : ctx scope) T (s : tsub G G') : tsub G (snoc G' T) :=
gmap G (fun _ => tm G') (fun _ => tm (snoc G' T)) (fun _ t => app_vsub_tm _ t (weakening_vsub G' T)) s.

Definition exttsub (G G' : ctx scope) T (s : tsub G G') : tsub (snoc G T) (snoc G' T) :=
pair (wkntsub G G' T s) (tv (@top _ G' T)).
Implicit Arguments exttsub [G G' T].

Fixpoint idtsub (G : ctx scope) : tsub G G :=
match G return tsub G G with
| nil => tt
| snoc G' T => exttsub (idtsub G')
end.
Implicit Arguments idtsub [G].

Fixpoint app_tsub D D' (t : tm D) (s : tsub D D') : tm D' :=
match t with
| tv T' x => glookup _ x s
| tlam t' => tlam (app_tsub _ t' (exttsub s))
| tapp t1 t2 => tapp (app_tsub _ t1 s) (app_tsub _ t2 s)
| tpair t1 t2 => tpair (app_tsub _ t1 s) (app_tsub _ t2 s)
| tfst t1 => tfst (app_tsub _ t1 s)
| tsnd t2 => tsnd (app_tsub _ t2 s)
| tinl t1 => tinl (app_tsub _ t1 s)
| tinr t1 => tinr (app_tsub _ t1 s)
| tcase t1 t2 t3 => tcase (app_tsub _ t1 s) (app_tsub _ t2 (exttsub s)) (app_tsub _ t3 (exttsub s))
| tinj t1 => tinj (app_tsub _ t1 s)
| trec t1 t2 => trec (app_tsub _ t1 s) t2
| tout t1 => tout (app_tsub _ t1 s)
| tcorec t1 t2 => tcorec (app_tsub _ t1 s) t2
end.

Definition single_tsub D T (t : tm D)  : tsub (snoc D T) D := pair idtsub t.
Implicit Arguments single_tsub [ D T ].
Definition app_tsub1 D T (t : tm (snoc D T)) (t2 : tm D) : tm D :=
app_tsub _ t (single_tsub t2).

Implicit Arguments app_tsub1 [ D T ].

(* Gotta define map... *)

Inductive step (G : ctx scope) : tm G -> tm G -> Prop :=
| step_lam : forall (t1 t2 : tm (snoc G tt)), @step (snoc G tt) t1 t2 -> step (tlam t1) (tlam t2)
| step_appl : forall (t1 t2 : tm G) t3, step t1 t2 -> step (tapp t1 t3) (tapp t2 t3)
| step_appr : forall (t1 : tm G) (t2 t3 : tm G), step t2 t3 -> step (tapp t1 t2) (tapp t1 t3)
| step_pairl : forall (t1 t1' : tm G) (t2 : tm G), step t1 t1' -> step (tpair t1 t2) (tpair t1' t2)
| step_pairr : forall (t1 : tm G) (t2 t2' : tm G), step t2 t2' -> step (tpair t1 t2) (tpair t1 t2')
| step_fst : forall (t t' : tm G), step t t' -> step (tfst t) (tfst t')
| step_snd : forall (t t' : tm G), step t t' -> step (tsnd t) (tsnd t')
| step_inl : forall (t t' : tm G), step t t' -> step (tinl t) (tinl t')
| step_inr : forall (t t' : tm G), step t t' -> step (tinr t) (tinr t')
| step_case : forall (t t' : tm G) (t1 : tm (snoc G tt)) t2, step t t' -> step (tcase t t1 t2) (tcase t' t1 t2)
| step_case1 : forall (t : tm G) (t1 t1' : tm (snoc G tt)) t2, @step _ t1 t1' -> step (tcase t t1 t2) (tcase t t1' t2)
| step_case2 : forall (t : tm G) (t1 : tm (snoc G tt)) t2 t2', @step _ t2 t2' -> step (tcase t t1 t2) (tcase t t1 t2')
| step_inj : forall (t t' : tm G), step t t' -> step (tinj t) (tinj t')
| step_rec1 : forall (t1 t1' : tm G) (t2 : tm (snoc nil tt)), step t1 t1' -> step (trec t1 t2) (trec t1' t2)
| step_rec2 : forall (t1 : tm G) (t2 t2' : tm (snoc nil tt)), @step _ t2 t2' -> step (trec t1 t2) (trec t1 t2')
| step_out : forall (t t' : tm G), step t t' -> step (tout t) (tout t')
| step_corec1 : forall (t1 t1' : tm G) (t2 : tm (snoc nil tt)), step t1 t1' -> step (tcorec t1 t2) (tcorec t1' t2)
| step_corec2 : forall (t1 : tm G) (t2 t2' : tm (snoc nil tt)), @step _ t2 t2' -> step (tcorec t1 t2) (tcorec t1 t2')

| step_arrow : forall (t1 : tm (snoc G tt)) (t2 : tm G), step (tapp (tlam t1) t2) (app_tsub1 t1 t2)
| step_times1 : forall (t1 : tm G) (t2 : tm G), step (tfst (tpair t1 t2)) t1
| step_times2 : forall (t1 : tm G) (t2 : tm G), step (tsnd (tpair t1 t2)) t2
| step_plus1 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)), step (tcase (tinl t1) t2 t3) (app_tsub1 t2 t1)
| step_plus2 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)), step (tcase (tinr t1) t2 t3) (app_tsub1 t3 t1)
(* TODO: cases for nu and mu: map *)
.

Inductive sn G : tm G -> Prop :=
| con_sn : forall t, (forall t', step t t' -> sn t') -> sn t.

Inductive SNe G : tm G -> Prop :=
| sne_var : forall T (x : var G T), SNe (tv x)
| sne_app : forall (t1 : tm G) t2, SNe t1 -> SN t2 -> SNe (tapp t1 t2)
| sne_fst : forall (t1 : tm G), SNe t1 -> SNe (tfst t1)
| sne_snd : forall (t1 : tm G), SNe t1 -> SNe (tsnd t1)
| sne_case : forall (t1 : tm G) (t2 : tm (snoc G tt)) t3, SNe t1 -> @SN _ t2 -> @SN _ t3 -> SNe (tcase t1 t2 t3)
| sne_rec : forall (t1 : tm G) (t2 : tm (snoc nil tt)), SNe t1 -> @SN _ t2 -> SNe (trec t1 t2)
| sne_out : forall (t1 : tm G), SNe t1 -> SNe (tout t1)
with SN G : tm G -> Prop :=
| sn_sne : forall (t : tm G), SNe t -> SN t
| sn_lam : forall (t : tm (snoc G tt)), @SN _ t -> SN (tlam t)
| sn_pair : forall (t1 : tm G) (t2 : tm G), SN t1 -> SN t2 -> SN (tpair t1 t2)
| sn_inl : forall (t1 : tm G), SN t1 -> SN (tinl t1)
| sn_inr : forall (t1 : tm G), SN t1 -> SN (tinr t1)
| sn_inj : forall (t : tm G), SN t -> SN (tinj t)
| sn_corec : forall (t1 : tm G) (t2 : tm (snoc nil tt)), SN t1 -> @SN _ t2 -> SN (tcorec t1 t2)
| sn_closed : forall (t t' : tm G), step_SN t t' -> SN t' -> SN t
with step_SN G : tm G -> tm G -> Prop :=
| step_SN_app : forall (t t' : tm G) (u : tm G), step_SN t t' -> step_SN (tapp t u) (tapp t' u)
| step_SN_arrow : forall (t : tm (snoc G tt)) (u : tm G), SN u -> step_SN (tapp (tlam t) u) (app_tsub1 t u)
| step_SN_fst : forall (t t' : tm G), step_SN t t' -> step_SN (tfst t) (tfst t')
| step_SN_snd : forall (t t' : tm G), step_SN t t' -> step_SN (tsnd t) (tsnd t')
| step_SN_times1 : forall (t1 : tm G) (t2 : tm G), SN t2 -> step_SN (tfst (tpair t1 t2)) t1
| step_SN_times2 : forall (t1 : tm G) (t2 : tm G), SN t2 -> step_SN (tsnd (tpair t1 t2)) t2
| step_SN_case : forall (t t' : tm G) (t1 : tm (snoc G tt)) t2, step_SN t t' -> step_SN (tcase t t1 t2) (tcase t' t1 t2)
| step_SN_plus1 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)),
                  SN t1 -> @SN _ t3 -> step_SN (tcase (tinl t1) t2 t3) (app_tsub1 t2 t1)
| step_SN_plus2 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)),
                  SN t1 -> @SN _ t2 -> step_SN (tcase (tinr t1) t2 t3) (app_tsub1 t3 t1)
| step_SN_rec1 : forall (t1 t1' : tm G) (t2 : tm (snoc nil tt)), step_SN t1 t1' -> step_SN (trec t1 t2) (trec t1' t2)
| step_SN_out : forall (t t' : tm G), step_SN t t' -> step_SN (tout t) (tout t')
(* TODO: Cases for nu and mu: map *)
.

Lemma step_SN_closed_vsub G G' (t t' : tm G) (w : vsub G G') : step_SN t t' -> step_SN (app_vsub_tm _ t w) (app_vsub_tm _ t' w).
Admitted.
Lemma SNe_closed_vsub G G' (t : tm G) (w : vsub G G') : SNe t -> SNe (app_vsub_tm _ t w).
Admitted.
Lemma SN_closed_vsub G G' (t : tm G) (w : vsub G G') : SN t -> SN (app_vsub_tm _ t w).
Admitted.

Inductive step_SN_star G : tm G -> tm G -> Prop :=
| step_SN_star_refl : forall t, step_SN_star t t
| step_SN_star_step : forall t1 t2 t3, step_SN t1 t2 -> step_SN_star t2 t3 -> step_SN_star t1 t3.
Hint Constructors step_SN_star.

Lemma sn_closed_step_star G (t t' : tm G) : step_SN_star t t' -> SN t' -> SN t.
intros.
induction H; eauto.
eapply sn_closed; eauto.
Qed.

Lemma step_SN_star_trans G (t1 t2 : tm G) (H : step_SN_star t1 t2) : forall t3, step_SN_star t2 t3 -> step_SN_star t1 t3.
induction H; intros; eauto.
Qed.

Definition Rel := forall (G : ctx scope), tm G -> Prop.

Definition Rarrow (R1 R2 : Rel) : Prop := forall G (t : tm G), R1 G t -> R2 G t.

Definition lfp (FR : Rel -> Rel) : Rel:=
 fun G t => forall CR, (Rarrow (FR CR) CR) -> CR G t.

Definition monotone (FR : Rel -> Rel) : Prop :=
 forall (R1 R2 : Rel), Rarrow R1 R2 -> Rarrow (FR R1) (FR R2).

Lemma lfp_inj (FR : Rel -> Rel) (H : monotone FR) : Rarrow (FR (lfp FR)) (lfp FR).
intros G t H0.
intros R f.
eapply f.
eapply H.
Focus 2.
eexact H0.
intros G' t' H1.
eapply H1. intros.
eapply f.
Qed.

Definition gfp (FR : Rel -> Rel) : Rel :=
 fun G t => exists CR : Rel, (Rarrow CR (FR CR)) /\ CR G t.

Lemma gfp_out (FR : Rel -> Rel) (H : monotone FR) : Rarrow (gfp FR) (FR (gfp FR)).
intros G t H0.
destruct H0. destruct H0.
pose proof (H0 _ _ H1).
eapply H.
Focus 2.
eexact H2.
intros.
eexists.
split.
eexact H0.
eexact H3.
Qed.

Fixpoint Rsub (D : ctx sort) : Type :=
match D with
| nil => unit
| snoc D' _ => Rsub D' * Rel
end.

Fixpoint Rlookup D T (x : var D T) : Rsub D -> Rel :=
match x in var D T return Rsub D -> Rel with
| top D' T' => fun r => snd r
| pop D' T' S' y => fun r => Rlookup y (fst r) 
end.

Fixpoint RedF (D : ctx sort) (F : functor D) (r : Rsub D) {struct F} : Rel :=
match F (* return Rel (app_fsub _ F s) *) with
| fv D' X => fun G t => Rlookup X r t
| arrow A F' => fun G t => forall G' (w : vsub G G') u, RedF A tt u -> RedF F' r (tapp (app_vsub_tm _ t w) u)
| times F1 F2 => fun G t => RedF F1 r (tfst t) /\ RedF F2 r (tsnd t)
| plus F1 F2 => fun G t =>    (exists t', step_SN_star t (tinl t') /\ RedF F1 r t')
                           \/ (exists t', step_SN_star t (tinr t') /\ RedF F2 r t')
                           \/ (exists t', step_SN_star t t' /\ SNe t')
| mu F => lfp (fun RR G t => (exists t', step_SN_star t (tinj t') /\ RedF F (r, RR) t')
                          \/ (exists t', step_SN_star t t' /\ SNe t'))
| nu F => gfp (fun RR G t => SN t /\ RedF F (r, RR) (tout t))
end.

Definition closed_under_step_SN (R : Rel) : Prop := forall G (t' : tm G), R G t' -> forall t, step_SN t t' -> R G t.
Definition closed_under_step_SN_star (R : Rel) : Prop := forall G (t' : tm G), R G t' -> forall t, step_SN_star t t' -> R G t.
Lemma closed_to_star (R : Rel) : closed_under_step_SN R -> closed_under_step_SN_star R.
intros H. intros G t H0 t0 H1. induction H1; eauto.
Qed.
Lemma closed_star_out G (t1 t2 : tm G) : step_SN_star t1 t2 -> step_SN_star (tout t1) (tout t2).
induction 1; eauto.
econstructor.
econstructor. eauto.
eauto.
Qed.

Definition includes_SNe (R : Rel) : Prop := forall G (t : tm G), SNe t -> R G t.
Definition contained_in_SN (R : Rel) : Prop := forall G (t : tm G), R G t -> SN t.
Record candidate (R : Rel) : Prop := {
 closed : closed_under_step_SN R;
 includes_neut : includes_SNe R;
 contained_SN : contained_in_SN R
}.

Fixpoint Rsub_candidates D : forall (r : Rsub D), Prop :=
match D return forall (r : Rsub D), Prop with
| nil => fun r => True
| snoc D' _ => fun r => (Rsub_candidates D' (fst r)) /\ (candidate (snd r))
end.

Hint Constructors SNe.
Hint Constructors step_SN.
Hint Constructors SN.

Fixpoint Rarrows D : forall (r1 r2 : Rsub D), Prop :=
match D return forall (r1 r2 : Rsub D), Prop with
| nil => fun r1 r2 => True
| snoc D' _ => fun r1 r2 => (Rarrows D' (fst r1) (fst r2)) /\ (Rarrow (snd r1) (snd r2))
end.

Definition Rarr_id (R : Rel) : Rarrow R R := fun G t p => p.

Fixpoint Rarrs_id D : forall (r : Rsub D), Rarrows D r r :=
match D return forall (r : Rsub D), Rarrows D r r with
| nil => fun r => I
| snoc D' _ => fun r => conj (Rarrs_id D' (fst r)) (Rarr_id (snd r))
end.

Lemma RedF_monotone (D : ctx sort) (F : functor D) (r1 r2 : Rsub D) (H : Rarrows D r1 r2) : Rarrow (RedF F r1) (RedF F r2).
Admitted.

Lemma RedF_mu_inj (D : ctx sort) (F : functor (snoc D type)) (r : Rsub D)
 : Rarrow (fun G (t : tm G) =>    (exists t', step_SN_star t (tinj t') /\ RedF F (r, (RedF (mu F) r)) t')
                               \/ (exists t', step_SN_star t t' /\ SNe t'))
   (RedF (mu F) r).
intros G t H.
simpl.
eapply lfp_inj.
intros R1 R2 arr G' t' H0.
destruct H0. destruct H0. destruct H0.
left.
eexists. split. eexact H0. apply (RedF_monotone F (r, R1) (r, R2)).
simpl. split. eapply Rarrs_id.
eexact arr.
eexact H1.
destruct H0. destruct H0.
right.
eexists. split. eexact H0. eexact H1.
eexact H.
Qed.

Lemma RedF_nu_out (D : ctx sort) (F : functor (snoc D type)) (r : Rsub D)
 : Rarrow (RedF (nu F) r)
          (fun G t => SN t /\ RedF F (r, (RedF (nu F) r)) (tout t)).
intros G t H.
pose proof (@gfp_out (fun RR G t => SN t /\ RedF F (r, RR) (tout t))).
eapply H0.
Focus 2.
eexact H.
intros R1 R2 arr G' u H1.
destruct H1.
split. auto.
eapply (RedF_monotone F (r , R1) (r, R2)).
split. eapply Rarrs_id.
eexact arr.
auto.
Qed.

Lemma SN_candidate : candidate SN.
split;
intros G t H. 
intros. eapply sn_closed. eexact H0. eexact H.
eauto.
eauto.
Qed.

Lemma RedF_candidate (D : ctx sort) (F : functor D) (r : Rsub D) (H : Rsub_candidates D r)
  : candidate (RedF F r).
induction F; simpl.
admit.
pose proof (IHF2 r H).
pose proof (IHF1 tt I).
destruct H0. destruct H1.
split.
intros G t' H0 t st G' w u H1.
eapply closed0.
Focus 2.
eapply step_SN_app.
eapply step_SN_closed_vsub.
eexact st.
eauto.
intros G t H0 G' w u H1.
eapply includes_neut0.
eapply sne_app.
eapply SNe_closed_vsub.
eauto.
eauto.
intros G t H0.
pose proof (includes_neut1 (snoc G tt) (tv top) (sne_var top)) as H1.
pose proof (H0 (snoc G tt) (weakening_vsub G tt) (tv top) H1).
pose proof (contained_SN0 (snoc G tt) _ H2).
(* TODO: SN closed under subterms *)
inversion H3.
inversion H4.
subst.
admit.
subst.
admit.

(* Case: times *)
pose proof (IHF1 r H).
pose proof (IHF2 r H).
destruct H0. destruct H1.
split.
intros G t' H1 t H0. 
destruct H1.
split; eauto.

intros G t H0.
split; eauto.

intros G t H0.
destruct H0.
admit. (* TODO: Same *)

(* Case: plus *)
pose proof (IHF1 r H). destruct H0.
pose proof (IHF2 r H). destruct H0.
clear closed0.
split.
intros G t' H1 t H0.
destruct H1.
destruct H1.
destruct H1.
left.
eexists.
split.
eapply step_SN_star_step.
eexact H0. eexact H1.
eauto.
destruct H1.
destruct H1.
destruct H1.
right. left.
eexists. split.
eapply step_SN_star_step.
eexact H0.
eexact H1.
eauto.
right. right.
destruct H1. destruct H1.
eexists. split. eapply step_SN_star_step.
eapply H0. eapply H1.
eauto.

intros G t H0.
right. right. eexists. split. eapply step_SN_star_refl.
eexact H0.

intros G t H0.
destruct H0. destruct H0. destruct H0.
eapply sn_closed_step_star.
eexact H0.
eapply sn_inl.
eauto.

destruct H0. destruct H0. destruct H0.
eapply sn_closed_step_star.
eexact H0.
eapply sn_inr.
eauto.

destruct H0. destruct H0.
eapply sn_closed_step_star.
eapply H0. eauto.

(* Case: mu *)
split.

intros G t' H0.
set (P := fun G (u' : tm G) => forall u, step_SN_star u u' -> RedF (mu F) r u).
specialize (H0 P).
intros.
eapply H0.
intros G' u H2.
destruct H2. destruct H2. destruct H2.
intros u0 st.
eapply RedF_mu_inj.
left.
eexists. split.
eapply step_SN_star_trans.
eexact st. eexact H2.

eapply RedF_monotone.
Focus 2. eexact H3.
simpl. split. eapply Rarrs_id.
intros G'' t'' H4. 
eapply H4.
eapply step_SN_star_refl.

destruct H2. destruct H2.
intros G'' t''.
eapply RedF_mu_inj. right.
eexists. split.
eapply step_SN_star_trans. eexact t''.
eexact H2. eexact H3.
eauto.

intros G t H0.
eapply RedF_mu_inj. right.
eexists. split.
eapply step_SN_star_refl.
eauto.

intros G t H0.
eapply H0.
intros G' t' H1.
destruct H1. destruct H1. destruct H1.

pose proof (IHF (r, SN) (conj H SN_candidate)).
destruct H3.
eapply sn_closed_step_star.
eexact H1.
eapply sn_inj.
eapply contained_SN0.
eexact H2.

destruct H1. destruct H1.
eapply sn_closed_step_star.
eexact H1. eauto.

(* Case: nu *)
split.
intros G t H0 t0 st.
set (P :=  (fun G (t0 : tm G) => exists t, step_SN_star t0 t /\ RedF (nu F) r t)).
exists P.
split.
Focus 2. eexists t. split. eauto. eexact H0.
intros G' t' H1. destruct H1. destruct H1. 
pose proof (RedF_nu_out H2).
destruct H3.
split.
eapply sn_closed_step_star; eauto.

assert (candidate P).
split. intros G'' u'' H5 t1 st'.
destruct H5.  destruct H5.
exists x0. split. eauto. eauto.
admit. (* TODO: Redundant *)
intros G'' u'' H5. destruct H5. destruct H5. pose proof (RedF_nu_out H6). destruct H7. eapply sn_closed_step_star; eauto. (* TODO: Redundant, but easy *)

pose proof (IHF (r, P) (conj H H5)).
destruct H6.
pose proof (closed_to_star closed0).
eapply H6.
Focus 2.  eapply closed_star_out. eexact H1.
eapply RedF_monotone.
Focus 2. eexact H4.
split. eapply Rarrs_id.
unfold snd.
intros G'' u H7.
exists u. split; eauto.




Program Definition Red (T : tp) : Rel := RedF T tt. 

Fixpoint RedS (G : ctx tp) (G' : ctx scope) : tsub (forget G) G' -> Prop :=
match G return tsub (forget G) G' -> Prop with
| nil => fun s => True
| snoc G1 T => fun s => (RedS G1 G' (fst s)) /\ (Red T (snd s))
end.

Lemma main_lemma G G' T (t : tm (forget G)) (d : oft G t T) (s : tsub (forget G) G') (H : RedS G G' s) : Red T (app_tsub _ t s).
induction d; simpl.
admit.
admit.
pose proof (IHd1 s H).
unfold Red in H0. simpl in H0.
admit.
unfold Red. simpl.

split.





(* Interesting side notes:
   - This syntactic characterization of SN would work in LF (Andreas observed this -- he did SN in Twelf)
   - View it as an initial algebra in a presheaf category (just like LF definitions, duh)
     and get the weakening in SN for free.
*)
