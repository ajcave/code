Require Import Coq.Program.Equality.

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

Inductive gsub' (A : Type) (F : A -> Type) : forall (Γ : ctx A), Type :=
| gnil : gsub' F nil
| gsnoc : forall Γ T, gsub' F Γ -> F T -> gsub' F (snoc Γ T).
Implicit Arguments gnil [A F].
Implicit Arguments gsnoc [A Γ F T].

Fixpoint glookup (A : Type) (G : ctx A) (F : A -> Type) T (x : var G T) : gsub G F -> F T :=
match x in var G T return gsub G F -> F T with
| top G' T' => fun s => snd s
| pop G' T' S' y => fun s => glookup F y (fst s)
end.

Definition glookup' (A : Type) (G : ctx A) (F : A -> Type) T (x : var G T) : gsub' F G -> F T.
intros.
induction G. inversion x.
inversion x; subst.
inversion X; subst.
exact X1.
inversion X; subst.
apply IHG.
exact X0.
exact X1.
Defined.
Print glookup'.

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
 | trec : forall (F : functor (snoc nil type)), tm G -> tm (snoc nil tt) -> tm G
 | tout : tm G -> tm G
 | tcorec : functor (snoc nil type) -> tm G -> tm (snoc nil tt) -> tm G
 | tmap : forall Δ (F : functor Δ), tm G -> gsub' (fun _ => tm (snoc nil tt)) Δ -> tm G
.

Definition map_arrow (Δ : ctx sort) : Type :=
gsub' (fun _ => tm (snoc nil tt)) Δ.

Fixpoint forget (G : ctx tp) : ctx scope :=
match G with
| nil => nil
| snoc G' T => snoc (forget G') tt
end.

Inductive mem : forall (G : ctx tp) (x : var (forget G) tt), tp -> Prop :=
| mtop : forall G T, mem (snoc G T) top T
| mpop : forall G T S x, mem G x T -> mem (snoc G S) (pop x) T.

Inductive oft : forall (G : ctx tp), tm (forget G) -> tp -> Prop :=
 | tpv : forall G T x, mem G x T -> oft G (tv x) T
 | tplam : forall G T S t, oft (snoc G T) t S -> oft G (tlam t) (arrow T S)
 | tpapp : forall G T S t1 t2, oft G t1 (arrow T S) -> oft G t2 T -> oft G (tapp t1 t2) S
 | tppair : forall G T S t1 t2, oft G t1 T -> oft G t2 S -> oft G (tpair t1 t2) (times T S)
 | tpfst : forall G T S t, oft G t (times T S) -> oft G (tfst t) T
 | tpsnd : forall G T S t, oft G t (times T S) -> oft G (tsnd t) S
 | tpinl : forall G S T t, oft G t T -> oft G (tinl t) (plus T S)
 | tpinr : forall G T S t, oft G t S -> oft G (tinr t) (plus T S)
 | tpcase : forall G T S C t1 t2 t3, oft G t1 (plus T S) -> oft (snoc G T) t2 C -> oft (snoc G S) t3 C -> oft G (tcase t1 t2 t3) C
 | tpinj : forall G F t, oft G t (app_fsub1 F (mu F)) -> oft G (tinj t) (mu F)
 | tprec : forall G F C t1 t2, oft G t1 (mu F) -> oft (snoc nil (app_fsub1 F C)) t2 C -> oft G (trec F t1 t2) C
 | tpout : forall G F t, oft G t (nu F) -> oft G (tout t) (app_fsub1 F (nu F))
 | tpcorec : forall G F C t1 t2, oft G t1 C -> oft (snoc nil C) t2 (app_fsub1 F C) -> oft G (tcorec F t1 t2) (nu F)
 | tpmap : forall Δ Γ (F : functor Δ) ρ₁ ρ₂ η M, oft Γ M (app_fsub _ F ρ₁)
   -> ofts ρ₁ η ρ₂ -> oft Γ (tmap F M η) (app_fsub _ F ρ₂) 
with ofts : forall Δ (ρ₁ : fsub Δ nil) (η : map_arrow Δ) (ρ₂ : fsub Δ nil), Prop :=
 | onil : @ofts nil tt gnil tt
 | osnoc : forall Δ (ρ₁ : fsub Δ nil) η ρ₂ A M B, ofts ρ₁ η ρ₂ -> oft (snoc nil A) M B
               -> @ofts (snoc Δ type) (ρ₁ , A) (gsnoc η M) (ρ₂ , B)
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
| trec F t1 t2 => trec F (app_vsub_tm _ t1 s) t2
| tout t1 => tout (app_vsub_tm _ t1 s)
| tcorec F t1 t2 => tcorec F (app_vsub_tm _ t1 s) t2
| tmap _ F M η => tmap F (app_vsub_tm _ M s) η
end.

Definition tsub (D D' : ctx scope) := gsub D (fun _ => tm D').

Definition wkn_tm G T (t : tm G) : tm (snoc G T) :=
app_vsub_tm _ t (weakening_vsub G T).
Implicit Arguments wkn_tm [G T].

Definition wkntsub (G G' : ctx scope) T (s : tsub G G') : tsub G (snoc G' T) :=
gmap G (fun _ => tm G') (fun _ => tm (snoc G' T)) (fun _ t => wkn_tm t) s.

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
| trec F t1 t2 => trec F (app_tsub _ t1 s) t2
| tout t1 => tout (app_tsub _ t1 s)
| tcorec F t1 t2 => tcorec F (app_tsub _ t1 s) t2
| tmap _ F M η => tmap F (app_tsub _ M s) η
end.

Definition single_tsub D T (t : tm D)  : tsub (snoc D T) D := pair idtsub t.
Implicit Arguments single_tsub [ D T ].
Definition app_tsub1 D T (t : tm (snoc D T)) (t2 : tm D) : tm D :=
app_tsub _ t (single_tsub t2).

Implicit Arguments app_tsub1 [ D T ].

(* TODO: type preservation! Because I'm not sure I believe I got these definitions right *)

Definition tmap1 (F : functor (snoc nil type)) G (f : tm (snoc nil tt)) (t : tm G) : tm G :=
tmap F t (gsnoc gnil f).

(* For this logical relation, this is the most natural step relation:
   Weak head reduction (i.e. only goes as far as confirming that, yep, its of the form tpair,
   and doesn't care what's underneath *)
(* TODO: Hmm, I think we could consider either going under pairs or not.
   If we were just defining an equality test, it seems like a redundant stage,
   but for normalization it seems relevant. "Positive" vs "Negative"?
   Hmm. We can normalize further *)
Inductive step (G : ctx scope) : tm G -> tm G -> Prop :=
| step_appl : forall (t1 t2 : tm G) t3, step t1 t2 -> step (tapp t1 t3) (tapp t2 t3)
| step_fst : forall (t t' : tm G), step t t' -> step (tfst t) (tfst t')
| step_snd : forall (t t' : tm G), step t t' -> step (tsnd t) (tsnd t')
| step_case : forall (t t' : tm G) (t1 : tm (snoc G tt)) t2, step t t' -> step (tcase t t1 t2) (tcase t' t1 t2)
| step_rec1 : forall F (t1 t1' : tm G) (t2 : tm (snoc nil tt)), step t1 t1' -> step (trec F t1 t2) (trec F t1' t2)
| step_out : forall (t t' : tm G), step t t' -> step (tout t) (tout t')

| step_arrow : forall (t1 : tm (snoc G tt)) (t2 : tm G), step (tapp (tlam t1) t2) (app_tsub1 t1 t2)
| step_times1 : forall (t1 : tm G) (t2 : tm G), step (tfst (tpair t1 t2)) t1
| step_times2 : forall (t1 : tm G) (t2 : tm G), step (tsnd (tpair t1 t2)) t2
| step_plus1 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)), step (tcase (tinl t1) t2 t3) (app_tsub1 t2 t1)
| step_plus2 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)), step (tcase (tinr t1) t2 t3) (app_tsub1 t3 t1)
| step_mu : forall F (t1 : tm G) (t2 : tm (snoc nil tt)),
   step (trec F (tinj t1) t2) (app_tsub _ t2 (tt, tmap1 F (trec F (tv top) t2) t1))
| step_nu : forall F (t1 : tm G) (t2 : tm (snoc nil tt)),
   step (tout (tcorec F t1 t2)) (tmap1 F (tcorec F (tv top) t2) (app_tsub _ t2 (tt, t1)))
| step_map : forall Δ (F : functor Δ) M M' η,
     step M M'
  -> step (tmap F M η) (tmap F M' η) (* Should we only do this for mu F? *)
| step_map_fv : forall Δ (X : var Δ type) M η,
   step (tmap (fv X) M η) (app_tsub _ (glookup' X η) (tt , M))
| step_map_arrow : forall Δ T (F2 : functor Δ) M η,
    step (tmap (arrow T F2) M η) (tlam (tmap F2 (tapp (wkn_tm M) (tv top)) η))
| step_map_times : forall Δ (F1 : functor Δ) F2 M η, 
    step (tmap (times F1 F2) M η) (tpair (tmap F1 (tfst M) η) (tmap F2 (tsnd M) η))
| step_map_plus : forall Δ (F1 : functor Δ) F2 M η,
    step (tmap (plus F1 F2) M η) (tcase M (tinl (tmap F1 (tv top) η)) (tinr (tmap F2 (tv top) η)))
| step_map_mu : forall Δ (F : functor (snoc Δ type)) M η,
    step (tmap (mu F) (tinj M) η) (tinj (tmap F M (gsnoc η (tmap (mu F) (tv top) η))))
| step_map_nu : forall Δ (F : functor (snoc Δ type)) M η,
    step (tout (tmap (nu F) M η)) (tmap F (tout M) (gsnoc η (tmap (nu F) (tv top) η)))
.
Hint Constructors step.
(* Could we somehow incorporate η laws? If we were intrinsically typed?
   Obviously only η laws for arrow, times, and unit. The rest would be
   beta only, and hence only (very) weakly normalizing (i.e. not under constructors).
   The ones without η need to be very weakly normalizing *)
(* Why do we use Kripke if we don't go under binders? (we still need _something_ reducible to stick in)*)
(* Seems like 2 choices for each type former:
   a) have η laws
   b) do very weakly normalizing (not under constructor) *)

Inductive step_star G : tm G -> tm G -> Prop :=
| step_refl : forall M, step_star M M (* Build in refl and trans for convenience *)
| step_trans1 : forall M1 M2 M3, step M1 M2 -> step_star M2 M3 -> step_star M1 M3.
(* Note that we don't normalize inside the "arrow" of a map. We could, at least in the
   non-temporal mu-nu language *)
Hint Constructors step_star.

Lemma step_trans G (M1 M2 M3 : tm G) : step_star M1 M2 -> step_star M2 M3 -> step_star M1 M3.
intros. induction H; eauto.
Qed.
Hint Resolve step_trans.

Section step_star_lemmas.
Variable G : ctx scope.
Lemma  step_star_appl : forall (t1 t2 : tm G) t3, step_star t1 t2 -> step_star (tapp t1 t3) (tapp t2 t3).
induction 1; eauto. Qed.
Lemma  step_star_fst : forall (t t' : tm G), step_star t t' -> step_star (tfst t) (tfst t').
induction 1; eauto. Qed.
Lemma  step_star_snd : forall (t t' : tm G), step_star t t' -> step_star (tsnd t) (tsnd t')
. induction 1; eauto. Qed.
Lemma  step_star_case : forall (t t' : tm G) (t1 : tm (snoc G tt)) t2, step_star t t' -> step_star (tcase t t1 t2) (tcase t' t1 t2)
. induction 1; eauto. Qed.
Lemma  step_star_rec1 : forall F (t1 t1' : tm G) (t2 : tm (snoc nil tt)), step_star t1 t1' -> step_star (trec F t1 t2) (trec F t1' t2)
. induction 1; eauto. Qed.
Lemma  step_star_out : forall (t t' : tm G), step_star t t' -> step_star (tout t) (tout t')
. induction 1; eauto. Qed.
Lemma  step_star_arrow : forall (t1 : tm (snoc G tt)) (t2 : tm G), step_star (tapp (tlam t1) t2) (app_tsub1 t1 t2). eauto. Qed.
Lemma  step_star_times1 : forall (t1 : tm G) (t2 : tm G), step_star (tfst (tpair t1 t2)) t1
. eauto. Qed.
Lemma  step_star_times2 : forall (t1 : tm G) (t2 : tm G), step_star (tsnd (tpair t1 t2)) t2
.  eauto. Qed.
Lemma  step_star_plus1 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)), step_star (tcase (tinl t1) t2 t3) (app_tsub1 t2 t1)
.  eauto. Qed.
Lemma  step_star_plus2 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)), step_star (tcase (tinr t1) t2 t3) (app_tsub1 t3 t1). eauto. Qed.
Lemma  step_star_mu : forall F (t1 : tm G) (t2 : tm (snoc nil tt)),
   step_star (trec F (tinj t1) t2) (app_tsub _ t2 (tt, tmap1 F (trec F (tv top) t2) t1))
. eauto. Qed.
Lemma  step_star_nu : forall F (t1 : tm G) (t2 : tm (snoc nil tt)),
   step_star (tout (tcorec F t1 t2)) (tmap1 F (tcorec F (tv top) t2) (app_tsub _ t2 (tt, t1))).
eauto. Qed.
Lemma  step_star_map : forall Δ (F : functor Δ) (M M' : tm G) η,
     step_star M M'
  -> step_star (tmap F M η) (tmap F M' η) (* Should we only do this for mu F? *)
. induction 1; eauto. Qed.
Lemma  step_star_map_fv : forall Δ (X : var Δ type) (M : tm G) η,
   step_star (tmap (fv X) M η) (app_tsub _ (glookup' X η) (tt , M)).
eauto. Qed.
Lemma  step_star_map_arrow : forall Δ T (F2 : functor Δ) (M : tm G) η,
    step_star (tmap (arrow T F2) M η) (tlam (tmap F2 (tapp (wkn_tm M) (tv top)) η)). eauto. Qed.
Lemma  step_star_map_times : forall Δ (F1 : functor Δ) F2 (M : tm G) η, 
    step_star (tmap (times F1 F2) M η) (tpair (tmap F1 (tfst M) η) (tmap F2 (tsnd M) η)). eauto. Qed.
Lemma  step_star_map_plus : forall Δ (F1 : functor Δ) F2 (M : tm G) η,
    step_star (tmap (plus F1 F2) M η) (tcase M (tinl (tmap F1 (tv top) η)) (tinr (tmap F2 (tv top) η))).
eauto. Qed.
Lemma  step_star_map_mu : forall Δ (F : functor (snoc Δ type)) (M : tm G) η,
    step_star (tmap (mu F) (tinj M) η) (tinj (tmap F M (gsnoc η (tmap (mu F) (tv top) η)))).
eauto. Qed.
Lemma  step_star_map_nu : forall Δ (F : functor (snoc Δ type)) (M : tm G) η,
    step_star (tout (tmap (nu F) M η)) (tmap F (tout M) (gsnoc η (tmap (nu F) (tv top) η)))
. eauto. Qed.
End step_star_lemmas.
Hint Resolve step_star_appl step_star_fst step_star_snd step_star_case step_star_rec1 step_star_out
             step_star_arrow step_star_times1 step_star_times2 step_star_plus1 step_star_plus2
             step_star_mu step_star_nu step_star_map step_star_map_fv step_star_map_arrow
             step_star_map_times step_star_map_plus step_star_map_mu step_star_map_nu.

Inductive isNeutral G : tm G -> Prop :=
 | ne_v : forall (x : var G tt), isNeutral (tv x)
 | ne_app : forall t1 t2, isNeutral t1 -> isNeutral (tapp t1 t2)
 | ne_fst : forall t, isNeutral t -> isNeutral (tfst t)
 | ne_snd : forall t, isNeutral t -> isNeutral (tsnd t)
 | ne_case : forall t1 t2 t3, isNeutral t1 
     -> isNeutral (tcase t1 t2 t3)
 | ne_rec : forall F t1 t2, isNeutral t1 -> isNeutral (trec F t1 t2)
 | ne_out : forall t, isNeutral t -> isNeutral (tout t)
 | ne_map : forall Δ (F : functor (snoc Δ type)) η M,
      isNeutral M
   -> isNeutral (tmap (mu F) M η)
with isNormal G : tm G -> Prop :=
 | no_lam : forall t, isNormal (tlam t)
 | no_pair : forall t1 t2, (* isNormal t1 -> isNormal t2 -> *) isNormal (tpair t1 t2)
 | no_inl : forall t, (* isNormal t -> *) isNormal (tinl t)
 | no_inr : forall t, (* isNormal t -> *) isNormal (tinr t)
 | no_inj : forall t, (* isNormal t -> *) isNormal (tinj t)
 | no_corec : forall F t1 t2, isNormal (tcorec F t1 t2) 
 | no_map_nu : forall Δ (F : functor (snoc Δ type)) η M,
   isNormal (tmap (nu F) M η)
 | no_ne : forall t, isNeutral t -> isNormal t
.

Definition Rel := forall (G : ctx scope), tm G -> Prop.

Inductive normalizing G : tm G -> Prop :=
 | norm_intro : forall M N, step_star M N -> isNormal N -> normalizing M.

Definition Rarrow (R1 R2 : Rel) : Prop := forall G (t : tm G), R1 G t -> R2 G t.

Definition contained_in_normalizing (R : Rel) : Prop := Rarrow R normalizing.

Definition includes_neutral (R : Rel) : Prop := Rarrow isNeutral R.

Definition closed_under_step (R : Rel) : Prop :=
  forall G (t' : tm G), R G t' -> forall t, step_star t t' -> R G t.

Record candidate (R : Rel) : Prop := {
 CR1 : Rarrow R normalizing;
 CR2 : closed_under_step R;
 CR3 : Rarrow isNeutral R
}.
Hint Resolve CR1 CR2 CR3.


Definition closure (C : Rel) : Rel := fun G t => exists t', step_star t t' /\ (C G t' \/ isNeutral t').


Hint Constructors step.
Hint Constructors normalizing.
Hint Constructors isNormal isNeutral.

Lemma normalizing_candidate : candidate normalizing.
constructor.
intros G t. auto.
intros G t' H t p.
inversion H; subst.
econstructor. eapply step_trans; eauto. auto.
intros G t H. econstructor; eauto.
Qed.
Hint Resolve normalizing_candidate.
Hint Resolve step_trans.


Lemma closure_cand (C : Rel) (H : Rarrow C normalizing) : candidate (closure C).
split.
(* CR1 *)
intros G t Hy0. destruct Hy0. destruct H0. destruct H1.
eapply CR2. eauto.
eapply H. eapply H1. auto.
eauto. eauto.
(* CR2*)
intros G t' Hy1 t s.
destruct Hy1. destruct H0.
eexists.
split. Focus 2.
eexact H1.
eauto.
(* CR3 *)
intros G t Hy0.
eexists. split. Focus 2. right. eauto.
eauto.
Qed.
Hint Resolve closure_cand.

Lemma adjunction_closure C D (H : candidate D) (r : Rarrow C D) : Rarrow (closure C) D.
intros G t Hy0.
destruct Hy0. destruct H0. destruct H1.
eapply CR2; eauto.
eapply CR2; eauto.
eapply CR3; eauto.
Qed.

Lemma closure_unit C : Rarrow C (closure C).
firstorder.
Qed.

Lemma Rarrow_compose A B C : Rarrow B C -> Rarrow A B -> Rarrow A C.
firstorder.
Qed.
Hint Resolve closure_unit Rarrow_compose.

Definition glb (Pred : Rel -> Prop) : Rel := fun G t => (forall C, Pred C -> C G t) /\ normalizing t. 

Definition lub (Pred : Rel -> Prop) : Rel := closure (fun G t => exists C, Pred C /\ C G t).

Lemma glb_cand (Pred : Rel -> Prop) (Hy : forall C, Pred C -> candidate C) : candidate (glb Pred).
unfold glb.
constructor.
(* CR1 *)
intros G t H0. tauto.
(* CR2 *)
intros G t' H0 t s.
destruct H0.
split.
intros.
eapply CR2; eauto.  eapply H; eauto.
eapply CR2. eapply normalizing_candidate. eauto. eauto.
(* CR3 *)
intros G t H0.
split.
intros.
eapply CR3; eauto.
eauto.
Qed.

Lemma lub_cand (Pred : Rel -> Prop) (Hy : forall C, Pred C -> candidate C) : candidate (lub Pred).
eapply closure_cand.
firstorder.
Qed.

Definition lfp (F : Rel -> Rel) : Rel :=
 glb (fun C => candidate C /\ Rarrow (F C) C).

Definition gfp (F : Rel -> Rel) : Rel :=
 lub (fun C => candidate C /\ Rarrow C (F C)).

Definition monotone (F : Rel -> Rel) : Prop :=
 forall (R1 R2 : Rel), Rarrow R1 R2 -> Rarrow (F R1) (F R2).

Lemma lfp_candidate (F : Rel -> Rel) : candidate (lfp F).
eapply glb_cand. firstorder.
Qed.

Lemma gfp_candidate (F : Rel -> Rel) : candidate (gfp F).
eapply lub_cand. firstorder.
Qed.
Hint Resolve lfp_candidate gfp_candidate.

(* This is simply a special case of Knaster-Tarski *)

Lemma lfp_inj (FR : Rel -> Rel) (H : monotone FR) (Hy : forall C, candidate C -> candidate (FR C))
  : Rarrow (FR (lfp FR)) (lfp FR).
intros G t H0.
split.
intros C Hy1.
destruct Hy1 as [Hy0 f].
eapply f.
eapply H.
Focus 2.
eexact H0.
intros G' t' H1.
eapply H1. split.
eexact Hy0. eexact f.
eapply CR1.
eapply Hy.
eapply lfp_candidate.
eexact H0.
Qed.

Lemma lfp_ind (F : Rel -> Rel) C (H0 : candidate C) (r : Rarrow (F C) C) : Rarrow (lfp F) C.
firstorder.
Qed.

Lemma gfp_out (F : Rel -> Rel) (H : monotone F) (Hy : forall C, candidate C -> candidate (F C))
  : Rarrow (gfp F) (F (gfp F)).
eapply adjunction_closure; eauto.
intros G t Hy0.
destruct Hy0 as [C H0]. destruct H0. destruct H0.
eapply H.
Focus 2.
eapply H2. eexact H1.
eapply Rarrow_compose.
eapply closure_unit.
firstorder.
Qed.

Lemma gfp_coind (F : Rel -> Rel) C (H0 : candidate C) (r : Rarrow C (F C)) : Rarrow C (gfp F).
firstorder.
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

Definition star (R : Rel) (f : forall G, tm G -> tm G) : Rel := fun G t => exists t', t = f _ t' /\ R G t'.
Definition circ (R : Rel) (f : forall G, tm G -> tm G) : Rel := fun G t => R G (f G t).

Definition Meet (C D : Rel) : Rel := fun G t => C G t /\ D G t.
Definition Join (C D : Rel) : Rel := fun G t => C G t \/ D G t.

Lemma Join_elim (C D R : Rel) : Rarrow C R -> Rarrow D R -> Rarrow (Join C D) R.
firstorder.
Qed.
Lemma Join_inl C D : Rarrow C (Join C D). firstorder. Qed.
Lemma Join_inr C D : Rarrow D (Join C D). firstorder. Qed.
Lemma Meet_elim1 C D : Rarrow (Meet C D) C. firstorder. Qed.
Lemma Meet_elim2 C D : Rarrow (Meet C D) D. firstorder. Qed. 
Lemma Meet_intro C D R : Rarrow R C -> Rarrow R D -> Rarrow R (Meet C D). firstorder. Qed.
(* Hint Resolve Join_elim Join_inl Join_inr Meet_elim1 Meet_elim2 Meet_intro. *)

Definition Arrow (C D : Rel) : Rel := 
 fun G t => forall G' (w : vsub G G') u, C G' u -> D G' (tapp (app_vsub_tm _ t w) u).
Definition Times (C D : Rel) : Rel := Meet (circ C tfst) (circ D tsnd).
Definition PrePlus C D := Join (star C tinl) (star D tinr).
Definition Plus (C D : Rel) : Rel := closure (PrePlus C D).
Definition Mu (F : Rel -> Rel) := lfp (fun C => closure (star (F C) tinj)).
Definition Nu (F : Rel -> Rel) := gfp (fun C => circ (F C) tout).

Fixpoint RedF (D : ctx sort) (F : functor D) (r : Rsub D) {struct F} : Rel :=
match F with
| fv D' X => Rlookup X r
| arrow A F' => Arrow (RedF A tt) (RedF F' r)
| times F1 F2 => Times (RedF F1 r) (RedF F2 r)
| plus F1 F2 => Plus (RedF F1 r) (RedF F2 r)
| mu F => Mu (fun R => RedF F (r , R))
| nu F => Nu (fun R => RedF F (r , R))
end.

Fixpoint Rsub_candidates D : forall (r : Rsub D), Prop :=
match D return forall (r : Rsub D), Prop with
| nil => fun r => True
| snoc D' _ => fun r => (Rsub_candidates D' (fst r)) /\ (candidate (snd r))
end.

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
induction F; simpl.
Admitted.

Lemma step_wkn Γ Γ' (t t' : tm Γ) (w : vsub Γ Γ') :
 step_star t t' -> step_star (app_vsub_tm _ t w) (app_vsub_tm _ t' w).
Admitted.
Hint Resolve step_wkn.

Lemma isNeutral_wkn Γ Γ' (t : tm Γ) (w : vsub Γ Γ') : isNeutral t -> isNeutral (app_vsub_tm _ t w).
Admitted.
Hint Resolve isNeutral_wkn.

Lemma tapp_norm G (t u : tm G) : normalizing (tapp t u) -> normalizing t.
intros. inversion H; subst. clear H.
dependent induction H0.
inversion H1; subst. inversion H; eauto.
inversion H; subst.
eapply CR2; eauto.
eauto.
Qed.

Lemma wkn_norm G G' (w : vsub G G') t : normalizing (app_vsub_tm _ t w) -> normalizing t.
Admitted.

Lemma Arrow_candidate C D : candidate C -> candidate D -> candidate (Arrow C D).
intros. split.
(* CR1 *)
intros G t Hy0. unfold Arrow in Hy0.
eapply wkn_norm. eapply tapp_norm.
eapply CR1. exact H0. eapply (Hy0 (snoc G tt) (weakening_vsub _ _) (tv top)). eapply CR3; eauto.
(* CR2 *)
intros G t' Hy0 t s G0 w u Hy1.
eapply CR2; eauto.
(* CR3 *)
intros G t Hy0 G0 w u Hy1.
eapply CR3; eauto.
Qed.

(* TODO: Hmm, we will probably need to add a requirement for candidates saying they are closed
   under weakening *)

Lemma fst_norm G (t : tm G) : normalizing (tfst t) -> normalizing  t.
intros.
inversion H; subst. clear H.
dependent induction H0.
inversion H1; subst. inversion H; subst; eauto.
inversion H; subst.
eapply CR2; eauto.
eauto.
Qed.
 
Lemma Times_candidate C D : candidate C -> candidate D -> candidate (Times C D).
intros. split.
(* CR1 *)
intros G t [Hy0 Hy1]. unfold circ in *.
eapply fst_norm. eapply CR1. eexact H. eauto.
(* CR2 *)
intros G t' Hy0 t s. destruct Hy0.
unfold Times. unfold Meet. unfold circ in *.
firstorder.
(* CR3 *)
eapply Meet_intro; unfold circ; firstorder.
Qed.

Lemma tinl_norm G (t : tm G) : normalizing t -> normalizing (tinl t).
eauto.
Qed.

Lemma tinr_norm G (t : tm G) : normalizing t -> normalizing (tinr t).
eauto.
Qed.

Lemma Plus_normalizing C D : candidate C -> candidate D -> Rarrow (PrePlus C D) normalizing.
intros.
eapply Join_elim; unfold star; intros G t Hy0;
destruct Hy0; destruct H1; subst.
eapply tinl_norm; firstorder.
eapply tinr_norm; firstorder.
Qed.

Lemma Plus_candidate C D : candidate C -> candidate D -> candidate (Plus C D).
intros.
eapply closure_cand.
eapply Plus_normalizing; auto.
Qed.

Lemma tinj_norm G (t : tm G) : normalizing t -> normalizing (tinj t).
eauto.
Qed.

Lemma Mu_candidate F : candidate (Mu F).
eapply lfp_candidate.
Qed.

Lemma Nu_candidate F : candidate (Nu F).
eapply gfp_candidate.
Qed.

Hint Resolve Arrow_candidate Times_candidate Plus_candidate Mu_candidate Nu_candidate I.

Lemma Rlookup_candidate D T (v : var D T) (r : Rsub D) (H : Rsub_candidates D r) : candidate (Rlookup v r).
induction v; simpl in *; firstorder.
Qed.

Hint Resolve Rlookup_candidate.

Lemma RedF_candidate (D : ctx sort) (F : functor D) (r : Rsub D) (H : Rsub_candidates D r)
  : candidate (RedF F r).
induction F; simpl in *; eauto.
Qed. 

(* OHhh. We showed that arbitrary lubs and glbs of candidates are candidates.
   Meet and Join are just 2-ary lubs and glbs. So this amounts to simply showing
   that C ∘ fst is a candidate, C ∘ snd is a candidate,
   and.. still a little mysteriously, If C ⊆ normalizing then C ⋆ inl ⊆ normalizing...
   The whole thing is built out of lubs and glbs.
*)

Program Definition Red (T : tp) : Rel := RedF T tt. 

Lemma Red_candidate (T : tp) : candidate (Red T).
eapply RedF_candidate.
simpl.
eauto.
Qed.
Hint Resolve Red_candidate.

Lemma Red_closed_eq (T : tp) : forall G (t t' : tm G), Red T t' -> t = t' -> Red T t.
intros. subst.
auto.
Qed.

Definition Rels (G G' : ctx scope) := gsub G (fun _ => tm G' -> Prop).

Fixpoint RedS' (G : ctx scope) G' : Rels G G' -> tsub G G' -> Prop :=
match G return Rels G G' -> tsub G G' -> Prop with
| nil => fun Cs s => True
| snoc G1 tt => fun Cs s => (RedS' G1 G' (fst Cs) (fst s)) /\ (snd Cs (snd s))
end.

Definition SemTyping G (Cs : forall G', Rels G G') (t : tm G) (C : Rel) : Prop :=
 forall G' (s : tsub G G') (H : RedS' G G' (Cs G') s), C G' (app_tsub _ t s).
Implicit Arguments SemTyping [G].

Lemma SemTyping_Meet_intro G Γ (t : tm G) A B : SemTyping Γ t A -> SemTyping Γ t B -> SemTyping Γ t (Meet A B).
firstorder.
Qed.
Lemma SemTyping_Meet_elim1 G Γ (t : tm G) A B : SemTyping Γ t (Meet A B) -> SemTyping Γ t A.
firstorder.
Qed.
Lemma SemTyping_Meet_elim2 G Γ (t : tm G) A B : SemTyping Γ t (Meet A B) -> SemTyping Γ t B.
firstorder.
Qed.

Definition natural (f : forall G, tm G -> tm G) :=
 forall G G' t (s : tsub G G'), (app_tsub _ (f _ t) s) = f _ (app_tsub _ t s).

Lemma SemTyping_circ G Γ (t : tm G) A (f : forall G, tm G -> tm G)
  : natural f -> SemTyping Γ (f _ t) A -> SemTyping Γ t (circ A f).
unfold circ. repeat intro.
rewrite <- H.
eauto.
Qed.

Lemma SemTyping_circ' G Γ (t : tm G) A (f : forall G, tm G -> tm G)
  : natural f -> SemTyping Γ t (circ A f) -> SemTyping Γ (f _ t) A.
unfold circ. repeat intro.
rewrite -> H.
eauto.
Qed.

Ltac proveNatural :=
match goal with
| [ |- natural _] => firstorder
| _ => idtac
end.

Lemma SemTyping_closed G Γ (t t' : tm G) A 
  (H : forall G' (s : tsub G G'), step_star (app_tsub _ t s) (app_tsub _ t' s))
 : candidate A
 -> SemTyping Γ t' A -> SemTyping Γ t A.
repeat intro.
eapply CR2. auto.
Focus 2. eapply H.
eapply H1; eauto.
Qed.

Lemma Red_pair G Γ A B (t1 t2 : tm G) : candidate A -> candidate B -> SemTyping Γ t1 A -> SemTyping Γ t2 B
 -> SemTyping Γ (tpair t1 t2) (Times A B).
intros.
eapply SemTyping_Meet_intro; eapply SemTyping_circ; proveNatural;
eapply SemTyping_closed; simpl; eauto.
Qed.

Lemma Red_fst G Γ A B (t : tm G) : SemTyping Γ t (Times A B) 
 -> SemTyping Γ (tfst t) A.
intros.
eapply SemTyping_circ'; proveNatural.
eapply SemTyping_Meet_elim1.
eauto.
Qed.

Lemma Red_snd G Γ A B (t : tm G) : SemTyping Γ t (Times A B) 
 -> SemTyping Γ (tsnd t) B.
intros.
eapply SemTyping_circ'; proveNatural.
eapply SemTyping_Meet_elim2.
eauto.
Qed.

Definition snoc' G (Γ : forall G', Rels G G') (A : Rel) G' : Rels (snoc G tt) G' := ((Γ G') , (A G')).
Implicit Arguments snoc' [G].

Lemma Red_case G Γ A B C (t1 : tm G) (t2 t3 : tm (snoc G tt)) :
    SemTyping Γ t1 (Plus A B)
 -> SemTyping (snoc' Γ A) t2 C
 -> SemTyping (snoc' Γ B) t3 C
 -> SemTyping Γ (tcase t1 t2 t3) C.
intros.
Admitted. (* TODO: This is gonna be quite a pain.
 I guess it's consoling that it's a pain directly too?
 (see below, or the partial sn proof) *)


Lemma norm_rec G F M (t : tm G) : normalizing (trec F t M) -> normalizing t.
intros. inversion H; subst. clear H.
dependent induction H0. inversion H1; subst. inversion H; subst; eauto.
inversion H; subst.
eapply CR2; eauto.
eauto.
Qed.

Lemma rec_cand (F : functor (snoc nil type)) C (M : tm (snoc nil tt)) :
    candidate C
 -> candidate (circ C (fun G t => trec F t M)).
intros. unfold circ.
split.
(* CR1 *)
intros G t Hy0.
eapply norm_rec. eapply CR1; eauto.
(* CR2 *)
intros G t' Hy0 t s.
eapply CR2; eauto.
(* CR3 *)
intros G t Hy0.
eapply CR3; eauto.
Qed.

Lemma star_adj A B f : Rarrow A (circ B f) -> Rarrow (star A f) B.
repeat intro.
destruct H0. destruct H0. subst.
eapply H. auto.
Qed.

Lemma star_adj' A B f : Rarrow (star A f) B -> Rarrow A (circ B f).
repeat intro. unfold circ. eapply H.
firstorder.
Qed.

Inductive SemTypings : forall Δ (ρ₁ : Rsub Δ) (η : map_arrow Δ) (ρ₂ : Rsub Δ), Prop :=
| rnil : @SemTypings nil tt gnil tt
| rsnoc : forall Δ ρ₁ η ρ₂ A B (M : tm (snoc nil tt)), @SemTypings Δ ρ₁ η ρ₂
 -> Rarrow A (circ B (fun G t => app_tsub _ M (tt , t)))
 -> @SemTypings (snoc Δ type) (ρ₁ , A) (gsnoc η M) (ρ₂ , B).

Lemma Red_map1 (F : functor (snoc nil type)) A B (M : tm (snoc nil tt)) :
   Rarrow A (circ B (fun G t => app_tsub _ M (tt , t)))
-> Rarrow (RedF F (tt , A))
    (circ (RedF F (tt , B)) (fun G t => tmap1 F M t)).
Admitted. (* TODO: IMPORTANT *)


Lemma Red_rec'' (F : functor (snoc nil type)) C (M : tm (snoc nil tt)) :
    candidate C
 -> Rarrow (RedF F (tt , C)) (circ C (fun G t => app_tsub _ M (tt , t)))
 -> Rarrow (Red (mu F)) (circ C (fun G t => trec F t M)).
intros.
set (D := (circ C (fun G t => trec F t M))).
assert (candidate D). eapply rec_cand; auto.
unfold Red. simpl.
eapply lfp_ind.
auto.
eapply adjunction_closure. auto.
eapply star_adj. unfold D.
unfold circ.
intros G t Hy.
eapply CR2. auto. Focus 2. eapply step_star_mu.
eapply H0.
eapply Red_map1.
unfold circ. unfold app_tsub. simpl.
Focus 2. eexact Hy. firstorder.
Qed.

Lemma Mu_inj Δ (F : functor (snoc Δ type)) ρ :
 Rarrow (RedF F (ρ , (RedF (mu F) ρ)))
        (circ (RedF (mu F) ρ) tinj).
intros G t Hy0. unfold circ. simpl.
eapply lfp_inj.
admit. (* TODO *)
intros. eapply closure_cand.
eapply star_adj. unfold circ. intros G0 t0 Hy1.
eauto.
eapply closure_unit.
exists t. split. auto. auto.
Qed. (* This is Lemma 19.12 *)

Lemma Rarrow_id C : Rarrow C C. firstorder. Qed.

Hint Resolve RedF_candidate.

Print Rarrow.
Definition FancyArrow (R1 : Rel) (f : forall G, tm G -> tm G) (R2 : Rel) :=
 Rarrow R1 (circ R2 f).


Lemma Times_tpair G (F H : Rel) (t1 t2 : tm G) :
 candidate F -> candidate H -> F _ t1 -> H _ t2 -> Times F H (tpair t1 t2).
intros.
split; unfold circ; simpl.
eapply CR2; eauto.
eapply CR2; eauto.
Qed. (* TODO: This is kind of redundant with the semantic typing lemma for tpair *)

Lemma Red_map_times Δ (F : functor Δ) F1 F2 H H1 H2 η ρ₁ ρ₂
 (Hyp1 : Rsub_candidates Δ ρ₁)
 (Hyp2 : Rsub_candidates Δ ρ₂) :
   candidate F1 -> candidate F2 -> candidate H1 -> candidate H2
-> FancyArrow F1 (fun _ t => tmap F t η) F2
-> FancyArrow H1 (fun _ t => tmap H t η) H2
-> FancyArrow (Times F1 H1) (fun _ t => tmap (times F H) t η) (Times F2 H2).
intros.
intros G t Hy. unfold circ.
eapply CR2. eauto.
Focus 2. eauto. destruct Hy.
eapply Times_tpair; firstorder.
Qed.

Lemma tmap_mu_norm Δ (F : functor (snoc Δ type)) η G (t : tm G) :
 normalizing (tmap (mu F) t η) -> normalizing t.
intros.
inversion H; subst. clear H.
dependent induction H0.
inversion H1; subst. inversion H; subst. eauto.
inversion H; subst.
simpl_existT. simpl_existT. subst.
eapply CR2; eauto.
eauto.
Qed.

Lemma cand_tmap_mu Δ (F : functor (snoc Δ type)) η C :
 candidate C -> candidate (circ C (fun _ t => tmap (mu F) t η)).
intros. unfold circ. split.
(* CR1 *)
intros G t Hy. eapply tmap_mu_norm. eapply CR1; eauto.
(* CR2 *)
intros G t' Hy t s. eapply CR2; eauto.
(* CR3 *)
intros G t Hy. eapply CR3; eauto.
Qed.

Lemma Red_map Δ (F : functor Δ) ρ₁ ρ₂ η (Hyp : Rsub_candidates Δ ρ₁) :
   Rsub_candidates Δ ρ₂
-> SemTypings ρ₁ η ρ₂
-> FancyArrow (RedF F ρ₁) (fun G t => tmap F t η) (RedF F ρ₂).
intros.
induction F; simpl.
Focus 3. (* Times *)
eapply Red_map_times; eauto.

Focus 4. (* Mu *)
unfold FancyArrow.
set (C := (circ (Mu (fun R : Rel => RedF F (ρ₂, R)))
        (fun (G : ctx scope) (t : tm G) => tmap (mu F) t η))).
assert (candidate C). eapply cand_tmap_mu; eauto.
eapply lfp_ind; eauto.
eapply adjunction_closure; eauto.
eapply star_adj.
unfold C. unfold circ.
intros G t Hy.
eapply CR2; eauto.
eapply Mu_inj.
eapply IHF; eauto.
split; eauto.
split; simpl; eauto.
econstructor; simpl; eauto.
eapply Rarrow_id.
(* Yay! *)


(*

Lemma Red_case G T S C t1 t2 t3 : IsMorphism G t1 (plus T S) -> IsMorphism (snoc G T) t2 C -> IsMorphism (snoc G S) t3 C
 -> IsMorphism G (tcase t1 t2 t3) C.
repeat intro. unfold Red. unfold IsMorphism in *.
destruct (H _ _ H2).
destruct H3. destruct H3.
eapply Red_closed_star. Focus 2.
simpl.
eapply (closed_star_map (fun u => tcase u _ _)). eauto.
eassumption.
eapply Red_closed. Focus 2. eapply step_SN_plus1.
eapply Red_SN; eauto.
eapply Red_SN; eauto.
simpl.
eapply Red_closed_eq.
eapply (H0 _ (s, x)). split; simpl; eauto.
admit. (* TODO: Stupid equations *)
destruct H3.
destruct H3. destruct H3.
simpl.
eapply Red_closed_star. Focus 2. eapply (closed_star_map (fun u => tcase u _ _)). eauto.
eassumption.
eapply Red_closed. Focus 2. eapply step_SN_plus2; eauto.
eapply Red_SN. eassumption.
eapply Red_SN; eauto.
eapply Red_closed_eq.
eapply (H1 _ (s, x)).
split; simpl; auto.
admit. (* TODO: Stupid equations *)

destruct H3. destruct H3. simpl.
eapply Red_closed_star. Focus 2. eapply (closed_star_map (fun u => tcase u _ _)). eauto.
eassumption.
eapply Red_SNe.
econstructor. eauto.
eapply Red_SN.
eauto.
eapply Red_SN. eauto.
Qed.

Lemma Red_inl G T S t : IsMorphism G t T -> IsMorphism G (tinl t) (plus T S).
repeat intro. unfold IsMorphism in *. unfold Red. simpl.
left.
eexists. split. econstructor.
eapply H. auto.
Qed.

Lemma Red_inr G T S t : IsMorphism G t S -> IsMorphism G (tinr t) (plus T S).
repeat intro. unfold IsMorphism in *. unfold Red. simpl.
right. left.
eexists. split. econstructor.
eapply H. auto.
Qed.

Lemma Red_top G T : IsMorphism (snoc G T) (tv top) T.
repeat intro. simpl in *. tauto.
Qed.

Lemma Red_lam G T S t : IsMorphism (snoc G T) t S -> IsMorphism G (tlam t) (arrow T S).
unfold IsMorphism in *. unfold Red. simpl.
repeat intro. 
eapply Red_closed. Focus 2. eapply step_SN_arrow.
eapply Red_SN. eauto.
eapply Red_closed_eq.
eapply (H _ (compose_tsub_vsub w s, u)).
split; simpl.
eapply RedS_closed_vsub; eauto.
eauto.
admit. (* TODO: Stupid equations *)
Qed.

Lemma Red_app G T S t1 t2 : IsMorphism G t1 (arrow T S) -> IsMorphism G t2 T -> IsMorphism G (tapp t1 t2) S.
unfold IsMorphism in *. unfold Red. simpl. repeat intro.
eapply Red_closed_eq.
eapply (H _ _ H1 _ idvsub).
eapply H0. eassumption.
admit. (* TODO: Stupid equations *)
Qed.

Lemma Red_rec G F C t1 t2
 (Hy : (forall G1 (t : tm G1), RedF F (tt, (fun G2 (y : tm G2) => Red C (trec F C y t2))) t -> RedF F (tt, Red C) (tmap1 F C (mu F) (trec F C (tv top) t2) t)))
 : IsMorphism G t1 (mu F) -> IsMorphism (snoc nil (app_fsub1 F C)) t2 C
 -> IsMorphism G (trec F C t1 t2) C.
repeat intro.
set (P := (fun G (t : tm G) => Red C (trec F C t t2))).
assert (candidate P) as candP.

(* Showing that it's a candidate *)
split.

(* closed under SN *)
repeat intro.
unfold P in *.
eapply Red_closed. eexact H2.
econstructor. eauto.

(* neutral *)
repeat intro. unfold P.
eapply Red_SNe. econstructor. auto.
eapply Red_SN. eapply Red_closed_eq. eapply (H0 _ idtsub).
simpl; split; auto.
eapply Red_SNe. eauto.
admit. (* TODO: Stupid equations *)

(* normal *)
repeat intro. unfold P in *.
eapply SN_inversion_rec. eapply Red_SN.
eassumption.

(* Resume *)
unfold IsMorphism in H. unfold Red in H. simpl in H.
specialize (H _ _ H1 P). simpl in H.
eapply H.
repeat intro.
unfold P.
unfold IsMorphism in H0.
destruct H2. destruct H2. destruct H2.
eapply Red_closed_star. Focus 2. eapply (closed_star_map (fun t => trec F C t t2)). eauto.
eexact H2.
eapply Red_closed. Focus 2. eapply step_SN_mu.
eapply (RedF_SN F). Focus 2. eexact H3.
split; simpl; auto.

eapply H0.
split; simpl. auto.
eapply Red_compositional.
unfold P in H3.
eauto. (* This is where we use the fancy parameter *) 

destruct H2. destruct H2.
eapply Red_closed_star. Focus 2. eapply (closed_star_map (fun t => trec F C t t2)). eauto.
eassumption.
eapply Red_SNe. 
constructor. auto.
eapply Red_SN.
eapply Red_closed_eq.
eapply (H0 _ idtsub).
split; simpl; auto.
eapply Red_SNe.
eauto.
admit. (* TODO: Stupid equations *)
Qed.

Lemma Red_inj G F t : IsMorphism G t (app_fsub1 F (mu F)) -> IsMorphism G (tinj t) (mu F).
unfold IsMorphism in *. unfold Red. simpl.
intros H G' s reds.
eapply RedF_mu_inj.
left.
eexists. split. econstructor.
eapply Red_compositional.
eapply H. auto.
Qed.

Lemma Red_out G F t : IsMorphism G t (nu F) -> IsMorphism G (tout t) (app_fsub1 F (nu F)).
unfold IsMorphism. unfold Red. simpl.
intros.
pose proof (H _ _ H0).
eapply RedF_nu_out in H1.
destruct H1.
eapply Red_compositional.
auto.
Qed.

Lemma IsMorphism_closed_wkn G T t S : IsMorphism G t T -> IsMorphism (snoc G S) (wkn_tm t) T.
unfold IsMorphism. unfold wkn_tm. repeat intro.
destruct s.
Admitted.

Hint Resolve Red_pair Red_fst Red_snd Red_case Red_inl Red_inr Red_top.

Lemma RedF_map D (F : functor D) : forall G (t : tm (forget G))  (s1 s2 : fsub D nil) (a : map_arrow D) (a_wf : map_arr_red D a s1 s2),
  IsMorphism G t (app_fsub _ F s2) -> IsMorphism G (tmap F s1 s2 a t) (app_fsub _ F s1).
induction F; intros; simpl.
admit. (* TODO *)

(* Case: arrow *)
eapply Red_lam.
eapply IHF2. auto.
eapply Red_app.
Focus 2. eauto.
eapply IsMorphism_closed_wkn.
eassumption.

(* Case: times *)
eapply Red_pair; eauto.

(* Case: plus *)
eapply Red_case; eauto.
eapply Red_inl. eapply IHF1; eauto.
eapply Red_inr. eapply IHF2; eauto.

(* Case: mu *)
unfold IsMorphism in *. intros.
set (C := mu (app_fsub (snoc nil type) F (extfsub s1))).

set (t2 := (tinj (tmap F (s1, C) (s2, C) (a, tv top) (tv top)))).
(*eapply Red_rec.
intros.
unfold t2 in *. simpl. *)

set (P := (fun G (t : tm G) => Red C (trec (app_fsub (snoc nil type) F (extfsub s2)) C t t2))).
assert (candidate P) as candP.

(* Showing that it's a candidate *)
admit.

(* Resume *)
unfold IsMorphism in H. unfold Red in H. simpl in H.
specialize (H _ _ H0 P). simpl in H.
eapply H.
intros G0 t0 H1.
unfold P.
unfold IsMorphism in H0.
destruct H1. destruct H1. destruct H1.
eapply Red_closed_star. Focus 2. eapply (closed_star_map (fun t => trec _ C t t2)). eauto.
eassumption.
eapply Red_closed. Focus 2. eapply step_SN_mu.
eapply (RedF_SN (app_fsub (snoc nil type) F (extfsub s2))). Focus 2. eapply H2.
split; simpl; auto.

simpl.
Admitted.

Lemma Red_map (f : tm (snoc nil tt)) (F : functor (snoc nil type)) T1 T2 (R1 R2 : Rel) : (forall G (t : tm G), R1 G t -> R2 G (app_tsub _ f (tt, t)))
 -> (forall G (t : tm G), RedF F (tt, R1) t -> RedF F (tt, R2) (tmap1 F T1 T2 f t)).

Admitted.
(* TODO: This is an important lemma! *)




Lemma main_lemma G T (t : tm (forget G)) (d : oft G t T)
  : IsMorphism G t T.
induction d; simpl; intros G' s reds.
eapply RedS_lookup; auto.

(* Case: lam *)
eapply Red_lam; eauto.

(* Case: app *)
eapply Red_app; eauto.

(* Case: pair *)
eapply Red_pair; eauto.

(* Case: fst *)
eapply Red_fst; eauto.

(* Case: snd *)
eapply Red_snd; eauto.

(* Case: inl *)
eapply Red_inl; eauto.

(* Case: inr *) 
eapply Red_inr; eauto.

(* Case: case *)
eapply Red_case; eauto.

(* Case: inj *)
eapply Red_inj; eauto.

(* Case: rec *)
pose proof (IHd1 _ s reds).
unfold Red in H. simpl in H.
specialize (H (fun G t => Red C (trec F C t t2))).
eapply H.
intros G'' t' H1.
destruct H1.
(* Subcase: --> inj *)
destruct H0. destruct H0.
eapply Red_closed_star.
Focus 2.
eapply (closed_star_map (fun t => trec F C t t2)). intros. econstructor. auto.
eassumption.

eapply Red_closed. Focus 2.
eapply step_SN_mu.
eapply (RedF_SN F). Focus 2. eassumption. simpl.
split. auto.

(* annoying bit about showing this is a candidate *)
split.
intros G1 u1 Hy u2 Hy0.
eapply Red_closed. eexact Hy.
econstructor. auto.

intros G1 u1 Hy. eapply Red_SNe. econstructor. auto.
eapply Red_SN.
eapply Red_closed_eq. eapply (IHd2 _ idtsub).
simpl. split. auto. eapply Red_SNe. auto.
admit. (* TODO: Stupid equations *)

intros G1 u1 Hy.
pose proof (Red_SN _ _ Hy).
eapply SN_inversion_rec.
eassumption.
(* end annoying bit *)

eapply IHd2.
simpl. split. auto. 
eapply Red_compositional.
eapply Red_map. Focus 2. eassumption.
simpl. auto.

(* Subcase: neutral *)
destruct H0. destruct H0.
eapply Red_closed_star. Focus 2.
eapply (closed_star_map (fun t => trec F C t t2)). intros. econstructor. auto.
eassumption.
eapply Red_SNe. econstructor. auto.
pose proof (IHd2 _ idtsub (RedS_id _)).
simpl in H2.
eapply Red_SN.
eapply Red_closed_eq.
eassumption.
admit. (* TODO: Stupid equations *)

(* Case: out *)
eapply Red_out; eauto.

(* Case: corec *)

set (P := (fun G (t : tm G) => (exists u v, step_SN_star t (tcorec F C u v) /\ Red C u
                                /\ (IsMorphism (snoc nil C) v (app_fsub1 F C)))
                              \/ (exists t', step_SN_star t t' /\ SNe t'))).
assert (candidate P) as candP.
split.
intros G0 u Hy u' Hy0.
destruct Hy. destruct H. destruct H. destruct H. destruct H0.
left. eexists. eexists. split. eapply step_SN_star_step.
eassumption. eassumption. auto.
destruct H. destruct H. right. eexists. split.
eapply step_SN_star_step. eassumption. eassumption. auto.

intros G0 u Hy. right. eexists. split. econstructor. auto.

intros G0 u Hy. destruct Hy.
destruct H. destruct H. destruct H. destruct H0.

assert (SN x0) as SN_x0.
eapply Red_SN.
eapply Red_closed_eq.
eapply (H1 _ idtsub).
eapply RedS_id.
admit. (* TODO: Stupid equations *)

eapply sn_closed_step_star. eassumption.
eapply sn_corec. eapply Red_SN; eauto.
auto.

destruct H. destruct H. eapply sn_closed_step_star; eauto.

exists P.
split.

intros G0 u1 Hy.
destruct Hy. destruct H. destruct H. destruct H. destruct H0.

assert (SN x0) as SN_x0.
eapply Red_SN.
eapply Red_closed_eq.
eapply (H1 _ idtsub).
eapply RedS_id.
admit. (* TODO: Stupid equations *)

split. eapply sn_closed_step_star. eassumption.
eapply sn_corec.
eapply Red_SN; eauto.
auto.

eapply RedF_closed_star.
simpl. split. auto.
auto.
Focus 2.
eapply closed_star_out.
eassumption.
eapply RedF_closed.
split; simpl; auto.

Focus 2.
eapply step_SN_nu.
eapply Red_SN; eauto.
auto.

eapply (Red_map _ F _ _ (Red C)).
simpl.
Focus 2.
eapply Red_compositional.
eapply H1.
split; simpl; auto.

intros.
unfold P.
left. eexists. eexists. split. econstructor. split. eauto. 
auto.

destruct H. destruct H.
split.
eapply sn_closed_step_star.
eassumption. eauto.
eapply RedF_closed_star.
split; simpl; auto.
Focus 2. eapply closed_star_out.
eassumption.
eapply RedF_SNe.
simpl; auto.
eauto.

left. eexists. eexists. split.
econstructor.
split.
eapply IHd1. eauto.
eapply IHd2.
Qed.


Corollary strong_norm G T (t : tm (forget G)) (d : oft G t T) : SN t.
eapply (Red_SN T).
eapply Red_closed_eq.
eapply main_lemma.
eexact d.
eapply RedS_id.
admit. (* TODO: Stupid equations *)
Qed.
Print Assumptions strong_norm.
(* TODO: Important! Show soundness of SN for sn *)



(* Interesting side notes:
   - This syntactic characterization of SN would work in LF (Andreas observed this -- he did SN in Twelf)
   - View it as an initial algebra in a presheaf category (just like LF definitions, duh)
     and get the weakening in SN for free.
*)
