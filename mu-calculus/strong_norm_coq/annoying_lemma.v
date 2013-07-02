Set Implicit Arguments.
Inductive ctx (A : Type) : Type :=
 | cnil : ctx A
 | snoc : ctx A -> A -> ctx A.
Implicit Arguments cnil [A].

Inductive var (A : Type) : ctx A -> A -> Type :=
 | top : forall G T, var (snoc G T) T
 | pop : forall G T S, var G T -> var (snoc G S) T.
Implicit Arguments top [A G T].
Implicit Arguments pop [A G T S].

Open Scope type_scope.
Fixpoint gsub (A : Type) (G : ctx A) (F : A -> Type) : Type :=
match G with
| cnil => unit
| snoc G' T => (gsub G' F) * (F T)
end.

Inductive gsub' (A : Type) (F : A -> Type) : forall (Γ : ctx A), Type :=
| gnil : gsub' F cnil
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
| cnil => fun s => s
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
| cnil => tt
| snoc G' T => extvsub (idvsub G')
end.
Implicit Arguments idvsub [A G].

Definition weakening_vsub (A : Type) (G : ctx A) T : vsub G (snoc G T) :=
wknvsub G G T idvsub.

Inductive sort : Type :=
 | type : sort.

Inductive functor (D : ctx sort) : Set :=
 | fv : forall T, var D T -> functor D
 | arrow : functor cnil -> functor D -> functor D
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
| cnil => tt
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

Definition tp := functor cnil.

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
 | trec : forall (F : functor (snoc cnil type)), tm G -> tm (snoc cnil tt) -> tm G
 | tout : tm G -> tm G
 | tcorec : functor (snoc cnil type) -> tm G -> tm (snoc cnil tt) -> tm G
 | tmap : forall Δ (F : functor Δ), tm G -> gsub' (fun _ => tm (snoc cnil tt)) Δ -> tm G
.

Definition map_arrow (Δ : ctx sort) : Type :=
gsub' (fun _ => tm (snoc cnil tt)) Δ.

Fixpoint forget (G : ctx tp) : ctx scope :=
match G with
| cnil => cnil
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
 | tprec : forall G F C t1 t2, oft G t1 (mu F) -> oft (snoc cnil (app_fsub1 F C)) t2 C -> oft G (trec F t1 t2) C
 | tpout : forall G F t, oft G t (nu F) -> oft G (tout t) (app_fsub1 F (nu F))
 | tpcorec : forall G F C t1 t2, oft G t1 C -> oft (snoc cnil C) t2 (app_fsub1 F C) -> oft G (tcorec F t1 t2) (nu F)
 | tpmap : forall Δ Γ (F : functor Δ) ρ₁ ρ₂ η M, oft Γ M (app_fsub _ F ρ₁)
   -> ofts ρ₁ η ρ₂ -> oft Γ (tmap F M η) (app_fsub _ F ρ₂) 
with ofts : forall Δ (ρ₁ : fsub Δ cnil) (η : map_arrow Δ) (ρ₂ : fsub Δ cnil), Prop :=
 | onil : @ofts cnil tt gnil tt
 | osnoc : forall Δ (ρ₁ : fsub Δ cnil) η ρ₂ A M B, ofts ρ₁ η ρ₂ -> oft (snoc cnil A) M B
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
| cnil => tt
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

(* Gotta define map... *)


(*
Fixpoint tmap D (F : functor D) (s1 s2 : fsub D nil) (a : map_arrow D) G (t : tm G) : tm G :=
match F with
| fv _ X => app_tsub _ (glookup _ X a) (tt, t)
| arrow T F2 => tlam (tmap F2 s1 s2 a (tapp (wkn_tm t) (tv top)))
| times F1 F2 => tpair (tmap F1 s1 s2 a (tfst t)) (tmap F2 s1 s2 a (tsnd t))
| plus F1 F2 => tcase t (tinl (tmap F1 s1 s2 a (tv top))) (tinr (tmap F2 s1 s2 a (tv top)))
| mu F1 => trec (app_fsub _ F1 (extfsub s2)) (app_fsub _ (mu F1) s1) t (tinj (tmap F1 (s1, app_fsub _ (mu F1) s1) (s2, app_fsub _ (mu F1) s1) (a, (tv top)) (tv top)))
| nu F1 => tcorec (app_fsub _ F1 (extfsub s1)) (app_fsub _ (nu F1) s2) t (tmap F1 (s1, app_fsub _ (nu F1) s2) (s2, app_fsub _ (nu F1) s2) (a, (tv top)) (tout (tv top)))
end. *)

(* TODO: DO the typing lemma for map and type preservation! Because I'm not sure I believe I got these definitions right *)

Definition tmap1 (F : functor (snoc cnil type)) G (f : tm (snoc cnil tt)) (t : tm G) : tm G :=
tmap F t (gsnoc gnil f).

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
| step_rec1 : forall F (t1 t1' : tm G) (t2 : tm (snoc cnil tt)), step t1 t1' -> step (trec F t1 t2) (trec F t1' t2)
(*| step_rec2 : forall F (t1 : tm G) (t2 t2' : tm (snoc cnil tt)), @step _ t2 t2' -> step (trec F t1 t2) (trec F t1 t2') *)
| step_out : forall (t t' : tm G), step t t' -> step (tout t) (tout t')
| step_corec1 : forall F (t1 t1' : tm G) (t2 : tm (snoc cnil tt)), step t1 t1' -> step (tcorec F t1 t2) (tcorec F t1' t2)
| step_corec2 : forall F (t1 : tm G) (t2 t2' : tm (snoc cnil tt)), @step _ t2 t2' -> step (tcorec F t1 t2) (tcorec F t1 t2')

| step_arrow : forall (t1 : tm (snoc G tt)) (t2 : tm G), step (tapp (tlam t1) t2) (app_tsub1 t1 t2)
| step_times1 : forall (t1 : tm G) (t2 : tm G), step (tfst (tpair t1 t2)) t1
| step_times2 : forall (t1 : tm G) (t2 : tm G), step (tsnd (tpair t1 t2)) t2
| step_plus1 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)), step (tcase (tinl t1) t2 t3) (app_tsub1 t2 t1)
| step_plus2 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)), step (tcase (tinr t1) t2 t3) (app_tsub1 t3 t1)
| step_mu : forall F (t1 : tm G) (t2 : tm (snoc cnil tt)),
   step (trec F (tinj t1) t2) (app_tsub _ t2 (tt, tmap1 F (trec F (tv top) t2) t1))
| step_nu : forall F (t1 : tm G) (t2 : tm (snoc cnil tt)),
   step (tout (tcorec F t1 t2)) (tmap1 F (tcorec F (tv top) t2) (app_tsub _ t2 (tt, t1)))
| step_map : forall Δ (F : functor Δ) M M' η,
     step M M'
  -> step (tmap F M η) (tmap F M' η)
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

Inductive sn G : tm G -> Prop :=
| con_sn : forall t, (forall t', step t t' -> sn t') -> sn t.

Inductive context1 (G : ctx scope) : Set :=
 | capp : tm G -> context1 G
 | cfst : context1 G
 | csnd : context1 G
 | ccase : tm (snoc G tt) -> tm (snoc G tt) -> context1 G
 | crec : forall (F : functor (snoc cnil type)), tm (snoc cnil tt) -> context1 G
 | cout : context1 G
 | cmap : forall Δ (F : functor (snoc Δ type)), gsub' (fun _ => tm (snoc cnil tt)) Δ -> context1 G
.

Definition plug0 G (c : context1 G) : tm G -> tm G :=
match c with
| capp M => fun N => tapp N M
| cfst => fun N => tfst N
| csnd => fun N => tsnd N
| ccase M1 M2 => fun N => tcase N M1 M2
| crec F M => fun N => trec F N M
| cout => fun N => tout N
| cmap D F n => fun N => tmap (mu F) N n
end.


Definition context (G : ctx scope) : Set := list (context1 G).


Fixpoint plug G (ε : context G) (N : tm G) : tm G :=
match ε with
| nil => N
| cons ε1 ε' => plug ε' (plug0 ε1 N)
end.

Inductive step_SN G : tm G -> tm G -> Prop :=
(*| step_SN_app : forall (t t' : tm G) (u : tm G), step_SN t t' -> step_SN (tapp t u) (tapp t' u) *)
| step_SN_arrow : forall (t : tm (snoc G tt)) (u : tm G), sn u -> step_SN (tapp (tlam t) u) (app_tsub1 t u)
(*| step_SN_fst : forall (t t' : tm G), step_SN t t' -> step_SN (tfst t) (tfst t') 
| step_SN_snd : forall (t t' : tm G), step_SN t t' -> step_SN (tsnd t) (tsnd t') *)
| step_SN_times1 : forall (t1 : tm G) (t2 : tm G), sn t2 -> step_SN (tfst (tpair t1 t2)) t1
| step_SN_times2 : forall (t1 : tm G) (t2 : tm G), sn t2 -> step_SN (tsnd (tpair t1 t2)) t2
(*| step_SN_case : forall (t t' : tm G) (t1 : tm (snoc G tt)) t2, step_SN t t' -> step_SN (tcase t t1 t2) (tcase t' t1 t2) *)
| step_SN_plus1 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)),
                  sn t1 -> @sn _ t3 -> step_SN (tcase (tinl t1) t2 t3) (app_tsub1 t2 t1)
| step_SN_plus2 : forall (t1 : tm G) (t2 : tm (snoc G tt)) (t3 : tm (snoc G tt)),
                  sn t1 -> @sn _ t2 -> step_SN (tcase (tinr t1) t2 t3) (app_tsub1 t3 t1)
(*| step_SN_rec1 : forall F (t1 t1' : tm G) (t2 : tm (snoc nil tt)), step_SN t1 t1' -> step_SN (trec F t1 t2) (trec F t1' t2)

| step_SN_out : forall (t t' : tm G), step_SN t t' -> step_SN (tout t) (tout t') *)
| step_SN_mu : forall F (t1 : tm G) (t2 : tm (snoc cnil tt)),
   sn t1 -> 
   step_SN (trec F (tinj t1) t2) (app_tsub _ t2 (tt, tmap1 F (trec F (tv top) t2) t1))
| step_SN_nu : forall F (t1 : tm G) (t2 : tm (snoc cnil tt)),
   sn t1 -> @sn _ t2 ->
   step_SN (tout (tcorec F t1 t2)) (tmap1 F (tcorec F (tv top) t2) (app_tsub _ t2 (tt, t1)))
.

Inductive mstep G : tm G -> tm G -> Prop :=
| mrefl : forall M, mstep M M
| mtrans : forall M1 M2 M3, mstep M1 M2 -> mstep M2 M3 -> mstep M1 M3
| mone : forall M1 M2, step M1 M2 -> mstep M1 M2.

Inductive cstep_SN G : tm G -> tm G -> Prop :=
| cstep_con : forall ε M M', step_SN M M' -> cstep_SN (plug ε M) (plug ε M').


Inductive hstep1 (G : ctx scope) : context1 G -> context1 G -> Prop :=
| hstep_appr : forall t2 t3 , step t2 t3 -> hstep1 (capp t2) (capp t3)
| hstep_case1 : forall t1 t1' t2, @step _ t1 t1' -> hstep1 (ccase t1 t2) (ccase t1' t2)
| hstep_case2 : forall t1 t2 t2', @step _ t2 t2' -> hstep1 (ccase t1 t2) (ccase t1 t2')
.

Inductive hstep (G : ctx scope) : context G -> context G -> Prop :=
| hstep_cons1 : forall ε c1 c2, hstep1 c1 c2 -> hstep (cons c1 ε) (cons c2 ε)
| hstep_cons2 : forall ε ε' c, hstep ε ε' -> hstep (cons c ε) (cons c ε')
.


Require Import Coq.Program.Equality.
Hint Constructors hstep hstep1 step_SN cstep_SN mstep step.

Lemma mstep_sub G (t t0 : tm (snoc G tt)) (t3 : tm G) : mstep t t0 -> mstep (app_tsub1 t t3) (app_tsub1 t0 t3).
Admitted.
Hint Resolve mstep_sub.

Lemma annoying1 G c : forall (M N : tm G) c1, step (plug0 c (plug0 c1 M)) N ->
    (exists M', step (plug0 c1 M) M')
 \/ (exists c', hstep1 c c').
induction c; simpl in *; intros.
inversion H; subst; eauto; destruct c1; discriminate.
inversion H; subst; eauto; destruct c1; discriminate.
inversion H; subst; eauto; destruct c1; discriminate.
inversion H; subst; eauto; destruct c1; discriminate.
inversion H; subst; eauto; destruct c1; discriminate.
inversion H; subst; eauto; destruct c1; discriminate.
inversion H; subst; eauto; destruct c1; discriminate.
Qed.

Lemma annoying G ε : forall (M N : tm G) ε1, step (plug ε (plug0 ε1 M)) N ->
    (exists M', step (plug0 ε1 M) M')
 \/ (exists ε', hstep ε ε').
induction ε; simpl in *; intros.
eauto.
destruct (IHε _ _ a H).
destruct H0.
destruct (annoying1 _ _ _ H0); eauto.
destruct H1.
right. eexists. econstructor 1. eauto.
destruct H0.
right. eexists. econstructor 2. eauto.
Qed.