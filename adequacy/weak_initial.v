Set Implicit Arguments.

Lemma cong {A B : Set} (f : A -> B) x y : x = y -> f x = f y.
intros. rewrite H. reflexivity.
Qed.



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

Lemma gmap_funct (R1 R2 R3 : Tp -> Set) (f : forall T, R1 T -> R2 T) (g : forall T, R2 T -> R3 T) {G : Ctx Tp} (s : Gsubst R1 G) :
 gmap R2 R3 g (gmap R1 R2 f s) = gmap R1 R3 (fun T x => g T (f T x)) s.
induction G; simpl; intros. reflexivity.
erewrite IHG.
reflexivity.
Qed.

Lemma gmap_cong (R1 R2 : Tp -> Set) (f1 f2 : forall T, R1 T -> R2 T) {G : Ctx Tp} (s : Gsubst R1 G) :
 (forall T x, f1 T x = f2 T x) -> gmap R1 R2 f1 s = gmap R1 R2 f2 s.
induction G; simpl; intros. reflexivity. erewrite IHG.
erewrite H.
reflexivity.
exact H.
Qed.

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

Definition scomp {G1 G2 G3} (s1 : Subst G2 G1) (s2 : Subst G3 G2) : Subst G3 G1 :=
gmap (Tm G2) (Tm G3) (fun T t => subst t s2) s1.

Lemma substlemma {G1 G2 G3} T (t : Tm G1 T) (s1 : Subst G2 G1) (s2 : Subst G3 G2) :
 subst (subst t s1) s2 = subst t (scomp s1 s2).
Admitted.
Lemma substlemma2 {G1 G2 G3 T} (s1 : Subst G2 G1) (s2 : Subst G3 G2) (t : Tm G3 T) :
 scomp (Sextend T s1) (pair s2 t) = pair (scomp s1 s2) t.
Admitted.
Lemma substcomm {G1 G2 T S} (t : Tm (snoc G1 S) T) (s : Subst G2 G1) (u : Tm G2 S) :
 topsubst (subst t (Sextend S s)) u = subst t (pair s u).
Admitted.
Lemma substid {G T} (t : Tm G T) : subst t (idsubst G) = t.
Admitted.

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
Hint Constructors Mstep.


Inductive Val : Tm nil Nat -> Set :=
 | vzero : Val zero
 | vsucc : forall n, Val n -> Val (succ n)
.
Hint Constructors Val.

Fixpoint Red (T : Tp) : Tm nil T -> Set :=
match T as T return Tm nil T -> Set with
| Nat => fun t => { v : Tm nil Nat & (Mstep t v * Val v) }
| Arr U V => fun t => forall x, Red x -> Red (app t x)
| Prod U V => fun t => Red (fst' t) * Red (snd' t)
end.

Fixpoint RedS (G : Ctx Tp) : Subst nil G -> Set :=
match G as G return Subst nil G -> Set with
| nil => fun s => unit
| snoc G' T => fun s => (RedS G' (fst s)) * (Red (snd s))
end.


Lemma bwkclosed1 T (t t' : Tm nil T) : Mstep t t' -> Red t' -> Red t.
induction T; simpl; intros.
destruct H0. destruct p.
exists x. eauto.
destruct H0. split; eauto.
eauto.
Qed.

Lemma lookup1 G T (x : Var G T) (s : Subst nil G) (sred : RedS G s) : Red (lookup x s).
induction x; simpl; intros; destruct sred; auto.
Qed.

Hint Resolve bwkclosed1.

Lemma main1 G T (t : Tm G T) (s : Subst nil G) (sred : RedS G s) : Red (subst t s).
induction t; intros; simpl in *.
eapply lookup1; auto.
split; eauto.
firstorder.
firstorder.
exists zero. eauto.
specialize (IHt s sred).
destruct IHt. destruct p. exists (succ x). firstorder.
destruct (IHt3 s sred). destruct p.
clear IHt3.
eapply bwkclosed1.
eapply siter. eapply srefl. eapply srefl. eexact m.
clear m. clear t3.
induction v.
eapply bwkclosed1. eapply beta_nat1. auto.
eapply bwkclosed1. eapply beta_nat2. unfold topsubst. simpl.
specialize (IHt1 (pair s (iter (subst t1 (Sextend C s)) (subst t2 s) n))).
simpl in IHt1.
eapply eq_rec. Focus 2. symmetry. eapply (substcomm t1 s).
eapply IHt1. eauto.
intros.
eapply bwkclosed1. eapply beta_arr.
eapply eq_rec. Focus 2. symmetry. eapply substcomm.
eauto.
firstorder.
Qed.

(* Weak norm. for terms at type nat, yay *)




Definition inat : Set := forall (C : Set), (C -> C) -> C -> C.

Definition isucc (n : inat) : inat := fun C f i => f (n C f i).
Definition izero : inat := fun C f i => i.
Definition iiter {C : Set} (f : C -> C) (i : C) (n : inat) := n C f i.

Fixpoint SemT (T : Tp) : Set := match T with
 | Nat => inat
 | Prod U V => (SemT U) * (SemT V)
 | Arr U V => SemT U -> SemT V
end.

Definition SemC (G : Ctx Tp) : Set := Gsubst SemT G.

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

Require Import Coq.Logic.FunctionalExtensionality.


Definition comp2 {G1 G2} (s : Subst G2 G1) e := gmap (Tm G2) SemT (fun T t => Sem t e) s.
Definition comp2v {G1 G2} (s : VSubst G2 G1) e := gmap (Var G2) SemT (fun T t => SemV t e) s.

Lemma comp2v_idl {G} (e : SemC G) : comp2v (idvsubst G) e = e.
induction G; simpl; intros. unfold comp2v. simpl. destruct e. reflexivity.
unfold comp2v. unfold SVextend.
destruct e.
simpl.
erewrite gmap_funct.
eapply (cong (fun y => (y, s))).
eapply IHG.
Qed.


Lemma comp_var : forall (G : Ctx Tp) (T : Tp) 
                              (v : Var G T) (G2 : Ctx Tp) 
                              (s : Subst G2 G) (e : SemC G2),
                            Sem (lookup v s) e = SemV v (comp2 s e).
induction v; simpl; intros. reflexivity.
erewrite IHv. reflexivity.
Qed.

Lemma compv_var : forall (G : Ctx Tp) (T : Tp) 
                              (v : Var G T) (G2 : Ctx Tp) 
                              (s : VSubst G2 G) (e : SemC G2),
                            SemV (lookup v s) e = SemV v (comp2v s e).
induction v; simpl; intros. reflexivity.
erewrite IHv. reflexivity.
Qed.

Lemma comp2v_lemma {G1 G2} (s : VSubst G2 G1) {C} e x : comp2v (SVextend C s) (e, x) = (comp2v s e , x).
intros.
unfold comp2v. unfold SVextend. simpl.
erewrite gmap_funct.
reflexivity.
Qed.

Lemma compositionalityv {G1 T} (t1 : Tm G1 T) {G2} (s : VSubst G2 G1) e :
  Sem (vsubst t1 s) e = Sem t1 (comp2v s e).
induction t1; simpl; intros; try congruence.
eapply compv_var.
erewrite IHt1_3.
erewrite IHt1_2.
eapply (cong (fun y => iiter y (Sem t1_2 (comp2v s e)) (Sem t1_3 (comp2v s e)))).
eapply functional_extensionality.
intros.
erewrite IHt1_1.
eapply (cong (fun y => Sem t1_1 y)).
eapply comp2v_lemma.

eapply functional_extensionality.
intros.
erewrite IHt1.
eapply (cong (Sem t1)).
eapply comp2v_lemma.
Qed.

Lemma comp2_idl {G} (e : SemC G) : comp2 (idsubst G) e = e.
induction G; simpl; intros; unfold comp2. destruct e. reflexivity.
destruct e. unfold Sextend.
simpl.
eapply (cong (fun y => (y, s))).
erewrite gmap_funct.
erewrite gmap_cong.
eapply IHG. intros.
simpl.
erewrite compositionalityv.
unfold comp2v.
unfold wknvsubst.
erewrite gmap_funct.
simpl.
eapply (cong (Sem x)).
eapply comp2v_idl.
Qed.



Lemma comp2_lemma {G1 G2} (s : Subst G2 G1) {C} e x : comp2 (Sextend C s) (e, x) = (comp2 s e , x).
intros.
unfold comp2.
simpl.
eapply (cong (fun y => (y, x))).
erewrite gmap_funct.
eapply gmap_cong. intros.
erewrite compositionalityv.
eapply (cong (Sem x0)).
unfold comp2v. unfold wknvsubst.
erewrite gmap_funct.
simpl.
eapply comp2v_idl.
Qed.

Lemma compositionality {G1 T} (t1 : Tm G1 T) {G2} (s : Subst G2 G1) e :
  Sem (subst t1 s) e = Sem t1 (comp2 s e).
induction t1; simpl; intros; try congruence.
eapply comp_var. 
erewrite (IHt1_3 G2 s e).
erewrite (IHt1_2 G2 s e).
eapply (cong (fun y => iiter y (Sem t1_2 (comp2 s e)) (Sem t1_3 (comp2 s e)))).
eapply functional_extensionality. intros.
rewrite (IHt1_1 _ (Sextend C s) (e, x)).
eapply (cong (Sem t1_1)).
eapply (comp2_lemma s e x).
eapply functional_extensionality. intros.
transitivity (Sem t1 (comp2 (Sextend T s) (e, x))).
eapply IHt1.
eapply (cong (Sem t1)).
eapply comp2_lemma.
Qed.


Lemma soundness {G T} (t1 t2 : Tm G T) : Mstep t1 t2 -> Sem t1 = Sem t2.
intros.
eapply functional_extensionality. intros.
induction H; simpl; try congruence.
erewrite (IHMstep3 x). erewrite (IHMstep2 x).
eapply (cong (fun y => iiter y (Sem i' x) (Sem n' x))).
eapply functional_extensionality. intros.
eapply IHMstep1.
eapply functional_extensionality. intros.
eapply IHMstep.
pose proof (compositionality t (pair (idsubst G) u) x).
unfold topsubst.
erewrite H.
simpl.
eapply (cong (Sem t)).
unfold comp2. simpl.
eapply (cong (fun y => (y , Sem u x))).
symmetry. eapply comp2_idl.
unfold iiter.
unfold izero. reflexivity.
unfold iiter. unfold isucc.
pose proof (compositionality t (pair (idsubst G) (iter t i n)) x).
unfold topsubst.
rewrite H.
eapply (cong (Sem t)).
unfold comp2. simpl. unfold iiter.
pose proof (comp2_idl x).
unfold comp2 in H0. erewrite H0. reflexivity.
Qed.
Print Assumptions soundness.

Fixpoint Rel (T : Tp) : SemT T -> Tm nil T -> Set :=
match T as T return SemT T -> Tm nil T -> Set with
| Nat => fun x t => { v : Tm nil Nat & (Mstep t v * Val v * (x = Sem v tt)) }
| Arr U V => fun x t => forall y u, Rel y u -> Rel (x y) (app t u)
| Prod U V => fun x t => Rel (fst x) (fst' t) * Rel (snd x) (snd' t)
end.

Fixpoint RelS (G : Ctx Tp) : SemC G -> Subst nil G -> Set :=
match G as G return SemC G -> Subst nil G -> Set with
| nil => fun x s => unit
| snoc G' T => fun x s => (RelS G' (fst x) (fst s)) * (Rel (snd x) (snd s))
end.

Lemma bwkclosed2 T (t t' : Tm nil T) x : Mstep t t' -> Rel x t' -> Rel x t.
induction T; simpl; intros.
destruct H0. destruct p. destruct p.
exists x0. split. split. eauto. auto. rewrite <- e.
reflexivity.
firstorder.
eapply IHT2.
eapply (sapp H srefl).
auto.
Qed.

Hint Resolve bwkclosed2.

Lemma main2var G T (t : Var G T) (s : Subst nil G) x (sred : RelS G x s) : Rel (SemV t x) (lookup t s).
induction t; simpl; intros. tauto.
firstorder.
Qed.

Lemma main2 G T (t : Tm G T) (s : Subst nil G) x (sred : RelS G x s) : Rel (Sem t x) (subst t s).
induction t; simpl; intros.
eapply main2var. auto.

split.
eapply bwkclosed2.
eapply beta_prod1. auto.

eapply bwkclosed2.
eapply beta_prod2. auto.

firstorder.
firstorder.

exists zero.
split. split. eapply srefl.
eauto.
simpl. reflexivity.
destruct (IHt s x sred).
destruct p. destruct p.
exists (succ x0).
split. split. eauto.
eauto.
rewrite e. reflexivity.
destruct (IHt3 s x sred).
destruct p. destruct p.

rewrite e.

eapply bwkclosed2.
eapply siter. eexact (@srefl (snoc nil C) C (subst t1 (Sextend C s))).
eapply (@srefl nil).
eapply m.
clear e. clear IHt3. clear m. clear t3.

induction v.

eapply bwkclosed2.
apply beta_nat1.
unfold iiter. simpl. unfold izero.
eauto.

eapply bwkclosed2.
apply beta_nat2.
unfold iiter. simpl. unfold isucc.
erewrite substcomm.
eapply IHt1. split; simpl. auto.
eexact IHv.

eapply bwkclosed2.
eapply beta_arr.
eapply eq_rec.
Focus 2. symmetry. eapply substcomm.
eapply IHt.
split.
eexact sred.
eexact H.
eapply IHt1. eexact sred.
eapply IHt2.
eexact sred.
Qed.

Print Assumptions main2.

Lemma zeroNotSucc n : izero = isucc n -> False.
intros.
assert (iiter (fun _ => true) false izero = iiter (fun _ => true) false (isucc n)).
erewrite H. reflexivity.
inversion H0.
Qed.

Axiom funext_yay : forall (T : Set -> Set) (f g : forall X, T X), (forall C, f C = g C) -> f = g.

(*Lemma succInv n n0 : isucc n = isucc n0 -> n = n0.
intros.
eapply funext_yay. intros.
eapply functional_extensionality. intros.
eapply functional_extensionality. intros.


intros.
rewrite H.
unfold iiter. unfold isucc.
reflexivity.
unfold iiter in H0. unfold isucc in H0.
Admitted. *)

Theorem adequacy v (H : Val v) : forall t, Sem t = Sem v -> Mstep t v.
(* Ugh too tired. I still think this should be possible though *)







(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)