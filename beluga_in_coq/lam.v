Set Implicit Arguments.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import List.
Parameter world : Set.
Parameter link : world -> world -> Set.
Parameter name : world -> Set.
Notation "α ↪ β" := (link α β) (at level 90).
Parameter cast : forall {α β}, α↪β -> name β.
Coercion cast  : link >-> name.
Parameter empty : world.
Notation "∅" := empty.
Parameter s_w : world -> world.
Parameter s_l : forall α, α↪(s_w α). 
Parameter import : forall {α β}, α↪β -> name α -> name β.
Axiom export : forall {α β} (y:α↪β) (n:name β), name α + unit.
Axiom export_self : forall {α β} (y:α↪β), export y y = inr _ tt.
Axiom export_import_inv : forall {α β} (y:α↪β) (n:name α), export y (import y n) = inl _ n.
Axiom export_inr : forall {α β} (y:α↪β) x v, inr _ v = export y x -> x = y.  
Axiom export_inl : forall {α β} (y:α↪β) x v, inl _ v = export y x -> x = import y v.
Axiom empty_is_empty : forall {C:Set}, name ∅ -> C.

Inductive star {A} (R:A -> A -> Set) (a:A) : A -> Type :=
| s_nil : star R a a
| s_cons : forall b c, star R a b -> R b c -> star R a c.
Notation "a ↪* b" := (star link a b) (at level 90).

Axiom empty_is_initial : forall α, ∅↪*α.

Definition neq {α β} (y:α↪β) (n:name β) := export y n.
Notation "x ≠ y" := (neq x y) (at level 90).

Fixpoint export_star {α β} (l:α↪*β) : name β -> name α + unit :=
match l in star _ _ b return name b -> name α + unit with
| s_nil => fun x => inl _ x
| s_cons _ _ ys y => fun x =>
  match (export y x) with
   | inl x' => export_star ys x'
   | inr _ => inr _ tt
  end
end.

Definition list_from_maybe {A} (x:A + unit) : list A :=
match x with
| inl a => a::nil
| inr _ => nil
end.

Definition compose {A B C} (f:A -> B) (g:B -> C) (a:A) := g (f a).
Definition maybe {A C} (f:A -> C) (c:C) (x:A + unit) : C := match x with | inl a => f a | inr _ => c end.  
Notation "f ○ g" := (compose g f) (at level 90).
Notation "Γ ,, ( y , t )" := ((maybe Γ t) ○ (export y)) (at level 90).
Definition rn_cons {α β γ δ} (θ:name α -> name β) (z:β↪γ) (y:α↪δ) := ((import z) ○ θ,,(y,z)).
Notation "θ × y // x " := (rn_cons θ y x) (at level 90).
Inductive exp ψ : Set :=
| var : name ψ -> exp ψ
| lam : forall φ, ψ↪φ -> exp φ -> exp ψ
| app : exp ψ -> exp ψ -> exp ψ.

Definition sub α β := name α -> name β.
Notation "β [ α ]" := (sub β α) (at level 90).

Reserved Notation "[ σ ]" (at level 50).
Fixpoint app_subst {ψ φ} (σ:φ[ψ]) (M:exp φ) : exp ψ :=
match M with
| var x => var (σ x)
| app M N => app ([σ]M) ([σ]N)
| lam _ x M => 
  let z := s_l ψ in
  lam z ([σ × z // x] M)
end
where "[ σ ]" := (app_subst σ). 

Definition instances_viewable (view:forall ψ, exp ψ -> Set) {ψ} (M:exp ψ) := forall χ (σ:ψ[χ]), view _ ([σ]M).

Inductive sview ψ : exp ψ -> Set :=
| var_s : forall (x:name ψ), sview (var x)
| lam_s : forall {ψ'} (x:ψ↪ψ') (M:exp ψ'), instances_viewable (@sview) M -> sview (lam x M)
| app_s : forall (M1:exp ψ), instances_viewable (@sview) M1 ->
          forall (M2:exp ψ), instances_viewable (@sview) M2 ->
            sview (app M1 M2).

Inductive view ψ : exp ψ -> Set :=
| var_v : forall (x:name ψ), view (var x) (* Generalize? *)
| lam_v : forall {φ ψ'} (x:ψ↪ψ') (M:exp φ), instances_viewable (@view) M-> forall (σ:φ[ψ']), view (lam x ([σ]M))
| app_v : forall {φ1} (M1:exp φ1), instances_viewable (@view) M1 -> forall (σ1:φ1[ψ]),
          forall {φ2} (M2:exp φ2), instances_viewable (@view) M2 -> forall (σ2:φ2[ψ]),
            view (app ([σ1]M1) ([σ2]M2)).

Definition id {A} := fun (x:A) => x.
Notation "…" := id.

Lemma id_is_id {A B} (f:A -> B) : (f ○ id) = f.
eapply functional_extensionality_dep; intros.
reflexivity.
Qed.

Theorem foo : forall (ψ φ φ0 φ0' χ χ': world) (l : ψ ↪ φ) 
                           (σ1 : ψ [φ0]) (σ2 : φ0 [χ]) 
                           (l0 : χ ↪ χ') (l1 : φ0 ↪ φ0'),
                         ((σ2 × l0 // l1) ○ (σ1 × l1 // l)) =
                         ((σ2 ○ σ1) × l0 // l).
intros.
eapply functional_extensionality_dep.
intros.
unfold rn_cons at 1 3.
unfold compose.
destruct (export l x); simpl. (* There's some lemmas here... *)
unfold rn_cons. unfold compose. erewrite export_import_inv. reflexivity.
unfold rn_cons. unfold compose. erewrite export_self. reflexivity.
Qed.

Theorem subst_compose {ψ} {M:exp ψ} : forall φ (σ1:ψ[φ]) χ (σ2:φ[χ]), ([σ2]([σ1]M)) = [σ2 ○ σ1] M.
induction M; intros.
reflexivity.
simpl.
f_equal.
erewrite IHM.
f_equal.
erewrite foo.
reflexivity.
simpl.
erewrite IHM1.
erewrite IHM2.
reflexivity.
Qed.
Print Assumptions subst_compose.
Lemma subst_compose_nice ψ φ (σ1:ψ[φ]) χ (σ2:φ[χ]) : ([σ2] ○ [σ1]) = [σ2 ○ σ1].
eapply functional_extensionality_dep; intros.
eapply subst_compose.
Qed.

Theorem sview_sub {φ} (M:exp φ) : forall ψ (σ:φ[ψ]), sview ([σ]M).
induction M; intros.
econstructor.
simpl.
econstructor. unfold instances_viewable.
intros.
erewrite subst_compose; eauto.
simpl.
econstructor; unfold instances_viewable; intros.
erewrite subst_compose; eauto.
erewrite subst_compose; eauto.
Qed.

Hint Constructors sview.
Hint Unfold instances_viewable.
Theorem id_sview {ψ} (M:exp ψ) : sview M.
induction M; eauto using @sview_sub.
Qed.

(* TODO: Write this as a function. Same above. Also the strengthening version. *)
Theorem id_view {φ} (M:exp φ) : forall ψ (σ:φ[ψ]), view ([σ]M).
induction M; intros. unfold app_subst.
econstructor.
econstructor.
exact IHM.
econstructor.
exact IHM1.
exact IHM2.
Qed.

Definition exchange {ψ φ χ} (x:ψ↪φ) (y:φ↪χ) := 
 ((import y ○ import x ○ …,, (x,y),, (y,import y x))).
(* TODO: Is this a use case for name α β and general × ? *)

Fixpoint cnt {ψ'} {m:exp ψ'} (M:sview m) {ψ} (x:ψ↪ψ') : nat :=
match M with
| var_s y => if x ≠ y then 0 else 1
| lam_s _ y _ N => cnt (N _ (exchange x y)) y (* Swap x for y and then count the ys *)
| app_s _ M1 _ M2 => (cnt (M1 _ …) x) + (cnt (M2 _ …) x)
end.
(* We could use a 'different' world for N, and name the new
   variables x and y to make it look sane... *) 


Fixpoint fv {φ} (M:exp φ) {ψ} (Γ:ψ↪*φ) : list (name ψ) :=
match M with
| var x => list_from_maybe (export_star Γ x)
| lam _ x R => fv R (s_cons _ Γ x)
| app M1 M2 => (fv M1 Γ) ++ (fv M2 Γ)
end. 

Inductive subst_range {ψ ψ' φ} (y:ψ↪ψ') : forall (σ:φ[ψ']), Set :=
| subst_range_no : forall (σ':φ[ψ]), subst_range y (import y ○ σ')
| subst_range_yes  : forall (σ:φ[ψ']) x, σ x = y -> subst_range y σ.

Lemma subst_congr {ψ ψ' φ χ} (σ1:ψ[φ]) (σ2:φ[χ]) (y:ψ↪ψ') x : (σ2 ○ (σ1,,(y,x))) = (σ2 ○ σ1,,(y,σ2 x)). 
eapply functional_extensionality_dep; intros.
unfold compose at 1 2 3.
destruct (export y x0); reflexivity.
Qed.

Lemma decompose_subst {ψ ψ' φ} (y:ψ↪ψ') (σ:ψ'[φ]) : σ = ((σ ○ import y),,(y,σ y)).
eapply functional_extensionality_dep. intros.
unfold compose at 1.
remember (export y x).
destruct s; simpl.
pose proof (export_inl Heqs). subst.
reflexivity.
pose proof (export_inr Heqs). subst.
reflexivity.
Qed.

Lemma is_in_range {ψ ψ' φ} (y:ψ↪ψ') (σ:φ[ψ']) : subst_range y σ.
pose proof (empty_is_initial φ) as l.
induction l.
assert (σ = ((import y) ○ empty_is_empty)).
eapply functional_extensionality_dep; intros.
destruct (@empty_is_empty False x).
subst.
econstructor; eauto.
specialize (IHl (σ ○ (import r))).
inversion IHl.

remember (export y (σ r)).
destruct s.

pose proof (decompose_subst r σ).
pose proof (export_inl Heqs).
rewrite H1 in H.
rewrite <- H0 in H.
erewrite <- subst_congr in H.
rewrite H.
econstructor 1; eauto.

pose proof (export_inr Heqs).
econstructor 2; eauto.

econstructor 2.
unfold compose in H.
eexact H.
Qed.


Inductive subst_range2 {ψ' φ} (σ:φ[ψ']) : name ψ' -> Set :=
| subst_range2_yes  : forall x, subst_range2 σ (σ x).

Axiom name_eq_dec : forall {α} (x y:name α), {x = y} + {x <> y}.
Lemma export_diff : forall {α β} (y:α↪β) (x:name β), x <> y -> exists z, export y x = inl _ z.
intros.
remember (export y x).
destruct s.
pose proof (export_inl Heqs).
subst.
exists n.
reflexivity.
pose proof (export_inr Heqs).
contradiction.
Qed.

(* TODO: It may be possible to prove this without name_eq_dec, or even prove name_eq_dec, in the style similar to the previous proof *)
Lemma is_in_range2 {φ} : forall {ψ'} (y:name ψ') (σ:φ[ψ']), subst_range2 σ y + {subst_range2 σ y -> False}.
pose proof (empty_is_initial φ) as l.
induction l; intros.
right. intros.
inversion H.
eapply empty_is_empty; eauto.
destruct (IHl _ y (σ ○ import r)).
inversion s; subst.
left. unfold compose. econstructor 1.
destruct (name_eq_dec (σ r) y).
subst.
left. econstructor.
right.
intros.
inversion H.
destruct (name_eq_dec x r).
subst.
contradict n. reflexivity.
pose proof (export_diff n0).
destruct H1.
symmetry in H1.
pose proof (export_inl H1).
subst.
apply f.
change (σ (import r x0)) with ((σ ○ import r) x0).
econstructor.
Qed.

(* TODO: Define the strengthening view! *)

(* Note that there is some extra "flexibility" in this 
   definition corresponding to "how much strengthening to attempt".
   We can do none (id_view), all (str_view) or some combination.
   It's not clear to me if there are applications that might benefit
   from exploiting this. Maybe some terms are really big or far away or
   expensive in some sense, or "opaque", so you don't want to check them
   for occurrences. *)
(* Perform eta contractions recursively *)
Fixpoint eta {ψ} {m:exp ψ} (M:view m) : exp ψ :=
match M with
| var_v x => var x
| lam_v _ _ x _ N σ =>
 match (N _ σ) with 
 | app_v _ _ M1 σ1 _ (var y) M2 σ2 =>
    if x ≠ (σ2 y) then
       lam x (eta (N _ σ))
    else
       match (is_in_range x σ1) with
        | subst_range_no σ1' => eta (M1 _ σ1')
        | _ => lam x (eta (N _ σ))
       end
 | _ => lam x (eta (N _ σ))
 end
| app_v _ _ M1 σ1 _ _ M2 σ2 => app (eta (M1 _ σ1)) (eta (M2 _ σ2))
end.


(* TODO: We just need one definition of im, and use it on [σ], not σ. Can unite with the variable version *)
Inductive im ψ φ (σ:ψ[φ]) : exp φ -> Set :=
| in_im : forall M, im σ ([σ]M).

Definition preimages_viewable (view:forall ψ, exp ψ -> Set) {ψ} (M:exp ψ) :=
 forall χ (σ:χ[ψ]), forall (N:exp χ), (M = [σ]N) -> view _ N.

Inductive view2 ψ : exp ψ -> Set :=
| var_2 : forall (x:name ψ), view2 (var x)
| lam_2 : forall {ψ'} (x:ψ↪ψ') (M:exp ψ'), instances_viewable (@view2) M -> view2 (lam x M)
| app_2 : forall (M1:exp ψ), (forall χ1 (σ1:χ1[ψ]) (N1:exp χ1), (M1 = [σ1]N1) -> instances_viewable (@view2) N1) ->
          forall (M2:exp ψ), (forall χ2 (σ2:χ2[ψ]) (N2:exp χ2), (M2 = [σ2]N2) -> instances_viewable (@view2) N2) ->
            view2 (app M1 M2).

Inductive view3 ψ : exp ψ -> Set :=
| var_3 : forall (x:name ψ), view3 (var x)
| lam_3 : forall {ψ'} (x:ψ↪ψ') (M:exp ψ'), preimages_viewable (@view3) M -> view3 (lam x M)
| app_3 : forall (M1:exp ψ), preimages_viewable (@view3) M1 ->
          forall (M2:exp ψ), preimages_viewable (@view3) M2 ->
            view3 (app M1 M2).

Lemma view3_preim {ψ} (m:exp ψ) (M:view3 m) : preimages_viewable (@view3) m.
induction M; unfold preimages_viewable in *; intros.
destruct N; simpl in H; try discriminate.
econstructor.
destruct N; simpl in H0; try discriminate.
inversion H0; subst; simpl_existTs; subst.
econstructor.
intro. intros; subst.
eapply p.
erewrite subst_compose.
reflexivity.
destruct N; simpl in H1; try discriminate.
inversion H1; subst; simpl_existTs; subst.
econstructor;
intro; intros; subst.
eapply p.
erewrite subst_compose.
reflexivity.
eapply p0.
erewrite subst_compose.
reflexivity.
Qed.

Hint Constructors view3.
Theorem view3_all {ψ} (M:exp ψ) : view3 M.
induction M; eauto using @view3_preim.
Qed.

Axiom world_eq_dec : forall (α β:world), {α = β} + {α <> β}.
Axiom link_eq_dec : forall {α β} (x y:α↪β), {x = y} + {x <> y}. (* Is this provable from the export axioms? *)
(* The above axioms and their use in this lemma messes with alpha equality, I think. *)
Lemma im_dec φ (M:exp φ) : forall ψ (σ:ψ[φ]), (im σ M) + {im σ M -> False}.
induction M; intros.
destruct (is_in_range2 n σ).
inversion s. left.
change (im σ ([σ] (var x))).
econstructor.
right.
intros.
inversion H.
destruct M; simpl in H1; try discriminate.
inversion H1; subst.
apply f.
econstructor.

(* lam *)
destruct (world_eq_dec φ (s_w ψ)).
subst.
destruct (link_eq_dec l (s_l ψ)).
subst.
destruct (IHM _ (σ × (s_l ψ) // (s_l ψ0))).
left.
inversion i; subst.
change (im σ ([σ] (lam (s_l ψ0) M0))).
econstructor.

right.
intros.
inversion H.
destruct M0; simpl in H1; try discriminate.
inversion H1; subst; simpl_existTs; subst.
apply f.
pose proof (foo l … σ (s_l ψ) (s_l ψ0)).
erewrite id_is_id in H0.
rewrite <- H0.
erewrite <- subst_compose.
econstructor.

right.
intros.
inversion H.
destruct M0; simpl in H1; try discriminate.
inversion H1; subst; simpl_existTs; subst.
apply n. reflexivity.

right.
intros.
inversion H.
destruct M0; simpl in H1; try discriminate.
inversion H1; subst; simpl_existTs; subst.
apply n. reflexivity.

(* app *)
destruct (IHM1 _ σ).
destruct (IHM2 _ σ).
inversion i; subst.
inversion i0; subst. 
left.
change (im σ ([σ] (app M M0))).
econstructor.
right.
intros.
inversion H.
destruct M; simpl in H1; try discriminate.
inversion H1; subst.
apply f.
econstructor.
right.
intro.
inversion H.
destruct M; simpl in H1; try discriminate.
inversion H1; subst.
apply f. econstructor.
Qed.

Inductive im_c {ψ φ} (σ:ψ[φ]) (M:exp φ) : Set :=
| im_cl : forall N, M = ([σ]N) -> im_c σ M
| im_cr : (forall N, M <> ([σ]N)) -> im_c σ M.

Theorem im_c_dec {ψ φ} (σ:ψ[φ]) (M:exp φ) : im_c σ M.
destruct (im_dec M σ).
inversion i; subst. econstructor 1. reflexivity.
econstructor 2. intros.
intro. subst.
apply f.
econstructor.
Qed.

Notation "⇑ y" := (import y) (at level 90).

Axiom i : forall {ψ} (M:exp ψ), M = […]M.
Implicit Arguments i [ψ M].

(* Interesting that rather than write "lam (\x. N ..)" now we write "lam (N ⇑)"  *)
(* We might wish to define substitution on views directly, and state im_dec in terms of views
   to get it really clean looking in Agda *)
Fixpoint eta2 {ψ} {m:exp ψ} (M:view3 m) : exp ψ :=
match M with
| var_3 x => var x
| lam_3 _ x _ N =>
  match (N _ … _ i) with
   | app_3 m1 M1 (var y) M2 =>
     if x ≠ y then
       lam x (eta2 (N _ … _ i))
     else
       match im_c_dec (⇑x) m1 with (* TODO: Could use M1 here.. *)
        | im_cl _ e => (eta2 (M1 _ (⇑x) _ e))
        | im_cr _ => lam x (eta2 (N _ … _ i))
       end
   | _ => lam x (eta2 (N _ … _ i))
  end 
| app_3 _ M1 _ M2 => app (eta2 (M1 _ … _ i)) (eta2 (M2 _ … _ i))
end.

Fixpoint cnt2 {ψ'} {m:exp ψ'} (M:view3 m) {ψ} (x:ψ↪ψ') : nat :=
match M with
| var_3 y => if x ≠ y then 0 else 1
| lam_3 _ y n N =>
  match im_c_dec (exchange x y) n with
   | im_cl _ e => cnt2 (N _ (exchange x y) _ e) y
   | _ => 0 (* :( *)
  end
| app_3 _ M1 _ M2 => (cnt2 (M1 _ … _ i) x) + (cnt2 (M2 _ … _ i) x)
end.

Lemma exchange_inv {ψ φ χ} (x:ψ↪φ) (y:φ↪χ) : ((exchange x y) ○ (exchange x y)) = id.
eapply functional_extensionality_dep; intros.
unfold exchange. unfold compose.
remember (export y x0).
destruct s; simpl.
unfold id.
remember (export x n).
destruct s; simpl.
erewrite export_import_inv. simpl.
erewrite export_import_inv. simpl.
pose proof (export_inl Heqs); subst.
pose proof (export_inl Heqs0); subst.
reflexivity.
erewrite export_self. simpl.
pose proof (export_inl Heqs). subst.
pose proof (export_inr Heqs0). subst.
reflexivity.
erewrite export_import_inv. simpl.
erewrite export_self. simpl. unfold id.
pose proof (export_inr Heqs). subst.
reflexivity.
Qed.

Inductive im_c2 {ψ φ} (σ:ψ[φ]) (M:exp φ) : Set :=
| im_c2l : forall N, M = ([σ]N) -> im_c2 σ M.

Lemma inv_im_c2 {ψ φ} (σ:ψ[φ]) (ρ:φ[ψ]) (M:exp φ) : ((σ ○ ρ) = …) -> im_c2 σ M.
intros.
erewrite i. 
erewrite <- H. 
erewrite <- subst_compose.
econstructor. reflexivity.
Qed.

Fixpoint cnt3 {ψ'} {m:exp ψ'} (M:view3 m) {ψ} (x:ψ↪ψ') : nat :=
match M with
| var_3 y => if x ≠ y then 0 else 1
| lam_3 _ y n N =>
  let (_,eq) := inv_im_c2 n (exchange_inv x y) in
     cnt2 (N _ (exchange x y) _ eq) y
| app_3 _ M1 _ M2 => (cnt2 (M1 _ … _ i) x) + (cnt2 (M2 _ … _ i) x)
end.
Print Assumptions cnt3.
(* The cost of doing it this way is that now coverage is a burden.
   So view2 might be the most convenient in that it encompasses both *)
(* I imagine Brigitte might recognize this condition ("is the substitution invertible?")
   from coverage checking in Beluga *)

(* Observe that we're proving really general lemmas. Essentially, we're
   proving the theorems and lemmas that justify Beluga, and then writing the
   Beluga program *)

(* TODO: Try a proof. Say, subject reduction *)