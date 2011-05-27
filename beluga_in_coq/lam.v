Set Implicit Arguments.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Parameter world : Set.
Parameter link : world -> world -> Set.
Parameter name : world -> Set.
Notation "α ↪ β" := (link α β) (at level 90).
Parameter cast : forall {α β}, α↪β -> name β.
Coercion cast  : link >-> name.
Parameter s_w : world -> world.
Parameter s_l : forall α, α↪(s_w α). 
Parameter import : forall {α β}, α↪β -> name α -> name β.
Axiom export : forall {α β} (y:α↪β) (n:name β), name α + unit.
Axiom export_self : forall {α β} (y:α↪β), export y y = inr _ tt.
Axiom export_import_inv : forall {α β} (y:α↪β) (n:name α), export y (import y n) = inl _ n.
Axiom destruct1 : forall α β γ (x:α↪β) (y:α↪γ), β = γ.
Axiom destruct : forall α β γ (x:α↪β) (y:α↪γ), x ~= y.

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

Reserved Notation "[ σ ] M" (at level 90).
Fixpoint app_subst {ψ φ} (σ:φ[ψ]) (M:exp φ) : exp ψ :=
match M with
| var x => var (σ x)
| app M N => app ([σ]M) ([σ]N)
| lam _ x M => 
  let z := s_l ψ in
  lam z ([σ × z // x] M)
end
where "[ σ ] M" := (app_subst σ M). 

Inductive sview ψ : exp ψ -> Set :=
| var_s : forall (x:name ψ), sview (var x)
| lam_s : forall {ψ'} (x:ψ↪ψ') (M:exp ψ'), (forall χ (σ:ψ'[χ]), @sview _ ([σ]M)) -> sview (lam x M)
| app_s : forall (M1:exp ψ), (forall χ1 (σ1:ψ[χ1]), @sview _ ([σ1]M1)) ->
          forall (M2:exp ψ), (forall χ2 (σ2:ψ[χ2]), @sview _ ([σ2]M2)) ->
            sview (app M1 M2).

Inductive view ψ : exp ψ -> Set :=
| var_v : forall (x:name ψ), view (var x) (* Generalize? *)
| lam_v : forall {φ ψ'} (x:ψ↪ψ') (M:exp φ), (forall χ (σ:φ[χ]), @view _ ([σ]M)) -> forall (σ:φ[ψ']), view (lam x ([σ]M))
| app_v : forall {φ1} (M1:exp φ1), (forall χ1 (σ1:φ1[χ1]), @view _ ([σ1]M1)) -> forall (σ1:φ1[ψ]),
          forall {φ2} (M2:exp φ2), (forall χ2 (σ2:φ2[χ2]), @view _ ([σ2]M2)) -> forall (σ2:φ2[ψ]),
            view (app ([σ1]M1) ([σ2]M2)).

Definition id {A} := fun (x:A) => x.


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

Theorem sview_sub {φ} (M:exp φ) : forall ψ (σ:φ[ψ]), sview ([σ]M).
induction M; intros.
econstructor.
simpl.
econstructor.
intros.
erewrite subst_compose; eauto.
simpl.
econstructor; intros.
erewrite subst_compose; eauto.
erewrite subst_compose; eauto.
Qed.

Hint Constructors sview.
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
 ((import y ○ import x ○ id,, (x,y),, (y,import y x))).
(* TODO: Is this a use case for name α β and general × ? *)

Fixpoint cnt {ψ'} {m:exp ψ'} (M:sview m) {ψ} (x:ψ↪ψ') : nat :=
match M with
| var_s y => if (export x y) then 0 else 1
| lam_s _ y _ N => cnt (N _ (exchange x y)) y (* Swap x for y and then count the ys *)
| app_s _ M1 _ M2 => (cnt (M1 _ id) x) + (cnt (M2 _ id) x)
end.
(* We could use a 'different' world for N, and name the new
   variables x and y to make it look sane... *) 