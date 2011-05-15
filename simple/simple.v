Parameter world : Set.
Parameter empty : world.
Notation "∅" := empty.
Parameter name : world -> Set.
Parameter link : world -> world -> Set.
Notation "α ↪ β" := (link α β) (at level 90).
Parameter weaken : forall {α β}, α↪β -> name β.
Coercion weaken : link >-> name.
Parameter import : forall {α β}, α↪β -> name α -> name β.
Parameter next' : forall α, {β:world & α↪β}.
Definition next α : {β:world & α↪β} := existT _ (projT1 (next' α)) (projT2 (next' α)).
Definition next_name α := projT2 (next' α).
Parameter export : forall {α β} (y:α↪β) (n:name β), name α + unit.
Axiom empty_is_empty : name ∅ -> False.

Definition maybe {A C} (f:A -> C) (c:C) (x:A + unit) : C :=
match x with
| inl a => f a
| inr _ => c
end.
Definition compose {A B C:Set} (f:A -> B) (g:B -> C) (a:A) : C
 := g (f a). 
Notation "f ○ g" := (compose g f) (at level 10).

Inductive tp :=
| one : tp
| arrow : tp -> tp -> tp
| prod : tp -> tp -> tp.

Set Implicit Arguments.
Inductive exp (α:world) : Set :=
| tt : exp α
| var : name α -> exp α
| lam : forall β, α↪β -> tp -> exp β -> exp α
| app : exp α -> exp α -> exp α
| fst : exp α -> exp α
| snd : exp α -> exp α
| pair : exp α -> exp α -> exp α.
Implicit Arguments tt [α].
Coercion var : name >-> exp.

Definition tp_ctx γ := name γ -> tp.

Definition cdot {A} : name ∅ -> A :=
fun n => match (empty_is_empty n) with end.
Notation "·" := cdot.
Notation "Γ ,, ( x , T )" := ((maybe Γ T) ○ (export x)) (at level 90).

Reserved Notation "Γ ⊢ E ⇐ T" (at level 90).

Inductive of {γ} (Γ:tp_ctx γ) : exp γ -> tp -> Prop :=
| tt_of : Γ ⊢ tt ⇐ one
| var_of : forall x T,
          Γ x = T
        (*===============================*) ->
          Γ ⊢ x ⇐ T
| lam_of : forall γ' (x:γ↪γ') T S M,
          Γ,,(x,T) ⊢ M ⇐ S
        (*===============================*) ->
          Γ ⊢ lam x T M ⇐ arrow T S
| app_of : forall T S M N,
          Γ ⊢ M ⇐ arrow T S ->
          Γ ⊢ N ⇐ T 
        (*===============================*) ->
          Γ ⊢ app M N ⇐ S
| fst_of : forall T S M,
          Γ ⊢ M ⇐ prod T S
        (*===============================*) ->
          Γ ⊢ fst M ⇐ T
| snd_of : forall T S M,
          Γ ⊢ M ⇐ prod T S
        (*===============================*) ->
          Γ ⊢ snd M ⇐ S
| pair_of : forall T S M N,
          Γ ⊢ M ⇐ T ->
          Γ ⊢ N ⇐ S
        (*===============================*) ->
          Γ ⊢ pair M N ⇐ prod T S
where "Γ ⊢ E ⇐ T" := (@of _ Γ E T).

Inductive closure : Set :=
| clos : forall γ, exp γ -> (name γ -> closure) -> closure.
Definition env γ := name γ -> closure.
Notation "E [ ρ ]" := (clos E ρ) (at level 80).

Reserved Notation "C ∷ T" (at level 90).
Inductive closure_of : closure -> tp -> Prop :=
| clos_of : forall γ (M:exp γ) (Γ:tp_ctx γ) (ρ:env γ) T,
            (forall x, (ρ x) ∷ (Γ x)) ->
            Γ ⊢ M ⇐ T ->
          (*==============================*)
            M [ρ] ∷ T
where "C ∷ T" := (closure_of C T).

Inductive val : closure -> Prop :=
 | fn_val : forall γ γ' (x:γ↪γ') M T ρ,
      env_val ρ -> val ((lam x T M)[ρ])
 | tt_val : forall γ (ρ:env γ),
      env_val ρ -> val (tt[ρ])
 | pair_val : forall γ (ρ:env γ) M N,
      env_val ρ -> val (M[ρ]) -> val (N[ρ])
   -> val ((pair M N)[ρ])
with env_val : forall {γ}, env γ -> Prop :=
 | env_val_nil : env_val ·
 | env_val_cons : forall γ (ρ:env γ) γ' (x:γ↪γ') V,
      val V -> env_val (ρ,,(x,V)).

Reserved Notation "C ⇓ V" (at level 90).
Definition X := next_name ∅.
Definition Y := next_name (projT1 (next' ∅)).
Inductive eval : closure -> closure -> Prop :=
| val_eval : forall V,
          val V
        (*======*) ->
          V ⇓ V 
| var_eval : forall γ (ρ:env γ) x V,
          ρ x = V
        (*=========*) ->
          x[ρ] ⇓ V
| app_eval : forall γ γ' γ'' (ρ:env γ) ρ' (x:γ'↪γ'') T M N M' V1 V2,
          M[ρ] ⇓ (lam x T M')[ρ'] ->
          N[ρ] ⇓ V1 ->
          M'[ρ',,(x,V1)] ⇓ V2
        (*========================*) ->
          (app M N)[ρ] ⇓ V2  
| fst_eval : forall γ γ' (ρ:env γ) (ρ':env γ') M U V,
          M[ρ] ⇓ (pair U V)[ρ']
        (*========================*) ->
          (fst M)[ρ] ⇓ U[ρ']
| snd_eval : forall γ γ' (ρ:env γ) (ρ':env γ') M U V,
          M[ρ] ⇓ (pair U V)[ρ']
        (*========================*) ->
          (snd M)[ρ] ⇓ V[ρ']
(* | pair_eval : forall γ γ' (ρ:env γ) (ρ':env γ') M N V1 V2,
          M[ρ] ⇓ V1 ->
          N[ρ] ⇓ V2 ->
          (pair M N)[ρ] ⇓ (pair (import Y X) Y)[·,,(X,V1),,(Y,V2)]*)
where "C ⇓ V" := (eval C V).

Hint Constructors eval val.
Lemma eval_val V : val V -> eval V V.
induction 1; eauto.
Qed.

