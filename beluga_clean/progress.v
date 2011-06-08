Require Import divergence.
Require Import subj_red.

Axiom classical : forall P, P \/ ~P.

Hint Constructors eval div.

Ltac doesItConverge E :=
 let V := fresh "V" in
 let H := fresh "H" in
 destruct (classical (exists V, E ⇓ V)) as [ (V, H) | H ].

Theorem progress : forall {δ γ} θ ρ (E:checked_exp δ γ) T,
   ·;· ⊢ E[θ;;ρ] ⇐ T
-> (forall V, ~ (E[θ;;ρ] ⇓ V))
-> E[θ;;ρ] ⇑.
cofix. intros. invert_typing. nice_inversion H7.

(* synth *)
nice_inversion H.

(* var *)
clear progress.
admit. (* TODO *)

(* app *)
doesItConverge (I0[θ;;ρ]).
doesItConverge (E[θ;;ρ]).
clear progress. admit. (* TODO: Eval to val, canonical forms *)
eapply div_app2; eauto 7.
eapply div_app1; eauto 7.

(* mapp *)
doesItConverge (I0[θ;;ρ]).
clear progress. admit. (* TODO *)
eapply div_mapp1; eauto 7.

(* coercion *)
econstructor.
eapply progress; eauto.
intros v Hy.
eapply H0; eauto.

(* unfold *)
econstructor.
eapply progress; eauto.
intros v Hy.
clear progress. admit. (* TODO: Canonical forms *)

(* meta *)
edestruct H0; by eauto.

(* fn *)
edestruct H0; by eauto.

(* mlam *)
edestruct H0; by eauto.

(* rec *)
doesItConverge (E0 [θ;; ρ,, (f, (rec f E0) [θ;; ρ])]).
edestruct H0; by eauto.
econstructor.
eapply progress.
econstructor; eauto.
erewrite compose_cons.
by eauto.
by eauto.

(* inl *)
econstructor.
eapply progress; eauto.
intros v Hy.
eapply H0; by eauto.

(* inr *)
econstructor.
eapply progress; eauto.
intros v Hy.
eapply H0; by eauto.

(* pair *)
doesItConverge (E1[θ;;ρ]).
eapply div_pair2; eauto.
eapply progress; eauto.
intros v Hy. eapply H0; by eauto.
eapply div_pair1; eauto.
eapply progress; by eauto.

(* pack *)
econstructor.
eapply progress; eauto.
intros v Hy. 
eapply H0; by eauto.

(* fold *)
econstructor.
eapply progress; eauto.
intros v Hy.
eapply H0; by eauto.

(* tt *)
edestruct H0; by eauto.

clear progress.
admit.
Qed.