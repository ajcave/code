Require Import divergence.
Require Import subj_red.
Require Import Coq.Program.Equality.
Set Implicit Arguments.

Hint Constructors extended_val val.
Hint Constructors src_lang.

Lemma val_env_cons {γ γ'} (y:γ↪γ') (ρ:env γ) V :
   val_env ρ
-> extended_val V
-> val_env (ρ,,(y,V)).
intros.
nice_inversion H.
econstructor. intro.
unfold compose. destruct (export y x); unfold maybe; eauto.
Qed.
Hint Resolve @val_env_cons.

Lemma extval_srclang {δ γ} θ ρ (W:checked_exp δ γ) V2 :
   extended_val (W[θ;;ρ])
-> W[θ;;ρ] ⇓ V2
-> src_lang W /\ val_env ρ.
intros.
nice_inversion H0; nice_inversion H;
try match goal with 
| [ H : val (_[_;;_]) |- _] => nice_inversion H
end; eauto.
Qed.

Ltac invert_src_1 :=
match goal with
| [ H : src_lang (synth _) |- _ ] => nice_inversion_clear H
| [ H : ssrc_lang (coercion _ _) |- _] => nice_inversion_clear H
| [ H : src_lang (clos _ _ _)|- _] => nice_inversion_clear H
| [ H : ssrc_lang (app _ _) |- _] => nice_inversion_clear H
| [ H : src_lang (fn _ _) |- _] => nice_inversion_clear H
| [ H : src_lang (rec _ _) |- _] => nice_inversion_clear H
| [ H : ssrc_lang (mapp _ _) |- _] => nice_inversion_clear H
| [ H : src_lang (mlam _ _) |- _] => nice_inversion_clear H
| [ H : ssrc_lang (var _ _) |- _] => nice_inversion_clear H
| [ H : ssrc_lang (rec _ _) |- _] => nice_inversion_clear H
| [ H : src_lang (inl _) |- _ ] => nice_inversion_clear H
| [ H : src_lang (inr _) |- _ ] => nice_inversion_clear H
| [ H : src_lang (pair _ _) |- _ ] => nice_inversion_clear H
| [ H : src_lang (pack _ _) |- _ ] => nice_inversion_clear H
| [ H : src_lang (fold _) |- _ ] => nice_inversion_clear H
| [ H : ssrc_lang (unfold _) |- _ ] => nice_inversion_clear H
| [ H : src_lang (meta _ _) |- _ ] => nice_inversion_clear H
| [ H : src_lang tt |- _] => nice_inversion_clear H
end.
Ltac invert_src := repeat invert_src_1.

Lemma eval_to_val {γ δ} (E:checked_exp δ γ) (Hyp:src_lang E)
θ ρ V :
val_env ρ -> E[θ;;ρ] ⇓ V -> val V.
intros.
dependent induction H0; invert_src; eauto 3.

(* fn *)
assert (val (fn y E)[θ';;ρ']) by eauto.
nice_inversion H0.
eapply IHeval3. eexact H11.
eapply val_env_cons. eexact H5.
econstructor.
eapply IHeval2.
eexact H4. eexact H.

(* mlam *)
assert (val (mlam X E)[θ';;ρ']) by eauto.
nice_inversion H0. by eauto.

(* var *)
nice_inversion H.
specialize (H4 y). rewrite H0 in *.
pose proof (extval_srclang H4 H1).
by tauto.

(* rec *)
eapply IHeval.
eassumption.
eapply val_env_cons.
eexact H.
econstructor 2. eexact H.
eassumption.

(* pair *)
econstructor; by eauto.

(* fold *)
assert (val (fold V)) by eauto.
nice_inversion H1. by assumption.
Qed.
Hint Resolve @eval_to_val.

Inductive canonical : checked_exp ∅ ∅ -> tp ∅ -> Prop :=
| canon_fn : forall δ γ γ' (y:γ↪γ') (E:checked_exp δ γ') θ ρ T S,
                 canonical ((fn y E)[θ;;ρ]) (arr T S)
| canon_mlam : forall δ δ' γ (X:δ↪δ') (E:checked_exp δ' γ) θ ρ U T,
                 canonical ((mlam X E)[θ;;ρ]) (pi ₁ U T)
| canon_fold : forall ψ δ (Z:∅↪ψ) (X:∅↪δ) E C U T,
                 canonical (fold E) (tapp (mu Z X U T) C)
| canon_tt : canonical tt unit
| canon_inl : forall E T S, canonical (inl E) (sum T S)
| canon_inr : forall E T S, canonical (inr E) (sum T S)
| canon_pair : forall E1 E2 T S, canonical (pair E1 E2) (prod T S)
| canon_pack : forall δ (X:∅↪δ) C E U T,
                  canonical (pack C E) (sigma X U T)
| canon_meta : forall C U, canonical (meta _ C) (m_tp' U)
.

Hint Constructors canonical.

Lemma canonical_forms V T : val V -> ·;· ⊢ V ⇐ T -> canonical V T.
intros. nice_inversion H; invert_typing; simpl; eauto.
Qed.

Lemma canonical_forms' δ γ θ ρ (E:checked_exp δ γ) V
(Hyp:src_lang E) :
   val_env ρ
-> E[θ;;ρ] ⇓ V
-> forall Δ Γ, (· ⊩ θ ∷ Δ)
-> (·;· ⊪ ρ ⇐ (〚θ〛 ○ Γ))
-> forall T, Δ;Γ ⊢ E ⇐ T
-> canonical V (〚θ〛T).
intros.
eapply canonical_forms.
eauto using @eval_to_val.
eapply subj_red; eauto.
Qed.
Hint Resolve canonical_forms'.

Axiom classical : forall P, P \/ ~P.

Hint Constructors eval div.

Ltac doesItConverge E θ ρ :=
 let V := fresh "V" in
 let H := fresh "H" in
 destruct (classical (exists V, E[θ;;ρ] ⇓ V)) as [ (V, H) | H ].

Ltac canonical :=
let H1 := fresh "H" in
match goal with
| [ H : ?E[?θ;;_] ⇓ ?V,
    H0 : _;_ ⊢ ?E ⇐ ?T |- _] =>
     assert (·;· ⊢ V ⇐ (〚θ〛T)) by eauto 4 using @subj_red; 
     assert (canonical V (〚θ〛T)) by eauto 4;
     assert (val V) by eauto 4; clear H0
| [ H : (synth ?I)[?θ;;_] ⇓ ?V,
    H0 : _;_ ⊢ ?I ⇒ ?T |- _] =>
     assert (·;· ⊢ V ⇐ (〚θ〛T)) by eauto 4 using @subj_red;
     assert (canonical V (〚θ〛T)) by eauto 4;
     assert (val V) by eauto 4; clear H0
end.

Theorem progress : forall {δ γ} θ ρ (Hyp:val_env ρ)
(E:checked_exp δ γ) (Hyp:src_lang E) T,
   ·;· ⊢ E[θ;;ρ] ⇐ T
-> (forall V, (E[θ;;ρ] ⇓ V) -> False)
-> E[θ;;ρ] ⇑.
cofix. intros. invert_typing. nice_inversion H7; invert_src;
try (econstructor; by eauto);
try (edestruct H0; by eauto).

(* synth *)
nice_inversion H; invert_src.

(* var *)
nice_inversion Hyp. specialize (H3 x). inversion H3.
edestruct H0. eauto.
econstructor; eauto.
eapply progress; eauto.
rewrite H1. by eauto.

(* app *)
doesItConverge I0 θ ρ.
doesItConverge E θ ρ.
repeat canonical. nice_inversion H13. invert_typing.
nice_inversion H20.
eapply div_app3; eauto.
nice_inversion H14.
eapply progress; eauto.
econstructor; eauto.
erewrite compose_cons.
eapply env_tp_cons; eauto.
rewrite H1. by eauto.
eapply div_app2; by eauto 7.
eapply div_app1. eapply progress; by eauto.

(* mapp *)
doesItConverge I0 θ ρ.
canonical. nice_inversion H6. invert_typing. nice_inversion H16.
eapply div_mapp2; eauto.
nice_inversion H10.
eapply progress; eauto.
econstructor; eauto.
erewrite cons_import_mvar. by eauto.
eapply div_mapp1; eapply progress; by eauto 7.

(* coercion *)
econstructor. by eauto. 

(* unfold *)
econstructor.
eapply progress; eauto.
intros v Hy. canonical. nice_inversion H3. by eauto.

(* rec *)
econstructor.
eapply progress; eauto.
econstructor; eauto.
erewrite compose_cons.
by eauto.

(* pair *)
doesItConverge E1 θ ρ.
eapply div_pair2; by eauto.
eapply div_pair1; by eauto.
Qed.

Lemma dot_val_env : val_env ·.
econstructor. intro. edestruct (empty_is_empty x).
Qed.

Lemma dot_subst_typing : · ⊩ · ∷ ·.
intro. edestruct (empty_is_empty x).
Qed.

Lemma dot_env_typing Δ : ·; · ⊪ · ⇐ Δ.
intro. edestruct (empty_is_empty x).
Qed.
Hint Resolve dot_val_env dot_subst_typing dot_env_typing.

Theorem progress' : forall E T (Hyp:src_lang E),
   ·;· ⊢ E ⇐ T
-> (exists V, E[·;;·] ⇓ V) \/ E[·;;·] ⇑.
intros.
destruct (classical (exists V, E[·;;·] ⇓ V)); eauto.
right. eapply progress; eauto.
Qed.
Print Assumptions progress'.
