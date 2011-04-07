Require Import util.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import worlds.
Require Import meta_subst.
Require Import comp_expr.
Require Import meta_subst_meta_type.
Require Import meta_subst_meta_term.
Require Import meta_subst_typing.
Require Import meta_term.
Require Import meta_subst_meta_subst.
Require Import Setoid.

Definition import_msubst {δ δ' δ''} (X:δ'↪δ'')  (θ:msubst δ δ')  : msubst δ δ'' :=
 import_meta_term X ○ θ.

Section app_msubst_tp_sect.

Reserved Notation "[ θ ] T" (at level 90).
Definition context_mult {δ δ'} (θ:msubst δ δ') {δ'' δ'''} (y:δ'↪δ''') (x:δ↪δ'') := (import_msubst y θ,, (x,m_var y)).
Notation "θ × ( y // x )" := (context_mult θ y x) (at level 10).
Fixpoint app_msubst_tp {ψ} {δ δ'} (θ:msubst δ δ') (T:tp' ψ δ) : tp' ψ δ' :=
match T  with
 | m_tp U     =>
   m_tp _ (⟦θ⟧ U)
 | arr T1 T2  =>
   arr ([θ] T1) ([θ] T2)
 | pi _ X U T0 =>
   let (_,X') := next δ' in
   pi X' (⟦θ⟧ U) ([ θ × (X' // X )] T0)
 | sigma _ X U T0 =>
   let (_,X') := next δ' in
   sigma X' (⟦θ⟧ U) ([ θ × (X' // X )] T0)
 | unit =>
   unit _ _
 | prod T1 T2 =>
   prod ([θ] T1) ([θ] T2)
 | sum T1 T2 =>
   sum ([θ] T1) ([θ] T2)
 | tvar n =>
   tvar _ n
 | tapp T0 C =>
   tapp ([θ] T0) (⟦θ⟧ C)
 | eq_constraint C1 C2 T0 =>
   eq_constraint (⟦θ⟧ C1) (⟦θ⟧ C2) ([θ] T0)
end
where "[ θ ] T" := (app_msubst_tp θ T).

Instance tp_substitutable' : substitutable tp := {
  app_subst := @app_msubst_tp empty
}.
pose proof (@assoc _ mtype_substitutable).
pose proof (@assoc _ meta_term_substitutable).
unfold app_subst in *. unfold mtype_substitutable in *.
unfold meta_term_substitutable in *.

intros α T. induction T; intros;
simpl;
f_equal; firstorder.
remember (next' γ).
remember (next' β).
destruct s0.
destruct s1.
simpl.
erewrite IHT.
f_equal.
eapply functional_extensionality_dep.
intro. unfold compose at 1.
unfold context_mult at 2.
unfold compose at 1.

unfold context_mult at 2.
unfold compose at 1.

remember (export s x1).
destruct s2; simpl in *.
unfold import_msubst.
unfold import_meta_term.
unfold app_subst.
unfold meta_term_substitutable.
unfold compose at 1.
erewrite H0.
unfold compose at 1.
assert ((fun a => app_msubst (θ' ×  (s0 // s1)) (m_var (import s1 a))) = import_msubst s0 θ').
eapply functional_extensionality_dep.
intro.  erewrite app_msubst_mvar_result.
unfold context_mult.
unfold compose.
erewrite export_import_inv.
simpl.
reflexivity.
rewrite H1.
unfold compose.
erewrite H0.
unfold import_msubst.
unfold import_meta_term.
unfold app_subst.
unfold meta_term_substitutable.
reflexivity.

unfold context_mult.
unfold compose.
erewrite app_msubst_mvar_result.
erewrite export_self. reflexivity.
admit. (* TODO: Extract lemma. (It's the same proof) *)
Defined.
End app_msubst_tp_sect.
Implicit Arguments app_msubst_tp.

Instance tp_substitutable : substitutable tp := tp_substitutable'.

Definition msubst_single_t {δ δ'} (X:δ↪δ') (t:meta_term δ) : tp δ' -> tp δ :=
 ⟦ (maybe (@m_var _ ) t) ○ (export X) ⟧.