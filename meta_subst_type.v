Require Import util.
Require Import worlds.
Require Import meta_subst.
Require Import comp_expr.
Require Import meta_subst_meta_type.
Require Import meta_subst_meta_term.
Require Import meta_subst_typing.
Require Import meta_term.


Definition import_msubst {δ δ' δ''} (X:δ'↪δ'')  (θ:msubst δ δ')  : msubst δ δ'' :=
 import_meta_term X ○ θ.

Section app_msubst_t2_sect.

Reserved Notation "[ θ ] T" (at level 90).

Fixpoint app_msubst_t2 {ψ} {δ δ'} (θ:msubst δ δ') (T:tp' ψ δ) : tp' ψ δ' :=
match T  with
 | m_tp U     =>
   m_tp _ (⟦θ⟧ U)
 | arr T1 T2  =>
   arr ([θ] T1) ([θ] T2)
 | pi _ X U T0 =>
   let (_,X') := next δ' in
   pi X' (⟦θ⟧ U) ([import_msubst X' θ,, (X,m_var X')] T0)
 | sigma _ X U T0 =>
   let (_,X') := next δ' in
   sigma X' (⟦θ⟧ U) ([import_msubst X' θ,, (X,m_var X')] T0)
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
where "[ θ ] T" := (app_msubst_t2 θ T).
End app_msubst_t2_sect.
Implicit Arguments app_msubst_t2.


 Instance tp_substitutable : substitutable tp := (@app_msubst_t2 empty).

Axiom msubst_single_t : forall {D D'} (X:wlink D D'), meta_term D -> tp D' -> tp D.
(* TODO: Write this as a simultaneous substitution: (id,C/X) ? *)