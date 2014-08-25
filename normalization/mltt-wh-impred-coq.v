Set Implicit Arguments.
Open Scope type_scope.
Fixpoint fin (n : nat) : Set := match n with
| 0 => False
| S n' => sum (fin n') unit
end.
Inductive tm (n : nat) : Set :=
| app : tm n -> tm n -> tm n
| ttrue : tm n
| tfalse : tm n
| tif : tm n -> tm n -> tm n -> tm n
| tmvar : fin n -> tm n
.
Inductive tp (d : nat) (n : nat) : Set :=
| pi : tp d n -> tp d (S n) -> tp d n
| all : tp (S d) n -> tp d n
| iftp : tm n -> tp d n -> tp d n -> tp d n
| tvar : fin d -> tp d n
| bool : tp d n
| univ : tp d n
.

Arguments ttrue [n].
Arguments tfalse [n].

Arguments bool [d n].
Implicit Arguments tvar [d n].

Definition interp := tm 0 -> Set.
(* Definition interp := tm 0 -> Prop. (* This also works. Need to change normalizable to Prop though *) *)

Inductive step {n} : forall (M N : tm n), Set :=
| step_if_t : forall M1 M2, step (tif ttrue M1 M2) M1
.
Inductive mstep {n} : forall (M N : tm n), Set :=
| mrefl : forall {M}, mstep M M
| mtrans1 : forall {M M' N}, step M M' -> mstep M' N -> mstep M N.

Inductive msteptp {d n} : forall (M N : tp d n), Set := 
(* TODO ... *) .

Inductive normal {n} : forall (M : tm n), Set :=
| normal_true : normal ttrue
| normal_false : normal tfalse
with neutral {n} : forall (M : tm n), Set :=
| neut_var : forall {x}, neutral (tmvar n x).

Inductive normalizable {n} (M : tm n) : Set :=
 | norm : forall N, mstep M N -> normal N -> normalizable M.

Record isCand (R : interp) : Type := {
 cr1 : forall {M}, R M -> normalizable M ;
 cr2 : forall {M N}, mstep M N -> R N -> R M ;
 cr3 : forall {M}, neutral M -> R M
}.

Open Scope type_scope.

Fixpoint interpretation (d : nat) : Type :=
match d with
| O => unit
| S d' => (interpretation d') * interp
end.
Fixpoint lookup (d : nat) : interpretation d -> fin d -> interp :=
match d return interpretation d -> fin d -> interp with
| 0 => fun rho x => match x with end
| S d' => fun rho x => match x with inl x' => lookup d' (fst rho) x' | inr _ => snd rho end
end.

Definition tpsub1 {d n} (a : tm n) (B : tp d (S n)) : tp d n.
Admitted. (* TODO *)

(* It's inductive definitions inside Type that give us the extra expressive power 
   to skirt Godel's incompleteness (or simply having the extra universe) *)
Set Printing Universes.
Inductive Psi {d} (rho : interpretation d) : tp d 0 -> interp -> Type :=
| Psi_bool : Psi rho bool normalizable
| Psi_pi :
  forall {A B} {psiA : interp}, 
  forall (psiB : forall a, psiA a -> interp),
  Psi rho A psiA
 -> (forall a (p : psiA a), Psi rho (tpsub1 a B) (psiB a p))
 -> Psi rho (pi A B) (fun t => normalizable t * (forall a (p : psiA a), psiB a p (app t a)))
| Psi_all :
  forall {B},
  forall (psiB : forall (R : interp), isCand R -> interp),
  (forall (R : interp) (pf : isCand R), @Psi (S d) (rho , R) B (psiB R pf))
 -> Psi rho (all B) (fun t => forall (R : interp) (pf : isCand R), psiB R pf t)
| Psi_var : forall {X}, Psi rho (tvar X) (lookup d rho X)
| Psi_closed :
  forall {A B} {psiB : interp},
  msteptp A B -> Psi rho B psiB -> Psi rho A psiB
.
Print Psi.

Set Printing Universes.
(* Inductive Phi {d} (rho : interpretation d) : tp d 0 -> interp -> Type := *)
(* | Phi_bool : Phi rho bool normalizable *)
(* | Phi_univ : Phi rho univ  *)
(* | Phi_pi : *)
(*   forall {A B} {phiA : interp},  *)
(*   forall (phiB : forall a, phiA a -> interp), *)
(*   Phi rho A phiA *)
(*  -> (forall a (p : phiA a), Phi rho (tpsub1 a B) (phiB a p)) *)
(*  -> Phi rho (pi A B) (fun t => normalizable t * (forall a (p : phiA a), phiB a p (app t a))) *)
(* | Phi_all : *)
(*   forall {B}, *)
(*   forall (phiB : forall (R : interp), isCand R -> interp), *)
(*   (forall (R : interp) (pf : isCand R), @Phi (S d) (rho , R) B (phiB R pf)) *)
(*  -> Phi rho (all B) (fun t => forall (R : interp) (pf : isCand R), phiB R pf t) *)
(* | Phi_var : forall {X}, Phi rho (tvar X) (lookup d rho X) *)
(* | Phi_closed : *)
(*   forall {A B} {phiB : interp}, *)
(*   msteptp A B -> Phi rho B phiB -> Phi rho A phiB *)
(* . *)
(* Print Phi. *)


(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** End: ***
*)