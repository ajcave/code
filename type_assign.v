Require Import util.
Require Import worlds.
Require Import comp_expr.

Open Scope type_scope. 
Definition var_tp D G1 G2 := (slink G1 G2)*(tp D).
 Definition tp_assign D := star (var_tp D) empty.
 Definition tp_assign_nil D := @s_nil _ (var_tp D).
 Definition v_cons D := @s_cons _ (var_tp D) empty.
 Implicit Arguments v_cons.
 Print Implicit v_cons.

 (* TODO: We could eliminate the duplication between this and the other one *)
 Inductive var_assigned D G : tp_assign D G -> name G -> tp D -> Prop :=
  | v_asn_top : forall G' (A:tp_assign D G') T x,
                    var_assigned D G (v_cons A (x,T)) x T
  | v_asn_else : forall G' T A x (y:slink G' G) U,
                 var_assigned D G' A x T
                 -> var_assigned D G (v_cons A (y,U)) (import y x) T.
 Implicit Arguments var_assigned.