Require Import util.
Require Import worlds.
Require Import comp_expr.

Open Scope type_scope. 
Definition var_tp D G1 G2 := (slink G1 G2)*(tp D).
 Definition tp_assign G D := star (var_tp D) empty G.
 Definition tp_assign_nil D := @s_nil _ (var_tp D).

 (* TODO: We could eliminate the duplication between this and the other one *)
 Inductive var_assigned D G : tp_assign G D -> name G -> tp D -> Prop :=
  | v_asn_top : forall G' (A:tp_assign G' D) T x,
                    var_assigned D G (A,, (x,T)) x T
  | v_asn_else : forall G' T A x (y:slink G' G) U,
                 var_assigned D G' A x T
                 -> var_assigned D G (A,, (y,U)) (import y x) T.
 Implicit Arguments var_assigned.