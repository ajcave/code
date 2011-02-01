Parameter U : Set -> Set.

Inductive tp (G:Set) : Set :=
 | u_tp : U G -> tp G
 | t_arr : tp G -> tp G -> tp G
 | t_prod : U G -> tp (G + unit) -> tp G.

