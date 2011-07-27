Require Import Omega.
Theorem foo : bool <> unit.
intro.
assert (exists x:bool, exists y:bool, x <> y).
exists true. exists false. discriminate. 
rewrite H in H0.
dest ruct H0.
destruct H0.
destruct x.
destruct x0.
contradict H0. reflexivity.
Qed. 