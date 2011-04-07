Parameter world : Set.
 Parameter empty : world.
 Parameter name : world -> Set.
 Axiom empty_is_empty : name empty -> False.
 Parameter wlink : world -> world -> Set.
 Definition slink := wlink. (* ??? *)
 Notation "α ↪ β" := (slink α β) (at level 90).
 Definition weaken1 {a b} (x:slink a b) : wlink a b := x.
 Axiom weaken1_inj : forall {W W'} {y y':slink W W'}, weaken1 y = weaken1 y' -> y = y'.
 Parameter weaken : forall {a b}, slink a b -> name b.
 Coercion weaken : slink >-> name.
 Parameter import : forall {a b}, slink a b -> name a -> name b.
 Parameter next' : forall a, {b:world & a↪b}.
 Definition next a : {b:world & a↪b} := existT _ (projT1 (next' a)) (projT2 (next' a)).
 Axiom import_inj : forall {α β} {y:α↪β} {x x0}, import y x = import y x0 -> x = x0. 
 Axiom import_img : forall {α β} (y:α↪β) x, import y x <> y.
 Parameter export : forall {α β} (y:α↪β) (n:name β), name α + {n = y}.
 Axiom export_exclusive : forall {α β} {y:α↪β} {n:name α}, inleft _ n = export y y -> False.