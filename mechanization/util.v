Section star.
 Hypotheses (A:Set) (Rel:A -> A -> Set).
 Inductive star (a:A) : A -> Set :=
  | s_nil : star a a
  | s_cons : forall b c, star a b -> Rel b c -> star a c.
 End star.
 Implicit Arguments star.
 Implicit Arguments s_nil.
 Implicit Arguments s_cons.
 Print Implicit s_cons.
 Implicit Arguments s_nil [A Rel a].
 Notation "A ,, B" := (s_cons _ A B) (at level 90).
