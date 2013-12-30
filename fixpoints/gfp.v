
Inductive SPF : Set :=
| One : SPF
| Times : SPF -> SPF -> SPF
| Sum : SPF -> SPF -> SPF
| Var : SPF. 

Fixpoint interp (F : SPF) (X : Set) : Set :=
match F with
| One => unit
| Var => X
| Sum F G => sum (interp F X) (interp G X)
| Times F G => prod (interp F X) (interp G X)
end.

Fixpoint iter (F : Set -> Set) (n : nat) (X : Set) : Set :=
match n with
| 0 => X
| S m => F (iter F m X)
end.

Definition limit (H : nat -> Set) (h : forall n, H n -> H (S n)) :=
{ f : forall n, H n | forall n h, h n (f n) = f (S n) }.

