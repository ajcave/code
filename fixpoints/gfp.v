
Fixpoint iter (F : Set -> Set) (n : nat) (X : Set) : Set :=
match n with
| 0 => X
| S m => iter F m (F X)
end.

Definition limit (H : nat -> Set) (h : forall n, H (S n) -> H n) :=
{ f : forall n, H n | forall n h, h n (f (S n)) = f n }.

Definition gfp_diagram F n : Set :=
iter F n unit.

Definition HasMap (F : Set -> Set) :=
 forall {X Y : Set}, (X -> Y) -> (F X -> F Y).

Fixpoint IterMap F (map : HasMap F) n : HasMap (iter F n) :=
match n return HasMap (iter F n) with
| 0 => fun X Y f => f
| S m => fun X Y f => IterMap F map m _ _ (map _ _ f)
end.

Definition gfp_diagram_arrows F (map : HasMap F)
 : forall n, gfp_diagram F (S n) -> gfp_diagram F n
:= fun n => IterMap F map n _ _ (fun _ => tt).

Definition gfp_lim F (map : HasMap F) :=
limit (gfp_diagram F) (gfp_diagram_arrows F map).

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
