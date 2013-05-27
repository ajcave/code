Definition compose {A B C} (g : B -> C) (f : A -> B) : A -> C := fun x => g (f x).
Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity).

Set Implicit Arguments.
Section mu.
 Variable F : Set -> Set.
 Variable map : forall {C D : Set} (f : C -> D), F C -> F D.

Definition mu := { fold : forall (C:Set), (F C -> C) -> C |
     forall {C D : Set} (g : C -> D) (hc : F C -> C) (hd : F D -> D),
           g ∘ hc = hd ∘ (map g)
        -> g (fold C hc) = fold D hd
        }.

Definition inj (x : F mu) : mu.
set (t := (fun (C : Set) => fun (f : F C -> C) => f (map (fun y => proj1_sig y _ f) x))).
refine (exist _ t _).
intros.
unfold t.