Require Import Ascii String List EqNat NPeano.

(*********************************************************************************)
(*                                                                               *)
(*           A  Coq version of the 2048 game                                     *)
(*                tested with 8.4pl2                                             *)
(*                                             Laurent.Thery@inria.fr            *)
(*                                                                               *)
(*********************************************************************************)

(* Possible moves *)
Inductive move := Rm (* right *) | Lm (* left *) | Um (* up *) | Dm (* down *).

(* Remove all the elements a of l such that p a holds *)
Fixpoint strip {A : Type} (p : A -> bool) l := 
      match l with
      | nil => l
      | a :: l1 => if p a then strip p l1 else a :: strip p l1
      end.

(* Cumulative action on a line *)
Fixpoint cumul (n : nat) (l : list nat) {struct n} : list nat :=
  match n with
  | 0 => nil | 1 => hd 0 l :: nil
  | S (S n2 as n1) =>
      let l1 := strip (beq_nat 0) l in
      let a := hd 0 l1 in
      let l2 := tl l1 in
      let b := hd 0 l2 in
          if beq_nat a b then a + b :: cumul n1 (tl l2)
          else a :: cumul n1 l2
  end.

(* Cumulative action + strip on lines *)
Definition icumul n := map (cumul n).

(* Count the number of occurrences of p on a line *)
Definition count (p : nat -> bool) :=
  fold_right (fun n => if p n then S else id) 0.

(* Count the number of occurrences of p on lines *)
Definition icount p := fold_right (fun l => plus (count p l)) 0.

(* Check if v occurs in the lines *)
Definition is_won v ll := negb (beq_nat (icount (beq_nat v) ll) 0).

(* Count the number of zeros in the lines *)
Definition zeros := icount (beq_nat 0).

(* Replace the n th occurrence of p with v in ligne l *)
Fixpoint replace n (p : nat -> bool) v l  :=
  match l with 
  | a :: l1 => if p a then
              match n with 
              | O => v :: l1 
              | S n1 => a :: replace n1 p v l1
              end
              else a :: replace n p v l1
  | nil => nil
  end.

(* Replace the n th occurrence of p with v in lignes ll *)
Fixpoint ireplace n (p : nat -> bool) v ll  :=
  match ll with 
  | l :: ll1 => let m := count p l in
    if ltb n m then (replace n p v l) :: ll1
    else l :: ireplace (n - m) p v ll1
  | nil => nil
end.

(* Flip the board *)
Definition iflip (n : nat) := map (@rev nat).

(* Rotate the board *)
Fixpoint irotate (n : nat) ll := 
  match n with
  | 0    => nil
  | S n1 =>  map (hd 0) ll :: irotate n1 (map (@tl _) ll) 
  end.

(* Iterator *)
Fixpoint iter {A : Type} n (f : A -> A) a  :=
  match n with 0 => a | S n1 => f (iter n1 f a) end.

(* Make Empty board *)
Fixpoint make_board n :=
  let l := iter n (cons 0) nil in iter n (cons l) nil.
 
(* Apply a test on a list *)
Fixpoint test_list {A: Type} (f : A -> A -> bool) l1 l2 :=
  match l1, l2 with
  | nil, nil => true
  | a :: l3, b :: l4 => if f a b then test_list f l3 l4 else false
  | _, _ => false
  end.

(* Equal boards *)
Definition eq_board := test_list (test_list beq_nat).

(* Make a move *)
Definition make_move n move b :=
   match move with
  | Lm => icumul n b 
  | Rm => iflip n (icumul n (iflip n b))
  | Um => irotate n (icumul n (irotate n b))
  | Dm => irotate n (iflip n (icumul n (iflip n (irotate n b))))
  end.

(* Add a number from gl inside b *)
Definition add_val s gl b := 
      let z := zeros b in
      if beq_nat z 0 then None else
      (* Which empty cell gets the new number *)
      let k := modulo s z in
      let s1 := s / z in
      (* Which value to put in the empty cell *)
      let v1 := nth (modulo s1 (length gl)) gl 0 in
      let s2 := s1 / (length gl) in
      let b1 := ireplace k (beq_nat 0) v1 b in
      Some (s2, b1).

(* Encoding of the result *)
Definition Invalid_Move := False.
Definition Lost := False.
Definition Won (t : list move) := True.

(* Printing Stuff *)

Definition nl := (String (ascii_of_nat 10) "")%string.

(* Number of digits of a number *)
Fixpoint digit_aux m n :=
  if beq_nat n 0 then 0
  else
  match m with 0 => 0 | S m1 => S (digit_aux m1 (n / 10))
  end.
Definition digit n := digit_aux n n.

(* Digit to ascii *)
Definition d2a d := ascii_of_nat (48 + d).

(* Number to string *)
Fixpoint n2s n m :=
  match n with 0 => ""%string | S n1 =>
  if beq_nat m 0 then
     iter n (fun l => " " ++ l)%string ""%string
  else
    ((n2s n1 (m / 10)) ++ (String (d2a (modulo m 10)) ""))%string
  end.

(* Line to string *)
Definition l2s n l :=
  (fold_right (fun r s => "|" ++ n2s n r ++ s) ("|" ++ nl) l)%string.

(* Make a line *)
Definition make_line n :=
    iter n (fun l => "-" ++ l)%string nl.
 
(* Board to string *)
Definition b2s n m l :=
  let li := make_line (m * (n + 2))  in
  (nl ++ fold_right (fun r s => li ++ l2s n r ++ s) li l)%string.

(* Apply the list of moves ms to a position b *)
Fixpoint games n d s gl v ms b st :=
  match ms with
  | m :: ms1 =>
    let b1 := make_move n m b in
    if eq_board  b b1 then Invalid_Move
    else 
      if is_won v b1 then Won ms1 else
      let z := zeros b1 in
      if beq_nat z 0 then Lost else
      match add_val s gl b1 with
      | None => Lost
      | Some (s1, b2) =>
          games n d s1 gl v ms1 b2 (b2s d n b2)
      end
  | _ => Lost
  end.

Definition start_game n s gl v ms b :=
      match add_val s gl b with
      | None => Lost
      | Some (s1, b1) =>
          let d := digit v in 
          games n d s1 gl v ms b1 (b2s d n b1)
      end.

Definition new_game n s gl v ms :=
  start_game n s gl v ms (make_board n).

Definition g2048 s ms :=
  new_game 4 s (2 :: 4 :: nil) 2048 ms.

Definition s2048 s ms b :=
  start_game 4 s (2 :: 4 :: nil) 2048 ms b.

(* Board simpl *)
Ltac bsimpl :=
  simpl;
  try (set (x := b2s _ _ _); vm_compute in x; unfold x; clear x).

(* Generic tactic for move *)
Ltac gen_tac v := 
  match goal with
  |- games ?X1 ?X2 ?X3 ?X4 ?X5 ?X6 ?X7 ?X8 => 
       refine (_ : games X1 X2 X3 X4 X5 (v :: _) X7 X8)
  end; bsimpl.

(* Four tactic for the moves *)
Ltac R := gen_tac Rm.
Ltac L := gen_tac Lm.
Ltac U := gen_tac Um.
Ltac D := gen_tac Dm.
Ltac F := refine (_ : Won nil); apply I.

Ltac S := eexists; do 3 red; simpl;
  try (set (x := b2s _ _ _); vm_compute in x; unfold x; clear x).

(* Trick the prettyprinter *)
Notation "[T2048]  a " := (games _ _ _ _ _ _ _ a) (at level 10).
Notation "! Won" := (Won _) (at level 10).

(******************************************************************************)
(* In order to win the game we have to provide a list of moves                *)
(* A game is parametrised by a seed that determines which of 2 and 4 appears  *)
(* and where (there is no random number inside Coq ;-) )                      *)
(* You can either give the winning list of moves or try to build it           *)
(*  interactively :                                                           *)
(*       S to start                                                           *)
(*       D to move down                                                       *)
(*       U to move up                                                         *)
(*       R to move right                                                      *)
(*       L to move left                                                       *)
(*       F to end a winning game                                              *)
(******************************************************************************)


(* An example *)
Definition seed := 0. (* The 2 always appears in the first free cell *)

Lemma thm1 : exists ms, g2048 seed ms.
Proof. 
S.
R.
R.
R.
R.
R.
R.
R.
R.
R.
R.
R.
R.
R.
R.
D.
U.
R.
R.
R.
R.
R.
R.
R.
L.
U.
R.
R.
R.
L.
R.
L.
U.
L.
U.
R.
R.
R.
R.
R.
R.
R.
L.
U.
R.
L.
R.
L.
U.
L.
U.
R.
R.
R.
L.
U.
L.
U.
R.
L.
R.
U.
R.
L.
U.
R.
R.
R.
L.
L.
U.
R.
R.
R.
R.
R.
R.
U.
U.
R.
L.
U.
R.
L.
U.
R.
R.
R.
L.
U.
R.
L.
U.
L.
U.
L.
L.
L.
U.
R.
R.
R.
L.
U.
L.
U.
R.
L.
R.
U.
L.
R.
L.
U.
R.
R.
D.
U.
L.
R.
L.
U.
R.
U.
L.
U.
U.
U.
L.
U.
U.
R.
U.
L.
R.
U.
U.
U.
L.
R.
L.
U.
L.
U.
R.
R.
R.
D.
U.
R.
D.
U.
U.
R.
R.
R.
U.
L.
U.
L.
R.
R.
L.
D.
U.
R.
U.
R.
L.
U.
R.
L.
U.
L.
U.
L.
L.
L.

U.
R.
L.
U.
R.
L.
D.
U.
L.
L.
R.
L.
U.
U.
U.
U.
R.
U.
L.
U.
U.
U.
R.
U.
R.
U.
L.
L.
U.
R.

D.
U.
D.
U.
D.
U.
U.
L.
L.
U.
L.
U.
U.
R.
L.
R.
D.
U.
R.
L.
U.
L.
R.
L.
U.
U.
L.
L.
U.
R.
L.
R.
D.
U.
R.
L.
U.
L.
R.
L.
R.
U.
R.
R.
U.
L.
R.
U.
R.
R.
U.
R.
R.
R.
R.
R.
U.
L.
L.
U.
R.
U.
R.
R.

L.
R.
U.
R.
L.
U.
R.
L.
U.
L.
U.

R.
L.
U.
R.
L.
U.
R.
L.
D.
U.
R.
L.
U.
U.
R.
R.
L.
U.
L.
U.
L.
L.
L.
U.
R.

L.
U.
R.
L.
U.
R.
L.
D.
U.
R.
U.
R.
L.
U.
D.
U.
L.
R.
U.
R.
U.

L.
L.
U.
R.
R.
L.
D.
U.
R.
D.

U.
D.
U.
R.
U.
L.
R.
U.
U.
R.
U.
U.
U.
U.
L.
U.
R.
D.
U.
L.
U.
U.
U.
L.
U.
U.
L.
L.
D.
U.
R.
U.
L.
R.
U.
U.
U.
R.
L.
U.
U.
U.
R.
U.
L.
U.
L.
R.
U.
L.
R.
L.
R.
L.
R.
U.
R.
U.
L.
L.
U.
D.
U.
R.
U.
R.
U.

U.
R.
L.
U.
R.
L.
U.
R.
L.
U.
D.
U.
L.
D.
U.
L.
R.
U.
R.
U.
U.
U.
U.
R.
L.
U.
U.
R.
U.
L.
U.

U.
U.
R.
L.
U.
U.
D.
U.
R.
U.
L.
R.
U.
U.
U.
R.
L.
U.
U.
U.
R.
U.
L.
D.
U.
L.
U.
R.
U.
L.
U.
R.
L.
U.
U.
U.
L.
U.
L.
R.
U.
L.
L.
U.
U.
U.
R.
L.
U.
R.
L.
L.
U.
L.
U.
U.
R.
L.
U.
L.
U.
R.
L.
R.
U.
L.
L.
L.
R.
D.
U.