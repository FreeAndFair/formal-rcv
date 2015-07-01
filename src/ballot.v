Require Import List.
Import ListNotations.
Require Import EqNat.

Class Ballot (A : Type) := 
  {
    no_contestants : A -> nat;
    contestant_rank : A -> nat -> option nat;
    ranked_contestant : A -> nat -> option nat
  }.

Print Ballot.

Fixpoint find_nat' n l c :=
match l with 
  | h :: t => if beq_nat n h then Some c else find_nat' n t (S c)
  | nil => None
end.

Fixpoint find_nat n l :=
find_nat' n l 0.

Fixpoint nth_option {A} n (l : list A):=
  match n, l with 
  | S n', h :: t => nth_option n' t
  | 0, h :: t => Some h
  | _, nil => None
  end.

Instance ballot_list : Ballot (list nat) := 
  {
    no_contestants l := length l;
    contestant_rank l n := find_nat n l;
    ranked_contestant l n := nth_option n l
  }.

Definition get_winner {A: Type} {i : Ballot A} (ballot : A): nat :=
(match (ballot.(ranked_contestant) 0) with
       | Some x => x 
       | None => 0
 end).

Compute get_winner [3; 2; 1; 0].

