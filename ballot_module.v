Require Import List.
Import ListNotations.
Require Import EqNat.


Module Type Ballot.
  Parameter A : Type.
  
  Parameter no_contestants : A -> nat.

  Parameter contestant_rank : A -> nat -> option nat.

  Parameter ranked_contestant : A -> nat -> option nat.
End Ballot.

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

Module Ballot_list <: Ballot.
   
  Definition A := list nat.
  
  Definition no_contestants (l : A) := length l.
  Definition contestant_rank (l : A) n := find_nat n l.
  Definition ranked_contestant (l : A) n := nth_option n l.

End Ballot_list.

Module Get_winner (B : Ballot).
Import B.

Definition get_winner (b : A) : nat :=
(match (B.ranked_contestant b 0) with
       | Some x => x 
       | None => 0
 end).

End Get_winner.

Module X := Get_winner (Ballot_list).

Compute X.get_winner [3; 2; 1; 0].



 

  
