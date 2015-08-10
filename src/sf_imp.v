Require Import sf_spec.
Require Import RelDec.
Require Import List.
Require Import Sorting.
Require Import Orders.
Require Import Compare_dec.
Require Import NPeano.
Import ListNotations.

Section candidate.

Variable candidate : Set.
Variable reldec_candidate : RelDec (@eq candidate).

Definition rankSelection := rankSelection candidate.
Definition ballot := ballot candidate.

(** A record of an election will be a list of the candidates that are eliminated 
in each step *)
Definition record := list (list candidate).

(** a ballot
shall be deemed "exhausted," and not counted in further stages of the
tabulation, if all of the choices have been eliminated or there are no
more choices indicated on the ballot. If a ranked-choice ballot gives
equal rank to two or more candidates, the ballot shall be declared
exhausted when such multiple rankings are reached. *)

Definition eliminated (rec : record) (cand : candidate) : bool :=
  existsb (existsb (eq_dec cand)) rec.

Definition no_viable_candidates_selection (rec : record) (sel : rankSelection) : bool :=
  forallb (eliminated rec) sel.

Definition no_viable_candidates (rec : record) (bal : ballot) : bool :=
  forallb (no_viable_candidates_selection rec) bal.

Fixpoint next_ranking (rec : record) (bal : ballot) : option (candidate * ballot) :=
match bal with
| [] :: t => next_ranking rec t
| (h :: l) :: t => if (forallb (eq_dec h) l) then 
                     if (eliminated rec h) then next_ranking rec t else Some (h, bal)
                   else  None
| [] => None
end.


Fixpoint drop_none {A} (l : list (option A)) :=
match l with
| None :: t => drop_none t
| Some x :: t => x :: drop_none t
| [] => []
end.

Fixpoint increment (r : list (candidate * nat)) (c : candidate) :=
match r with 
| (c1, n) :: t => if (eq_dec c1 c) then (c1, S n) :: t else (c1, n) :: increment t c
| nil => [(c, 1)]
end.


Fixpoint tabulate'' (rs : list candidate) lc: list (candidate * nat) :=
match rs with
| h :: t => tabulate'' t (increment lc h)
| nil => lc
end.

Definition tabulate' (rs : list candidate) :=
tabulate'' rs nil.

Definition cnlt (a b : (candidate * nat)) : bool :=
match a, b with
(_, n1), (_, n2) => NPeano.ltb n1 n2
end.

Fixpoint insert {A} (cmp : A -> A -> bool) (i : A) (l : list A) :=
match l with
| h :: t => if (cmp h i) then i :: t else h :: (insert cmp i t)
| _ => [i]
end.

Fixpoint insertionsort' {A} (cmp : A -> A -> bool) (l : list A) (srtd : list A) :=
match l with 
| h :: t => insertionsort' cmp t (insert cmp h srtd)
| [] => srtd
end.

Definition insertionsort {A} (cmp : A-> A -> bool) (l : list A) := insertionsort' cmp l nil.

Definition election := list ballot.


(** Here we count the number of votes for each candidate, returning a sorted
    list of (candidate, number of votes). It also returns an election, where any
    exhausted ballots are removed. *)
Definition tabulate (rec : record) (elect : election) : ((list (candidate * nat) * election)) :=
let get_candidates := drop_none (map (next_ranking rec) elect) in
let (next_ranks, next_election) := split (get_candidates) in
let counts := tabulate' next_ranks in
let sorted_ranks := insertionsort cnlt counts in
(sorted_ranks, next_election).

Definition gtb_nat (a b : nat) : bool:=
match (nat_compare a b) with
| Gt => true
| _ => false
end.

Require Import Omega.

Lemma gtb_nat_gt : forall a b,
gtb_nat a b = true <-> a > b.
unfold gtb_nat in *.
intros. destruct (nat_compare a b) eqn:?;
intuition.
- apply  nat_compare_eq in Heqc. omega. 
- apply nat_compare_lt in Heqc. omega.
- apply nat_compare_gt in Heqc. auto.
Qed.

Check filter.

Definition get_bottom_votes (votes : list (candidate * nat)) :=
match votes with
| (c, v) :: t => map fst (filter (fun (x : candidate * nat) => let (_, v') := x in 
                                  beq_nat v v') votes)
| nil => nil
end.

Variable break_tie : list candidate -> option candidate.

(* This expects a list of candidates sorted ascending in number of votes *)
Fixpoint find_eliminated' (eliminated : list candidate) (votes : list (candidate * nat)) (sum : nat) :=
  match votes with
  | (cand, count) :: t =>
    match t with 
    |  (cand2, count2) :: _ =>  
       let newsum := sum + count in
       if (ltb (newsum) count2) then
         find_eliminated' (cand :: eliminated)
                          t sum
       else
         match eliminated with 
         | nil => match break_tie (get_bottom_votes votes) with
                  | Some l => [l]
                  | None => nil
                  end
         | _ => eliminated
         end
    | _ => eliminated
    end
  | _ => eliminated
  end.

Definition find_eliminated votes :=
  find_eliminated' [] votes 0.
                      
Fixpoint run_election' (elect : election) (rec : record) (fuel : nat) :  (option candidate * record) :=
match fuel with
| S n' => let (ranks, elect') := (tabulate rec elect) in
          let win_threshhold := (length elect') / 2 in (* here we use elect' because exhausted ballots
                                                          have been removed *) 
          match ranks with
          | (cand1, cand1_votes) :: _ => 
            if (gtb_nat cand1_votes win_threshhold) then
              (Some cand1, rec)
            else
              run_election' elect' (find_eliminated (rev ranks) :: rec) n'
          | nil => (None, rec)
          end
| _ => (None, rec)
end.

Fixpoint run_election elect :=
run_election' elect nil (length elect).


End candidate.

Global Instance RelDec_eq : RelDec (@eq nat) :=
{ rel_dec := EqNat.beq_nat }.

Global Instance RelDec_lt : RelDec lt :=
{ rel_dec := NPeano.ltb }.

Global Instance RelDec_le : RelDec le :=
{ rel_dec := NPeano.leb }.

Global Instance RelDec_gt : RelDec gt :=
{ rel_dec := fun x y => NPeano.ltb y x }.

Global Instance RelDec_ge : RelDec ge :=
{ rel_dec := fun x y => NPeano.leb y x }.

Definition nat_tabulate := tabulate nat _.

Definition ballot1 : (ballot nat) :=
[[3]; [2]; [1]; [0]].

Definition ballot2 : (ballot nat) :=
[[2]; [1]; [3]; [0]].

Definition ballot3 : (ballot nat) := ballot1.

Definition ballot4 := 
[[0]; [1]].

Definition election1 :=
[ballot1;
 ballot2;
 ballot3;
 ballot4].

Compute (nat_tabulate nil (election1)).

Definition tiebreak (l : list nat) :=
match l with
| h :: t => Some h
| _ => None
end.


Compute (run_election nat _ tiebreak election1).




  