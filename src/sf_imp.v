Require Import sf_spec.
Require Import RelDec.
Require Import List.
Require Import Sorting.
Require Import Orders.
Require Import Compare_dec.
Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.
Import ListNotations.

Section candidate.

Local Open Scope N_scope.

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

Fixpoint increment (r : list (candidate * N)) (c : candidate) :=
match r with 
| (c1, n) :: t => if (eq_dec c1 c) then (c1, (n + 1)) :: t else (c1, n) :: increment t c
| nil => [(c, 1)]
end.


Fixpoint tabulate'' (rs : list (option candidate)) lc: list (candidate * N) :=
match rs with
| (Some h) :: t => tabulate'' t (increment lc h)
| None :: t => tabulate'' t lc
| nil => lc
end.

Definition tabulate' (rs : list (option candidate)) :=
tabulate'' rs nil.

Definition cnle (a b : (candidate * N)) : bool :=
match a, b with
(_, n1), (_, n2) => N.leb n1 n2
end.

Fixpoint insert {A} (cmp : A -> A -> bool) (i : A) (l : list A) :=
match l with
| h :: t => if (cmp i h) then i :: l else h :: (insert cmp i t)
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
Fixpoint option_split {A B : Type} (l : list (option (A * B))) :=
match l with
| nil => (nil, nil)
| (Some (a, b)) :: t => let (l1, l2) := option_split t in ((Some a :: l1), (Some b :: l2))
| None :: t => let (l1, l2) := option_split t in ((None :: l1), ( None :: l2))
end.

Definition tabulate (rec : record) (elect : election) : ((list (candidate * N) * election)) :=
let get_candidates := (map (next_ranking rec) elect) in
let (next_ranks, next_election) := option_split (get_candidates) in
let counts := tabulate' next_ranks in
let sorted_ranks := insertionsort cnle counts in
(sorted_ranks, drop_none next_election).

Definition gtb_N (a b : N) : bool:=
negb (N.leb a b). 

Require Import Omega.

Lemma gtb_nat_gt : forall a b,
gtb_N a b = true <-> a > b.
unfold gtb_N in *.
intros. 
destruct ( a <=? b) eqn:?; intuition; try discriminate.
 - rewrite N.leb_le in Heqb0. exfalso. apply N.gt_lt in H. 
   rewrite N.lt_eq_cases in Heqb0. 
   destruct Heqb0. apply N.lt_asymm in H. auto. subst.
   apply N.lt_irrefl in H. auto.
 - rewrite N.leb_gt in Heqb0. clear H. apply N.gt_lt_iff. auto.
Qed.


Definition get_bottom_votes (votes : list (candidate * N)) :=
match votes with
| (c, v) :: t => map (@fst _ _) (filter (fun (x : candidate * N) => let (_, v') := x in 
                                  N.eqb v v') votes)
| nil => nil
end.

Variable break_tie : list candidate -> option candidate.

(* This expects a list of candidates sorted ascending in number of votes *)
Fixpoint find_eliminated' (eliminated : list candidate) (votes : list (candidate * N)) (sum : N) :=
  match votes with
  | (cand, count) :: t =>
    match t with 
    |  (cand2, count2) :: _ =>  
       let newsum := sum + count in
       if (N.ltb (newsum) count2) then
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

Definition find_eliminated_noopt votes :=
  match break_tie (get_bottom_votes votes) with
    | Some c => Some [c]
    | None => None
  end.

Fixpoint last_item votes : option (candidate * N) :=
match votes with
| h :: [] => Some h
| [] => None
| h :: t => last_item t
end.

Fixpoint run_election' (elect : election) (rec : record) (fuel : nat) :  (option candidate * record) :=
match fuel with
| S n' => let (ranks, elect') := (tabulate rec elect) in
          let win_threshhold := N.of_nat (length elect')  in 
          (* here we use elect' because exhausted ballots have been removed *) 
          match last_item ranks with
          | Some (cand1, cand1_votes)  => 
            if (gtb_N (cand1_votes * 2) (win_threshhold)) then
              (Some cand1, rec)
            else
              match (find_eliminated_noopt ranks) with 
              | Some el =>
                run_election' elect(*' hopefully just an optimization...*)
                              (el :: rec) n'
              | None => (None, rec)
              end
          | None => (None, rec)
          end
| _ => (None, rec)
end.

Check filter.

Definition find_0s (all_candidates : list candidate) (el : election) :=
let get_candidates := (map (next_ranking nil) el) in
let (next_ranks, _) := option_split (get_candidates) in
let initial := map (fun x => (x, 0)) all_candidates in
let counts := tabulate'' next_ranks initial in
map fst (filter (fun (x : candidate * N) => let (_, ct) := x in N.eqb ct 0) counts).

Definition run_election elect all_candidates :=
let initial_selected := drop_none (fst (option_split (map (next_ranking nil) elect))) in
run_election' elect ([find_0s all_candidates elect]) (length elect).


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

Fixpoint repeat_append {A : Type} (l : list A) (n : nat) : list A :=
match n with 
| O => nil
| S n' => l ++ (repeat_append l n')
end.

Definition election1 :=
[ballot1;
 ballot2;
 ballot3;
 ballot4].

Definition election2 := repeat_append election1 1000.

Compute (nat_tabulate nil (election1)).

Definition tiebreak (l : list nat) :=
match l with
| h :: t => Some h
| _ => None
end.
