Require Import List.
Import ListNotations.
Require Import EqNat.
Require Import Strings.String.

(** * A Section
  This is a 
  #<a href=https://coq.inria.fr/refman/Reference-Manual017.html##sec578>coqdoc</a>#
  it works by running <<make html>> in this directory. The link above is the reference for Coqdoc
  ** A subsection
     To escape the pound sign in the html block, use it twice
  *** Subsubsection
     The makefile was created with the command 
<<
coq_makefile -o Makefile *.v
>>
     and can be updated for new files using the same command 
*)
Local Open Scope string_scope.

Record contestant : Type := 
  {
    name : string;
    identifier : nat
  }.


(** Function to decide equality between contestants *)
Definition beq_contestant (a b : contestant) :=
if (string_dec a.(name) b.(name)) 
then beq_nat a.(identifier) b.(identifier)
else false.

(** Proof that [beq_contestant] decides equality *)
Lemma beq_contestant_eq : forall a b, 
beq_contestant a b = true <-> a = b.
Proof.
intros. destruct a, b.
unfold beq_contestant. simpl.
destruct (string_dec name0 name1).
subst. 
rewrite (beq_nat_true_iff  identifier0 identifier1). 
intuition. inversion H. auto.
intuition. inversion H. intuition.
Qed.

Definition rank := nat.

Class Ballot (A : Type) := 
  {
    no_contestants_voted : A -> nat;
    contestant_rank : A -> contestant  -> option rank;
    ranked_contestant : A -> rank -> option contestant
  }.

(* begin hide *)
Print Ballot.
(* end hide *)


Fixpoint find_candidate' (n : contestant) (l : list contestant) c :=
match l with 
  | h :: t => if beq_contestant n h then Some c else find_candidate' n t (S c)
  | nil => None
end.

Definition find_candidate n l :=
find_candidate' n l 0.

Fixpoint nth_option {A} n (l : list A):=
  match n, l with 
  | S n', h :: t => nth_option n' t
  | 0, h :: t => Some h
  | _, nil => None
  end.

Instance ballot_list : Ballot (list contestant) := 
  {
    no_contestants_voted l := List.length l;
    contestant_rank l n := find_candidate n l;
    ranked_contestant l n := nth_option n l
  }.

(** We can use sections so that we don't need to define the same parameters in every definition. 
    outside of the section, the parameters will appear automatically if they were used 
    in some definition *)

Section blt.

Context {A : Type}.
Context {BA : Ballot A}.

(** The comment below was in the previous version, removed because we are in
    a section with A and i defined now *)
Definition get_winner (* {A: Type} {i : Ballot A} *) (ballot : A): option contestant :=
ballot.(ranked_contestant) 0.

Inductive has_winning_vote : list A -> contestant -> Prop :=
| has_vote_eq : forall h t c, get_winner h = Some c -> has_winning_vote (h :: t) c 
| has_vote_rest : forall h t c, has_winning_vote t c -> has_winning_vote (h :: t) c.

Fixpoint has_winning_vote_comp (l : list A) (c : contestant) :=
match l with
| h :: t => 
  if 
    (match (get_winner h) with
     | Some w => beq_contestant c w
     | None => false
     end)
  then true 
  else has_winning_vote_comp t c
| nil => false
end.

Theorem has_winning_vote_correct : 
  forall l c, has_winning_vote_comp l c = true -> has_winning_vote l c.
Proof.
induction l; intros.
- simpl in *. inversion H.
- simpl in *. remember (get_winner a). 
  destruct o.
  + remember (beq_contestant c c0).
    destruct b.
    * symmetry in Heqb.
      rewrite beq_contestant_eq in Heqb. subst.
      apply has_vote_eq. auto.
    * apply has_vote_rest. auto.
  + apply has_vote_rest. auto.
Qed.

End blt.
Print contestant.

Definition alice := 
  {| 
    name := "Alice";
    identifier := 0
  |}.

Definition bob := 
  {| 
    name := "Bob";
    identifier := 1
  |}.


Definition charles := 
  {| 
    name := "Charles";
    identifier := 2
  |}.

Compute get_winner [charles; bob; alice].

Compute has_winning_vote_comp [[charles; bob; alice]] charles.

(** In the end we can get a proof that we have done the computation correctly by
    applying our correctness theorem to the computational thing. The eq_refl tells
    Coq it should attempt to unify [has_winning_vote_comp [[charles; bob; alice]] charles]
    with [true], which it can do easily *)

Definition someone_likes_charles := has_winning_vote_correct [[charles; bob; alice]] charles 
                                                             (eq_refl _).

