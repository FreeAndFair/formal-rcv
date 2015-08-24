Require Import List.
Require Import Classical.

Section election_spec.
  (** For this section, we hold the set of candidates abstract,
      and define ballots and some properties of ballots irrespective
      of how candidates are defined.
   *)
  Variable candidate:Set.

  (** Voters cast votes, which consist of a sequence of rank positions.
      For each rank position, a voter selects 0 or more candidates.
      A properly cast vote will have (1) no more than one candidate selected
      at each rank, (2) each candidate selected at most once, and (3) no
      candidate selected at a rank position later than a rank position with
      zero candidates.  However, voters do not always follow the rules;
      voters may select more than one candidate at a given rank, may select
      the same candidate more than once, or may skip rankings.

      The vote tabulation system must handle these cases.
   *)
  Definition rankSelection := list candidate.
  Definition ballot := list rankSelection.
  Definition election := list ballot.
  Definition contestants := list candidate.
(*  Variable tiebreak : list candidate -> candidate -> Prop. *)
  
  Section ballot_properties.
    (**  At any given round of a tabulation, some collection of candidates
         have been eliminated.  The following definitions are all defined
         with respect to the candidates that have been eliminated thus far.
         The abstract 'eliminated' predicate indicates which candidates are
         already eliminated.
      *)

    Variable eliminated : candidate -> Prop.

    (**  One condition for a ballot to be exhausted is that it
         all the candidates it selects have already been eliminated.
         This vacuously covers the case of an empty ballot.
     *)  
    Definition no_viable_candidates (b:ballot) :=
      forall rank, In rank b ->
        forall candidate, In candidate rank ->
          eliminated candidate.
    
    (**  From a given ballot, find the first rank selection
         (if it exists) which contains at least one
         continuing candidate.
      *)
    Fixpoint next_ranking (b:ballot) (r:rankSelection) : Prop :=
       match b with
         | nil => False
         | r'::b' =>
           ((forall c, In c r' -> eliminated c) /\ next_ranking b' r)
           \/
           ((exists c, In c r' /\ ~eliminated c) /\ r = r')
         end.
           
    (**  A ballot is an overvote if its next ranking contains
         two distinct candidates.
      *)
    Definition overvote (b:ballot) : Prop :=
      exists r, next_ranking b r /\
         exists c1 c2, In c1 r /\ In c2 r /\ c1 <> c2.

    (**  A ballot is exhausted if it selects no vaiable candidates
         or is an overvote 
      *)
    Definition exhausted_ballot (b:ballot) :=
      no_viable_candidates b \/ overvote b.

    Definition continuing_ballot (b:ballot) :=
      ~exhausted_ballot b.
 
    (**  A ballot selects a particular candidate iff it is a
         continuing ballot and its next ranking contains that
         candidate.
      *)
    Definition selected_candidate (b:ballot) (c:candidate) :=
      continuing_ballot b /\
      exists r, next_ranking b r /\ In c r.


    (** If a candidate receives a majority of the first choices, that
candidate shall be declared elected.*)

    Inductive first_choices (c : candidate) : election ->  nat -> Prop :=
    | first_choices_nil : first_choices c nil 0
    | first_choices_selected : forall h t n', selected_candidate h c ->
                                              first_choices c t n' ->
                                              first_choices c (h::t) (S n')
    | first_choices_not_selected : forall h t n, ~selected_candidate h c ->
                                                 first_choices c t n ->
                                                 first_choices c (h::t) n.


    (* this may not even be useful *)
   

    Definition all_candidates (e : election) (c : list candidate) :=
      NoDup c /\ Forall (Forall (Forall (fun x => In x c))) e.
    
    Definition most_votes (e : election) (winner : candidate) :=
      forall candidates, all_candidates e candidates ->
                         Forall 
                           (fun candidate => (exists n n_winner, (first_choices candidate e n) ->
                                                                 (first_choices winner e n_winner) ->
                                                                 n < n_winner) \/
                                             candidate = winner) candidates. 
    
    Inductive total_selected : election -> nat -> Prop :=
    | total_nil : total_selected nil 0
    | total_continuing : forall b e' n, continuing_ballot b ->
                                        total_selected e' n ->
                                        total_selected (b :: e') (S n)
    | total_exhausted : forall b e' n, exhausted_ballot b ->
                                       total_selected e' n ->
                                       total_selected (b :: e') (n).

    Definition majority (e : election) (winner : candidate) :=
      forall total_votes winner_votes, 
        (total_selected e total_votes) ->
        first_choices winner e winner_votes ->
        (winner_votes * 2) > total_votes.

    (** If no candidate receives a
majority, the candidate who received the fewest first choices shall be
eliminated and each vote cast for that candidate shall be transferred to
the next ranked candidate on that voter's ballot. *)

  Definition participates (c:candidate) (e:election) :=
    exists b, In b e /\ exists r, In r b /\ In c r.

  Definition is_loser (e:election) (loser:candidate) :=
    ~eliminated loser /\
    participates loser e /\
    forall c' n m,
      ~eliminated c' ->
      participates c' e ->
      first_choices loser e n ->
      first_choices c' e m ->
      n <= m.

    Definition no_majority (e : election) :=
      forall c, 
        all_candidates e c ->
        Forall (fun candidate => ~majority e candidate) c.

(*
    Definition possibly_eliminated_candidates 
               (e : election) (losers : list candidate) :=
      forall c, all_candidates e c ->
      exists n_loser, (Forall (fun cd => first_choices cd e n_loser) losers) /\ 
                      Forall (fun cd => exists n, first_choices cd e n ->
                                                  n_loser < n \/ 
                                                  In cd losers) c. 

    Definition eliminated_candidate (e : election) (loser : candidate) :=
      forall losers, 
        possibly_eliminated_candidates e losers /\ tiebreak losers loser. 
*)
    

    (**  Every ballot has at most one next ranking.
     *)
    Lemma next_ranking_unique (b:ballot) r1 r2 :
      next_ranking b r1 ->
      next_ranking b r2 ->
      r1 = r2.
    Proof.
      induction b; simpl; intuition.
      destruct H0 as [?[??]]; firstorder.
      destruct H as [?[??]]; firstorder.
      subst; auto.
    Qed.

    (**  Every ballot selects at most one candidate.
     *)
    Lemma selected_candidate_unique (b:ballot) (c1 c2:candidate) :
      selected_candidate b c1 ->
      selected_candidate b c2 ->
      c1 = c2.
    Proof.
      unfold selected_candidate.
      intros [Hb [r1 [??]]].
      intros [_ [r2 [??]]].
      assert (r1 = r2) by (apply (next_ranking_unique b); auto).
      subst r2.
      destruct (classic (c1=c2)); auto.
      elim Hb. red. right.
      red; firstorder.
    Qed.

    (**
What to do if a ballot has multiple choices for a rank, but all
have already been eliminated?  Shall the ballot be deemed exhausted,
or will we continue to consider later choices?

E.g.,

     A
     B, C
     D

Suppose both B and C were eliminated in earlier rounds, but
A is not eliminated.  We should count this ballot as a vote
for A.  Suppose, in a subsequent round, A is also eliminated.
Now, should this ballot be considered an overvote and removed;
or should it count as a vote for D?  The statue language is
unclear.

The formal specification above counts this situation as a vote for D.
*)

    (**  Whenever a ballot selects a candidate, that candidate
         is not yet eliminated.
      *)
    Lemma selected_candidate_not_eliminated (b:ballot) :
      forall c, selected_candidate b c -> ~eliminated c.
    Proof.
      induction b.
      unfold selected_candidate. intros c [Hc [r [??]]].
      elim H.
      intros c [Hc [r [??]]].
      destruct H as [[??]|[??]].
      apply IHb.
      split.
      red; intro.
      destruct H2.
      apply Hc.
      left. red; simpl; intros.
      destruct H3. subst rank.
      apply H; auto.
      red in H2. eapply H2; eauto.
      apply Hc.
      right.
      destruct H2 as [r' [??]].
      assert (r = r').
      apply (next_ranking_unique b); auto.
      subst r'.
      exists r; split; auto.
      simpl.
      left; split; auto.

      exists r. split; auto.
      subst a.
      intro.
      apply Hc.
      destruct H as [c' [??]].
      destruct (classic (c=c')).
      subst c'. elim H2. auto.
      right.
      exists r. split; auto.
      simpl.
      right.
      split; auto. exists c'; split; auto.
      exists c, c'. intuition.
    Qed.

  End ballot_properties.

  Definition update_eliminated (eliminated : candidate -> Prop) (c : candidate) :=
    fun cs => eliminated cs \/ c = cs.
  
  Inductive winner : 
    election -> (candidate -> Prop) -> candidate -> Prop :=
  | winner_now : forall election winning_candidate eliminated, 
      majority eliminated election winning_candidate ->
      winner election eliminated winning_candidate
  | winner_elimination : forall election winning_candidate eliminated loser,
      no_majority eliminated election ->
      is_loser eliminated election loser ->
      let eliminated' := update_eliminated eliminated loser in
      winner election eliminated' winning_candidate ->
      winner election eliminated winning_candidate.      

End election_spec. 

(**
SAN FRANCISCO CHARTER

[Obtained from-- http://www.amlegal.com/library/ca/sfrancisco.shtml on
June 13, 2015.]

ARTICLE XIII: ELECTIONS

SEC. 13.102. INSTANT RUNOFF ELECTIONS.

(a) For the purposes of this section: (1) a candidate shall be deemed
"continuing" if the candidate has not been eliminated; (2) a ballot
shall be deemed "continuing" if it is not exhausted; and (3) a ballot
shall be deemed "exhausted," and not counted in further stages of the
tabulation, if all of the choices have been eliminated or there are no
more choices indicated on the ballot. If a ranked-choice ballot gives
equal rank to two or more candidates, the ballot shall be declared
exhausted when such multiple rankings are reached. If a voter casts a
ranked-choice ballot but skips a rank, the voter's vote shall be
transferred to that voter's next ranked choice.

(b) The Mayor, Sheriff, District Attorney, City Attorney, Treasurer,
Assessor-Recorder, Public Defender, and members of the Board of
Supervisors shall be elected using a ranked-choice, or "instant runoff,"
ballot. The ballot shall allow voters to rank a number of choices in
order of preference equal to the total number of candidates for each
office; provided, however, if the voting system, vote tabulation system
or similar or related equipment used by the City and County cannot
feasibly accommodate choices equal to the total number of candidates
running for each office, then the Director of Elections may limit the
number of choices a voter may rank to no fewer than three. The ballot
shall in no way interfere with a voter's ability to cast a vote for a
write-in candidate.

(c) If a candidate receives a majority of the first choices, that
candidate shall be declared elected. If no candidate receives a
majority, the candidate who received the fewest first choices shall be
eliminated and each vote cast for that candidate shall be transferred to
the next ranked candidate on that voter's ballot. If, after this
transfer of votes, any candidate has a majority of the votes from the
continuing ballots, that candidate shall be declared elected.

(d) If no candidate receives a majority of votes from the continuing
ballots after a candidate has been eliminated and his or her votes have
been transferred to the next-ranked candidate, the continuing candidate
with the fewest votes from the continuing ballots shall be eliminated.
All votes cast for that candidate shall be transferred to the next-
ranked continuing candidate on each voter's ballot. This process of
eliminating candidates and transferring their votes to the next-ranked
continuing candidates shall be repeated until a candidate receives a
majority of the votes from the continuing ballots.

(e) If the total number of votes of the two or more candidates credited
with the lowest number of votes is less than the number of votes
credited to the candidate with the next highest number of votes, those
candidates with the lowest number of votes shall be eliminated
simultaneously and their votes transferred to the next-ranked continuing
candidate on each ballot in a single counting operation.

(f) A tie between two or more candidates shall be resolved in accordance
with State law.

(g) The Department of Elections shall conduct a voter education campaign
to familiarize voters with the ranked-choice or, "instant runoff,"
method of voting.

(h) Any voting system, vote tabulation system, or similar or related
equipment acquired by the City and County shall have the capability to
accommodate this system of ranked-choice, or "instant runoff,"
balloting.

(i) Ranked choice, or "instant runoff," balloting shall be used for the
general municipal election in November 2002 and all subsequent
elections. If the Director of Elections certifies to the Board of
Supervisors and the Mayor no later than July 1, 2002 that the Department
will not be ready to implement ranked-choice balloting in November 2002,
then the City shall begin using ranked-choice, or "instant runoff,"
balloting at the November 2003 general municipal election.

If ranked-choice, or "instant runoff," balloting is not used in November
of 2002, and no candidate for any elective office of the City and
County, except the Board of Education and the Governing Board of the
Community College District, receives a majority of the votes cast at an
election for such office, the two candidates receiving the most votes
shall qualify to have their names placed on the ballot for a runoff
election held on the second Tuesday in December of 2002.
 *)
