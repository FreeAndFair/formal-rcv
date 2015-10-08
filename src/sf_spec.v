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
    Definition overvote (r : rankSelection) := 
       exists c1 c2, In c1 r /\ In c2 r /\ c1 <> c2.

    Inductive next_ranking : ballot -> rankSelection -> Prop :=
    | next_ranking_eliminated : forall b r r', 
        Forall eliminated r' ->
        ~overvote r' ->
        next_ranking b r ->
        next_ranking (r' :: b) r
    | next_ranking_valid : forall b r c,
        In c r  ->
        (overvote r \/ ~eliminated c) ->
        next_ranking (r :: b) r.

    Definition properly_selects r c :=
      Forall (eq c) r /\ In c r /\ ~eliminated c.

    Definition does_not_select r :=
      r = nil \/ (exists c, Forall (eq c) r /\ In c r /\ eliminated c).

    Lemma not_overvote_cons :
      forall h t,
        ~overvote (h :: t) ->
        Forall (eq h) t /\ ~overvote t.
    Proof.
      induction t; intros.
      - split. 
        + constructor.
        + intro. unfold overvote in H0.
          destruct H0. destruct H0.
          intuition.
      -split.
        + constructor.
          destruct (classic (h = a)).
          * auto.
          * exfalso.
            apply H.
            unfold overvote.
            exists h. exists a. intuition.
          * unfold overvote in H.
            apply IHt.
            intro.
            apply H.
            clear H.
            destruct H0.
            destruct H.
            exists x. exists x0.
            simpl in *. intuition.
        + intuition.
          apply H; clear H.
          unfold overvote in H0.
          destruct H0.
          destruct H.
          destruct H.
          destruct H0.
          unfold overvote.
          exists x. exists x0.
          intuition.
    Qed.

    Lemma not_overvote_all_same :
      forall r c,
        ~overvote r ->
        In c r ->
        Forall (eq c) r.
    Proof.
      induction r; intros.
      - inversion H0.
      - apply not_overvote_cons in H.
        intuition. destruct H0. subst.
        rewrite Forall_forall. intros. simpl in *.
        intuition. assert (In x r) by auto.
        eapply IHr in H0; eauto.
        rewrite Forall_forall in *.
        specialize (H0 x).
        specialize (H1 x). intuition.
        constructor; intuition.
        rewrite Forall_forall in H1. specialize (H1 c).
        intuition. 
    Qed.

    Lemma ranking_cases : forall r,
    overvote r \/ (exists c, properly_selects r c) \/ does_not_select r.
    intros.
    destruct r. 
    - right. right. left. auto.
    - destruct (classic (overvote (c :: r))).
      + auto.
      + right. destruct (classic (eliminated c)).
        * right. right. exists c. simpl. intuition.
          apply not_overvote_all_same; simpl; auto.
        * left. exists c. repeat split; auto.
          apply not_overvote_all_same; simpl; auto.
          simpl; auto.
    Qed.

    Lemma next_ranking_not_not_selects : forall b r,
        next_ranking b r ->
        ~does_not_select r.
    Proof.
      intros. 
      induction H. 
      - auto.
      - intro.
        unfold does_not_select in *.
        destruct H1. subst. elim H.
        destruct H1.
        destruct H1.
        rewrite Forall_forall in H1.
        apply H1 in H. subst. intuition.
        unfold overvote in *.
        destruct H2. destruct H0. intuition. apply H5. transitivity c; eauto. 
        symmetry. eauto.
    Qed.

    Lemma next_ranking_spec : forall b r,
        next_ranking b r -> 
        overvote r \/ (exists c, properly_selects r c).
    Proof.
      intros.
      destruct (ranking_cases r); intuition.
      apply next_ranking_not_not_selects in H.
      intuition.
    Qed. 
      
    (**  TODO: Do we need a notion of overvote for a ballot any more?
         A ballot is an overvote if its next ranking contains
         two distinct candidates.
      *)
   (* Definition overvote (b:ballot) : Prop :=
      exists r, next_ranking b r /\
         exists c1 c2, In c1 r /\ In c2 r /\ c1 <> c2.*)

    (**  A ballot is exhausted if it selects no vaiable candidates
         or is an overvote 
      *)

    Definition exhausted_ballot (b:ballot) :=
      (~ exists r, next_ranking b r ) \/ 
      (exists r, next_ranking b r /\ overvote r). 
    
    Ltac inv H := inversion H; subst; clear H.
    Lemma next_ranking_unique : forall b r1 r2,
        next_ranking b r1 ->
        next_ranking b r2 ->
        r1= r2.
    Proof. 
      intros.
      induction b.
      inversion H.
      inv H; inv H0; try rewrite Forall_forall in *; firstorder.
    Qed. 

    Lemma exhausted_ballot_next_ranking_iff : forall (b : ballot),
          exhausted_ballot b <-> forall r, next_ranking b r -> overvote r.
    Proof. 
      intros.
      split; intros.
      - unfold exhausted_ballot in H.
        intuition. exfalso.
        apply H1. exists r. auto.
        destruct H1. destruct H. eapply next_ranking_unique in H0; eauto.
        subst; auto.
      - unfold exhausted_ballot.
        destruct (classic (exists r, next_ranking b r)).
        destruct H0. right.
        exists x. auto.
        left. auto.
    Qed.
          

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


    Lemma sf_first_choices_unique : forall e c n1 n2,
        first_choices c e n1 ->
        first_choices c e n2 ->
        n1 = n2.
    Proof.
      induction e.
      * intros. inversion H. inversion H0. auto.
      * intros.
        inversion H; clear H; subst;
        inversion H0; clear H0; subst; try contradiction.
        f_equal; eauto.
        eauto.
    Qed.

    Lemma sf_first_choices_total : forall e c, exists n,
        first_choices c e n.
    Proof.
      induction e.
      * intros. exists 0. apply first_choices_nil.
      * intros.
        destruct (IHe c) as [n ?].
        destruct (classic (selected_candidate a c)).
        exists (S n). apply first_choices_selected; auto.
        exists n. apply first_choices_not_selected; auto.
    Qed.

   
    Inductive total_selected : election -> nat -> Prop :=
    | total_nil : total_selected nil 0
    | total_continuing : forall b e' n, continuing_ballot b ->
                                        total_selected e' n ->
                                        total_selected (b :: e') (S n)
    | total_exhausted : forall b e' n, exhausted_ballot b ->
                                       total_selected e' n ->
                                       total_selected (b :: e') (n).

    Lemma total_selected_total : forall e,
        exists n, total_selected e n.
    Proof. 
      induction e; intros.
      - exists 0; constructor.
      - destruct IHe.
        destruct (classic (exhausted_ballot a)).
        + exists x; constructor; auto. 
        + exists (S x). apply total_continuing; auto.
    Qed.

    Definition majority (e : election) (winner : candidate) :=
      forall total_votes winner_votes, 
        total_selected e total_votes ->
        first_choices winner e winner_votes ->
        (winner_votes * 2) > total_votes.

    (** If no candidate receives a
majority, the candidate who received the fewest first choices shall be
eliminated and each vote cast for that candidate shall be transferred to
the next ranked candidate on that voter's ballot. *)

    Definition participates (c:candidate) (e:election) :=
      exists b, In b e /\ exists r, In r b /\ In c r.

    Definition viable_candidate (e:election) (c:candidate) :=
      ~eliminated c /\ participates c e.

    Definition is_loser (e:election) (loser:candidate) :=
      viable_candidate e loser /\
      forall c' n m,
        viable_candidate e c' ->
        first_choices loser e n ->
        first_choices c' e m ->
        n <= m.

    Definition no_majority (e : election) :=
      ~(exists c, majority e c).


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
      elim Hb. red. right. firstorder.
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

However, actual practice seems to be that a ballot is decared an overvote
as soon as the first ranking with more than one selection becomse relevant;
i.e., when all properly-selected candidates above it have been eliminated.
In other words, the ballot is considered to be truncated at the position
of the first ranking with more than one selection.

The formal specification above follows suit, and counts this situation
as an overvote as soon as A is eliminated.
*)

    (**  Whenever a ballot selects a candidate, that candidate is not eliminated.
      *)
    Lemma selected_candidate_not_eliminated (b:ballot) :
      forall c, selected_candidate b c -> ~eliminated c.
    Proof.
      induction b.
      unfold selected_candidate. intros c [Hc [r [??]]]. inv H.
      unfold selected_candidate. intros c [Hc [r [??]]]. inv H.
      * apply IHb. split; eauto.
        red; intro.
        apply Hc.
        destruct H.
        elim H; eauto.
        destruct H as [r' [??]].
        right. exists r'. split; auto.
        apply next_ranking_eliminated; auto.
      * intro Helim.
        elim Hc. red.
        right. exists r. split; auto.
        eapply next_ranking_valid; eauto.
        destruct H5; auto.
        red. exists c. exists c0. intuition.
        subst c0. contradiction.
    Qed.

    (* The next ranking for a ballot is in the ballot. *)
    Lemma next_ranking_in_ballot (b:ballot) :
      forall r, next_ranking b r -> In r b.
    Proof.
      intros r H. induction H; intuition; eauto.
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
