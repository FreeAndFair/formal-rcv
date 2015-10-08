Require Import Classical.
Require Import List.

Section ranked_preference_voting_properties.
  Variable candidate:Type.

  (** The following is a techincal property we need to make some proofs work out.
      This says that the set of potential candidates is nonempty, and contains at least
      two distinct candidates.  Note, this propery holds for almost all elections,
      even when only one candidate is one the ballot because of the potential
      for write-in candidates.
   *)
  Variable candidate_set_nontrivial : exists c1 c2:candidate, c1 <> c2.

  Let rankSelection := list candidate.
  Let ballot := list rankSelection.
  Let election := list ballot.

  Definition rank_selects (c:candidate) (r:rankSelection) : Prop :=
    In c r /\ forall c', In c' r -> c = c'.

  Inductive first_choice (c:candidate) : ballot -> Prop :=
  | first_top : forall b r,
                rank_selects c r ->
                first_choice c (r::b)

  | first_skip : forall b,
                first_choice c b ->
                first_choice c (nil::b).

  Inductive prefers (c1 c2:candidate) : ballot -> Prop :=
  | prefers_first : forall b r,
                rank_selects c1 r ->
                prefers c1 c2 (r::b)

  | prefers_skip : forall b,
                prefers c1 c2 b ->
                prefers c1 c2 (nil::b)

  | prefers_after : forall b c' r,
                c' <> c1 ->
                c' <> c2 ->
                rank_selects c' r ->
                prefers c1 c2 b ->
                prefers c1 c2 (r::b).

  Lemma alternatives_exist :
    forall c:candidate, exists c', c <> c'.
  Proof.
    intro c.
    destruct candidate_set_nontrivial as [c1 [c2 ?]].
    destruct (classic (c = c1)).
    subst c. exists c2. auto.
    exists c1. auto.
  Qed.

  Lemma rank_selects_unique c1 c2 r:
    rank_selects c1 r ->
    rank_selects c2 r ->
    c1 = c2.
  Proof.
    unfold rank_selects; intuition.
  Qed.

  (** A ballot which has candiate A as a first choice is precicely
      a ballot that prefers that candidate to every other candidate.
   *)
  Lemma first_choice_prefers c b :
    first_choice c b <-> (forall c2, c <> c2 -> prefers c c2 b).
  Proof.
    split.
    * intro H. induction H; intros.
      apply prefers_first; trivial.
      apply prefers_skip; auto.

    * intro Hpref.
      destruct (alternatives_exist c) as [c' Hc'].
      generalize (Hpref c' Hc'); intros.
      induction H.
      apply first_top. auto.
      apply first_skip; auto.
      apply IHprefers.
      intros.
      generalize (Hpref c2 H0). intros.
      inversion H1; auto.
      destruct H3. elim H3.
      assert (c <> c'0); auto.
      generalize (Hpref c'0 H3); intros. inversion H4; subst.
      apply first_top; auto.
      apply first_skip.
      apply IHprefers.
      intros.
      generalize (Hpref c2 H5); intros. inversion H7; subst; auto.
      destruct H9. destruct H8.
      cut( c'1 = c'0 ); [ intros; contradiction | ].
      eapply rank_selects_unique; eauto.
  Qed.

  Inductive count_votes (P:ballot -> Prop) : election -> nat -> Prop :=
  | count_satisfies : forall b e n,
        P b ->
        count_votes P e n ->
        count_votes P (b::e) (S n)
  | count_not_satisfies : forall b e n,
        ~P b ->
        count_votes P e n ->
        count_votes P (b::e) n
  | count_nil :
      count_votes P nil 0.

  Definition total_votes e n :=
    count_votes (fun b => exists c, first_choice c b) e n.

  Definition majority_satisfies (P:ballot -> Prop) (e:election) :=
    exists n t, count_votes P e n /\
                total_votes e t /\
                2*n > t.

  Definition prefers_group (group:list candidate) (b:ballot) : Prop :=
    forall cin cout,
      In cin group ->
      ~In cout group ->
      prefers cin cout b.

  Definition nontrivial_grouping (group:list candidate) :=
    (exists c, In c group) /\
    (exists c, ~In c group).

  Definition wins_pairwise_contest (cwins closes:candidate) (e:election) :=
    exists m n,
       count_votes (prefers cwins closes) e m /\
       count_votes (prefers closes cwins) e n /\
       m > n.

  Definition condorcet_winner (c:candidate) (e:election) :=
    forall c', c <> c' -> wins_pairwise_contest c c' e.

  Definition condorcet_loser (c:candidate) (e:election) :=
    forall c', c <> c' -> ~wins_pairwise_contest c c' e.


  Section criteria_definitions.
    Variable may_win_election : candidate -> election -> Prop.

    Definition shall_win_election (c:candidate) (e:election) :=
      may_win_election c e /\
      forall c', may_win_election c' e -> c = c'.

    Definition group_shall_win_election (group:list candidate) e :=
      (exists c, In c group /\ may_win_election c e) /\
      (forall c, may_win_election c e -> In c group).

    Definition majority_criterion : Prop :=
      forall (c:candidate) (e:election),
        majority_satisfies (first_choice c) e ->
        shall_win_election c e.

    Definition mutual_majority_criterion : Prop :=
      forall (group:list candidate) (e:election),
        nontrivial_grouping group ->
        majority_satisfies (prefers_group group) e ->
        group_shall_win_election group e.

    Definition later_no_harm_criterion :=
      forall (e:election) (b b':ballot) (c:candidate),
        let e1 := ( b :: e ) in
        let e2 := ( (b ++ b') :: e ) in
        (exists r, In r b /\ rank_selects c r) ->
        may_win_election c e1 ->
        may_win_election c e2.

    Definition condorcet_winner_criterion :=
      forall c e, condorcet_winner c e -> shall_win_election c e.

    Definition condorcet_loser_criterion :=
      forall c e, condorcet_loser c e -> ~may_win_election c e.

    Definition monotonicity_raise_criterion :=
      forall b1 b2 b3 c r e,
        rank_selects c r ->
        may_win_election c ( (b1 ++ b2 ++ (r::nil) ++ b3) :: e) ->
        may_win_election c ( (b1 ++ (r::nil) ++ b2 ++ b3) :: e).

    Definition participation_criterion :=
      forall b e c1 c2,
        prefers c1 c2 b ->
        may_win_election c1 e ->
        may_win_election c1 (b :: e).

  End criteria_definitions.


  Lemma count_eq (P Q:ballot -> Prop) (e:election) :
    (forall b, P b <-> Q b) ->
    forall n, count_votes P e n -> count_votes Q e n.
  Proof.
    intros HPQ n H. induction H.
    * apply count_satisfies; auto. apply HPQ; auto.
    * apply count_not_satisfies; auto.
      intro; apply H. apply HPQ; auto.
    * apply count_nil.
  Qed.

 Lemma count_monotone (P Q:ballot -> Prop) (e:election) :
    (forall b, P b -> Q b) ->
    forall m, count_votes P e m ->
      exists n, m <= n /\ count_votes Q e n.
  Proof.
    intros HPQ m Hcount. induction Hcount.
    * destruct IHHcount as [n' [??]].
      exists (S n'). split; auto with arith.
      apply count_satisfies; auto.
    * destruct IHHcount as [n' [??]].
      destruct (classic (Q b)).
      exists (S n'). split; auto with arith.
      apply count_satisfies; auto.
      exists n'; split; auto.
      apply count_not_satisfies; auto.
    * exists 0. split; auto. apply count_nil.
  Qed.

  Theorem mutual_majority_implies_majority rule :
    mutual_majority_criterion rule ->
    majority_criterion rule.
  Proof.
    intros Hmmj c e Hsat.
    set (group := c::nil).
    destruct (Hmmj group e).
    * split; [ exists c; red; simpl; auto | ].
      destruct (alternatives_exist c) as [c' Hc'].
      exists c'; red; simpl; intuition.
    * destruct Hsat as [n [t [Hcount [Hmaj Hnt]]]].
      exists n, t; split; auto.
      revert Hcount; apply count_eq.
      intro b; split; intro.
      + red; intros. apply first_choice_prefers.
        simpl in H0; intuition; subst cin; auto.
        intro. apply H1. subst cin; auto.
      + apply first_choice_prefers.
        intros. apply H.
        red; simpl; auto.
        red; simpl; intuition.
    * split.
      + destruct H.
        simpl in H; intuition; subst x; auto.
      + intros. apply H0 in H1.
        destruct H1; auto.
        elim H1.
  Qed.

  (** Admitted for now.  This fact is widely clamed,
      but I'm not sure offhand how to prove it.
  *)
  Theorem condorcet_winner_later_no_harm_incompatible rule :
    condorcet_winner_criterion rule ->
    later_no_harm_criterion rule ->
    False.
  Proof.
    intros Hcondorcet Hlater.
  Admitted.

End ranked_preference_voting_properties.
