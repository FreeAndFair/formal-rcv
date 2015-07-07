Require sf_imp.
Require sf_spec.
Require Import RelDec.
Require Import List.
Import ListNotations.


Section cand.

Variable candidate : Set.
Variable reldec_candidate : RelDec (@eq candidate).
Variable reldec_correct_candidate : RelDec_Correct reldec_candidate.

Definition in_record (rec : sf_imp.record candidate) (c : candidate) :=
exists e, In e rec /\ In c e.

Lemma no_viable_candidates_correct : 
forall rec bal,
sf_imp.no_viable_candidates candidate _ rec bal = true -> 
sf_spec.no_viable_candidates candidate (in_record rec) bal.
Proof.
intros.
unfold sf_imp.no_viable_candidates in *. rewrite forallb_forall in H.
unfold sf_spec.no_viable_candidates.
intros.
specialize (H _ H0). unfold sf_imp.no_viable_candidates_selection in *.
rewrite forallb_forall in H. apply H in H1.
unfold sf_imp.eliminated in H1.
rewrite existsb_exists in H1.
destruct H1.
unfold in_record. destruct H1.
rewrite existsb_exists in H2. destruct H2.
destruct H2. 
apply reldec_correct_candidate in H3. subst.
exists x. auto.
Qed.

Lemma existsb_false_forall :
forall A (b: A -> bool) l,
existsb b l = false ->
forallb (fun x => (negb (b x))) l = true.
Proof.
intros. rewrite forallb_forall. intros.
induction l.
- simpl in H. inversion H0.
- simpl in *. rewrite Bool.orb_false_iff in H.
  destruct H. 
  destruct H0.
  + subst. rewrite H. auto.
  + intuition.
Qed.

Lemma eliminated_correct :
forall rec can,
sf_imp.eliminated candidate _ rec can = true ->
in_record rec can.
Proof.
intros.
unfold sf_imp.eliminated in *. rewrite existsb_exists in H.
destruct H; intuition.
rewrite existsb_exists in H1. destruct H1; intuition.
unfold in_record.
apply reldec_correct_candidate in H2. subst; eauto.
Qed.

Definition no_viable_candidates eliminated (b : sf_spec.ballot candidate) :=
Forall (Forall eliminated) b.

Lemma no_viable_candidate_Forall :
forall eliminated b,
no_viable_candidates eliminated b <->
sf_spec.no_viable_candidates candidate eliminated b.
Proof.
intros.
unfold no_viable_candidates.
unfold sf_spec.no_viable_candidates.
intuition. rewrite Forall_forall in *.
specialize (H rank). rewrite Forall_forall in H. 
intuition.
rewrite Forall_forall. intro. rewrite Forall_forall. intuition.
specialize (H x). intuition.
Qed.

Lemma next_ranking_correct :
forall rec bal cd bal',
sf_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
sf_spec.next_ranking candidate (in_record rec) bal [cd].
Proof.
intros.
induction bal.
- simpl in *. congruence.
- simpl in *.
  destruct a.
  + intuition.
  + destruct a.
    * { destruct (sf_imp.eliminated candidate reldec_candidate rec c) eqn:?.
         - apply IHbal in H.
           left. split. 
           + intros. inversion H0. 
             * subst.
               unfold sf_imp.eliminated in Heqb. rewrite existsb_exists in Heqb.
               destruct Heqb. intuition. rewrite existsb_exists in H3. destruct H3.
               destruct H1.  apply reldec_correct_candidate in H3. subst.
               unfold in_record. exists x. auto.
             * inversion H1.
           + auto.
         - inversion H. subst. clear H.
           right.
           split.
           + unfold sf_imp.eliminated in *. 
             apply existsb_false_forall in Heqb.
             rewrite forallb_forall in Heqb.
             exists cd.
             split.
             * constructor. auto.
             * intro. unfold in_record in *.
               destruct H. destruct H. specialize (Heqb x H).
               rewrite Bool.negb_true_iff in Heqb.
               apply existsb_false_forall in Heqb.
               rewrite forallb_forall in Heqb.
               specialize (Heqb cd). intuition.
               rewrite Bool.negb_true_iff in H1.
               assert (cd = cd) by reflexivity.
               apply reldec_correct_candidate in H2.
               unfold eq_dec in *.
               congruence.
           + reflexivity.
      } 
    * congruence.
Qed.




Lemma next_ranking_selected :
forall bal cd bal' rec,
sf_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
sf_spec.selected_candidate candidate (in_record rec) bal cd.
intros.
unfold sf_spec.selected_candidate. split.
unfold sf_spec.continuing_ballot. intro.
induction bal.
- simpl in *. congruence.
- simpl in *.
  destruct a.
  + intuition. unfold sf_spec.exhausted_ballot in H0.
    destruct H0.
    * unfold sf_spec.exhausted_ballot in H1.
      apply H1.
      left.
      unfold sf_spec.no_viable_candidates in H0.
      intro. intros.
      eapply H0; eauto. simpl. right. auto.
    * apply H1. unfold sf_spec.exhausted_ballot.
      right.
      unfold sf_spec.overvote in *.
      destruct H0. exists x. intuition.
      simpl in H2. intuition. 
      destruct H2. intuition.
  + destruct a.
    destruct ( sf_imp.eliminated candidate reldec_candidate rec c) eqn:?.
    intuition.
    apply H1. apply eliminated_correct in Heqb.
    unfold sf_spec.exhausted_ballot in H0. destruct H0.
    rewrite  <- no_viable_candidate_Forall in H0.
    unfold no_viable_candidates in H0.
    inversion H0. subst.
    unfold sf_spec.exhausted_ballot.
    rewrite <- no_viable_candidate_Forall. intuition.
Admitted.    

    



   
    

Lemma tabulate_continuing :
forall rec elect res elect',
sf_imp.tabulate candidate _ rec elect = (res, elect') ->
Forall (sf_spec.continuing_ballot candidate (in_record rec)) elect'.
Proof.
intros.
rewrite Forall_forall. intros.
induction elect.
- simpl in *.
  inversion H.
  subst.
  inversion H0.
- unfold sf_imp.tabulate in H. simpl in H.
  destruct (sf_imp.next_ranking candidate reldec_candidate rec a) eqn:?.
  + destruct p. 
  
  unfold sf_imp.next_ranking in H.
Admitted. 

