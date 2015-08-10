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
sf_imp.eliminated candidate _ rec can = true <->
in_record rec can.
Proof.
split.
intros.
unfold sf_imp.eliminated in *. rewrite existsb_exists in H.
destruct H; intuition.
rewrite existsb_exists in H1. destruct H1; intuition.
unfold in_record.
apply reldec_correct_candidate in H2. subst; eauto.
intros.
unfold sf_imp.eliminated in *. rewrite existsb_exists.
unfold in_record in H. destruct H. exists x. intuition.
rewrite existsb_exists. exists can. intuition.
apply reldec_correct_candidate. auto.
Qed.

Definition no_viable_candidates eliminated (b : sf_spec.ballot candidate) :=
Forall (Forall eliminated) b.

Lemma no_viable_candidates_Forall :
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
forall rec bal cd bal' ,
sf_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
exists l,(sf_spec.next_ranking candidate (in_record rec) bal l /\ Forall (eq cd) l).
Proof.
intros.
induction bal.
- simpl in *. congruence.
- simpl in *.
  destruct a.
  + intuition. destruct H0. exists x. intuition.
  + destruct (forallb (eq_dec c) a) eqn:Heqb0.
    * { destruct (sf_imp.eliminated candidate reldec_candidate rec c) eqn:?.
         - apply IHbal in H. clear IHbal.
           destruct H. destruct H. exists x.
           split. left. intuition.
           + intros.
             assert (c = c0).
             destruct H1. auto.
             rewrite forallb_forall in Heqb0.
             apply Heqb0 in H1.
             apply reldec_correct_candidate in H1. auto.
             subst.
             unfold sf_imp.eliminated in Heqb. rewrite existsb_exists in Heqb.
             destruct Heqb. intuition. rewrite existsb_exists in *. destruct H4.
             destruct H2. apply reldec_correct_candidate in H4. subst.
             unfold in_record. eauto.               
           + intuition.
         - inversion H. subst. clear H. 
           exists (cd :: a).
           split. right.
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
           + rewrite forallb_forall in Heqb0. rewrite Forall_forall. 
             intuition. destruct H. auto. apply Heqb0 in H. apply reldec_correct_candidate.
             auto.                                                                     
      } 
    * congruence.       
Qed.


Lemma next_ranking_in :
forall e bal x,
  sf_spec.next_ranking candidate e bal x ->
  In x bal.
Proof.
induction bal; intros.
- simpl in H. auto.
- simpl in *. intuition.
Qed.

Lemma next_ranking_cons_or :
forall b1 bal e x,
sf_spec.next_ranking candidate e (b1 :: bal) x ->
sf_spec.next_ranking candidate e [b1] x \/ 
sf_spec.next_ranking candidate e bal x.
intros. simpl in  H. intuition. destruct H. destruct H.
left. unfold sf_spec.next_ranking. right. eauto.
Qed.

Ltac inv H := inversion H; subst; clear H.

Lemma overvote_cons_or :
forall b1 bal e ,
sf_spec.overvote candidate e (b1 :: bal) ->
sf_spec.overvote candidate e [b1] \/ sf_spec.overvote candidate e bal.
Proof.
intros.
inv H.  
intuition.
destruct H1. destruct H0.
intuition.
edestruct (next_ranking_cons_or); eauto.
- unfold sf_spec.overvote.
  left. exists x. split; eauto.
- right. unfold sf_spec.overvote. exists x; split; eauto.
Qed.

Lemma next_ranking_not_overvote :
forall rec bal cd bal',
sf_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
~sf_spec.overvote candidate (in_record rec) bal.
Proof.
intros.
induction bal.
- simpl in *. congruence.
- simpl in *.
  destruct a.
  + intro.
    unfold sf_spec.overvote in H0.
    destruct H0.
    destruct H0.
    simpl in H0.
    intuition. 
    unfold sf_spec.overvote in H2. apply H2. eauto.
    subst. destruct H1. destruct H1. intuition.
  + destruct (forallb (eq_dec c) a) eqn:?.
    * { destruct (sf_imp.eliminated candidate reldec_candidate rec c) eqn:?.
        - intuition. 
          edestruct (overvote_cons_or); eauto.
          + rewrite forallb_forall in *. 
            clear -H2 Heqb reldec_correct_candidate.
            inversion H2. intuition.
            inversion H0. intuition.
            intuition. subst. intuition.
            destruct H1. destruct H.
            intuition. apply H5.
            simpl in *. intuition; subst; auto. 
            * specialize (Heqb x0). intuition.
              apply reldec_correct_candidate in H. auto.
            * specialize (Heqb x). intuition.
              apply reldec_correct_candidate in H. auto.
            * assert (x = c).
              specialize (Heqb x). intuition. apply reldec_correct_candidate in H.
              auto.
              assert (x0 = c).               
              specialize (Heqb x0). intuition. apply reldec_correct_candidate in H7.
              auto.
              subst. auto.
        - inv H. intro.
          inv H. clear IHbal.
          intuition.
          destruct H1. destruct H0. intuition. inv H.
          destruct H2. specialize (H cd). simpl in H. intuition.
          rewrite <- eliminated_correct in H. congruence.
          intuition. subst.
          apply H3.
          rewrite forallb_forall in Heqb. 
          simpl in *. intuition; subst; auto.
          + specialize (Heqb _ H1). apply reldec_correct_candidate in Heqb. 
            auto.
          + specialize (Heqb _ H2). apply reldec_correct_candidate in Heqb.
            auto.
          + assert (x0 = cd); subst. 
            specialize (Heqb _ H2). apply reldec_correct_candidate in Heqb. auto.
            assert (x1 = cd); subst.
            specialize (Heqb _ H1). apply reldec_correct_candidate in Heqb. auto.
            auto. } 
    * congruence.
Qed.
    
Lemma no_viable_candidates_cons :
forall a b e,
sf_spec.no_viable_candidates candidate (e) (a ::  b) ->
sf_spec.no_viable_candidates candidate e [a] /\
sf_spec.no_viable_candidates candidate e b.
intros.
unfold sf_spec.no_viable_candidates in *.
split.
intros. eapply H; eauto. inv H0; simpl in *; intuition.
intros. eapply H; eauto. simpl. intuition.
Qed.

Lemma next_ranking_viable :
forall bal rec cd bal',
sf_imp.next_ranking candidate reldec_candidate rec bal =
      Some (cd, bal') ->
~sf_spec.no_viable_candidates candidate (in_record rec) bal.
Proof.
induction bal; intros.
- simpl in *. congruence.
- simpl in *. destruct a.
  + intro. apply no_viable_candidates_cons in H0. destruct H0.
    eapply IHbal in H1; eauto.
  + destruct (forallb (eq_dec c) a).
    * { destruct (sf_imp.eliminated candidate reldec_candidate rec c) eqn:?.
        - apply eliminated_correct in Heqb.
          intro. apply no_viable_candidates_cons in H0.
          destruct H0.
          eapply IHbal in H1; eauto.
        - inv H. intro. apply no_viable_candidates_cons in H. destruct H.
          unfold sf_spec.no_viable_candidates in H. 
          specialize (H (cd :: a)). simpl in H. intuition. clear H2.
          specialize (H cd). intuition. clear H2. 
          rewrite <- eliminated_correct in H. congruence.
      }
    * congruence.
Qed.
  

Lemma next_ranking_selected :
forall bal cd bal' rec,
sf_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
sf_spec.selected_candidate candidate (in_record rec) bal cd.
intros.
unfold sf_spec.selected_candidate. split.
- unfold sf_spec.continuing_ballot. intro. 
  unfold sf_spec.exhausted_ballot in H0.
  destruct H0. 
  + apply next_ranking_viable in H. auto.
  + eapply next_ranking_not_overvote in H0; eauto.
- apply next_ranking_correct in H. destruct H. destruct H.
  exists x. intuition.
  destruct x. induction bal. inv H. simpl in *. intuition. subst. 
  destruct H; intuition.
  inv H0. simpl in *. auto.
Qed.

  
    

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

