Require Import Classical.
Require Import List.
Require Import Omega.
Require Import Arith.
Require Import Wf.

Require Import ranked_properties.
Require sf_spec.

Section sf_spec_properties.
  Variable candidate:Set.

  Let rankSelection := list candidate.
  Let ballot := list rankSelection.
  Let election := list ballot.

  Let wins_election c e :=
    sf_spec.winner candidate e (fun _ => False) c.
 
  Definition all_candidates : election -> list candidate :=
    fold_right (fun a b => b ++ fold_right (@app _) nil a) nil.

  Lemma all_candidates_participates : forall c e,
     In c (all_candidates e) <-> sf_spec.participates _ c e.
  Proof.
    intros c e. induction e; simpl; intuition.
    destruct H as [? [??]]. elim H.
    apply in_app_or in H1. destruct H1.
    apply H in H1.
    destruct H1 as [? [??]].     
    exists x. split; simpl; auto.
    exists a. split; simpl; auto.
    induction a; simpl in *.
    elim H1.
    apply in_app_or in H1.
    destruct H1.
    exists a. split; auto.
    apply IHa in H1.
    destruct H1 as [r [??]].
    eauto.
    apply in_or_app.
    destruct H1 as [b [??]].
    simpl in H1.
    destruct H1.
    subst a.
    right.
    induction b.
    destruct H2 as [r [??]].
    elim H1.
    simpl.
    apply in_or_app.
    destruct H2 as [r [??]].
    simpl in H1. destruct H1.
    subst a.
    auto.
    right. eauto.
    left. apply H0.
    red; eauto.
  Qed.

  Lemma list_remove_prop_weak : forall A (l:list A) (P:A -> Prop),
       exists l',
           length l' <= length l /\
           (forall a, In a l -> In a l' \/ P a) /\
           (forall a, In a l' -> In a l /\ ~P a).
  Proof.
    intro A. induction l; simpl; intuition.
    * exists nil; simpl; intuition.
    * destruct (IHl P) as [l' [?[??]]].
      destruct (classic (P a)).
      + exists l'. simpl; intuition.
        subst; auto.
        apply H1 in H3. intuition.
        apply H1 in H3; intuition.
      + exists (a::l'). simpl; intuition.
        destruct (H0 a0); intuition.
        subst a0. auto.
        destruct (H1 a0); auto.
        destruct (H1 a0); auto.
  Qed.

  Lemma list_remove_prop : forall A (l:list A) (P:A -> Prop) x,
        P x -> In x l ->
        exists l',
           length l' < length l /\
           (forall a, In a l -> In a l' \/ P a) /\
           (forall a, In a l' -> In a l /\ ~P a).
  Proof.
    intro A. induction l; simpl; intuition.
    * subst a.
      destruct (list_remove_prop_weak A l P) as [l' [?[??]]].
      exists l'. simpl; intuition; subst; auto.
      apply H2 in H3. intuition.
      apply H2 in H3. intuition.
    * destruct (IHl P x) as [l' [?[??]]]; auto.
      destruct (classic (P a)).
      + exists l'; intuition.
        subst; auto.
        apply H3 in H5. intuition.
        apply H3 in H5. intuition.
      + exists (a::l'); simpl; intuition.
        destruct (H2 a0); intuition; subst; auto.
        subst; auto.
        apply H3 in H6. intuition.
        apply H3 in H6. intuition.
  Qed.

  Lemma majority_satisfies_ballot_exists P e :
    majority_satisfies candidate P e ->
    exists b, P b /\ In b e.
  Proof.
    intros [n [??]].
    induction H.
    exists b; intuition.
    destruct IHcount_votes as [b' [??]].
    simpl in H0. omega.
    simpl; eauto.
  Qed.


  Lemma sf_forced_majority (e:election) (eliminated:candidate -> Prop) c :
    (forall c', sf_spec.participates _ c' e -> ~eliminated c' -> c' = c) ->
    sf_spec.majority _ eliminated e c.
  Admitted.

  Section sf_spec_existential_induction.
    Variable e : election.
    Variable P : (candidate -> Prop) -> Prop.
    Variable Q : (candidate -> Prop) -> candidate -> Prop.
    Variable Hbase : forall eliminated c,
       P eliminated ->
       sf_spec.majority _ eliminated e c ->
       Q eliminated c.
    Variable Hind : forall eliminated,
       P eliminated ->
       (exists c0, ~eliminated c0 /\ sf_spec.participates _ c0 e) ->
       sf_spec.no_majority _ eliminated e ->
       exists loser,
         sf_spec.is_loser _ eliminated e loser /\
         let eliminated' := sf_spec.update_eliminated _ eliminated loser in
         P eliminated' /\
         (forall c, Q eliminated' c -> Q eliminated c).
    
    Lemma sf_spec_existential_induction_aux : forall
      (n:nat)
      (viable:list candidate)
      (eliminated:candidate -> Prop),
      (forall c, In c viable -> sf_spec.participates _ c e) ->
      (forall c, eliminated c <-> sf_spec.participates _ c e /\ ~In c viable) ->
      1 <= length viable <= n ->
      P eliminated ->
      exists c, Q eliminated c.
    Proof.
      induction n; [ simpl; intros; omega | ].
      intros.
      destruct (classic (exists c, sf_spec.majority _ eliminated e c)).
      * destruct H3 as [c ?].
        exists c. apply Hbase; auto.
      * destruct (Hind eliminated) as [loser [?[??]]]; auto.
        + destruct viable. destruct H1. elimtype False.  simpl in H1. omega.
          exists c.
          split. intro.
          apply H0 in H4.
          destruct H4. apply H5; simpl; auto.
          apply H. simpl; auto.
        + red; intros.
          apply Forall_forall. intros.
          intro. elim H3. eauto.
        + destruct (list_remove_prop candidate viable (eq loser) loser) 
            as [viable' [?[??]]]; auto.
          destruct (classic (In loser viable)); auto.
          destruct H4 as [?[??]].
          elim H4. apply H0. split; auto.
          set ( eliminated' := sf_spec.update_eliminated _ eliminated loser).
          destruct (IHn viable' eliminated') as [c ?]; auto.
          intros.
          apply H. apply H9. auto.
          unfold eliminated'.
          unfold sf_spec.update_eliminated.
          intuition.
          apply H0 in H12; intuition.
          apply H0 in H12; intuition.
          apply H14. apply H9. auto.
          subst c.
          destruct H4 as [?[??]]; auto.
          subst c; auto.
          apply H9 in H1.
          intuition.
          destruct (classic (c = loser)).
          subst c. auto.
          left.
          apply H0.
          split; auto.
          intros. apply H13.
          apply H8 in H14.
          intuition.
          subst. intuition.
          split; auto.
          destruct viable'; simpl; auto.
          elim H3.
          exists loser.
          apply sf_forced_majority.
          intros.
          destruct (H8 c'); auto.
          destruct (classic (In c' viable)); auto.
          elim H11.
          apply H0. split; auto.
          elim H12.
          omega.
          omega.
          exists c.
          apply H6. auto.
    Qed.      

    Lemma sf_spec_existential_induction : forall (eliminated:candidate -> Prop),
      (forall c0, eliminated c0 -> sf_spec.participates _ c0 e) ->
      (exists c0, sf_spec.participates _ c0 e /\ ~eliminated c0) ->
      P eliminated -> exists c, Q eliminated c.
    Proof.
      intros.
      destruct (list_remove_prop_weak _ (all_candidates e) eliminated)
               as [viable [?[??]]].
      apply (sf_spec_existential_induction_aux (length viable) viable); auto.
      intros.
      apply H4 in H5. apply all_candidates_participates. intuition.
      intros.
      split; intros.
      split.
      apply H; auto.
      intro.
      apply H4 in H6.
      intuition.
      destruct H5.
      apply all_candidates_participates in H5.
      apply H3 in H5. destruct H5; auto.
      contradiction.
      split; auto.
      destruct H0 as [c0 [??]].
      destruct (H3 c0).
      apply all_candidates_participates; auto.
      destruct viable. elim H6.
      simpl; auto. omega.
      contradiction.
    Qed.

  End sf_spec_existential_induction.

  Section sf_loser_exists.
    Variable (e:election).
    Variable (eliminated:candidate -> Prop).

    Lemma sf_first_choices_total : forall c, exists n,
        sf_spec.first_choices _ eliminated c e n.
    Admitted.

    Lemma sf_first_choices_unique : forall c n1 n2,
        sf_spec.first_choices _ eliminated c e n1 ->
        sf_spec.first_choices _ eliminated c e n2 ->
        n1 = n2.
    Admitted.

    Lemma sf_loser_exists_aux :
      forall (n:nat) c,
        ~eliminated c ->
        sf_spec.participates _ c e ->
        sf_spec.first_choices _ eliminated c e n ->
        exists c', sf_spec.is_loser _ eliminated e c'.
    Proof.
      induction n using (well_founded_induction lt_wf).
      intros.
      destruct (classic (exists c', ~eliminated c' /\
                           sf_spec.participates _ c' e /\
                           exists n', n' < n /\
                               sf_spec.first_choices _ eliminated c' e n')).
      * destruct H3 as [c' [?[?[n' [??]]]]].
        apply (H n') with c'; auto.
      * exists c. split; auto. split; auto.
        intros.
        destruct (classic (n0 <= m)); auto.
        elim H3. exists c'. split; auto. split; auto.
        assert( n = n0 ).
        eapply sf_first_choices_unique; eauto.
        subst n0.
        exists m. split; auto. omega.
    Qed.

    Lemma sf_loser_exists : 
      (exists c, ~eliminated c /\ sf_spec.participates _ c e) ->
      exists c, sf_spec.is_loser _ eliminated e c.
    Proof.
      intros.
      destruct H as [c [??]].
      destruct (sf_first_choices_total c) as [n ?].
      apply sf_loser_exists_aux with n c; auto.
    Qed.
  End sf_loser_exists.

  Theorem sf_spec_total e (eliminated:candidate -> Prop) : 
    (forall c0, eliminated c0 -> sf_spec.participates _ c0 e) ->
    (exists c, sf_spec.participates candidate c e /\ ~eliminated c) ->
    exists c, sf_spec.winner _ e eliminated c.
  Proof.
    intros.
    apply sf_spec_existential_induction with e (fun _ => True); intuition.
    apply sf_spec.winner_now; auto.
    destruct (sf_loser_exists e eliminated0) as [loser ?]; auto.
    exists loser; intuition.
    apply sf_spec.winner_elimination with loser; auto.
  Qed.    

  Theorem sf_mutual_majority :
    mutual_majority_criterion candidate wins_election.
  Proof.
    red; intros. red.
    cut (forall (eliminated:candidate -> Prop) c,
           (forall c', eliminated c' -> In c' group -> False) ->
           sf_spec.winner _ e eliminated c ->
           In c group).
    { intuition.
      destruct (sf_spec_total e (fun _ => False)).
      intuition.
      destruct (majority_satisfies_ballot_exists _ _ H0) as [b [??]].
      red in H2.
      destruct H as [[cin ?] [cout ?]].
      generalize (H2 cin cout H H4); intros.
      assert (exists c r, In r b /\ In c r).
      { clear -H5.
        induction H5.
        destruct H.
        exists cin, r; intuition.
        simpl; firstorder.
        firstorder.
      }
      firstorder.
      exists x. split; auto.
      apply (H1 (fun _ => False)); auto.
      apply (H1 (fun _ => False)); auto.
    }

    intros.
    induction H2.
    red in H0.
    red in H2.
    destruct H0 as [n [??]].
 admit. (* a winning candidate is always selected from the group *)
    apply IHwinner; auto.
    intros.
    unfold eliminated' in H5.
    red in H5.
    destruct H5.
    eapply H1; eauto.
    subst c'.
 admit. (* an eliminated candidate is never selected from the group *)
  Qed.
  