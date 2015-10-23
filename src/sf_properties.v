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

  Lemma next_ranking_elim_unchanged :
    forall (elim elim':candidate -> Prop) b c r,
      (forall x, elim x -> elim' x) ->
      ~elim' c ->
      sf_spec.next_ranking candidate elim b r ->
      In c r ->
      sf_spec.next_ranking candidate elim' b r.
  Proof.
    intros.
    induction H1.
    * apply sf_spec.next_ranking_eliminated; auto.
      rewrite Forall_forall in *; firstorder.
    * apply sf_spec.next_ranking_valid with c; auto.
  Qed.

  Lemma selected_candidate_elim_unchanged :
    forall (elim elim':candidate -> Prop) b c,
      sf_spec.selected_candidate candidate elim b c ->
      (forall x, elim x -> elim' x) ->
      ~elim' c ->
      sf_spec.selected_candidate candidate elim' b c.
  Proof.
    intros.
    destruct H.
    destruct H2 as [r [Hr Hc]].
    split.
    * intro. apply H.
      destruct H2.
      elim H2.
      exists r. eapply next_ranking_elim_unchanged; eauto.
      destruct H2 as [r' [??]].
      assert (r = r').
      { cut (sf_spec.next_ranking candidate elim' b r'); [ apply sf_spec.next_ranking_unique; auto | auto ].
        eapply next_ranking_elim_unchanged; eauto.
      }
      subst r'.
      right; exists r; split; auto.
    * exists r; split; auto.
      eapply next_ranking_elim_unchanged; eauto.      
  Qed.

  (** As we eliminate candidates, the first-choice counts of the remaining
      candidates increases monotonically.
    *)
  Lemma first_choices_monotone :
    forall elim elim' e c m n,
      ~elim' c ->
      sf_spec.first_choices candidate elim c e m ->
      sf_spec.first_choices candidate elim' c e n ->
      (forall x, elim x -> elim' x) ->
      m <= n.
  Proof.
    intros.
    revert n H1.
    induction H0; intros.
    * auto with arith.
    * inversion H3; subst; clear H3.
      - cut (n' <= n'0). auto with arith.
        apply IHfirst_choices; auto.
      - elim H6.
        eapply selected_candidate_elim_unchanged; eauto.
    * inversion H3; subst; clear H3.
      transitivity n'; auto with arith.
      apply IHfirst_choices; eauto.
  Qed.


  Let sf_may_win_election c e :=
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
    intros [n [t [?[??]]]].
    revert t H0 H1.
    induction H; intros.
    exists b; intuition.
    red in H1.
    inversion H1; subst; clear H1.
    destruct (IHcount_votes n0) as [b' [??]]; auto.
    omega.
    exists b'. split; simpl; auto.
    destruct (IHcount_votes t) as [b' [??]]; auto.
    exists b'. split; simpl; auto.
    omega.
  Qed.

  Lemma continuing_ballot_selects (b:ballot) (eliminated:candidate -> Prop) :
    sf_spec.continuing_ballot _ eliminated b <->
    exists c, sf_spec.selected_candidate _ eliminated b c.
  Proof.
    split; intros.
    destruct (classic (exists c, sf_spec.selected_candidate _ eliminated b c )); auto.
    elim H. clear H.
    rewrite sf_spec.exhausted_ballot_next_ranking_iff.
    intros.
    destruct (sf_spec.next_ranking_spec candidate eliminated b r); auto.
    destruct H1 as [c[?[??]]].
    elim H0. exists c.
    split; eauto.
    intro. destruct H4.
    elim H4. eauto.
    destruct H4 as [r' [??]].
    assert (r = r'). { eapply sf_spec.next_ranking_unique; eauto. }
    subst r'.
    destruct H5 as [r1 [r2 [?[??]]]].
    rewrite Forall_forall in H1.
    apply H7. transitivity c; firstorder.

    destruct H as [c ?].
    intros [?|?].
    destruct H as [? [r [??]]].
    elim H0; eauto.
    destruct H0 as [r [??]].
    destruct H.
    apply H.
    right. exists r. split; auto.
  Qed.

  Lemma sf_forced_majority (e:election) (eliminated:candidate -> Prop) :
    forall c n,
    n > 0 ->
    sf_spec.first_choices _ eliminated c e n ->
    (forall c', sf_spec.participates _ c' e -> ~eliminated c' -> c' = c) ->
    sf_spec.majority _ eliminated e c.
  Proof.
    induction e; simpl; intros.
    red; simpl; intros.
    inversion H3; subst; clear H3.
    inversion H2; subst; clear H2.
    inversion H0. subst n. omega.
    red; intros.
    assert ( winner_votes = n ) by
        (eapply sf_spec.sf_first_choices_unique; eauto).
    subst n. clear H0.
    inversion H2; clear H2; subst.
    inversion H3; clear H3; subst.
    * 
    destruct n'.
    simpl.
    assert( n = 0 ).
    { cut (forall c', sf_spec.participates _ c' e -> ~eliminated c' -> c' = c).
      clear -H7 H8.
      revert n H7; induction e; intros.
      + inversion H7; subst; auto.
      + inversion H8; subst; clear H8; subst; auto.
        inversion H7; subst; clear H7; subst; auto.
        apply continuing_ballot_selects in H3.
        destruct H3 as [c' ?].
        elim H2.
        replace c with c'; auto.
        apply H; auto.
        exists a. split; simpl; auto.
        destruct H0 as [?[?[??]]].
        exists x; split; auto.
        eapply sf_spec.next_ranking_in_ballot; eauto.
        eapply sf_spec.selected_candidate_not_eliminated; eauto.
        apply IHe; eauto.
        intros. apply H; auto.
        destruct H0 as [b [??]].
        exists b; intuition.
      + intros. apply H1; auto.
        destruct H0 as [b [??]].
        exists b; intuition.
    }
    subst n. omega.
    cut (S n' * 2 > n). omega.
    eapply (IHe c (S n')); auto.
    omega.
    intros. apply H1; auto.
    destruct H0 as [b [??]].
    exists b; intuition.
  * apply continuing_ballot_selects in H5.
    destruct H5 as [c' ?].
    elim H4.
    replace c with c'; auto.
    apply H1; auto.
    destruct H0.
    destruct H2 as [r [??]].
    exists a. split; simpl; auto.
    exists r; split; simpl; auto.
    eapply sf_spec.next_ranking_in_ballot; eauto.
    assert (sf_spec.continuing_ballot _ eliminated a).
    apply continuing_ballot_selects.
    eauto.
    eapply sf_spec.selected_candidate_not_eliminated; eauto.
  * inversion H3; clear H3; subst.
    destruct H4. elim H0. auto.
    apply (IHe c winner_votes); auto.
    intros. apply H1; auto.
    destruct H0 as [b [??]].
    exists b; intuition.
  Qed.

    Lemma nonzero_first_choices_selected :
      forall (eliminated:candidate -> Prop) c e n,
        sf_spec.first_choices _ eliminated c e n ->
        n > 0 ->
        exists b, In b e /\ sf_spec.selected_candidate _ eliminated b c.
    Proof.
      intros. induction H.
      * omega.
      * simpl; eauto.
      * destruct IHfirst_choices as [b [??]]; simpl; eauto.
    Qed.


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
       (exists c0 n, n > 0 /\ sf_spec.first_choices _ eliminated c0 e n) ->
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
      (exists c, In c viable /\ exists n, n > 0 /\ sf_spec.first_choices _ eliminated c e n) ->
      (forall c, eliminated c <-> sf_spec.participates _ c e /\ ~In c viable) ->
      1 <= length viable <= n ->
      P eliminated ->
      exists c, Q eliminated c.
    Proof.
      induction n; [ simpl; intros; omega | ].
      intros viable eliminated Hviable ????.
      destruct (classic (exists c, sf_spec.majority _ eliminated e c)).
      * destruct H3 as [c ?].
        exists c. apply Hbase; auto.
      * destruct (Hind eliminated) as [loser [?[??]]]; auto.
        + destruct H as [c [??]]; eauto.
        + destruct (list_remove_prop candidate viable (eq loser) loser)
            as [viable' [?[??]]]; auto.
          destruct (classic (In loser viable)); auto.
          destruct H4 as [[??]?].
          elim H4. apply H0. split; auto.
          set ( eliminated' := sf_spec.update_eliminated _ eliminated loser).
          assert (Hviable' : exists c', In c' viable').
          { destruct viable'; simpl; auto.
            destruct H as [c [? [nc [??]]]].
            exists c.
            apply H8 in H. destruct H. elim H. subst c.
            elim H3. exists loser.
            apply sf_forced_majority with nc; auto.
            intros.
            destruct (H8 c'); auto.
            destruct (classic (In c' viable)); auto.
            elim H12.
            apply H0. split; auto.
            elim H13.
            eauto.
          }
          destruct (IHn viable' eliminated') as [c ?]; auto.
          - intros. apply H9 in H10. intuition.
          - destruct H as [c [? [cn [??]]]].
            destruct (classic (c = loser)).
            subst c.
            destruct Hviable' as [c' ?].
            exists c'. split; auto.
            destruct (sf_spec.sf_first_choices_total candidate eliminated' e c') as [n' ?].
            destruct (sf_spec.sf_first_choices_total candidate eliminated e c') as [n'' ?].
            exists n'; split; auto.
            cut (n'' <= n'). intro Hn''.
            cut (cn <= n'').  omega.
            { destruct H4.
              apply (H15 c'); auto.
              split.
              intro. apply H0 in H16. intuition.
              apply H19.
              apply H9 in H12; intuition.
              apply Hviable.
              apply H9 in H12. intuition.
            }
            { apply first_choices_monotone with eliminated eliminated' e c'; auto.
              intro. hnf in H15. apply H9 in H12.
              destruct H15.
              apply H0 in H15.
              intuition.
              intuition.
              intros. hnf. auto.
            } 
            
            exists c; intuition.
            apply H8 in H. intuition.
            elim H12; auto.
            destruct (sf_spec.sf_first_choices_total candidate eliminated' e c) as [cn' ?].
            exists cn'; split; auto.
            cut (cn <= cn'). omega.
            apply first_choices_monotone with eliminated eliminated' e c; auto.
            intro. hnf in H15.
            destruct H15.
            apply H0 in H15.
            intuition.
            elim H12; auto.
            intros. hnf. auto.

          - unfold eliminated'.
            unfold sf_spec.update_eliminated.
            intuition.
            apply H0 in H12; intuition.
            apply H0 in H12; intuition.
            apply H14. apply H9. auto.
            subst c.
            destruct H4 as [[??]?]; auto.
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
          - split; auto.
            destruct viable'; simpl; auto.
            destruct Hviable' as [?[]].
            omega.
            omega.
          - exists c.
            apply H6. auto.
    Qed.

    Lemma sf_spec_existential_induction : forall (eliminated:candidate -> Prop),
      (forall c0, eliminated c0 -> sf_spec.participates _ c0 e) ->
      (exists c0 n, n > 0 /\ sf_spec.first_choices _ eliminated c0 e n) ->
      P eliminated -> exists c, Q eliminated c.
    Proof.
      intros.
      destruct (list_remove_prop_weak _ (all_candidates e) eliminated)
               as [viable [?[??]]].
      apply (sf_spec_existential_induction_aux (length viable) viable); auto.
      * intros. apply H4 in H5. destruct H5.
        apply (all_candidates_participates c e); auto.
      * destruct H0 as [c [n[??]]].
        exists c; split; eauto.
        destruct (nonzero_first_choices_selected eliminated c e n) as [b [??]]; auto.
        generalize (sf_spec.selected_candidate_not_eliminated _ _ b c H7); intro.
        assert ( sf_spec.participates candidate c e ).
        destruct H7.
        red; exists b. split; auto.
        destruct H9 as [r [??]].
        exists r; split; auto.
        eapply sf_spec.next_ranking_in_ballot; eauto.
        generalize (all_candidates_participates c e); intros [??].
        apply H11 in H9.
        apply H3 in H9.
        intuition.
      * intuition.
        apply H4 in H6. intuition.
        generalize (all_candidates_participates c e); intros [??].
        apply H8 in H6.
        apply H3 in H6.
        intuition.
      * intuition.
        destruct H0 as [c [n [??]]].
        destruct (nonzero_first_choices_selected eliminated c e n) as [b [??]]; auto.
        generalize (sf_spec.selected_candidate_not_eliminated _ _ b c H7); intro.
        assert ( sf_spec.participates candidate c e ).
        destruct H7.
        red; exists b. split; auto.
        destruct H9 as [r [??]].
        exists r; split; auto.
        eapply sf_spec.next_ranking_in_ballot; eauto.
        generalize (all_candidates_participates c e); intros [??].
        apply H11 in H9.
        apply H3 in H9.
        destruct H9.
        - destruct viable. elim H9.
          simpl. omega.
        - contradiction.
    Qed.

  End sf_spec_existential_induction.

  Section sf_loser_exists.
    Variable (e:election).
    Variable (eliminated:candidate -> Prop).

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
        destruct H4.
        elim H3. exists c'. split; auto. split; auto.
        assert( n = n0 ).
        eapply sf_spec.sf_first_choices_unique; eauto.
        subst n0.
        exists m. split; auto. omega.
    Qed.

    Lemma sf_loser_exists :
      (exists c, ~eliminated c /\ sf_spec.participates _ c e) ->
      exists c, sf_spec.is_loser _ eliminated e c.
    Proof.
      intros.
      destruct H as [c [??]].
      destruct (sf_spec.sf_first_choices_total _ eliminated e c) as [n ?].
      apply sf_loser_exists_aux with n c; auto.
    Qed.
  End sf_loser_exists.


  Theorem sf_spec_total e (eliminated:candidate -> Prop) :
    (forall c0, eliminated c0 -> sf_spec.participates _ c0 e) ->
    (exists c n, n > 0 /\ sf_spec.first_choices _ eliminated c e n) ->
    exists c, sf_spec.winner _ e eliminated c.
  Proof.
    intros.
    apply sf_spec_existential_induction with e (fun _ => True); intuition.
    * apply sf_spec.winner_now; auto.
    * destruct (sf_loser_exists e eliminated0) as [loser ?]; auto.
      + destruct H2 as [c [n [??]]].
        destruct (nonzero_first_choices_selected eliminated0 c e n) as [b [??]]; auto.
        exists c.
        generalize (sf_spec.selected_candidate_not_eliminated _ _ b c H6); intro.
        split; auto.
        destruct H6.
        red; exists b. split; auto.
        destruct H8 as [r [??]].
        exists r; split; auto.
        eapply sf_spec.next_ranking_in_ballot; eauto.
      + exists loser; intuition.
        apply sf_spec.winner_elimination with loser; auto.
  Qed.

  Definition mutual_majority_invariant (e:election) (group:list candidate) (eliminated:candidate -> Prop) :=
    exists c, In c group /\ ~eliminated c.

  Lemma majority_satisfies_monotone (P Q:ballot -> Prop) : 
    forall e,
      (forall b, P b -> Q b) ->
      majority_satisfies _ P e ->
      majority_satisfies _ Q e.
  Proof.
    intros e HPQ [nmaj [ntotal [?[??]]]].
    destruct (count_monotone _ P Q e HPQ nmaj H) as [nmaj' [??]].
    exists nmaj'. exists ntotal. intuition.
  Qed.

  Lemma selected_candidate_tail (eliminated : candidate -> Prop) :
    forall a h c,
      sf_spec.does_not_select _ eliminated a ->
      sf_spec.selected_candidate _ eliminated h c ->
      sf_spec.selected_candidate _ eliminated (a :: h) c.
  Proof.
    intros. destruct H0. split.
    intro. apply H0.
    destruct H2.
    left.
    intros [q ?].
    apply H2. exists q.
    apply sf_spec.next_ranking_eliminated; auto.
    rewrite Forall_forall.
    intros.
    destruct H. subst a. elim H4.
    destruct H as [c' [?[??]]].
    rewrite Forall_forall in H.
    replace x with c'; auto.
    intros [?[?[?[??]]]].
    destruct H. subst a. elim H4.
    apply H6.
    destruct H as [c' [?[??]]].
    rewrite Forall_forall in H.
    transitivity c'; auto. symmetry; auto.
    right.
    destruct H2 as [q [??]].
    exists q; split; auto.
    inversion H2; clear H2; subst; auto.
    elimtype False.
    destruct H.
    subst q. elim H6.
    destruct H as [c' [?[??]]].
    rewrite Forall_forall in H.
    destruct H8.
    destruct H5 as [?[?[?[??]]]].
    apply H8.
    transitivity c'; auto. symmetry; auto.
    apply H5.
    replace c0 with c'; auto.

    destruct H1 as [r [??]].
    exists r; split; auto.
    apply sf_spec.next_ranking_eliminated; auto.
    rewrite Forall_forall. intros.
    destruct H. subst a. elim H3.
    destruct H as [c' [?[??]]].
    rewrite Forall_forall in H.
    replace x with c'; auto.
    intros [?[?[?[??]]]].
    apply H5.
    destruct H. subst. elim H3.
    destruct H as [c' [?[??]]].
    rewrite Forall_forall in H.
    transitivity c'; auto. symmetry; auto.
  Qed.

  Lemma sf_total_le_total (eliminated : candidate -> Prop) :
    forall e n n',
      sf_spec.total_selected _ eliminated e n ->
      total_votes _ e n' ->
      n <= n'.
  Proof.
    induction e; intros.
    inversion H. inversion H0. auto.
    inversion H; subst; clear H;
    inversion H0; subst; clear H0; auto.
    cut (n0 <= n). omega.
    apply IHe; auto.
    elim H2.
    rewrite (continuing_ballot_selects a eliminated) in H3.
    destruct H3 as [c ?].
    clear -H.
    destruct H. destruct H0 as [r [??]].
    induction H0.
    rewrite Forall_forall in H0.
    destruct r'.
    destruct IHnext_ranking as [c' ?]; auto.
    { intro. elim H.
      destruct H4.
      left. intros [q ?].
      apply H4. exists q.
      inversion H5; clear H5; subst; auto.
      elim H8.
      destruct H4 as [q [??]].
      right. exists q; split; auto.
      apply sf_spec.next_ranking_eliminated; auto.
    }
    exists c'.
    apply first_skip. auto.
    exists c0. apply first_top.
    split; simpl; auto.
    intros.
    destruct (classic (c0 = c')); auto.
    elim H2.
    exists c0, c'. simpl; intuition.
    exists c.
    apply first_top.
    split; auto.
    intros.
    destruct (classic (c = c')); auto.
    elim H.
    right.
    exists r.
    split.
    apply sf_spec.next_ranking_valid with c0; auto.
    exists c. exists c'; intuition.
  Qed.

  Theorem sf_mutual_majority :
    mutual_majority_criterion candidate sf_may_win_election.
  Proof.
    red; intros. red.
    cut (forall (eliminated:candidate -> Prop) c,
           mutual_majority_invariant e group eliminated ->
           sf_spec.winner _ e eliminated c ->
           In c group).
    { intuition.
      destruct (sf_spec_total e (fun _ => False)).
      intuition.
      destruct (majority_satisfies_ballot_exists _ _ H0) as [b [??]].
      red in H2.
      destruct H as [[cin ?] [cout ?]].
      generalize (H2 cin cout H H4); intros.
      clear -H2 H3 H5.
      { induction e; intros.
      * elim H3.
      * simpl in H3. destruct H3.
        + clear IHe. subst b.
          clear H2.
          induction H5.
          - destruct (sf_spec.sf_first_choices_total _ (fun _ => False) ((r::b) :: e) cin) as [n ?].
            exists cin. exists n. split; auto.
            inversion H0; subst; clear H0.
            omega.
            elim H3; clear H3. split.
            intro. destruct H0.
            apply H0.
            exists r.
            apply sf_spec.next_ranking_valid with cin; auto.
            destruct H. auto.
            destruct H0 as [r' [??]].
            assert (r = r').
            eapply sf_spec.next_ranking_unique; eauto.
            apply sf_spec.next_ranking_valid with cin.
            destruct H; auto.
            right; auto.
            subst r'.
            destruct H.
            destruct H1 as [c1 [c2 [?[??]]]].
            elim H4.
            transitivity cin; firstorder.
            exists r. split; auto.
            apply sf_spec.next_ranking_valid with cin.
            destruct H; auto.
            right; auto.
            destruct H; auto.
          - destruct IHprefers as [c [n [??]]].
            exists c. exists n. split; auto.
            inversion H0; subst; clear H0.
            apply sf_spec.first_choices_selected.
            destruct H3. split.
            intro. apply H0.
            destruct H2.
            left. intro.
            apply H2.
            destruct H3 as [r ?].
            exists r. apply sf_spec.next_ranking_eliminated.
            rewrite Forall_forall. simpl; auto.
            intros [?[?[??]]]. elim H4.
            auto.
            right.
            destruct H2 as [r [??]].
            exists r; split; auto.
            inversion H2; subst; clear H2.
            auto.
            destruct H3 as [?[?[??]]]. elim H2.
            destruct H1 as [r [??]].
            exists r; split; auto.
            apply sf_spec.next_ranking_eliminated.
            rewrite Forall_forall. simpl; auto.
            intros [?[?[??]]]. elim H3.
            auto.
            auto.
            apply sf_spec.first_choices_not_selected; auto.
            intro. apply H3.
            destruct H0. split.
            intro. apply H0.
            destruct H2. left.
            intro. apply H2.
            destruct H4 as [r ?].
            exists r.
            inversion H4; subst; clear H4.
            auto.
            elim H9.
            right.
            destruct H2 as [r [??]].
            exists r; split; auto.
            apply sf_spec.next_ranking_eliminated.
            rewrite Forall_forall; auto.
            intros [?[?[??]]]. elim H7.
            auto.
            destruct H1 as [r [??]].
            exists r. split; auto.
            inversion H1; subst; clear H1.
            auto.
            elim H2.
          - destruct IHprefers as [c [n [??]]].
            destruct (sf_spec.sf_first_choices_total _ (fun _ => False) ((r::b)::e) c').
            exists c'. exists x. split; auto.
            inversion H4; subst; clear H4.
            omega.
            elim H8.
            split.
            intro. destruct H4.
            apply H4.
            exists r.
            apply sf_spec.next_ranking_valid with c'.
            destruct H1. auto.
            auto.
            destruct H4 as [r' [??]].
            inversion H4; subst; clear H4.
            destruct H1.
            rewrite Forall_forall in H11.
            apply H11 in H1. auto.
            destruct H6 as [?[?[?[??]]]].
            destruct H1.
            elim H7.
            transitivity c'; auto.
            symmetry; auto.
            exists r; split; auto.
            2: destruct H1; auto.
            apply sf_spec.next_ranking_valid with c'.
            destruct H1; auto.
            auto.

        + destruct IHe as [c [n [??]]]; auto.
          destruct (classic (sf_spec.selected_candidate _ (fun _ => False) a c)).
          exists c. exists (S n).
          split. omega.
          apply sf_spec.first_choices_selected; auto.
          exists c. exists n.
          split; auto.
          apply sf_spec.first_choices_not_selected; auto.
      }

      exists x; split; auto.
      apply (H1 (fun _ => False)); auto.
      red.
      destruct H.
      destruct H as [c ?]. eauto.
      apply (H1 (fun _ => False)); auto.
      red; simpl; auto.
      destruct H.
      destruct H as [c' ?]. eauto.
    }

    intros.
    induction H2.

    (* a winning candidate is always selected from the group *)
    * red in H0.
      red in H2.
      destruct H0 as [n [t [?[??]]]].
    
      destruct (sf_spec.sf_first_choices_total _ eliminated election0 winning_candidate) as [nwin ?].
      destruct (sf_spec.total_selected_total _ eliminated election0) as [ntotal ?].
      assert (nwin * 2 > ntotal) by (apply H2; auto). clear H2.
      destruct (classic (In winning_candidate group)); auto.
      elimtype False.
      destruct H1 as [cg [??]].
      assert( ntotal <= t ).
      { eapply sf_total_le_total; eauto. }
      assert( ntotal < n + nwin ) by omega.
      assert( n + nwin <= ntotal ).
      { revert cg H1 H8 H0 H2 H5 H6. clear. revert n nwin ntotal.
        induction election0; simpl; intros.
        * inversion H0; subst; clear H0.
          inversion H5; subst; clear H5.
          simpl. omega.
        * inversion H6; clear H6; subst.
          inversion H0; clear H0; subst;
          inversion H5; clear H5; subst.
          { elimtype False.
            hnf in H6.
            generalize (H6 cg winning_candidate H1 H2); intro.
            clear IHelection0 H9 H10 H11.
            assert (Hnelim : ~eliminated winning_candidate) by
                (eapply sf_spec.selected_candidate_not_eliminated; eauto).
            clear H6.
            induction H.
          - inversion H3; clear H3; subst.
            destruct H5 as [r' [??]].
            destruct H.
            inversion H3; clear H3; subst.
            rewrite Forall_forall in H10.
            elim H8. apply H10. auto.
            elim H2.
            replace winning_candidate with cg; auto.
          - apply IHprefers; auto.
            intro. apply H4.
            destruct H0.
            left. intros [q ?]. apply H0. exists q.
            inversion H5; clear H5; subst. auto.
            elim H9.
            right.
            destruct H0 as [q [??]].
            exists q. split; auto.
            constructor.
            rewrite Forall_forall. simpl. intuition.
            intro. destruct H6 as [?[?[??]]]. elim H6.
            auto.
            destruct H3. split; auto.
            intro. apply H0.
            clear -H5.
            destruct H5.
            left.
            intros [r ?].
            apply H. exists r. inversion H0; subst; auto.
            elim H3.
            right.
            destruct H as [r [??]].
            exists r; split; auto.
            constructor; auto.
            intros [?[?[??]]]. elim H1.
            destruct H3 as [r [??]].
            exists r; split; auto.
            inversion H3; clear H3; subst; auto.
            elim H9.
          - destruct H3.
            destruct H7 as [q [??]].
            inversion H7; clear H7; subst.
            assert (sf_spec.continuing_ballot candidate eliminated b).
            { intro. destruct H7.
              apply H7; eauto.
              destruct H7 as [q' [??]].
              apply H3.
              right.
              exists q'. split; auto.
              apply sf_spec.next_ranking_eliminated; auto.
            }
            apply IHprefers; auto.
            split; auto.
            exists q; split; auto.
            destruct H5.
            apply H0.
            apply H7. auto.
          }

          - cut (n1 + nwin <= n0). omega.
            eapply IHelection0; eauto.
          - cut (n + n' <= n0). omega.
            eapply IHelection0; eauto.
          - cut (n + nwin <= n0). omega.
            eapply IHelection0; eauto.
          - inversion H5; clear H5; subst; auto.
            elimtype False.
            destruct H6.
            apply H; auto.
            inversion H0; clear H0; subst; auto.
            hnf in H5.
            elimtype False.
            generalize (H5 cg winning_candidate H1 H2).
            clear H11 H5 n0 H10 H6 H9.
            intro.
            induction H.
            destruct H4.
            elim H0. exists r.
            apply sf_spec.next_ranking_valid with cg.
            destruct H; auto.
            right; auto.
            destruct H0 as [q [??]].
            inversion H0; clear H0; subst.
            rewrite Forall_forall in H6.
            apply H8. apply H6.
            destruct H; auto.
            destruct H3 as [?[?[?[??]]]].
            destruct H.
            apply H4.
            transitivity cg; auto.
            symmetry; auto.
            apply IHprefers.
            destruct H4.
            left; intro.
            apply H0.
            destruct H3 as [q ?].
            exists q.
            apply sf_spec.next_ranking_eliminated.
            rewrite Forall_forall. simpl. intuition.
            intros [?[?[?[??]]]]. elim H4.
            auto.
            right.
            destruct H0 as [q [??]].
            exists q. split; auto.
            inversion H0; clear H0; subst.
            auto.
            elim H6.
            destruct (classic (eliminated c')).
            apply IHprefers.
            destruct H4.
            left.
            intros [q ?].
            apply H4.
            exists q.
            apply sf_spec.next_ranking_eliminated.
            rewrite Forall_forall.
            intros.
            destruct H3.
            replace x with c'; auto.
            intros [?[?[?[??]]]].
            apply H11; auto.
            destruct H3.
            transitivity c'; auto. symmetry; auto.
            auto.
            destruct H4 as [q [??]].
            right.
            exists q.
            split; auto.
            inversion H4; clear H4; subst; auto.
            destruct H13.
            destruct H4 as [?[?[?[??]]]].
            elim H10.
            destruct H3.
            transitivity c'; auto. symmetry; auto.
            elim H4.
            replace c with c'; auto.
            destruct H3; auto.
            destruct H4.
            apply H4.
            exists r.
            apply sf_spec.next_ranking_valid with c'; auto.
            destruct H3; auto.
            destruct H4 as [q [??]].
            inversion H4; clear H4; subst; auto.
            rewrite Forall_forall in H11.
            apply H6. apply H11. destruct H3; auto.
            destruct H7 as [?[?[?[??]]]].
            apply H9.
            destruct H3.
            transitivity c'; auto. symmetry; auto.
            eapply IHelection0; eauto.
      }
      omega.

    (* After every elimination, some member from the group remains in the running, because otherwise the last
       remaining member of the group must have had a majority. *)
    * apply IHwinner; auto. clear IHwinner. hnf.
      destruct (classic (exists c, In c group /\ ~eliminated' c)); auto.
      assert (forall c, In c group -> eliminated' c).
      intros.
      destruct (classic (eliminated' c)); auto.
      elim H5; eauto.
      elimtype False. clear H5.
      unfold eliminated' in H6.
      unfold sf_spec.update_eliminated in H6.
      elim H2.
      destruct H1 as [winner [??]].
      exists winner.
      hnf; intros.
      destruct H0 as [n [t [?[??]]]].
      assert (n <= winner_votes).
      {
        assert (winner = loser).
        {
          destruct (H6 _ H1); auto.
          elim H5; auto.
        }
        clear -H H0 H1 H5 H6 H8 H11.
        subst loser.
        revert n H0. induction H8; intros.
        * inversion H0; clear H0; subst; auto.
        * inversion H2; clear H2; subst; auto.
          cut (n0 <= n'). omega.
          apply IHfirst_choices; auto.
        * inversion H2; clear H2; subst; auto.
          elim H0.
          clear t n n1 IHfirst_choices H0 H8 H10.
          destruct H as [_ [cOther ?]].
          specialize (H7 winner).
          induction h.
          - generalize (H7 cOther H1 H).
            intros. inversion H0.
          - destruct (sf_spec.ranking_cases _ eliminated a) as [?|[?|?]].
            + generalize (H7 cOther H1 H); intros.
              inversion H2; clear H2; subst.
              destruct H0 as [?[?[?[??]]]].
              elim H3. destruct H4.
              transitivity winner; auto. symmetry; auto.
              destruct H0 as [?[?[?[??]]]]. elim H0.
              destruct H0 as [?[?[?[??]]]].
              destruct H10.
              elim H3.
              transitivity c'; auto. symmetry; auto.
            + destruct H0 as [c [?[??]]].
              assert (c = winner).
              { destruct (classic (In c group)).
                apply H6 in H4. intuition.
                generalize (H7 c H1 H4). intros.
                inversion H8; clear H8; subst.
                destruct H10.
                symmetry; auto.
                inversion H2.
                elim H12.
                destruct H13. auto.
              }
              subst c.
              split.
              intros [?|?].
              elim H4.
              exists a. apply sf_spec.next_ranking_valid with winner; auto.
              destruct H4 as [q [??]].
              inversion H4; clear H4; subst.
              rewrite Forall_forall in H11.
              elim H5. apply H11. auto.
              rewrite Forall_forall in H0.
              destruct H8 as [?[?[?[??]]]].
              elim H9.
              transitivity winner; auto. symmetry; auto.

              exists a; split; auto.
              apply sf_spec.next_ranking_valid with winner; auto.
            +
              apply selected_candidate_tail; auto.
              apply IHh.
              intros.
              generalize (H7 cout H2 H3).
              intros.
              inversion H4; clear H4; subst; auto.
              destruct H0.
              subst a. destruct H9. elim H0.
              destruct H0 as [c' [?[??]]].
              rewrite Forall_forall in H0.
              destruct H9.
              assert (c' = winner) by auto.
              subst c'.
              elim H5; auto.
      }
      assert (total_votes <= t).
      { eapply sf_total_le_total; eauto. }
      omega.
  Qed.
End sf_spec_properties.

Check sf_mutual_majority.
Print Assumptions sf_mutual_majority.

Check sf_spec_total.
Print Assumptions sf_spec_total.
