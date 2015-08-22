Require sf_imp.
Require sf_spec.
Require Import RelDec.
Require Import List.
Require Import Sorted.
Require Import Permutation.
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
sf_spec.no_viable_candidates candidate (e) (a ::  b) <->
(sf_spec.no_viable_candidates candidate e [a] /\
sf_spec.no_viable_candidates candidate e b).
split.
intros.
unfold sf_spec.no_viable_candidates in *.
split.
intros. eapply H; eauto. inv H0; simpl in *; intuition.
intros. eapply H; eauto. simpl. intuition.
intros. intuition.
unfold sf_spec.no_viable_candidates in *. simpl in *.
intuition. eapply H0; eauto. 
eapply H1; eauto.
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
split.
intros.
unfold sf_spec.selected_candidate. 
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

Lemma next_ranking_elimintaed :
forall bal rec,
sf_imp.next_ranking candidate _ rec bal = None ->
sf_spec.exhausted_ballot candidate (in_record rec) bal.
Proof.
intros.
unfold sf_spec.exhausted_ballot.
induction bal.
-  left. unfold sf_spec.no_viable_candidates. intros. inv H0.
- simpl in *. destruct a.
   + intuition. left. apply no_viable_candidates_cons. intuition.
     unfold sf_spec.no_viable_candidates. intros. inv H0; intuition.
     right. unfold sf_spec.overvote in *. destruct H1. exists x.
     intuition. simpl. intuition.
   + destruct (forallb (eq_dec c) a) eqn:?.
     destruct (sf_imp.eliminated candidate reldec_candidate rec c) eqn:?; try congruence.
     rewrite eliminated_correct in *.  
     intuition. 
     * left. unfold sf_spec.no_viable_candidates. intros. simpl in *. destruct H0.  
       assert (candidate0 = c); subst; auto. rewrite forallb_forall in Heqb.
       specialize (Heqb candidate0). simpl in H2. destruct H2; auto.
       specialize (Heqb H0). apply reldec_correct_candidate in Heqb. auto.
       unfold sf_spec.no_viable_candidates in *.
       eapply H1; eauto.
     * right. clear H Heqb0.
       unfold sf_spec.overvote in *. 
       destruct H1. intuition. destruct H1. destruct H. intuition.
       exists x. simpl. intuition. left. intuition.
       subst.
       rewrite forallb_forall in Heqb. specialize (Heqb x0). 
Admitted.
 
    
Definition boolCmpToProp {A} (c : A -> A -> bool) :=
fun a b => match c a b with
           | true => True
           | false => False
end. 

Lemma insert_sorted : forall {A} c sorted (a : A),
    (forall a b, c a b = false -> c b a = true) ->
    Sorted (boolCmpToProp c) sorted ->
    Sorted (boolCmpToProp c) (sf_imp.insert c a sorted).
induction sorted; intros. 
+ simpl. auto.
+ simpl. inv H0.
  destruct (c a0 a) eqn:?. 
  constructor. auto. constructor. unfold boolCmpToProp. rewrite Heqb. auto.
  constructor. auto.  
  specialize (IHsorted a0 H H3). 
  destruct (sf_imp.insert c a0 sorted) eqn:?.
Admitted. 
  
       
Lemma insertion_sort_sorted' : forall {A} (l : list A) (sorted : list A) c,
    (forall a b, c a b = false -> c b a = true) -> 
    Sorted (boolCmpToProp c) sorted ->
    Sorted (boolCmpToProp c) (sf_imp.insertionsort' c l sorted).   
Proof.
induction l.
+ intros. simpl. auto.
+ intros. simpl in *. apply IHl; auto.
  apply insert_sorted; auto.
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

Locate Permutation.
Print Permutation.

Axiom insertionsort_permutation : forall A c (l: list A), Permutation (sf_imp.insertionsort c l) (l).

Definition tb_func_to_Prop {c : Set} (f : list c -> option c) :=
fun l cd => match f l with 
         | Some x => x = cd
         | None => False
end.

Lemma tabulate_correct : forall rec election rs election',
sf_imp.tabulate candidate _ rec election = (rs, election') ->
Forall (fun (x: (candidate * nat)) => let (cd, fc) := x in
                 sf_spec.first_choices candidate (in_record rec) cd election fc) rs.
Proof.
intros.
unfold sf_imp.tabulate in H. destruct (sf_imp.option_split
             (map (sf_imp.next_ranking candidate reldec_candidate rec)
                election)) eqn:?.
induction election.
- simpl in *. rewrite Forall_forall. intros. destruct x. inv Heqp. simpl in *. inv H.
  simpl in *. inv H0.
- simpl in Heqp. destruct (sf_imp.next_ranking candidate reldec_candidate rec a) eqn:?.
  destruct p. destruct (sf_imp.option_split
                (map (sf_imp.next_ranking candidate reldec_candidate rec)
                   election)) eqn:?. inv Heqp. rewrite Forall_forall.
  intros. destruct x. constructor.  
  + admit.
  + inv H.
    pose proof (insertionsort_permutation _ (sf_imp.cnlt candidate) 
                                          (sf_imp.tabulate' candidate reldec_candidate (Some c :: l1))).
    eapply Permutation_in in H0; eauto.
    unfold sf_imp.tabulate' in H0. simpl in H0.
Admitted. 

Lemma in_split : forall A B (f : A) (l : list (A * B)), 
              In f (fst (split l)) -> 
              exists n : B, In (f, n) l.
Proof.
induction l; intros.
- simpl in *. inv H.
- simpl in *. destruct a. simpl in *.
  destruct (split l) eqn:?.
  simpl in *. destruct H. 
  + subst. eauto.
  + intuition. destruct H0. eauto. 
Qed.

Lemma first_choices_app : 
forall c l1 l2 x1 x2  r cnd, 
sf_spec.first_choices c r cnd l1 x1 ->
sf_spec.first_choices c r cnd l2 x2 ->
sf_spec.first_choices c r cnd (l1 ++ l2) (x1 + x2).
Proof.
induction l1; intros.
- simpl in *. inv H. simpl. auto.
- simpl in *. Print sf_spec.first_choices.
  inv H.
  + apply sf_spec.first_choices_selected. auto. fold plus.
    apply IHl1; auto.
  + apply sf_spec.first_choices_not_selected; auto.
Qed.

Lemma first_choices_app_gt :
forall c l1 l2 x1 x2 r cnd,
sf_spec.first_choices c r cnd l1 x1 ->
sf_spec.first_choices c r cnd (l1 ++ l2) (x2) ->
x2 >= x1.
Proof.
induction l1; intros.
- simpl in *. inv H. omega.
- simpl in *. inv H; inv H0; try congruence; try omega.
  eapply IHl1 in H5; eauto. omega.
  eapply IHl1; eauto.
Qed.

Lemma first_choices_perm : 
forall c l1 l2 x r cnd,
Permutation l1 l2 ->
sf_spec.first_choices c r cnd l1 x ->
sf_spec.first_choices c r cnd l2 x.
Proof.
induction l1; intros.
- apply Permutation_nil in H. subst. auto. 
- assert (exists l2s l23, l2 = l2s ++ (a :: l23)). 
  { eapply Permutation_in in H. instantiate (1 := a) in H.
    apply List.in_split in H. auto.
    constructor; auto. }
  destruct H1. destruct H1.
  subst.
  apply Permutation_cons_app_inv in H.
  inv H0.
  + eapply (IHl1 _ n' r cnd) in H; auto.
    clear - H H3.
    { generalize dependent x1. generalize dependent n'.
      induction x0; intros.
      - simpl in *. constructor; auto.
      - simpl in *. inv H. 
        + constructor; auto.
        + apply sf_spec.first_choices_not_selected; auto.
    }
  + eapply IHl1 in H; eauto.
    { clear - H H3.
      generalize dependent x1. generalize dependent x.
      induction x0; intros.
      - simpl in *. apply sf_spec.first_choices_not_selected; auto.
      - simpl in *. inv H.
        + constructor; auto.
        + apply sf_spec.first_choices_not_selected; auto.
    }
Qed.

Lemma rel_dec_refl : forall c, rel_dec c c = true.
Proof.
intros. apply rel_dec_correct. auto.
Qed.

Lemma increment_spec : forall m cd cds ct,
cds = (fst (split m)) ->
NoDup (cds) -> 
(In (cd, ct) m -> In (cd, S ct) (sf_imp.increment candidate _ m cd)) /\
(~In cd cds -> In (cd, 1) (sf_imp.increment candidate _ m cd)). 
Proof.
induction m; intros.
- simpl in *. intuition.
- simpl in *. destruct a. 
  destruct (split m) eqn:?.
  simpl in *. 
  destruct (in_dec rel_dec_p cd cds). 
  + subst.
    split.
    * { intros. simpl in *.
        unfold eq_dec.
        intuition.
        - inv H2.  rewrite rel_dec_refl.
          simpl. auto.
        - subst. clear -Heqp H2 H0.
          inv H0. assert (In cd l). apply in_split_l in H2. 
          simpl in H2. rewrite Heqp in *. auto.
          intuition.
        - inv H2. inv H0. intuition.
        - assert (c <> cd).
          intro. subst. inv H0. intuition.
          eapply rel_dec_neq_false in H.
          rewrite H. simpl. right.
          edestruct IHm. reflexivity.
          inv H0; auto.
          clear H4. auto. apply reldec_correct_candidate.
      } 
    * intuition.  
  + subst. simpl in *. inv H0. unfold eq_dec.  
    split. 
      * { intuition.
        - inv H0. intuition.
        - eapply rel_dec_neq_false in H. rewrite H. 
          edestruct IHm; eauto. simpl in *. auto.
          apply reldec_correct_candidate.
        }
      * intuition. eapply rel_dec_neq_false in H4. rewrite H4.
        simpl. 
        edestruct IHm; eauto.
        eapply reldec_correct_candidate.
Grab Existential Variables. exact O.
Qed.


Lemma increment_not_0 : forall running cd,
NoDup (fst (split running)) ->
~In (cd, 0) (sf_imp.increment candidate reldec_candidate running cd).
Proof.
induction running; intros; intro.
- unfold sf_imp.increment in *. simpl in *; intuition. congruence.
- simpl in *. destruct a. destruct (eq_dec c cd) eqn:?.
  + clear IHrunning. apply reldec_correct_candidate in Heqb. subst.
    simpl in *. destruct (split running) eqn:?. simpl in *. 
    inv H. intuition. congruence. apply in_split_l in H. 
    simpl in H. rewrite Heqp in H. simpl. intuition.
  + simpl in *. destruct (split running) eqn:?. simpl in *.
    apply neg_rel_dec_correct in Heqb. destruct H0.
    * inv H0. auto.
    * inv H. intuition. eapply IHrunning; eauto.
Qed.

Lemma increment_nodup' : forall running cd c,
~In c (fst (split running)) ->
c <> cd ->
~In c (fst (split (sf_imp.increment candidate reldec_candidate running cd))).
Proof.
induction running; intros.
- simpl in *. intuition.
- simpl in *.
  destruct a. 
  destruct (split running) eqn:?. simpl in H. intuition.
  destruct (eq_dec c0 cd) eqn:?.
  + simpl in *. rewrite Heqp in *. simpl in *. intuition.
  + simpl in *. destruct (split
                   (sf_imp.increment candidate reldec_candidate running cd)) eqn:?.
    simpl in *. intuition. eapply IHrunning; eauto. 
    rewrite Heqp0. simpl. auto.
Qed.

Lemma increment_nodup : forall running cd,
NoDup (fst (split running)) -> 
NoDup (fst (split (sf_imp.increment candidate reldec_candidate running cd))).
induction running; intros.
- simpl in *. constructor; auto. 
- simpl in *. destruct a. destruct (eq_dec c cd) eqn:?.
  + apply reldec_correct_candidate in Heqb. subst.
    simpl in *.
    destruct (split running) eqn:?. simpl in *. auto.
  + simpl in *. destruct ( split (sf_imp.increment candidate reldec_candidate running cd)) eqn:?.
    simpl.
    destruct (split running) eqn:?. simpl in *. inv H.
    eapply IHrunning in H3. instantiate (1:=cd) in H3. rewrite Heqp in H3.
    simpl in H3. constructor; auto. intro. apply neg_rel_dec_correct in Heqb.
    eapply increment_nodup'; eauto. instantiate (1:=running). 
    rewrite Heqp0. simpl. auto.
    rewrite Heqp. auto.
Qed.    

Lemma increment_neq : forall running c cd v,
In (c, v) running ->
c <> cd ->
In (c, v) (sf_imp.increment candidate reldec_candidate running cd).
Proof.
induction running; intros.
- inv H.
- destruct a.
  simpl in *.
  destruct (eq_dec c0 cd) eqn:?.
  + simpl in *. intuition.
    apply reldec_correct_candidate in Heqb. inv H1. intuition.
  + simpl in *. intuition.
Qed.


Lemma tabulate_not_0 : forall l cd v running,
NoDup (fst (split running)) ->
In (cd, v) running ->
v <> 0 ->
~In (cd, 0)
   (sf_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl in *. intuition. apply H1.
  clear H1. induction running.
  + inv H0.
  + simpl in *. destruct a. destruct (split running) eqn:?. simpl in *.
    intuition.
    * inv H1. inv H0. auto.
    * inv H1. inv H. intuition. apply in_split_l in H0. simpl in *.
      rewrite Heqp in *. simpl in *. intuition.
    * inv H. inv H0. apply in_split_l in H1. rewrite Heqp in *. simpl in *.
      intuition.
    * inv H. intuition.
- simpl in *. destruct a. intro. intuition.
  destruct (rel_dec_p c cd). 
  + subst.
    eapply IHl in H2; auto.
    * apply increment_nodup. auto.
    * instantiate (1:=S v). edestruct increment_spec. reflexivity.
      apply H. apply H3. auto.
    * intuition.
  + eapply IHl in H2; auto.
    * apply increment_nodup; auto.
    * instantiate (1:=v). edestruct increment_spec. reflexivity.
      apply H. apply increment_neq; auto.
    * auto.
  + eapply IHl in H0; auto.
Grab Existential Variables. apply 0. apply c. (*ugh*)
Qed.
   
Lemma opt_eq_dec : forall A,
(forall (a b : A), {a = b} + {a <> b}) ->
forall (a b : option A), {a = b} + {a <> b}.
Proof.
intros.
destruct a, b; auto.
specialize (X a a0). destruct X. subst. auto. right.
intro. inv H. auto.
right. intro. congruence.
right. congruence.
Qed.

Lemma opt_eq_dec_cand : 
forall (a b : option candidate), {a = b} + {a <> b}.
Proof.
apply opt_eq_dec. apply rel_dec_p.
Qed.

Lemma NoDup_In_fst :
forall A B l (a :A) (b :B) c,
NoDup (fst (split l)) ->
In (a, b) l ->
In (a, c) l ->
b = c.
Proof.
induction l; intros.
- inv H0.
- simpl in *.
  destruct (split l) eqn:?.
  destruct a. intuition; try congruence.
  + simpl in *. inv H2. inv H. apply in_split_l in H0. simpl in H0. 
    rewrite Heqp in *. intuition.
  + simpl in *. inv H. inv H0. 
    apply in_split_l in H2. simpl in*. rewrite Heqp in *.
    intuition.
  + eapply IHl; eauto. simpl. simpl in H. inv H. auto.
Qed.

Lemma tab_inc_s : forall cd ct l running running' cr,
NoDup (fst (split running)) ->
NoDup (fst (split running')) ->
In (cd, S ct)
   (sf_imp.tabulate'' candidate reldec_candidate l running') ->
In (cd, cr) running ->
In (cd, (S cr)) running' ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl in *. 
  assert (cr = ct).
  eapply NoDup_In_fst in H3. instantiate (1:=S ct) in H3. congruence.
  auto. auto. subst. auto.
- simpl in *.
  destruct a. 
  + destruct (rel_dec_p cd c).
    * subst. eapply IHl.
      apply increment_nodup. auto. 
      apply increment_nodup. apply H0.
      eauto. 
      eapply increment_spec in H2; eauto.
      eapply increment_spec in H3; eauto.
    * eapply increment_neq in H2; eauto.
      eapply increment_neq in H3; eauto.
      eapply IHl.
      apply increment_nodup. auto.
      apply increment_nodup. apply H0.
      apply H1.
      eauto.
      eauto.
  + eapply IHl; eauto.
Qed.


Ltac copy H :=
match goal with 
[ H : ?P |- _] => assert P by exact H end.

Lemma increment_neq' : forall running cd ct  c,
In (cd, ct) (sf_imp.increment candidate reldec_candidate running c) ->
c <> cd ->
In (cd, ct) running.
Proof.
induction running; intros.
- simpl in H. intuition. congruence.
- simpl in *. destruct a.
  + destruct (eq_dec c0 c) eqn:?.
    apply rel_dec_correct in Heqb. subst.
    simpl in *. intuition. inv H1. intuition.
    simpl in *. intuition.
    right. eapply IHrunning; eauto.
Qed.

Lemma tabulate''_same : forall cd l running running' cr ct,
NoDup (fst (split running)) ->
NoDup (fst (split running')) ->
In (cd, cr) running ->
In (cd, cr) running' ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running) ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running').
Proof.
induction l; intros.
- simpl in *. 
  assert (cr = ct).
  eapply NoDup_In_fst. apply H.
  apply H1. apply H3. subst.
  auto.
- simpl in *.
  destruct a.
  + destruct (rel_dec_p cd c).
    * eapply IHl.
      apply increment_nodup. apply H.
      apply increment_nodup. auto. 
      subst.
      eapply increment_spec in H1. apply H1.
      auto. auto.
      subst. eapply increment_spec in H2; eauto.
      eauto.
    * eapply IHl.
      apply increment_nodup. apply H.
      apply increment_nodup. auto.
      eapply increment_neq in n. apply n. eauto.
      eapply increment_neq in n.
      eauto. auto.
      eauto.
  + eapply IHl; eauto.
Qed.

Lemma tabulate''_same_notin : forall cd ct l running running',
NoDup (fst (split running)) ->
NoDup (fst (split running')) ->
~In cd (fst (split running)) ->
~In cd (fst (split running')) ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running) ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running').
Proof.
induction l; intros.
- simpl in *. intuition. 
  apply in_split_l in H3. simpl in H3. intuition.
- simpl in *.
  destruct a; try solve [eapply IHl; eauto].
  destruct (rel_dec_p cd c).
  + subst. eapply increment_spec in H1; eauto.
    eapply increment_spec in H2; eauto.
    eapply (tabulate''_same _ _ _ _ _ _ _ _ _ H2).
    eauto. 
  + eapply IHl. apply H.
    apply increment_nodup. auto. auto. apply increment_nodup'; eauto.
    eapply IHl in H3. eauto. 
    apply increment_nodup. auto. auto. apply increment_nodup'; eauto.  
    auto. Grab Existential Variables. auto.
    apply increment_nodup. auto. apply increment_nodup. auto.
Qed.

Lemma tab_inc_s_l :
forall l cd ct running,
In (cd, S ct) (sf_imp.tabulate'' candidate reldec_candidate l
               (sf_imp.increment candidate reldec_candidate running cd)) ->
~ In cd (fst (split running)) ->
NoDup (fst (split running)) ->
In (Some cd) l ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- inv H2.
- simpl in *. destruct a.
  destruct (rel_dec_p cd c). 
  + subst. clear H2.
    simpl in *. eapply increment_spec in H0; auto.
    copy H0.
    eapply increment_spec in H0; auto.
    eapply tab_inc_s. apply increment_nodup. auto. apply increment_nodup.
    apply increment_nodup. eauto. eauto. eauto. eauto.
    apply increment_nodup. auto. 
  + destruct H2. congruence. 
    eapply tabulate''_same_notin.
    eauto. apply increment_nodup. auto.
    auto.
    apply increment_nodup'; auto.
    eapply IHl; eauto.
    eapply (tabulate''_same) in H.
    apply H. apply increment_nodup. apply increment_nodup.
    auto. apply increment_nodup. auto.
    apply increment_neq; auto. eapply increment_spec in H0; eauto.
    eapply increment_spec in H0; eauto.
  + intuition. congruence.
Qed.

Lemma tabulate_not_in_l :
forall l cd ct running,
NoDup (fst (split running)) ->
In (cd, ct) running ->
~In (Some cd) l ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl. auto.
- simpl in *.
  destruct a; intuition; try congruence.
  eapply IHl; eauto. apply increment_nodup. auto.
  apply increment_neq; auto. intuition. subst. auto.
Qed.

Lemma tabulate_nodup :
forall l running,
NoDup (fst (split running)) -> 
NoDup (fst (split (sf_imp.tabulate'' candidate reldec_candidate l running))).
Proof.
induction l; intros.
- simpl.  auto.
- simpl in *.
  destruct a.
  + apply IHl. apply increment_nodup; auto.
  + apply IHl. auto.
Qed.


Lemma tabulate''_first_choices : forall ef cd ct es running r
(NODUP : NoDup (fst (split running))),
In (cd, ct) (sf_imp.tabulate'' candidate _ 
                               (fst (sf_imp.option_split
                                      (map (sf_imp.next_ranking candidate reldec_candidate r)
                                           ef))) running) -> 
(forall cnd, ~In cnd (fst (split running)) -> sf_spec.first_choices candidate (in_record r) cnd es 0) ->
Forall (fun x => let (cnd, n) := (x: candidate * nat) 
                 in sf_spec.first_choices candidate (in_record r) cnd es n) running ->
sf_spec.first_choices candidate (in_record r) cd (es ++ ef) ct. 
Proof.
induction ef; intros.
- simpl in *. rewrite Forall_forall in *. specialize (H1 _ H). simpl in H1.
  rewrite app_nil_r.  auto.
- simpl in H. destruct (sf_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  +  destruct p. destruct (sf_imp.option_split
                     (map (sf_imp.next_ranking candidate reldec_candidate r)
                          ef)) eqn:?. simpl in *. 
     assert (Permutation (a :: (es ++ ef)) (es ++ a :: ef)). 
     apply Permutation_middle.
     eapply first_choices_perm; eauto. clear H2.
     apply next_ranking_selected in Heqo.
     destruct (rel_dec_p c cd). 
     * subst. 
       { destruct ct.
         - clear - H NODUP.
           exfalso. 
           eapply (tabulate_not_0 _ _ _ _ _ _ _ H).
         - constructor. auto. 
           destruct (in_dec rel_dec_p cd (fst (split running))).
           + eapply IHef; eauto.
             edestruct in_split. apply i.
             eapply tab_inc_s; auto.
             apply increment_nodup. eauto.
             rewrite Heqp. simpl. eauto.
             apply H2. eapply increment_spec in H2; eauto.
           + destruct (in_dec opt_eq_dec_cand (Some cd) l).
             * eapply IHef; eauto.
               rewrite Heqp. simpl.
               apply tab_inc_s_l; auto.
             * copy n. eapply increment_spec in n; eauto.
               eapply tabulate_not_in_l in n; eauto.
               assert (1 = (S ct)). eapply NoDup_In_fst; [ | eauto | eauto ].
               apply tabulate_nodup. apply increment_nodup. auto.
               inv H3. change 0 with (0 + 0). 
               apply first_choices_app. 
               
               
               
               SearchAbout In.

eapply tabulate''_same.



  apply nodup_in.
  
    eapply increment_neq';

    simpl in *.
    apply neg_rel_dec_correct in H0. unfold eq_dec in H. rewrite H0 in H.

    eapply increment_neq.
    assert (In (cd, 1) (sf_imp.increment candidate reldec_candidate running cd)).
    eapply increment_spec; eauto.
    eapply increment_neq in H3; eauto.
    eapply tab_inc_s. apply increment_nodup.
    auto.
    apply increment_nodup. apply increment_nodup. eauto.
    eauto. 
    
Check increment_spec.
    eapply increment_spec in n.
       

    
Lemma inc_spec_rev : forall running cd ct,
In (cd, S ct) (sf_imp.increment candidate reldec_candidate running cd) ->
In (cd, ct) running.
Proof.
induction running; intros.
- simpl in *. intuition. inv H0.


edestruct increment_spec; eauto.
             
edestruct increment_spec. Focus 3.
         apply H0 in H.



         apply increment_spec in H.
         apply tabulate_spec in H.
         simpl in *. unfold sf_imp.increment in H.
          - unfold sf_imp.increment in *.
            induction l. simpl in H. intuition. congruence.
            apply IHl. simpl in H. destruct a0. destruct (eq_dec cd c).
            apply IHl in H.
         
       
       assert (l = fst (sf_imp.option_split
         (map (sf_imp.next_ranking candidate reldec_candidate r) ef))). 
       destruct ( sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate r) ef)).
       inv Heqp. auto.
       subst. eapply IHef in H. 
       rewrite app_comm_cons. apply H.
       intros.
       specialize (H0 cnd).
       intuition. apply H0.  
       { clear - H2.
         induction running; auto.
         simpl in *. destruct a. intros.
         destruct (split running) eqn:?. simpl in *.
         destruct H. 
         subst. 
         destruct (eq_dec cnd cd) eqn:?. simpl in *. rewrite Heqp in *. simpl in *.
         auto. simpl in *. apply H2.
         destruct (split (sf_imp.increment candidate reldec_candidate running cd)) eqn:?.
         simpl. auto. apply IHrunning; auto.
         destruct (eq_dec c cd). simpl in *. rewrite Heqp in *. simpl in *. intuition.
         simpl in *. intros. apply H2.
         destruct (split (sf_imp.increment candidate reldec_candidate running cd)).
         simpl in *. auto.  }


  +
           
                             

apply sf_spec.first_choices_selected.
       constructor; auto.
           pose proof (first_choices_app _ _ (a::ef) _ (ct - x) _ _ H3).
           cut (ct >= x). intros. 
           rewrite <- Minus.le_plus_minus in H1; auto.
           apply H1.
           assert (ct >= x). eapply first_choices_app_gt; eauto.
           apply H1.
         SearchAbout app.
         rewrite app_cons.
         eapply first_choices_app.
       



    
    

       specialize (H1 (c, b)).
  assert (sf_spec.first_choices candidate (in_record r) cd (es ++ ef) ct).
  eapply IHef.
 
  assert (l = fst (sf_imp.option_split
         (map (sf_imp.next_ranking candidate reldec_candidate r) ef))). 
  destruct ( sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate r) ef)).
  inv Heqp. auto. subst. eauto.
  rewrite Forall_forall in *. intros.  
  specialize (H0 (c, n)). apply H0. simpl in *.


  
  
  
 

forall b s, In b election ->
                    continuing_ballot b ->
                    In s (sf_imp.drop_none
                            (map (sf_imp.next_ranking candidate reldec_candidate rec)
                                 election)) ->  
                    sf_spec.selected_candidate candidate (in_record rec) bal (fst x)).

                                      

Lemma run_election'_correct : forall fuel election winner tb rec rec',
    sf_imp.run_election' candidate _ tb election rec fuel = (Some winner, rec') ->
    sf_spec.winner candidate (tb_func_to_Prop tb) election (in_record []) winner.
induction fuel; intros.
simpl in *. congruence.
Admitted.



Theorem run_election_correct : forall election winner tb rec, 
    sf_imp.run_election candidate _ tb election = (Some winner, rec) ->
    sf_spec.winner candidate (tb_func_to_Prop tb) election (in_record []) winner.
intros. unfold sf_imp.run_election in H. apply run_election'_correct in H. auto.
Qed.


