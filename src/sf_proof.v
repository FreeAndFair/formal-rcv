Require sf_imp.
Require sf_spec.
Require Import sf_lemmas.
Require Import RelDec.
Require Import List.
Require Import Sorted.
Require Import Permutation.
Require Import FunctionalExtensionality.
Require Import Classical.
Require Import sf_tactic.
Require Import Coq.Numbers.BinNums.
Require Import Coq.NArith.BinNat.

Import ListNotations.


Section cand.

Variable candidate : Set.
Variable reldec_candidate : RelDec (@Logic.eq candidate).
Variable reldec_correct_candidate : RelDec_Correct reldec_candidate.

Local Open Scope N_scope.

Ltac solve_rcv := sf_tactic.solve_rcv reldec_correct_candidate.
Ltac intuition_nosplit := sf_tactic.intuition_nosplit reldec_correct_candidate.

Lemma no_viable_candidates_correct : 
forall rec bal,
sf_imp.no_viable_candidates candidate _ rec bal = true -> 
sf_spec.no_viable_candidates candidate (in_record rec) bal.
Proof.
solve_rcv.  
specialize (H _ H0). solve_rcv.  
apply H in H1.
Unset Ltac Debug.
solve_rcv. 
Qed.



Lemma eliminated_correct :
forall rec can,
sf_imp.eliminated candidate _ rec can = true <->
in_record rec can.
Proof.
split; solve_rcv.
 exists x. solve_rcv. intuition.
 exists can.  solve_rcv. 
Qed.

(*
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
Qed.*)

Ltac force_specialize P :=
repeat
match goal with
| [ H : _ |- _] => extend (P H)
end. 

Ltac force_specialize_all :=
repeat
match goal with
| [ H : (forall x, _) |- _ ] => progress (force_specialize H)
end.



Lemma next_ranking_not_overvote :
forall rec bal cd bal' a,
sf_imp.next_ranking candidate _ rec (a :: bal) = Some (cd, bal') ->
~sf_spec.overvote candidate a.
Proof.
intros. intro.
simpl in *. 
destruct a; solve_rcv;
force_specialize_all;
simpl in *; intuition; subst; solve_rcv.
Qed.

Lemma next_ranking_selects : forall a bal cd bal' rec,
    sf_imp.next_ranking candidate reldec_candidate rec (a :: bal) =
    Some (cd, bal') ->
    sf_spec.does_not_select candidate (in_record rec) a ->
    sf_imp.next_ranking candidate reldec_candidate rec (bal) = Some (cd, bal').
Proof.
intros.
destruct a; simpl in *; solve_rcv.
destruct H0; solve_rcv.
assert (x=cd).
simpl in H0; intuition; force_specialize_all; solve_rcv.
subst. clear H0. 
force_specialize_all; solve_rcv.
force_specialize_all; solve_rcv. 
Qed. 
                            
Hint Resolve next_ranking_not_overvote : rcv.

Lemma next_ranking_correct :
forall rec bal cd bal' ,
sf_imp.next_ranking candidate _ rec bal = Some (cd, bal') ->
exists h t,(sf_spec.next_ranking candidate (in_record rec) bal (h::t) /\ Forall (Logic.eq cd) (h::t)).
Proof.
intros.
induction bal.
- solve_rcv. 
- solve_rcv.
  destruct (sf_spec.ranking_cases _  (in_record rec) a); [ | destruct H0].
  + apply next_ranking_not_overvote in H. intuition.
  + solve_rcv. destruct a; simpl in *; solve_rcv. 
    * { destruct H1. 
        - exfalso. apply H2.
          subst. exists x2. auto.
        - exists x0; exists (x1); solve_rcv.
          + constructor; solve_rcv.
            * exists x2. split; auto. 
              destruct H7. subst; auto.
              force_specialize_all; solve_rcv.
            * force_specialize_all; solve_rcv.
      }
    * { destruct H1. 
        - subst. exists x. exists a. solve_rcv.
          eapply sf_spec.next_ranking_valid; solve_rcv.
        - exists cd.  exists a. 
          solve_rcv. eapply sf_spec.next_ranking_valid; solve_rcv.
          simpl in H1. intuition.
          force_specialize_all; solve_rcv.
      }
  + apply next_ranking_selects in H; auto.
    solve_rcv.
    exists x; solve_rcv. exists x0.
    destruct H0; solve_rcv. constructor; solve_rcv. 
    constructor; solve_rcv. force_specialize_all; solve_rcv.
    force_specialize_all; solve_rcv.
Qed.
 


(* These don't have meaning anymore now that overvote is a ranking
   level predicate 

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
Qed. *)
    


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
solve_rcv.
- destruct H0.
 + apply H0; clear H0.
   apply next_ranking_correct in H. 
   solve_rcv.
 + destruct bal; solve_rcv.
   copy H.
   apply next_ranking_correct in H. solve_rcv.
   unique; subst.
   force_specialize_all; solve_rcv. 
- apply next_ranking_correct in H; solve_rcv.
  exists (x :: x0); solve_rcv.  simpl in *.
  force_specialize_all; solve_rcv; intuition.
Qed.

Lemma next_ranking_eliminated :
forall bal rec,
sf_imp.next_ranking candidate _ rec bal = None ->
sf_spec.exhausted_ballot candidate (in_record rec) bal.
Proof.
intros. 
induction bal.
- left. solve_rcv. 
- simpl in *. destruct a; solve_rcv. 
  + destruct IHbal; solve_rcv.
    * left. intro. apply H0. solve_rcv.
      exists x. inv H1; solve_rcv.
    * right. exists x. solve_rcv. constructor; solve_rcv.
  + destruct IHbal. 
    * left. intro. apply H2; solve_rcv.
      { inv H3. 
        - solve_rcv.
        - destruct H8; solve_rcv.  
          + exfalso. simpl in *. repeat (intuition; subst); force_specialize_all; solve_rcv.
          + inv H6; solve_rcv. 
            * exfalso. apply H3. clear H3. exists x; solve_rcv.
            * force_specialize_all. solve_rcv.
              exfalso. apply H3; solve_rcv.
      }
    * right. solve_rcv. 
      exists x1; solve_rcv.
      constructor; solve_rcv. exists x; inv H6; force_specialize_all; solve_rcv.
      simpl in *. intuition; force_specialize_all; solve_rcv.
  + right. clear IHbal. exists (c::a). solve_rcv.
    eapply sf_spec.next_ranking_valid. simpl. auto.
    left. solve_rcv. exists x. exists c. 
    simpl. auto.
    exists x. exists c. simpl. auto.
Qed.
 
    
Definition boolCmpToProp {A} (c : A -> A -> bool) :=
fun a b => match c a b with
           | true => True
           | false => False
end. 

Lemma insert_sorted : forall {A} c sorted (a : A),
    (forall a b, c a b = false -> c b a = true) ->
    Sorted (boolCmpToProp c) sorted ->
    Sorted (boolCmpToProp c) (sf_imp.insert c a sorted).
intros.
induction H0.
- simpl. auto.
- simpl.
  destruct (c a a0) eqn:?. 
  constructor. auto. constructor. unfold boolCmpToProp. rewrite Heqb. auto.
  constructor. auto.
  clear IHSorted H0.
  induction l.
  + simpl in *.
    constructor. unfold boolCmpToProp. apply H in Heqb. rewrite Heqb.
    auto.
  + simpl in *. destruct (c a a1) eqn:?. constructor. apply H in Heqb. 
    unfold boolCmpToProp. rewrite Heqb. auto.
    constructor; auto.
    unfold boolCmpToProp.
    apply H in Heqb. inv H1. unfold boolCmpToProp in H2. 
    auto.
Qed.
  
       
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

Lemma insertion_sort_sorted : forall {A} (l : list A) c,
    (forall a b, c a b = false -> c b a = true) -> 
    Sorted (boolCmpToProp c) (sf_imp.insertionsort c l). 
intros.
apply insertion_sort_sorted'; auto.
Qed.

Lemma insert_permutation :
  forall {A} l2 l1  (a : A) c,
    Permutation l1 l2 ->
    Permutation (a :: l1) (sf_imp.insert c a l2).
Proof.
induction l2; intros. 
- apply Permutation_sym in H. apply Permutation_nil in H. subst. simpl in *. auto.
- simpl in *. destruct (c a0 a).
  constructor. auto.
  eapply Permutation_trans. instantiate (1:= (a0 :: a :: l2)).
  auto. rewrite perm_swap. constructor.
  apply IHl2. auto.
Qed.


Lemma insertion_sort_permutation' :
  forall {A} (le ls : list A) c sorted,
    Permutation ls sorted -> 
    Permutation (ls ++ le) (sf_imp.insertionsort' c le sorted).
Proof.
induction le; intros.
- simpl in *. rewrite app_nil_r. auto.
- simpl. rewrite <- Permutation_middle.
  rewrite app_comm_cons.
  apply IHle. apply insert_permutation. auto.
Qed.

Lemma insertion_sort_permutation :
  forall {A} (l : list A) c,
    Permutation l (sf_imp.insertionsort c l).
intros. rewrite <- app_nil_l at 1.
unfold sf_imp.insertionsort.
apply insertion_sort_permutation'. auto.
Qed.


Definition tb_func_to_Prop {c : Set} (f : list c -> option c) :=
fun l cd => match f l with 
         | Some x => x = cd
         | None => False
end.


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



Lemma rel_dec_refl : forall c, rel_dec c c = true.
Proof.
intros. apply rel_dec_correct. auto.
Qed.

Lemma increment_spec : forall (m : list (candidate *  N)) cd cds (ct : N),
cds = (fst (split m)) ->
NoDup (cds) -> 
(In (cd, ct) m -> In (cd, (ct + 1)%N) (sf_imp.increment candidate _ m cd)) /\
(~In cd cds -> In (cd, 1%N) (sf_imp.increment candidate _ m cd)). 
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
Grab Existential Variables. exact 0.
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
    inv H. intuition. inv H. rewrite N.add_comm in H1. rewrite N.eq_add_0 in H1. 
    intuition. congruence.  apply in_split_l in H. 
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
    apply reldec_correct_candidate in Heqb. inv H1. subst. intuition.
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
    * instantiate (1:=v + 1). edestruct increment_spec. reflexivity.
      apply H. apply H3. auto.
    * intuition.  rewrite N.eq_add_0 in H3. destruct H3. congruence. 
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
In (cd, ct + 1)
   (sf_imp.tabulate'' candidate reldec_candidate l running') ->
In (cd, cr) running ->
In (cd, (cr + 1)) running' ->
In (cd, ct) (sf_imp.tabulate'' candidate reldec_candidate l running).
Proof.
induction l; intros.
- simpl in *. 
  assert (cr = ct).
  eapply NoDup_In_fst in H3. instantiate (1:= ct + 1) in H3.
  apply N.add_cancel_r in H3. auto.
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
In (cd, ct + 1) (sf_imp.tabulate'' candidate reldec_candidate l
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


Lemma selected_not_in :
forall  ef l cd r l0, 
~(In (Some cd ) l) ->
sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate r) ef) =
         (l, l0) ->
sf_spec.first_choices candidate (in_record r) cd ef 0.
Proof.
induction ef; intros.
- simpl in *. inv H0. constructor.
- simpl in *. 
  destruct (sf_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  + destruct p. destruct (sf_imp.option_split
                            (map (sf_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    simpl in *. inv H0. simpl in *.
    intuition.
    apply next_ranking_selected in Heqo.
    constructor.
    intro. eapply sf_spec.selected_candidate_unique in Heqo; eauto.
    subst; auto.
    eapply IHef; eauto.
  + destruct (sf_imp.option_split
              (map (sf_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    inv H0.
    simpl in *.
    apply sf_spec.first_choices_not_selected.
    intro. intuition. unfold sf_spec.selected_candidate in H0.
    destruct H0. apply next_ranking_eliminated in Heqo.
    unfold sf_spec.continuing_ballot in H. intuition.
    eapply IHef; eauto.
Qed.

Lemma increment_same_s : 
forall c running,
NoDup (fst (split running)) ->
exists n, In (c, n + 1) (sf_imp.increment candidate _ running c).
intros. 
destruct (in_dec rel_dec_p c (fst (split running))).
apply in_split in i. destruct i.
exists x. eapply increment_spec in H; eauto.
destruct H. apply H. auto.
exists 0. eapply increment_spec in n; eauto. apply 0.
Qed.


Lemma tabulate''_first_choices : forall ef cd ct es running r
(NODUP : NoDup (fst (split running))),
In (cd, ct) (sf_imp.tabulate'' candidate _ 
                               (fst (sf_imp.option_split
                                      (map (sf_imp.next_ranking candidate reldec_candidate r)
                                           ef))) running) -> 
(forall cnd, ~In cnd (fst (split running)) -> sf_spec.first_choices candidate (in_record r) cnd es 0) ->
Forall (fun x => let (cnd, n) := (x: candidate * N) 
                 in sf_spec.first_choices candidate (in_record r) cnd es (N.to_nat n)) running ->
sf_spec.first_choices candidate (in_record r) cd (es ++ ef) (N.to_nat ct). 
Proof.
induction ef; intros.
- simpl in *. rewrite Forall_forall in *. specialize (H1 _ H). simpl in H1.
  rewrite app_nil_r.  auto.
- simpl in H. 
  assert (Permutation (a :: (es ++ ef)) (es ++ a :: ef)). 
  apply Permutation_middle.
  eapply first_choices_perm; eauto. clear H2.
  destruct (sf_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  +  destruct p. destruct (sf_imp.option_split
                     (map (sf_imp.next_ranking candidate reldec_candidate r)
                          ef)) eqn:?. simpl in *. 
     apply next_ranking_selected in Heqo.
     destruct (rel_dec_p c cd). 
     * subst. 
       { destruct ct. 
         - clear - H NODUP.
           assert (X := increment_same_s cd running NODUP).
           destruct X.
           exfalso. eapply tabulate_not_0; [ | | | apply H]; eauto.
           apply increment_nodup. auto. intro. rewrite N.eq_add_0 in H1. intuition; congruence.
         - assert (exists p', N.to_nat (N.pos p) = S p').
           rewrite Znat.positive_N_nat.
           apply Pnat.Pos2Nat.is_succ. destruct H2. rewrite H2 in *.
           apply sf_spec.first_choices_selected; auto. 
           destruct (in_dec rel_dec_p cd (fst (split running))).
           + rewrite <- (Nnat.Nat2N.id x). eapply IHef; eauto.
             edestruct in_split. apply i.
             eapply tab_inc_s; auto.
             apply increment_nodup. eauto.
             rewrite Heqp. simpl. 
             assert (N.of_nat x+1 = N.pos p).
             assert (1 = (N.of_nat 1)). auto. rewrite H4.
             rewrite <- Nnat.Nat2N.inj_add.
             rewrite Plus.plus_comm. simpl (1 + x)%nat.
             rewrite <- H2. rewrite Nnat.N2Nat.id. auto.
             rewrite H4.
             eauto.
             apply H3. eapply increment_spec in H3; eauto.
           + destruct (in_dec opt_eq_dec_cand (Some cd) l).
             * rewrite <- (Nnat.Nat2N.id x).
               eapply IHef; eauto.
               rewrite Heqp. simpl.
               apply tab_inc_s_l; auto.
               assert (N.of_nat x+1 = N.pos p).
               assert (1 = (N.of_nat 1)). auto. rewrite H3.
               rewrite <- Nnat.Nat2N.inj_add.
               rewrite Plus.plus_comm. simpl (1 + x)%nat.
               rewrite <- H2. rewrite Nnat.N2Nat.id. auto.
               rewrite H3.
               eauto.
             * copy n. eapply increment_spec in n; eauto.
               eapply tabulate_not_in_l in n; eauto.
               assert (1 = (Npos p)). eapply NoDup_In_fst; [ | eauto | eauto ].
               apply tabulate_nodup. apply increment_nodup. auto.
               assert (1%nat = (S x)). rewrite <- H2.
               rewrite <- H4. simpl. auto. 
               rewrite <- H4 in *. inv H5.
               change 0%nat with (0 + 0)%nat. 
               { apply first_choices_app. 
                 - apply H0. auto.
                 - eapply selected_not_in; eauto.
               } 
               apply increment_nodup; auto. constructor.
       }
     * apply sf_spec.first_choices_not_selected. intro.
       apply n. eapply sf_spec.selected_candidate_unique; eauto.
       { destruct (in_dec rel_dec_p cd (fst (split running))).
         - copy i. apply in_split in H2. destruct H2.
           eapply IHef; eauto.
           rewrite Heqp. simpl. eapply tabulate''_same in H; eauto.
           eauto.
           apply increment_nodup. auto. 
           apply increment_neq; auto.
         - eapply IHef; eauto.
           rewrite Heqp. simpl.
           eapply tabulate''_same_notin in H.
           eauto. apply increment_nodup. auto.
           auto. intro.
           apply in_split in H2.
           destruct H2. 
           apply n0.
           eapply increment_neq' in H2. 
           apply in_split_l in H2. auto.
           auto. auto.
       }
  + destruct ( sf_imp.option_split
                 (map (sf_imp.next_ranking candidate reldec_candidate r)
                      ef)) eqn:?.
    simpl in *. 
    apply next_ranking_eliminated in Heqo.
    apply sf_spec.first_choices_not_selected.
    intro. unfold sf_spec.selected_candidate in H2.
    intuition.
    eapply IHef; eauto. rewrite Heqp. simpl. auto.
Qed.

Lemma tabulate'_first_choices : forall l cd ct  r,
In (cd, ct) (sf_imp.tabulate' _ _ (fst (sf_imp.option_split
                                      (map (sf_imp.next_ranking candidate reldec_candidate r)
                                           l)))) -> 
sf_spec.first_choices candidate (in_record r) cd (l) (N.to_nat ct). 
Proof.
intros.
rewrite <- app_nil_l at 1.
eapply tabulate''_first_choices in H. eauto.
constructor.
intros. constructor.
constructor.
Qed.

Lemma tabulate_correct : forall rec election rs election',
sf_imp.tabulate candidate _ rec election = (rs, election') ->
Forall (fun (x: (candidate * N)) => let (cd, fc) := x in
                 sf_spec.first_choices candidate (in_record rec) cd election (N.to_nat fc)) rs.
Proof.
intros.
unfold sf_imp.tabulate in H. destruct (sf_imp.option_split
             (map (sf_imp.next_ranking candidate reldec_candidate rec)
                election)) eqn:?.
assert (PRM := insertion_sort_permutation (sf_imp.tabulate' candidate reldec_candidate l)
                                          (sf_imp.cnle candidate)).
rewrite Forall_forall. intros. destruct x. destruct ((sf_imp.insertionsort (sf_imp.cnle candidate)
         (sf_imp.tabulate' candidate reldec_candidate l),
      sf_imp.drop_none l0)) eqn:?. inv H.
inv Heqp0.
apply Permutation_sym in PRM.
eapply Permutation_in in PRM; eauto.
assert (l = fst (sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate rec) election))).
rewrite Heqp. auto.  subst.
clear H0.
apply tabulate'_first_choices in PRM. auto.
Qed.

(*Lemma leb_false :
forall n0  n,
NPeano.leb n0 n = false ->
n <= n0.
Proof. 
induction n0; intros.
- inv H.
- simpl in *.  destruct n.
  omega. 
  apply IHn0 in H. omega.
Qed.*)


Lemma tabulate_sorted : 
forall rec election rs election',
sf_imp.tabulate _ _ rec election = (rs, election') ->
Sorted (boolCmpToProp (sf_imp.cnle candidate)) rs.
Proof.
intros.
intros.
unfold sf_imp.tabulate in H. destruct (sf_imp.option_split
             (map (sf_imp.next_ranking candidate reldec_candidate rec)
                election)) eqn:?.
inv H. apply insertion_sort_sorted.
intros. unfold sf_imp.cnle. destruct b. 
destruct a. simpl in *. rewrite N.leb_le in *.
rewrite N.leb_gt in *. apply N.lt_le_incl in H. auto.
Qed.

Lemma tabulate_continuing :
forall election rs election' rec,
sf_imp.tabulate _ _ rec election = (rs, election') ->
Forall (fun x =>~ in_record rec x)(fst (split rs)) .
Proof.
  intros. 
unfold sf_imp.tabulate in *.
Check sf_imp.increment.

Lemma increment_not_eliminated : 
forall vs c rec,
~(in_record rec c) ->
Forall (fun cd =>  ~(in_record rec cd)) (fst (split vs)) ->
Forall (fun cd => ~(in_record rec cd)) (fst (split (sf_imp.increment candidate _ vs c))).
Proof.
induction vs; intros.
- simpl in *. auto.
- simpl in *. rewrite Forall_forall in *.
  intros. destruct a.
  destruct (eq_dec c0 c) eqn:?. 
  + simpl in *. destruct (split vs) eqn:?.
    simpl in *. intuition. subst. apply reldec_correct_candidate in Heqb.
    subst. intuition.
    specialize (H0 x). intuition.
  + simpl in *. destruct (split (sf_imp.increment candidate reldec_candidate vs c)) eqn:?.
    simpl in *. intuition.
    * subst. specialize (H0 x). 
      destruct (split vs) eqn:?. simpl in *. intuition.
    * eapply IHvs in H; eauto.
      rewrite Forall_forall in H.
      eapply H; eauto.       
      rewrite Heqp. auto.
      rewrite Forall_forall. intros.
      specialize (H0 x0). destruct (split vs).
      simpl in *. intuition.
Qed.


Lemma tabulate''_continuing : forall ef cd ct  running r,
In (cd, ct) (sf_imp.tabulate'' candidate _ 
                               (fst (sf_imp.option_split
                                      (map (sf_imp.next_ranking candidate reldec_candidate r)
                                           ef))) running) -> 
Forall (fun x => ~(in_record r x)) (fst (split running)) ->
~(in_record r cd). 
Proof.
induction ef; intros.
- simpl in *. rewrite Forall_forall in H0.
  specialize (H0 (cd)). intuition. apply H0; auto.
  apply in_split_l in H. simpl in H. auto.
- simpl in *. destruct ( sf_imp.next_ranking candidate reldec_candidate r a) eqn:?.
  + destruct p. apply next_ranking_selected in Heqo.
    destruct (sf_imp.option_split
                (map (sf_imp.next_ranking candidate reldec_candidate r)
                     ef)) eqn:?. simpl in *.
    apply sf_spec.selected_candidate_not_eliminated in Heqo. 
    eapply increment_not_eliminated in Heqo; eauto. 
    eapply IHef. rewrite Heqp. simpl. eauto.
    auto.
  + destruct (sf_imp.option_split
                (map (sf_imp.next_ranking candidate reldec_candidate r)
                     ef)) eqn:?.
    simpl in *.
    eapply IHef. rewrite Heqp. simpl. eauto.
    eauto.
Qed.

Lemma tabulate''_first_choices_complete : forall ef cd ct es running r
(NODUP : NoDup (fst (split running))), 
(forall cnd cnt, 
cnt <> 0 ->
sf_spec.first_choices candidate (in_record r) cnd es (N.to_nat cnt) -> In (cnd, cnt) running) ->
ct <> 0 -> 
sf_spec.first_choices candidate (in_record r) cd (es ++ ef) (N.to_nat ct) ->
In (cd, ct) (sf_imp.tabulate'' candidate _ 
                               (fst (sf_imp.option_split
                                      (map (sf_imp.next_ranking candidate reldec_candidate r)
                                           ef))) running). 
Proof.
induction ef; intros.
- simpl in *. rewrite app_nil_r in *. intuition.  
Admitted.
(*
- simpl in *. 
  destruct ( sf_imp.next_ranking candidate reldec_candidate r a ) eqn:?.
  + destruct p. simpl.
    destruct (sf_imp.option_split
                (map (sf_imp.next_ranking candidate reldec_candidate r) ef)) eqn:?.
    simpl in *. assert (Permutation (es ++ a :: ef) (a :: (es ++ ef))).
    rewrite Permutation_middle. auto.
    eapply first_choices_perm in H1; eauto.
    clear H0.
    inv H1.
    * apply next_ranking_selected in Heqo; auto.
      eapply sf_spec.selected_candidate_unique in Heqo; eauto. subst.
      assert (l = fst ( sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate r) ef))).
     rewrite Heqp. auto.
     subst. 
Admitted. *)

Lemma tabulate'_first_choices_complete : forall l cd ct r,
ct <> 0 ->
sf_spec.first_choices _ (in_record r) cd l (N.to_nat ct) ->
In (cd, ct) (sf_imp.tabulate' _ _ 
   (fst (sf_imp.option_split (map (sf_imp.next_ranking _ _ r) l)))).
Proof.
intros.
unfold sf_imp.tabulate'.
rewrite <- (app_nil_l l) in H0.
eapply tabulate''_first_choices_complete; eauto; try solve [constructor].
intros. inv H2. assert (cnt = 0). rewrite <- Nnat.Nat2N.inj_iff in H3. 
rewrite Nnat.N2Nat.id in H3. auto. subst. congruence.
Qed.

Lemma tabulate_first_choices_complete : forall l cd ct r,
ct <> 0 -> 
sf_spec.first_choices _ (in_record r) cd l (N.to_nat ct) ->
In (cd, ct) (fst (sf_imp.tabulate _ _ r l)). 
  intros.
  unfold sf_imp.tabulate.
  destruct (sf_imp.option_split
               (map (sf_imp.next_ranking candidate reldec_candidate r) l)) eqn:?.
  eapply Permutation_in.
  apply insertion_sort_permutation.
  assert (l0 = fst (sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate r) l))).
  rewrite Heqp. auto.
  subst.
  eapply tabulate'_first_choices_complete. auto.
  auto.
Qed.


Lemma cnlt_trans : Relations_1.Transitive (boolCmpToProp (sf_imp.cnle candidate)).
Proof.
intro. intros.
destruct x, y, z.
unfold boolCmpToProp in *. simpl in *.
destruct (n <=? n0) eqn:?, (n0 <=? n1) eqn:?, (n <=? n1) eqn:?; auto.
rewrite N.leb_le in *.
rewrite N.leb_gt in *.
eapply N.le_trans in Heqb0; eauto.
rewrite N.le_ngt in *. auto.
Qed.



Lemma tabulate''_participates : forall x election n rec,
In (x, n) (sf_imp.tabulate'' _ _ (fst (sf_imp.option_split 
                                        (map (sf_imp.next_ranking candidate reldec_candidate rec) 
                                             election))) nil) ->
sf_spec.participates candidate x election.
Proof.
induction election; intros.
- simpl in *. inv H.
- simpl in *.
  destruct (sf_imp.next_ranking candidate reldec_candidate rec a) eqn:?.
  + destruct p. 
    destruct ( sf_imp.option_split
                 (map
                    (sf_imp.next_ranking candidate reldec_candidate rec)
                    election)) eqn:?.
    simpl in *.
    destruct (rel_dec_p c x).
    * subst.
      apply next_ranking_selected in Heqo.
      eapply selected_participates. eauto. 
      simpl. auto.
    * apply participates_cons. right.
      eapply IHelection. instantiate (2 := n).
      assert (fst (sf_imp.option_split
                     (map (sf_imp.next_ranking candidate reldec_candidate rec) election)) = l).
      rewrite Heqp; auto. subst.
      eapply tabulate''_same_notin. instantiate (1 := [(c,1)]). 
      repeat constructor. auto. constructor.
      intro. simpl in H0. intuition. auto.
      apply H.
  + destruct (sf_imp.option_split
                     (map
                        (sf_imp.next_ranking candidate reldec_candidate rec)
                        election)) eqn:?.
    simpl in H. assert (l = (fst (sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate rec) election)))).
    rewrite Heqp. auto.
    subst.
    apply participates_cons. right.
    eapply IHelection. eauto.
Qed.

Lemma tabulate_participates : forall x n election rec,
In (x, n) (fst (sf_imp.tabulate _ _ rec election)) ->
sf_spec.participates candidate x election.
intros. unfold sf_imp.tabulate in *.
destruct (sf_imp.option_split
                  (map (sf_imp.next_ranking candidate reldec_candidate rec)
                     election)) eqn:?.
simpl in *.
assert (l = fst (sf_imp.option_split
           (map (sf_imp.next_ranking candidate reldec_candidate rec) election))).
rewrite Heqp. auto.
subst. clear Heqp. 
eapply Permutation_in in H.
eapply tabulate''_participates. apply H.
symmetry. apply insertion_sort_permutation.
Qed.

Lemma get_bottom_votes_is_loser :
forall election rec losers rs election'
(ELIMO : forall c, sf_spec.participates _ c election -> sf_spec.first_choices _ (in_record rec) c election 0 ->
           (in_record rec c)),
sf_imp.tabulate _ _ rec election = (rs, election') ->
sf_imp.get_bottom_votes  _ rs = losers ->
Forall (sf_spec.is_loser candidate (in_record rec) election) losers.
Proof.
intros.
destruct (sf_imp.tabulate _ _ rec election) eqn:?. inv H.
destruct rs. 
- simpl in *. auto.
- simpl in *. destruct p. rewrite N.eqb_refl.
  simpl. rewrite Forall_forall.
  intros. simpl in *.
  destruct H. 
  + subst. assert (SRTD := tabulate_sorted _ _ _ _ Heqp).
    apply Sorted_StronglySorted in SRTD.
    *    assert (CRCT := tabulate_correct _ _ _ _ Heqp).
         rewrite Forall_forall in CRCT.
         specialize (CRCT (x, n)). intuition.
         simpl in *. intuition. clear H0.
         inv SRTD.
         unfold sf_spec.is_loser.
         { repeat split.
           - unfold sf_imp.tabulate in Heqp. unfold
                                           sf_imp.tabulate' in Heqp.
             destruct (sf_imp.option_split
                         (map (sf_imp.next_ranking candidate reldec_candidate rec)
                              election)) eqn:?.
             inv Heqp.
             assert (PRM := insertion_sort_permutation ((sf_imp.tabulate'' candidate reldec_candidate l [])) 
                                                       (sf_imp.cnle candidate)).
             eapply Permutation_sym in PRM.
             eapply Permutation_in in PRM.
             instantiate (1 := (x, n)) in PRM.
             eapply tabulate''_continuing. instantiate (1 := nil). instantiate (1 := election). 
             erewrite Heqp0. simpl. eauto.
             constructor.
             rewrite H0. constructor. auto.
           - eapply tabulate_participates; eauto. instantiate (1:=rec). rewrite Heqp.
             simpl. left. reflexivity.
           - intros.
             assert (N.to_nat n = n0); [ | subst n0 ].
             { eapply sf_spec.sf_first_choices_unique in H0; [ | apply H1]. auto. }
             rewrite Forall_forall in H3.
             destruct H.
             unfold sf_spec.participates in H5.
             destruct H5.
             destruct H5. destruct H6. destruct H6.
             destruct (NPeano.Nat.eq_dec (N.to_nat n) m). 
             + omega.
             + cut (In (c', (N.of_nat m)) rs). 
               * intros.
                 apply H3 in H8. unfold boolCmpToProp in H8.
                 simpl in *. destruct (n <=? N.of_nat m) eqn:?; try contradiction.
                 apply N.leb_le in Heqb.  
                 edestruct (rel_dec_p c' x).
                 subst.
                 eapply sf_spec.sf_first_choices_unique in H4; [ | apply H1]. intuition.
                 rewrite <- (Nnat.Nat2N.id m) in H4.
                 apply tabulate_first_choices_complete in H4. 
                 rewrite Heqp in H4. simpl in H4. 
                 destruct H4. congruence.
                 destruct (n <=? N.of_nat m) eqn:?; auto.
                 rewrite N.leb_le in Heqb0.
                 rewrite N.lt_eq_cases in Heqb0.
                 destruct Heqb0. rewrite Znat.N2Z.inj_lt in H9. 
                 rewrite (Znat.Nat2Z.inj_le (N.to_nat n) m). rewrite Znat.N_nat_Z in *.
                 rewrite Znat.nat_N_Z in *. rewrite BinInt.Z.lt_eq_cases. auto.
                 subst. rewrite (Nnat.Nat2N.id) in *. intuition.
                 rewrite N.leb_gt in Heqb0. clear - Heqb.
                 rewrite Znat.N2Z.inj_le in Heqb.
                 rewrite Znat.nat_N_Z in *.
                 rewrite Znat.Nat2Z.inj_le.
                 rewrite Znat.N_nat_Z. auto.
                 intro. rewrite H9 in *.
                 eapply ELIMO in H4. auto.
                 unfold sf_spec.participates.
                 exists x0.
                 eauto.
               * admit.
         } 
    *  apply cnlt_trans.
  + assert (In (x, n) (filter
              (fun x0 : candidate * N =>
               let (_, v') := x0 in n =? v') rs)).
    rewrite filter_In. split.
    * rewrite in_map_iff in H. destruct H. destruct x0. simpl in H. intuition.
      subst. rewrite filter_In in H1. intuition.
      apply N.eqb_eq in H0. subst.
      auto.
    * symmetry. symmetry. apply N.eqb_refl .
    * clear H.
      rewrite filter_In in H0. destruct H0.
      assert (SRTD := tabulate_sorted _ _ _ _ Heqp).
      apply Sorted_StronglySorted in SRTD.
      assert (CRCT := tabulate_correct _ _ _ _ Heqp).
      rewrite Forall_forall in CRCT.
      inv SRTD.
      simpl in *. specialize (CRCT ((x, n))).
      intuition. clear H1.
      unfold sf_spec.is_loser.
      split.
      split.
      admit. (*TODO*)
      admit.
      intros ? ? ? [??] ? ?.
      eapply sf_spec.sf_first_choices_unique in H5; eauto. subst.
      rewrite Forall_forall in H4.
      specialize (H4 (c', (N.of_nat m))).
      destruct (rel_dec_p c c').
      subst.
      assert (CRCT := tabulate_correct _ _ _ _ Heqp).
      rewrite Forall_forall in CRCT.
      specialize (CRCT (c', n)). simpl in CRCT. intuition.
      clear H8.
      eapply sf_spec.sf_first_choices_unique in H7; eauto.
      subst.
      auto.
      assert (In (c', N.of_nat m) rs).
      rewrite <- Nnat.Nat2N.id in H7.
      apply tabulate_first_choices_complete in H7.
      rewrite Heqp in *. simpl in H7. destruct H7.
      inv H5. intuition.
      auto.
      intro.
      rewrite H5 in *. clear H5.
      apply ELIMO in H7; auto.
      intuition.
      unfold boolCmpToProp in H8. simpl in H8.
      destruct (n <=? N.of_nat m) eqn:?; intuition.
      apply N.leb_le in Heqb. admit.
      apply cnlt_trans.
Qed.


Lemma last_item_in :
forall l w n,
sf_imp.last_item candidate l = Some (w,n) ->
In (w,n) l.
Proof.
induction l; intros.
simpl in *. congruence.
simpl in *. destruct l. inv H. auto.
right. auto.
Qed.



Lemma tabulate_total_selected : forall r election election' vs,
sf_imp.tabulate _ _ r election = (vs, election') ->
sf_spec.total_selected candidate (in_record r) election (length election').
Proof.
  intros. unfold sf_imp.tabulate in *.
  destruct (sf_imp.option_split
             (map (sf_imp.next_ranking candidate reldec_candidate r) election)) eqn:?.
  simpl in *. inv H.
  generalize dependent l0. 
  revert r  election l.
  induction election; intros.
  -   simpl in *. inv Heqp. constructor.
  - simpl in *. destruct (sf_imp.next_ranking candidate reldec_candidate r a) eqn:?.
    + repeat dlp. 
      inv Heqp. simpl in *. apply sf_spec.total_continuing.
      apply next_ranking_selected in Heqo. 
      unfold sf_spec.selected_candidate in *. intuition.
      eapply IHelection. eauto.
    + dlp. inv Heqp. simpl in *.
      apply sf_spec.total_exhausted.
      eapply next_ranking_eliminated; eauto.
      eapply IHelection; eauto.
Qed.


Lemma last_item_cons :
forall h t l,
sf_imp.last_item candidate (h :: t) = Some l ->
(t = nil /\ h = l) \/ sf_imp.last_item candidate t = Some l.
induction t; intros.  
- simpl in *. inv H. auto.
- simpl in *. right.
  auto.
Qed.


Lemma tabulate_not_in : 
  forall (rec : sf_imp.record candidate)
         (election : sf_imp.election candidate) (rs : list (candidate * nat))
         (election' : sf_imp.election candidate) cd,
    sf_imp.tabulate candidate reldec_candidate rec election = (rs, election') ->
    ~In cd (fst (split rs)) -> 
    sf_spec.first_choices candidate (in_record rec) cd election 0.
Proof.
intros. 
eapply tabulate_correct in H. rewrite Forall_forall in H.
specialize (H (cd, 0)).  simpl in *. apply H.
Abort. 



Lemma ss_last :
forall l c n,
StronglySorted (boolCmpToProp (sf_imp.cnle candidate)) l ->
sf_imp.last_item candidate l = Some (c, n) ->
Forall (fun (r : candidate * nat) => let (_, y) := r in y <= n) l.
Proof.
induction l; intros.
- simpl in *. intuition.
- apply last_item_cons in H0.  
  rewrite Forall_forall; intros.
  intuition. subst.
  inv H1. auto. inv H0.
  inv H.
  destruct H1.
  + subst. destruct x. 
    rewrite Forall_forall in H5.
    specialize (H5 (c, n)).
    apply last_item_in in H2. intuition.
    unfold boolCmpToProp in H.
    simpl in *.
    destruct (NPeano.leb n0 n) eqn:?; try contradiction.
    rewrite NPeano.leb_le in Heqb. auto.
  + eapply IHl in H2; eauto.
    rewrite Forall_forall in H2.
    apply H2.  auto.
Qed.


Lemma run_election'_correct : 
  forall fuel election winner rec' rec tbreak
         (TB : forall c x, tbreak c = Some x -> In x c) 
         (N0 : forall c, sf_spec.participates _ c election -> 
                           sf_spec.first_choices _ (in_record rec) c election 0 ->
                           in_record rec c),
    sf_imp.run_election' candidate _ tbreak election rec fuel = (Some winner, rec') ->
    sf_spec.winner candidate election (in_record rec) winner.
induction fuel; intros.
- simpl in *. congruence.
- simpl in *. destruct (sf_imp.tabulate candidate reldec_candidate rec election) eqn:?; 
                       simpl in *; try congruence.
  destruct (sf_imp.last_item candidate l) eqn:?; try congruence.
  destruct p.
  destruct (sf_imp.gtb_nat (n * 2) (length e)) eqn:?.
  + inv H.
    apply sf_spec.winner_now. unfold sf_spec.majority.
    intros. assert (winner_votes = n).
    { apply tabulate_correct in Heqp.
      rewrite Forall_forall in Heqp. specialize (Heqp (winner, n)).
      apply last_item_in in Heqo. intuition.
      eapply sf_spec.sf_first_choices_unique in H1; eauto. }
    subst. 
    assert (total_votes = (length e)).
    { apply tabulate_total_selected in Heqp.
      eapply total_selected_unique; eauto. }
    subst. 
    rewrite sf_imp.gtb_nat_gt in Heqb. auto. apply _.
  + unfold sf_imp.find_eliminated_noopt in *. 
    destruct (tbreak (sf_imp.get_bottom_votes candidate l)) eqn:?. 
    * rename c0 into loser.
      rename Heqo0 into TBREAK.
      copy Heqp. rename H0 into ISLOSER.
      eapply get_bottom_votes_is_loser in ISLOSER; eauto.
      rewrite Forall_forall in ISLOSER.
      eapply TB in TBREAK.
      apply ISLOSER in TBREAK. 
      { eapply sf_spec.winner_elimination.
        - unfold sf_spec.no_majority. 
          intro. destruct H0.
          assert (~ sf_spec.majority _ (in_record rec) election c).
          { intro.
            unfold sf_spec.majority in *.
            specialize (H1 (length e) n).
            copy Heqp.
            apply tabulate_total_selected in H2. intuition. 
            apply tabulate_correct in Heqp. 
            rewrite Forall_forall in Heqp.
            specialize (Heqp (c, n)). simpl in *.
            apply last_item_in in Heqo. intuition.
            rewrite <- sf_imp.gtb_nat_gt in H4. congruence.
            apply _.
          }
          copy Heqp. 
          apply tabulate_sorted in Heqp.
          clear - Heqp Heqo H0 H1 H2 N0.
          destruct (majority_not_0 _ _ _ _ H0). intuition. 
          rename H4 into X0. rename H3 into FCX.
          apply Sorted_StronglySorted in Heqp; [ |  apply cnlt_trans].
          eapply ss_last in Heqp; eauto.
          rewrite Forall_forall in *.
          apply H1. clear H1. intro; intros.
          assert (winner_votes = n).
          { apply last_item_in in Heqo.
            apply tabulate_correct in H2.
            rewrite Forall_forall in H2. eapply H2 in Heqo; clear H2.
            eapply sf_spec.sf_first_choices_unique; eauto. }  
          subst.
          unfold sf_spec.majority in H0.
          copy FCX.
          apply tabulate_first_choices_complete in H3; auto.
          rewrite H2 in *. simpl in H3.
          specialize (Heqp (x, x0)).
          intuition.
          eapply H0 in FCX; eauto. omega. 
        - eauto.
        - rewrite update_eliminated_in_rec_eq_noc.
          eapply IHfuel.
          + eauto.
          + intros. edestruct (rel_dec_p c0 loser).
            * subst. unfold in_record. exists [loser]. 
              intuition.
            * apply N0 in H0. unfold in_record in *. 
              destruct H0.
              exists x. intuition.
              clear - H1 n0.
              eapply first_choices_rec_0; eauto.
          + apply H.
      }
    * congruence.
Qed.

Lemma no_dup_map_allc :  forall allc,
NoDup allc ->
NoDup (fst (split (map (fun x : candidate => (x, 0)) allc))).
Proof.
induction allc; intros.
- simpl. auto.
- simpl. inv H.
  destruct ( split (map (fun x : candidate => (x, 0)) allc) ) eqn:?.
  assert (l = fst (split (map (fun x : candidate => (x, 0)) allc))).
  rewrite Heqp. auto. subst.
  simpl in *. constructor; auto. intuition.   clear - H2 H reldec_correct_candidate.
  apply H2. apply in_split in H. intuition_nosplit. 
  apply in_map_iff in H. destruct H. intuition. inv H0. auto.
Qed.

Lemma nodup_not_in_filter :
forall allc c l,
NoDup allc ->
~ In c
         (map fst
            (filter
               (fun x : candidate * nat =>
                let (_, ct) := x in EqNat.beq_nat ct 0)
               (sf_imp.tabulate'' candidate reldec_candidate l
                  (sf_imp.increment candidate reldec_candidate
                     (map (fun x : candidate => (x, 0)) allc) c)))).
Proof.
intros. intro.
apply in_map_iff in H0. destruct H0. destruct H0. destruct x. simpl in *. subst.
apply filter_In in H1. destruct H1. apply EqNat.beq_nat_true_iff in H1.
subst. edestruct increment_same_s. Focus 2. 
 eapply tabulate_not_0. Focus 2. eauto. apply increment_nodup. 
instantiate (1:=map (fun x : candidate => (x, 0)) allc). apply no_dup_map_allc; auto.
auto.
eauto. apply no_dup_map_allc. auto.
Qed.

Lemma tabulate_0_running :
forall (c: candidate) l running
(NODUP: NoDup (fst (split (running)))), 
In (c, 0) (sf_imp.tabulate'' _ _ l running) ->
In (c, 0) running.
Proof.
induction l. 
- intros. simpl in *. auto.
- intros. simpl in *. destruct a.
  destruct (rel_dec_p c c0). 
  + subst. exfalso. 
    edestruct (increment_same_s c0).
    eauto. 
    eapply tabulate_not_0. 
    * apply increment_nodup. eauto. 
    * apply H0.
    * auto.
    * eauto.
  + apply IHl in H. 
    eapply increment_neq' in H; auto.
    apply increment_nodup. auto.
  + apply IHl in H; auto.
Qed.

Lemma find_0s_correct : 
forall allc election c
(PART: forall c, sf_spec.participates _ c election -> In c allc),
NoDup allc ->
In c (sf_imp.find_0s candidate reldec_candidate allc election) ->
sf_spec.first_choices _ (in_record nil) c election 0.
Proof.
intros. (*destruct (classic (sf_spec.participates _ c election)). rename H1 into PTCPT.*)
induction election; intros.
- constructor.
- unfold sf_imp.find_0s in *. simpl in *. 
  destruct (sf_imp.next_ranking candidate reldec_candidate [] a) eqn:?.
  + destruct p. destruct (sf_imp.option_split
                            (map (sf_imp.next_ranking candidate reldec_candidate [])
                                 election)) eqn:?.
    simpl in *. destruct (rel_dec_p c0 c). 
    * subst.
      eapply nodup_not_in_filter in H. exfalso. apply H. apply H0.
    * apply sf_spec.first_choices_not_selected. 
      intro. apply next_ranking_selected in Heqo.
      eapply sf_spec.selected_candidate_unique in Heqo; eauto.
      apply IHelection; eauto. intros. apply PART.
      apply participates_cons. auto.
      apply in_map_iff.
      apply in_map_iff in H0. intuition_nosplit.
      exists x. destruct x. simpl in H0. subst. intuition.
      apply filter_In in H1. apply filter_In. intuition.
      { destruct (classic (In (c, n0)
                            (sf_imp.tabulate'' candidate reldec_candidate l
                                               (map (fun x : candidate => (x, 0)) allc)))).
        - eapply tabulate''_same; [ | | | | exact H0]. apply increment_nodup.
          + apply no_dup_map_allc. auto. 
          + apply no_dup_map_allc. auto. 
          + apply increment_neq; eauto.
            specialize (PART c). apply in_map_iff. exists c. split.
            * reflexivity. 
            * apply EqNat.beq_nat_true_iff in H2. subst.
              apply tabulate_0_running in H1. apply in_map_iff in H1.
              destruct H1. destruct H1. inv H1. auto. apply no_dup_map_allc. auto.
          + rewrite (EqNat.beq_nat_true_iff) in H2. subst. 
            eapply tabulate_0_running. apply no_dup_map_allc; auto.
            eauto.
        - eapply tabulate''_same in H0. 
          + exfalso. apply H1. apply H0.
          + apply increment_nodup; auto.
            apply no_dup_map_allc; auto.
          + apply no_dup_map_allc; auto.
          + eapply increment_neq; auto.
            apply in_map_iff. exists c.
            intuition. apply EqNat.beq_nat_true_iff in H2. subst. 
            apply tabulate_0_running in H0. eapply increment_neq' in H0; auto.
            apply in_map_iff in H0; intuition_nosplit; auto.
            apply increment_nodup. apply no_dup_map_allc. auto.
          + apply in_map_iff. exists c. intuition. apply EqNat.beq_nat_true_iff in H2. subst. 
            apply tabulate_0_running in H0. eapply increment_neq' in H0; auto.
            apply in_map_iff in H0; intuition_nosplit; auto.
            apply increment_nodup. apply no_dup_map_allc. auto.
      }
  + destruct (sf_imp.option_split
                    (map (sf_imp.next_ranking candidate reldec_candidate [])
                       election)) eqn:?.
    simpl in *.
    apply IHelection in H0; auto.
    * constructor. intro. unfold sf_spec.selected_candidate in H1.
      intuition_nosplit. apply next_ranking_eliminated in Heqo.
      unfold sf_spec.continuing_ballot in *. intuition.
      auto.
    * intros. apply PART. apply participates_cons; auto.
Qed.

Lemma find_0s_complete :
  forall election allc c,
 sf_spec.first_choices candidate
     (in_record [sf_imp.find_0s candidate reldec_candidate allc election]) c
     election 0 ->
   sf_spec.participates candidate c election ->
   In c (sf_imp.find_0s candidate reldec_candidate allc election).
Admitted. (*might be hard, can it be worded better?*)
  
Theorem run_election_correct : forall election winner tb rec allc
  (TB : forall c x, tb c = Some x -> In x c)
  (PART : forall c, sf_spec.participates _ c election <-> In c allc) 
  (NODUP : NoDup allc),  
    sf_imp.run_election candidate _ tb election allc = (Some winner, rec) ->
    sf_spec.winner _ election (in_record []) winner.
intros. unfold sf_imp.run_election in H. 
apply run_election'_correct in H; auto.
- eapply winner_eliminate_0s in H; auto. admit.
  intros. eapply find_0s_correct. intros. apply PART. auto.  auto.
  destruct H0. intuition. inv H1. auto. inv H0.
- intros. 
  eexists. simpl. split. left. reflexivity.
  apply find_0s_complete; auto. 
Qed. 


