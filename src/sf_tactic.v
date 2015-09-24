Require sf_imp.
Require sf_spec.
Require Import RelDec.
Require Import List.
Require Import Sorted.
Require Import Permutation.
Require Import FunctionalExtensionality.
Require Import Classical.
Import ListNotations.


Definition in_record {candidate} (rec : sf_imp.record candidate) (c : candidate) :=
exists e, In e rec /\ In c e.

Hint Rewrite Forall_forall : rcv.
Hint Rewrite forallb_forall : rcv.
Hint Rewrite existsb_exists : rcv.
Hint Rewrite Bool.negb_true_iff : rcv.
Hint Rewrite Bool.negb_false_iff : rcv.
Hint Rewrite <- @neg_rel_dec_correct : rcv.

Ltac arw := try autorewrite with rcv in *.


Ltac unfold_defs := cbv [sf_imp.no_viable_candidates sf_spec.no_viable_candidates
                         sf_imp.eliminated sf_imp.no_viable_candidates_selection
                        in_record sf_spec.overvote sf_spec.properly_selects
                        sf_spec.does_not_select eq_dec sf_spec.selected_candidate
                        sf_spec.continuing_ballot sf_spec.exhausted_ballot
                        sf_spec.selected_candidate].

Ltac unfold_defs_star := cbv [sf_imp.no_viable_candidates sf_spec.no_viable_candidates
                         sf_imp.eliminated sf_imp.no_viable_candidates_selection in_record 
                         sf_spec.overvote sf_spec.properly_selects
                         sf_spec.does_not_select eq_dec sf_spec.selected_candidate
                         sf_spec.continuing_ballot sf_spec.exhausted_ballot
                         sf_spec.selected_candidate] in *.


Tactic Notation "unfold_defs" "in" "*" := unfold_defs_star.

Ltac copy H :=
match type of H with 
?P => assert P by exact H end.

Ltac destruct_exists :=
repeat
match goal with
| [ H : exists _, _ |- _ ] => destruct H
end.

Ltac intuitione :=
repeat (destruct_exists; intuition).


Ltac dlp := try
        match goal with
        | [ H : context[ let (a, b) := ?X in _ ] |- _ ] => destruct X eqn:?
        end.


Ltac inv H := inversion H; subst; clear H.

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

Ltac completer :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')
           | [ |- forall x, _ ] => intro
           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         (*  | [ H : forall (x : ?P), _, H' : ?P |- _ ] => extend (H H')*)
         end.

Lemma forallb_false_exists :
forall  {A} p (a : list A),
forallb p a = false ->
exists x, In x a /\ p x = false.
Proof.
intros. induction a.
inv H.
simpl in H. rewrite Bool.andb_false_iff in *.
destruct H. exists a. intuition.
intuition. destruct H0.  exists x. simpl. intuition.
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

Ltac intuition_nosplit t :=
repeat
match goal with
| [ H : _ /\ _ |- _ ] => destruct H
| [ H : False |- _] => inv H
| [ H : In _ [] |- _] => inv H
| [ H : eq_dec _ _ = true |- _] => apply t in H; subst
| [ |- eq_dec _ _ = true ] => apply t 
| [ H : _ ?[ eq ] _ = true |- _] => apply t in H; subst
| [|-  _ ?[ eq ] _ = true ] => apply t; subst
| [ H : existsb _ _ = false |- _] => apply existsb_false_forall in H
| [ H : forallb _ _ = false |- _] => apply forallb_false_exists in H
| [ H : (_, _) = (_, _) |- _] => inv H
| [ H : Some _ = Some _ |- _] => inv H
| [ |- ~_ ] => intro
| [ H :  sf_spec.next_ranking _ _ [] _ |- _ ] => inv H
| [ H : exists _, _ |- _ ] => destruct H
end.

Ltac unique :=
repeat match goal with
| [ H : sf_spec.next_ranking _ _ _ ?x, H' : sf_spec.next_ranking _ _ _ ?y |- _ ] =>
  first [ assert (x = y) as Trash by auto ; clear Trash | 
          extend (sf_spec.next_ranking_unique _ _ _ _ _ H H')]
end.

Ltac destruct_ifs :=
repeat
match goal with
| [ H : context[ if ?b then _ else _ ] |- _] => destruct b eqn:?
end. 


Ltac solve_rcv' t := repeat (intros; unfold_defs in *; arw; destruct_exists; 
                           destruct_ifs; intuition_nosplit t; completer; dlp; try subst;
                           try solve [simpl in *; eauto]; 
                          try solve [simpl in *; congruence]).


Ltac solve_rcv t := 
match goal with
| [ |- _ /\ _] => split; solve_rcv' t; []
| _ => solve_rcv' t
end.

