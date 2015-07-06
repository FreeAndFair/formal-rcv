(* 
Copyright (c) 2013, Gregory M. Malecha
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met: 

1. Redistributions of source code must retain the above copyright notice, this
   list of conditions and the following disclaimer. 
2. Redistributions in binary form must reproduce the above copyright notice,
   this list of conditions and the following disclaimer in the documentation
   and/or other materials provided with the distribution. 

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The views and conclusions contained in the software and documentation are those
of the authors and should not be interpreted as representing official policies, 
either expressed or implied, of the FreeBSD Project.
https://github.com/coq-ext-lib/coq-ext-lib/blob/master/theories/Core/RelDec.v *)

Require Import Coq.Bool.Bool.

Set Implicit Arguments.
Set Strict Implicit.

Class RelDec (T : Type) (equ : T -> T -> Prop) : Type :=
{ rel_dec : T -> T -> bool }.

Arguments rel_dec {_} {equ} {_} _ _.
Arguments rel_dec _ _ _ !x !y.

Class RelDec_Correct T (equ : T -> T -> Prop) (ED : RelDec equ) : Prop :=
{ rel_dec_correct : forall x y : T, rel_dec x y = true <-> equ x y }.

Notation "a ?[ r  ]  b" := (@rel_dec _ r _ a b) (at level 30, b at next level).

Definition eq_dec {T : Type} {ED : RelDec (@eq T)} := rel_dec.

Section neg_rel_dec_correct.
  Context {T} {R:T -> T -> Prop} {RD:RelDec R} {RDC:RelDec_Correct RD}.

  Definition neg_rel_dec_correct : forall {x y}, ~R x y <-> rel_dec x y = false.
  Proof. intros x y. destruct (bool_dec (rel_dec x y) true) ; constructor ; intros ;
    repeat
      match goal with
      | [ |- ~ _ ] => unfold not ; intros
      | [ H1 : ?P, H2 : ~?P |- _ ] => specialize (H2 H1) ; contradiction
      | [ H1 : ?P = true, H2 : ?P = false |- _ ] => rewrite H1 in H2 ; discriminate
      | [ H1 : ?P <> true |- ?P = false ] => apply not_true_is_false ; exact H1
      | [ H1 : ?rel_dec ?a ?b = true, H2 : ~?R ?a ?b |- _ ] =>
          apply rel_dec_correct in H1
      | [ H1 : ?rel_dec ?a ?b = false, H2 : ?R ?a ?b |- _ ] =>
          apply rel_dec_correct in H2
      end.
  Qed.
End neg_rel_dec_correct.

Section rel_dec_p.
  Context {T} {R:T -> T -> Prop} {RD:RelDec R} {RDC:RelDec_Correct RD}.

  Definition rel_dec_p (x:T) (y:T) : {R x y} + {~R x y}.
  Proof. destruct (bool_dec (rel_dec x y) true) as [H | H].
    apply rel_dec_correct in H ; eauto.
    apply not_true_is_false in H ; apply neg_rel_dec_correct in H ; eauto.
  Qed.

  Definition neg_rel_dec_p (x:T) (y:T) : {~R x y} + {R x y}.
  Proof. destruct (rel_dec_p x y) ; [ right | left ] ; auto. Qed.
End rel_dec_p.

Section lemmas.
  Variable T : Type.
  Variable eqt : T -> T -> Prop.
  Variable r : RelDec eqt.
  Variable rc : RelDec_Correct r.

  Theorem rel_dec_eq_true : forall x y,
    eqt x y -> rel_dec x y = true.
  Proof.
    intros. eapply rel_dec_correct in H. assumption.
  Qed.

  Theorem rel_dec_neq_false : forall x y,
    ~eqt x y -> rel_dec x y = false.
  Proof.
    intros. remember (x ?[ eqt ] y).
    symmetry in Heqb.
    destruct b; try reflexivity.
    exfalso. eapply (@rel_dec_correct _ _ _ rc) in Heqb. auto.
  Qed.

  Require Import RelationClasses.

  Theorem rel_dec_sym : Symmetric eqt -> forall x y,
    x ?[ eqt ] y = y ?[ eqt ] x.
  Proof.
    intros.
    remember (x ?[ eqt ] y); remember (y ?[ eqt ] x); intuition.
    destruct b; destruct b0; auto.
    { symmetry in Heqb; symmetry in Heqb0.
      eapply (@rel_dec_correct _ _ _ rc) in Heqb.
      symmetry in Heqb.
      eapply (@rel_dec_correct _ _ _ rc) in Heqb.
      congruence. }
    { symmetry in Heqb; symmetry in Heqb0.
      eapply (@rel_dec_correct _ _ _ rc) in Heqb0.
      symmetry in Heqb0.
      eapply (@rel_dec_correct _ _ _ rc) in Heqb0.
      congruence. }
  Qed.
End lemmas.