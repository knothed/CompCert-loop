(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*    David Knothe, FZI Research Center for Information Technology     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Properties of executions and behaviors in determinate semantics. *)

Require Import String.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Events.
Require Import Tracex.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Behaviors.
Require Import SmallstepBehaviors.
Require Import Equality.


Ltac subst_list :=
  match goal with
  | [ H: nil = ?a ** ?b |- _ ] => symmetry in H; subst_list
  | [ H: ?a ** ?b = nil |- _ ] => apply app_eq_nil in H as []; subst a b
  | [ H: ?e :: nil = ?a ** ?b |- _ ] => symmetry in H; subst_list
  | [ H: ?a ** ?b = ?e :: nil |- _ ] => apply app_eq_unit in H as [[] | []]; subst a b
end.


(** * Lemmata about single_events semantics *)

Section SINGLE_EVENTS.

Variable L: semantics.
Hypothesis SE: single_events L.

Ltac use_SE H :=
  match type of H with
  | Step L ?s1 ?t ?s2 =>
    let t' := fresh "t" in let H' := fresh "H" in
    pose proof H as H'; apply SE in H';
    destruct t as [|? t']; [| destruct t'; [| simpl in H'; lia ] ]
  end. 

Lemma split_event_step_E0:
  forall s1 s2 e,
  Star L s1 (e::nil) s2 ->
  exists s1' s2', Star L s1 E0 s1' /\ Step L s1' (e::nil) s2' /\ Star L s2' E0 s2.
Proof.
  intros. dependent induction H.
  subst_list.
  * apply IHstar in SE as [s2' [s3' [? []]]]; auto.
    exists s2', s3'. split; auto. econstructor; eauto.
  * exists s1, s2. split; auto. constructor.
Qed.

Lemma split_first_event:
  forall s1 s2 t e,
  Star L s1 (e :: t) s2 ->
  exists s, Star L s1 (e::nil) s /\ Star L s t s2.
Proof.
  intros. dependent induction H; intros.
  use_SE H.
  * apply IHstar in SE as [s' []]; auto. exists s'. split; auto. econstructor; eauto. simpl in H1. now subst.
  * inv H1. exists s2. split; auto. apply star_one; auto.
Qed.

Lemma split_last_event:
  forall s1 s2 t e,
  Star L s1 (t ++ e::nil) s2 ->
  exists s, Star L s1 t s /\ Star L s (e::nil) s2.
Proof.
  intros. generalize dependent s1. dependent induction t; intros.
  * exists s1. split; auto. constructor.
  * replace ((a :: t) ++ e :: nil) with (a :: (t ++ e :: nil)) in H by traceEq.
    apply split_first_event in H as [s1' []]. apply IHt in H0 as [s2' []].
    exists s2'. split; auto. eapply star_trans; eauto.
Qed.

Lemma split_star:
  forall s1 s2 t1 t2,
  Star L s1 (t1**t2) s2 ->
  exists s', Star L s1 t1 s' /\ Star L s' t2 s2.
Proof.
  intros. generalize dependent s1. induction t1; intros.
  * exists s1. split; auto. constructor.
  * replace ((a::t1)**t2) with (a::(t1**t2)) in H by traceEq. apply split_first_event in H as [s1' []].
    apply IHt1 in H0 as [s' []]. exists s'. split; auto. eapply star_trans; eauto.
Qed.

Lemma split_event_step:
  forall s1 s2 t1 t2 e,
  Star L s1 (t1 ++ e::t2) s2 ->
  exists s1' s2', Star L s1 t1 s1' /\ Step L s1' (e::nil) s2' /\ Star L s2' t2 s2.
Proof.
  intros. apply split_star in H as [s1' []].
  apply split_first_event in H0 as [s2' []].
  apply split_event_step_E0 in H0 as [s1'' [s2'' [? []]]].
  exists s1'', s2''. repeat split. eapply star_trans; eauto; traceEq. exact H2. eapply star_trans; eauto; traceEq.
Qed.

(** * Behaviors *)

Lemma split_first_event_forever_reactive: forall s e T,
  Forever_reactive L s (Econsinf e T) ->
  exists s', Star L s (e::nil) s' /\ Forever_reactive L s' T.
Proof.
  intros. inv H. destruct t. easy.
  apply split_first_event in H1 as [s1 []].
  case t in *.
  + inv H0. exists s2. split; auto. eapply star_trans; eauto.
  + inv H0. exists s1. split; auto. rewrite <- Econsinf_assoc. econstructor; eauto. easy.
Qed.

Lemma split_forever_reactive: forall s t T,
  Forever_reactive L s (t***T) ->
  exists s', Star L s t s' /\ Forever_reactive L s' T.
Proof.
  intros. generalize dependent s. induction t; intros. exists s. split; auto; constructor.
  rewrite Econsinf_assoc in H. apply split_first_event_forever_reactive in H as [s' []]; auto.
  apply IHt in H0 as [s'' []].
  exists s''. split; auto. eapply star_trans; eauto.
Qed.

Lemma split_event_step_forever_reactive: forall s e t T,
  Forever_reactive L s (t *** Econsinf e T) ->
  exists s1 s2, Star L s t s1 /\ Step L s1 (e::nil) s2 /\ Forever_reactive L s2 T.
Proof.
  intros. apply split_forever_reactive in H as [s1 []].
  apply split_first_event_forever_reactive in H0 as [s2 []].
  apply split_event_step_E0 in H0 as [s1' [s2' [? []]]].
  exists s1', s2'. repeat split. eapply star_trans; eauto; traceEq. exact H2. rewrite <- E0_left_inf. eapply star_forever_reactive; eauto.
Qed.

End SINGLE_EVENTS.


(** * Lemmata requiring determinacy *)

Section DETERMINATE.

Variable L: semantics.
Hypothesis DET: determinate L.

Ltac use_SE H :=
  match type of H with
  | Step L ?s1 ?t ?s2 =>
    let t' := fresh "t" in let H' := fresh "H" in
    pose proof H as H'; apply DET in H';
    destruct t as [|? t']; [| destruct t'; [| simpl in H'; lia ] ]
  end. 

Ltac use_DET :=
  match goal with
  | [ H1: Step L ?s nil ?s1, H2: Step L ?s nil ?s2 |- _ ] =>
    assert (s1 = s2) by (eapply DET; eauto); subst s2; clear H2
  | [ H1: Step L ?s (?e::nil) ?s1, H2: Step L ?s (?e::nil) ?s2 |- _ ] =>
    assert (s1 = s2) by (eapply DET; eauto); subst s2; clear H2
  | [ H1: Step L ?s nil ?s1, H2: Step L ?s (?e::?f) ?s2 |- _ ] =>
    let H := fresh "XX" in eapply DET in H1 as [H]; [| apply H2]; inv H
  end.


Lemma cut_star_both_silent:
  forall s s1 s2,
  Star L s E0 s1 -> Star L s E0 s2 ->
  Star L s1 E0 s2 \/ Star L s2 E0 s1.
Proof.
  intros. dependent induction H. now left.
  subst_list. inv H2.
  * right; econstructor; eauto.
  * subst_list. use_DET. now apply IHstar in H3.
Qed.

Lemma cut_star_both_single:
  forall s s1 s2 e,
  Star L s (e::nil) s1 -> Star L s (e::nil) s2 ->
  Star L s1 E0 s2 \/ Star L s2 E0 s1.
Proof.
  intros. dependent induction H.
  subst_list.
  * apply IHstar; auto. inv H2. subst_list; now use_DET.
  * inv H2. subst_list; use_DET. eapply cut_star_both_silent; eauto.
Qed.

Lemma get_first_events_simul:
  forall s s1 s2 e t1 t2,
  Star L s (e::t1) s1 -> Star L s (e::t2) s2 ->
  exists s', Star L s (e::nil) s' /\ Star L s' t1 s1 /\ Star L s' t2 s2.
Proof.
  intros.
  apply split_first_event in H as [s1' []], H0 as [s2' []]; try apply DET.
  pose proof H. eapply cut_star_both_single in H. 2: apply H0.
  destruct H; [ eapply star_trans with (s2:=s1') in H | eapply star_trans with (s2:=s2') in H ]; eauto.
Qed.

Lemma cut_star_same_trace:
  forall s s1 s2 t,
  Star L s t s1 -> Star L s t s2 ->
  Star L s1 E0 s2 \/ Star L s2 E0 s1.
Proof.
  intros. generalize dependent s.
  induction t; intros.
  * eapply cut_star_both_silent; eauto.
  * eapply get_first_events_simul in H as [s' [? []]]; eauto.
Qed.

Lemma cut_star_same_trace_nostep:
  forall s s1 s2 t,
  Star L s t s1 -> Star L s t s2 ->
  Nostep L s2 ->
  Star L s1 E0 s2.
Proof.
  intros. eapply cut_star_same_trace in H as []; eauto.
  inv H. constructor. exfalso. now apply H1 in H2.
Qed.

Corollary cut_star_same_trace_step:
  forall s s1 s2 s1' s2' te1 te2 t,
  Star L s t s1 -> Star L s t s2 ->
  Step L s1 te1 s1' -> Step L s2 te2 s2' ->
  te1 <> E0 /\ te2 <> E0 ->
  s1 = s2.
Proof.
  intros. eapply cut_star_same_trace in H as []; eauto.
  inv H. auto. unfold E0 in H6. subst_list. destruct H3, te1, te2 eqn:?; try easy. use_DET.
  inv H. auto. unfold E0 in H6. subst_list. destruct H3, te1, te2 eqn:?; try easy. use_DET.
Qed.

Corollary cut_star_same_trace_step':
  forall s s1 s2 s1' s2' e1 e2 t,
  Star L s t s1 -> Star L s t s2 ->
  Step L s1 (e1::nil) s1' -> Step L s2 (e2::nil) s2' ->
  s1 = s2.
Proof.
  intros. eapply cut_star_same_trace_step; eauto. easy.
Qed.

Lemma cut_star_one_silent:
  forall s s1 s2 e t,
  Star L s E0 s1 -> Star L s (e::t) s2 ->
  Star L s1 (e::t) s2.
Proof.
  intros. dependent induction H. auto.
  subst_list. apply IHstar. auto.
  inv H2. use_SE H1.
  * simpl in H4. subst. now use_DET.
  * use_DET.
Qed.

Corollary cut_star:
  forall s s1 s2 t1 e t2,
  Star L s t1 s1 -> Star L s (t1++(e::t2)) s2 ->
  Star L s1 (e::t2) s2.
Proof.
  intros. generalize dependent s. dependent induction t1; intros.
  * simpl in *. eapply cut_star_one_silent; eauto.
  * eapply get_first_events_simul with (t1:=t1) (t2:=(t1++(e::t2))) in H as [s' [? []]].
    eapply IHt1; eauto. apply H0.
Qed.

Lemma cut_star_nostep:
  forall s s1 s2 t1 t2,
  Star L s t1 s1 -> Star L s (t1++t2) s2 ->
  Nostep L s2 ->
  Star L s1 t2 s2.
Proof.
  intros. destruct t2.
  * rewrite E0_right in H0. eapply cut_star_same_trace in H as []; eauto.
    inv H. constructor. exfalso. eapply H1; eauto.
  * eapply cut_star; eauto.
Qed.


(** * Behaviors *)

Lemma cut_forever_reactive:
  forall s1 s2 t T,
  Star L s1 t s2 ->
  Forever_reactive L s1 (t***T) ->
  Forever_reactive L s2 T.
Proof.
  intros. apply split_forever_reactive in H0 as [s' []]. 2: apply DET.
  eapply cut_star_same_trace in H; eauto.
  case H; intros.
  * inv H1. destruct t0. easy. eapply cut_star_one_silent in H3; eauto. econstructor; eauto.
  * replace T with (E0 *** T) by eauto. eapply star_forever_reactive; eauto.
Qed.

Lemma cut_forever_silent:
  forall s1 s2 t,
  Star L s1 t s2 ->
  Forever_silent L s1 ->
  Forever_silent L s2 /\ t = E0.
Proof.
  intros. induction H. auto.
  inv H0. unfold E0 in *; use_SE H; use_DET; auto.
Qed.

Lemma same_trace_forever_silent:
  forall s s1 s2 t,
  Star L s t s1 ->
  Star L s t s2 ->
  Forever_silent L s1 ->
  Forever_silent L s2.
Proof.
  intros. eapply cut_star_same_trace in H; eauto. destruct H.
  eapply star_forever_silent; eauto. eapply cut_forever_silent; eauto.
Qed.

Lemma unique_silent_reactive:
  forall s1 t s2 T,
  Star L s1 t s2 ->
  Forever_silent L s2 ->
  Forever_reactive L s1 (t***T) ->
  False.
Proof.
  intros.
  eapply cut_forever_reactive in H1; eauto.
  inv H1. eapply cut_forever_silent in H0; eauto; easy.
Qed.


Lemma no_silent_event:
  forall s1 s2 e t,
  Forever_silent L s1 ->
  Star L s1 (e::t) s2 ->
  False.
Proof.
  intros. rewrite <- E0_left in H0 at 1. eapply split_event_step in H0 as [s1' [s2' [? []]]]. 2: apply DET.
  eapply cut_forever_silent in H as []; eauto. inv H. unfold E0 in H4. use_DET.
Qed.

Lemma no_silent_nostep:
  forall s1 s2 t,
  Forever_silent L s1 ->
  Star L s1 t s2 ->
  Nostep L s2 ->
  False.
Proof.
  intros. eapply cut_forever_silent in H as []; eauto.
  inv H. exact (H1 _ _ H3).
Qed.

Lemma nostep_left_E0: forall s s1 s2 t1 t2,
  Star L s t1 s1 -> Star L s (t1**t2) s2 ->
  Nostep L s1 ->
  t2 = E0 /\ Star L s2 E0 s1.
Proof.
  intros. destruct t2.
  + split; auto. rewrite E0_right in H0. eapply cut_star_same_trace in H as []; eauto.
    inv H. apply star_refl. exfalso. eapply H1; eauto.
  + exfalso. eapply cut_star in H0; eauto. inv H0. eapply H1; eauto.
Qed.

Lemma nostep_right: forall s s1 s2 t1 t2,
  Star L s t1 s1 -> Star L s (t1**t2) s2 ->
  Nostep L s2 ->
  Star L s1 t2 s2.
Proof.
  intros. destruct t2.
  + rewrite E0_right in H0. eapply cut_star_same_trace in H as []; eauto.
    inv H. apply star_refl. exfalso. eapply H1; eauto.
  + eapply cut_star in H0; eauto.
Qed.

Lemma nostep_nostep_same: forall s s1 s2 t1 t2,
  Star L s t1 s1 -> Star L s (t1**t2) s2 ->
  Nostep L s1 -> Nostep L s2 ->
  t2 = E0 /\ s1 = s2.
Proof.
  intros. eapply nostep_left_E0 in H0 as []; eauto.
  split; auto. inv H3. auto. exfalso. eapply H2; eauto.
Qed.

End DETERMINATE.