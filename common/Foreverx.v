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

Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Tracex.
Require Import Smallstep.
Require Import SmallstepBehaviors.
Require Import Determinacy.
Require Import ClassicalEpsilon.
Require Import Equality.

(** This module defines a single, coinductive notion of divergence
    that is strong enough to distinguish between a finite and
    an infinite stream of events. *)

Set Implicit Arguments.

Section Guards.

(*
  An event guard enforces that each event at a finite position in the
  (finite or infinite) stream is emitted in finite time:
    - If the remaning trace t is empty, everything is good.
    - Otherwise: if n has dropped down to 0, an event (t1) must be emitted.
        If no event is emitted, the next index (M) must be smaller than n.

  That the indices n and m are whole numbers instead of, more naturally,
  natural ones, is only an implementation detail to make some coinductive proofs
  of bigstep transformations easier.
*)

Definition event_guard (t: tracex) (n: Z) (t1: trace) (M: Z) :=
  t = X0 \/ (M >= 0 /\ n >= 0 /\ ((n <= 0 -> t1 <> E0) /\ (t1 = E0 -> M < n))).


(* `silent_guard t n` can be used for (bigstep) transitions that never emit
   an event, as a shorthand for `event_guard t (n+1) E0 n`. *)
Definition silent_guard t n := t = X0 \/ n >= 0.


(** Some convenience lemmata about event guards. *)

(*
Lemma ev1: forall t T1 n M,
  n >= 0 -> M >= 0 ->
  event_guard T1 n t M ->
  event_guard (t°°T1) n t M.
Proof.
  intros. destruct H1 as [|[?[?[]]]].
  * destruct t. left. tracexEq. right. repeat split; easy.
  * right. repeat split; auto.
Qed.

Lemma ev2: forall t T1 n M,
  event_guard (t°°T1) n t M ->
  event_guard T1 n t M.
Proof.
  intros. destruct H as [|[?[?[]]]].
  * apply Xapp_X0_inv in H as []; subst. now left.
  * right. repeat split; auto.
Qed.*)

Lemma event_incr_left: forall t n1 n2 t1 M,
  n1 <= n2 ->
  event_guard t n1 t1 M ->
  event_guard t n2 t1 M.
Proof.
  intros. destruct H0 as [|[?[?[]]]]. now left.
  right. repeat split; try lia. intros. apply H2. lia. intros. apply H3 in H4. lia.
Qed.

Lemma event_incr1_left: forall t n t1 M,
  event_guard t n t1 M -> event_guard t (n+1) t1 M.
Proof.
  intros. eapply event_incr_left; eauto. lia.
Qed.

Lemma event_incr1_both: forall t n t1 M,
  event_guard t (n-1) t1 M -> event_guard t n t1 (M+1).
Proof.
  intros. destruct H as [|[?[?[]]]]. now left.
  right. repeat split; try lia. intros. apply H2 in H3. lia.
Qed.

Lemma event_incr2_both: forall t n t1 M,
  event_guard t (n-1-1) t1 M -> event_guard t n t1 (M+2).
Proof.
  intros. destruct H as [|[?[?[]]]]. now left.
  right. repeat split; try lia. intros. apply H2 in H3. lia.
Qed.

Lemma event_incr_both: forall t n d1 d2 t1 M,
  0 <= d2 <= d1 ->
  event_guard t (n-d1) t1 M ->
  event_guard t n t1 (M+d2).
Proof.
  intros. destruct H0 as [|[?[?[]]]]. now left.
  right. repeat split; try lia. intros. apply H2. lia. intros. apply H3 in H4. lia.
Qed.

Lemma event_decr_right: forall t n t1 M M',
  0 < M' <= M ->
  event_guard t n t1 M -> event_guard t n t1 M'.
Proof.
  intros. destruct H0 as [|[?[?[]]]]. now left.
  right. repeat split; auto; try lia. intros. apply H3 in H4. lia.
Qed.

Lemma event_double_both: forall t1 t2 n m,
  event_guard t1 n t2 m ->
  event_guard t1 (2*n) t2 (2*m).
Proof.
  intros. destruct H as [|[? [? []]]]. now left.
  right. repeat split. lia. lia. intros. apply H1. lia. intros. apply H2 in H3. lia.
Qed.

Lemma event_to_silent: forall t n t1 M,
  event_guard t n t1 M ->
  silent_guard t n.
Proof.
  intros. destruct H as [|[?[?[]]]]. now left. now right.
Qed.

Lemma event_silent_E0_equiv: forall t n,
  event_guard t (n+1) E0 n <->
  silent_guard t n.
Proof.
  split; intros.
  * destruct H as [|[?[?[]]]]. now left. right. lia.
  * inv H. now left. right. repeat split; lia.
Qed.

Lemma silent_to_event: forall t n t1,
  silent_guard t (n-1) ->
  event_guard t n t1 (n-1).
Proof.
  intros. destruct H. now left.
  right. repeat split; auto; lia.
Qed.

Lemma emit_event: forall t1 t2 n M,
  event_guard (t1°°t2) n t1 M ->
  silent_guard t2 M.
Proof.
  intros. destruct H as [|[?[?[]]]].
  apply Xapp_X0_inv in H as []; subst. now left.
  right. lia.
Qed.

Lemma guard_incr: forall t n1 n2,
  n1 <= n2 ->
  silent_guard t n1 ->
  silent_guard t n2.
Proof.
  intros. destruct H0. now left. right. lia.
Qed.

Lemma guard_incr1: forall t n,
  silent_guard t (n-1) ->
  silent_guard t n.
Proof.
  intros. destruct H. now left. right. lia.
Qed.

Lemma guard_incr2: forall t n,
  silent_guard t (n-1-1) ->
  silent_guard t n.
Proof.
  intros. destruct H. now left. right. lia.
Qed.

Lemma event_nonneg_left: forall t1 t2 n M,
  event_guard t1 n t2 M ->
  event_guard t1 (Z.max n 0) t2 M.
Proof.
  intros. destruct H as [|[?[?[]]]]. now left.
  right. repeat split; try lia; auto.
  intro. apply H1. lia. intro. apply H2 in H3. lia.
Qed.

End Guards.


Section ForeverX.

Variable L: semantics.

(** Two equivalent definitions of forever_x. *)

CoInductive forever_x_step: state L -> Z -> tracex -> Prop :=
  | forever_x_step_intro: forall s1 t s2 T1 T2 n M,
      Step L s1 t s2 ->
      forever_x_step s2 M T1 ->
      event_guard T2 n t M ->
      t °° T1 = T2 ->
      forever_x_step s1 n T2.

CoInductive forever_x_plus: state L -> Z -> tracex -> Prop :=
  | forever_x_plus_intro: forall s1 t s2 T1 T2 n M,
      Plus L s1 t s2 ->
      forever_x_plus s2 M T1 ->
      event_guard T2 n t M ->
      t °° T1 = T2 ->
      forever_x_plus s1 n T2.


Lemma forever_x_step_nonneg: forall s n t,
  forever_x_step s n t ->
  forever_x_step s (Z.max n 0) t.
Proof.
  intros. inv H. econstructor; eauto. now apply event_nonneg_left.
Qed.


Lemma forever_x_plus_nonneg: forall s n t,
  forever_x_plus s n t ->
  forever_x_plus s (Z.max n 0) t.
Proof.
  intros. inv H. econstructor; eauto. now apply event_nonneg_left.
Qed.

Lemma forever_x_plus_plus: forall s1 t1 s2 t2 n,
  Plus L s1 t1 s2 ->
  t2 <> X0 ->
  forever_x_plus s2 n t2 ->
  forever_x_plus s1 n (t1°°t2).
Proof.
  intros. inv H1. econstructor 1 with (s2:=s3); eauto.
  eapply plus_trans; eauto. destruct H4 as [|[?[?[]]]]. congruence.
  right. repeat split; auto. intros. apply H5 in H7. intro. apply H7. now apply Eapp_E0_inv in H8.
  intro. apply Eapp_E0_inv in H7 as []. auto. tracexEq.
Qed.

Lemma forever_x_plus_star: forall s1 t1 s2 t2 n,
  Star L s1 t1 s2 ->
  t2 <> X0 ->
  forever_x_plus s2 n t2 ->
  forever_x_plus s1 n (t1°°t2).
Proof.
  intros. inv H. tracexEq.
  eapply forever_x_plus_plus; eauto. econstructor; eauto.
Qed.

Lemma forever_x_plus_plus_gen: forall s1 t1 s2 t2 n,
  Plus L s1 t1 s2 ->
  forever_x_plus s2 n t2 ->
  forever_x_plus s1 (Z.max n 0) (t1°°t2).
Proof.
  intros. inv H0. econstructor 1 with (s2:=s3) (M:=Z.max M 0) (t:=t1**t).
  eapply plus_trans; eauto. apply forever_x_plus_nonneg; eauto.
  2: tracexEq.
  destruct H3 as [|[?[?[]]]].
  + apply Xapp_X0_inv in H0 as []; subst. tracexEq. rewrite X0_right.
    destruct t1. now left. right. repeat split; try lia; easy.
  + right. repeat split; try lia; auto.
    intros. enough (t<>E0) by (intro; now apply Eapp_E0_inv in H8). apply H4. lia.
    intros. apply Eapp_E0_inv in H6 as []. apply H5 in H7. lia.
Qed.

Lemma forever_x_plus_star_gen: forall s1 t1 s2 t2 n,
  Star L s1 t1 s2 ->
  forever_x_plus s2 n t2 ->
  forever_x_plus s1 (Z.max n 0) (t1°°t2).
Proof.
  intros. inv H. tracexEq. now apply forever_x_plus_nonneg.
  eapply forever_x_plus_plus_gen; eauto. econstructor; eauto.
Qed.


Lemma forever_x_plus_X0_irrel: forall s n1 n2,
  forever_x_plus s n1 X0 ->
  forever_x_plus s n2 X0.
Proof.
  intros. inv H. econstructor; eauto.
  apply Xapp_X0_inv in H3 as []; subst. now left.
Qed.

Lemma forever_x_step_X0_irrel: forall s n1 n2,
  forever_x_step s n1 X0 ->
  forever_x_step s n2 X0.
Proof.
  intros. inv H. econstructor; eauto.
  apply Xapp_X0_inv in H3 as []; subst. now left.
Qed.

Lemma forever_x_step_monotone: forall s n1 n2 t,
  n1 <= n2 ->
  forever_x_step s n1 t ->
  forever_x_step s n2 t.
Proof.
  intros. inv H0. econstructor; eauto. eapply event_incr_left; eauto.
Qed.

Lemma forever_x_plus_monotone: forall s n1 n2 t,
  n1 <= n2 ->
  forever_x_plus s n1 t ->
  forever_x_plus s n2 t.
Proof.
  intros. inv H0. econstructor; eauto. eapply event_incr_left; eauto.
Qed.

Lemma forever_x_step_star_helper: forall s1 t1 s2 t2 n,
  n >= 0 ->
  Star L s1 t1 s2 ->
  forever_x_step s2 n t2 ->
  exists n', forever_x_step s1 n' (t1°°t2) /\ (n' >= 0).
Proof.
  intros. induction H0.
  + rewrite X0_left. exists n. split; auto.
  + pose proof H1. apply IHstar in H1 as [n' []]. exists (Z.max (n'+1) n). split. econstructor; eauto.
    - right. repeat split; lia.
    - tracexEq.
    - lia.
Qed.

Lemma forever_x_step_star: forall s1 t1 s2 t2 n,
  Star L s1 t1 s2 ->
  forever_x_step s2 n t2 ->
  exists n', forever_x_step s1 n' (t1°°t2).
Proof.
  intros. apply forever_x_step_monotone with (n2:=Z.max n 0) in H0. 2: lia.
  eapply forever_x_step_star_helper in H0 as [? []]; eauto. lia.
Qed.


Section ConvertPlusToStep.

(* Counting the length of a Star *)

Inductive star_n: state L -> nat -> trace -> state L -> Prop :=
  | plus_0: forall s,
      star_n s 0 E0 s
  | plus_S: forall s1 t1 s2 t2 s3 t n,
      Step L s1 t1 s2 -> star_n s2 n t2 s3 -> t = t1 ** t2 ->
      star_n s1 (S n) t s3.

Lemma star_finite: forall s1 t s2,
  Star L s1 t s2 ->
  exists n, star_n s1 n t s2.
Proof.
  intros. induction H. exists O. now constructor.
  destruct IHstar. exists (S x). econstructor; eauto.
Qed.

Lemma plus_finite: forall s1 t s2,
  Plus L s1 t s2 ->
  exists n, star_n s1 (S n) t s2.
Proof.
  intros. inv H. apply star_finite in H1 as [n].
  exists n. econstructor; eauto.
Qed.

Lemma star_n_star: forall s1 t n s2,
  star_n s1 n t s2 ->
  Star L s1 t s2.
Proof.
  intros. induction H; econstructor; eauto.
Qed.

Lemma star_n_extract_event: forall s1 t n s2,
  star_n s1 n t s2 ->
  t <> E0 ->
  exists s1' s2' t1 t2 n1 n2,
    star_n s1 n1 E0 s1' /\
    Step L s1' t1 s2' /\
    star_n s2' n2 t2 s2 /\
    t1 <> E0 /\
    t = t1 ** t2 /\
    n = (n1 + n2 + 1)%nat.
Proof.
  intros. induction H. congruence.
  destruct t1.
  * destruct IHstar_n as [s1'[s2'[t1'[t2'[n1[n2[?[?[?[?[]]]]]]]]]]]. traceEq.
    exists s1', s2', t1', t2', (S n1), n2.
    repeat split; auto. econstructor; eauto. traceEq. lia.
  * exists s1, s2, (e::t1), t2, O, n.
    repeat split; auto. constructor. easy. lia.
Qed.

Lemma star_n_E0_simul_same_length: forall s1 s2 s3 n1 n2 tev
  (DET: determinate L),
  star_n s1 n1 E0 s2 ->
  star_n s1 n2 E0 s2 ->
  Step L s2 tev s3 ->
  tev <> nil ->
  n1 = n2.
Proof.
  intros. generalize dependent n2. dependent induction H; intros.
  * inv H0. auto. symmetry in H4. apply Eapp_E0_inv in H4 as []; subst.
    destruct tev. congruence. eapply DET in H1 as []; eauto. inv H0.
  * symmetry in H1. apply Eapp_E0_inv in H1 as []; subst.
    inv H4. destruct tev. congruence. eapply DET in H as []; eauto. inv H.
    apply IHstar_n with (n2:=n0) in H2; auto.
    symmetry in H6. apply Eapp_E0_inv in H6 as []; subst.
    eapply DET in H as []; eauto. enough (s5=s2) by now subst. auto.
Qed.

Lemma star_n_E0_simul_event_det: forall s s1 s2 s3 s4 n1 n2 t1 t2
  (DET: determinate L),
  star_n s n1 E0 s1 ->
  star_n s n2 E0 s2 ->
  Step L s1 t1 s3 ->
  Step L s2 t2 s4 ->
  t1 <> nil -> t2 <> nil ->
  s1 = s2 /\ n1 = n2.
Proof.
  intros. destruct t1, t2; try congruence.
  pose proof H. pose proof H0. apply star_n_star in H5, H6.
  eapply cut_star_same_trace_step in H5; eauto. subst.
  split; auto. eapply star_n_E0_simul_same_length; eauto.
Qed.

(* Another definition of forever_x, without using a counter *)

CoInductive forever_x_event: state L -> tracex -> Prop :=
  | forever_x_event_X0: forall s1 s2,
      Plus L s1 E0 s2 ->
      forever_x_event s2 X0 ->
      forever_x_event s1 X0
  | forever_x_event_Xapp: forall s1 t s2 T1 T2,
      Plus L s1 t s2 ->
      forever_x_event s2 T1 ->
      t <> nil ->
      t °° T1 = T2 ->
      forever_x_event s1 T2.

Lemma forever_x_event_star: forall s1 t1 s2 t2,
  Star L s1 t1 s2 ->
  forever_x_event s2 t2 ->
  forever_x_event s1 (t1°°t2).
Proof.
  intros. inv H0; destruct t1.
  * econstructor 1 with (s2:=s3); eauto. eapply star_plus_trans; eauto.
  * econstructor 2 with (s2:=s3); eauto. eapply star_plus_trans; eauto. tracexEq. easy.
  * econstructor 2 with (s2:=s3); eauto. eapply star_plus_trans; eauto. tracexEq.
  * econstructor 2 with (s2:=s3) (t:=e::t1**t); eauto. eapply star_plus_trans; eauto. easy. tracexEq.
Qed.

Lemma forever_x_plus_extract_event: forall s n t,
  t <> X0 ->
  forever_x_plus s n t ->
  exists s' t1 t2 n',
    Plus L s t1 s' /\
    forever_x_plus s' n' t2 /\
    t1 <> E0 /\ t = t1 °° t2.
Proof.
  intros. assert (n = Z.of_nat (Z.to_nat n)) by (inv H0; destruct H3; [congruence|lia]).
  remember (Z.to_nat n). rewrite H1 in *. clear H1 Heqn0. induction n0 using strong_ind.
  inv H0. destruct t0.
  - eapply forever_x_plus_plus in H3; eauto. 2: now rewrite X0_left in H.
    destruct H4 as [|[?[?[]]]]. congruence. pose proof (H6 eq_refl).
    apply H1 with (k:=(Z.to_nat M)). lia.
    now rewrite Z2Nat.id by lia.
  - now exists s2, (e::t0), T1, M.
Qed.

Lemma forever_x_plus_to_event: forall s n t,
  forever_x_plus s n t ->
  forever_x_event s t.
Proof.
  cofix CIH; intros.
  destruct (inv_tracex t) as [|[e[t']]].
  - subst. inv H. apply Xapp_X0_inv in H3 as []; subst. econstructor; eauto.
  - subst. assert (e°t' <> X0) by now destruct t'.
  destruct (forever_x_plus_extract_event H0 H) as [s'[t1[t2[n'[?[?[]]]]]]].
  econstructor; eauto.
Qed.

Section Steps.

(* Getting the number of steps until an event happens, classically *)

Context s t (EV: forever_x_event s t) (N: t <> X0).

Definition STEPS n := exists s1 s2 t1 t2,
  star_n s n E0 s1 /\
  Step L s1 t1 s2 /\
  forever_x_event s2 t2 /\
  t1 <> E0 /\
  t = t1 °° t2.

Lemma get_steps_descr: { n | STEPS n }.
  apply constructive_indefinite_description. unfold STEPS.
  inv EV. congruence.
  pose proof H. apply plus_finite in H as [n].
  apply star_n_extract_event in H as [s1'[s2'[t1'[t2'[n1[n2[?[?[?[?[]]]]]]]]]]]; auto.
  exists n1, s1', s2', t1', (t2'°°T1). repeat split; auto.
  eapply forever_x_event_star with (s2:=s2); eauto. now eapply star_n_star in H4.
  tracexEq.
Qed.

End Steps.

Definition to_go: forall s t,
  forever_x_event s t -> Z.
Proof.
  intros. destruct (inv_tracex_dec t) as [[?]|].
  destruct x. apply get_steps_descr in H as [].
  exact (Z.of_nat x). destruct t0; rewrite y; easy.
  exact 0.
Defined.

Lemma to_go_nonneg: forall s t (H: forever_x_event s t),
  to_go H >= 0.
Proof.
  intros. unfold to_go. destruct inv_tracex_dec.
  * destruct s0, x, get_steps_descr. lia.
  * lia.
Qed.

Context (DET: determinate L).

Lemma forever_x_event_to_step': forall s t
  (H: forever_x_event s t),
  forever_x_step s (to_go H) t.
Proof.
  cofix CIH; intros. destruct H.
  * remember (to_go _). clear Heqz. inv p. symmetry in H2. apply Eapp_E0_inv in H2 as []; subst.
    econstructor; eauto. now left. tracexEq.
    Unshelve. inv H1. auto. econstructor; eauto. econstructor; eauto.
  * unfold to_go. destruct inv_tracex_dec. destruct s, x, get_steps_descr. 
    2: { exfalso. subst. now apply Xapp_X0_inv in e0. }
    destruct s as [s1' [s2' [t' [? [? [? [? [?]]]]]]]].
    inv H0.
    + econstructor. eauto. eapply CIH with (H:=H2). right. repeat split. apply to_go_nonneg. lia. auto. easy. tracexEq.
    + symmetry in H7. apply Eapp_E0_inv in H7 as []; subst.
      assert (forever_x_event s3 (t'°°x0)).
      - econstructor; eauto. apply star_n_star in H6. eapply plus_right; eauto.
      - econstructor. eauto. eapply CIH with (H:=H0). 2: tracexEq.
        unfold to_go. destruct inv_tracex_dec. destruct s, x, get_steps_descr.
        2: { exfalso. now apply Xapp_X0_inv in e. }
        destruct s as [s1'' [s2'' [t'' [? [? [? [? [?]]]]]]]].
        eapply star_n_E0_simul_event_det in H1 as []; eauto.
        subst. right. repeat split; lia.
Qed.

Corollary forever_x_event_to_step: forall s t,
  forever_x_event s t ->
  exists n, forever_x_step s n t.
Proof.
  intros. exists (to_go H). now apply forever_x_event_to_step'.
Qed.

Corollary forever_x_plus_to_step: forall s n t,
  forever_x_plus s n t ->
  exists m, forever_x_step s m t.
Proof.
  intros. now apply forever_x_plus_to_event, forever_x_event_to_step in H.
Qed.

End ConvertPlusToStep.

Lemma forever_x_step_to_plus: forall s n t,
  forever_x_step s n t ->
  forever_x_plus s n t.
Proof.
  cofix CIH.
  intros. inv H. econstructor; eauto. now apply plus_one.
Qed.


(** Different definitions of forever_x *)

Definition forever_x s t := forever_x_event s t.

Definition forever_x_to_step := forever_x_event_to_step.

Definition forever_x_of_step s n t (H: forever_x_step s n t): forever_x s t :=
  forever_x_plus_to_event (forever_x_step_to_plus H).

Lemma forever_x_to_plus s t (DET: determinate L):
  forever_x s t -> exists n, forever_x_plus s n t.
Proof.
  intros. apply forever_x_to_step in H as []; auto. apply forever_x_step_to_plus in H. now exists x.
Qed.

Definition forever_x_of_plus := forever_x_plus_to_event.

(** * Relation to normal smallstep execution properties.

  We now have three different definitions of forever_x.
  Given determinacy of the semantics, they are equivalent. Otherwise it is:
  
    forever_x_step --> forever_x_plus --> forever_x(_event) -(DET)-> forever_x_step.
    
  We now prove, where possible, the strongest conversions in both directions without using determinacy. *)

Lemma forever_x_to_silent: forall s,
  forever_x s X0 -> Forever_silent L s.
Proof.
  enough (forall s, forever_x s X0 -> forever_silent_N (step L) lt (globalenv L) O s).
  + intros. eapply forever_silent_N_forever; eauto. apply lt_wf.
  + cofix H. intros. inv H0. econstructor 2; eauto. apply Xapp_X0_inv in H4 as []; now subst.
Qed.

Lemma forever_x_of_silent: forall s,
  Forever_silent L s -> forever_x_step s 0 X0.
Proof.
  intros. generalize dependent s. cofix CO; intros.
  inv H. econstructor; eauto. now left.
Qed.

Lemma forever_x_silent: forall s,
  forever_x s X0 <-> Forever_silent L s.
Proof.
  split; intros. now apply forever_x_to_silent. now eapply forever_x_of_step, forever_x_of_silent.
Qed.

Lemma forever_x_to_finite: forall s t,
  forever_x s (Tfin t) -> exists s', Star L s t s' /\ Forever_silent L s'.
Proof.
  intros. generalize dependent s. induction t using list_length_ind. intros. inv H0.
  + eapply forever_x_to_silent in H4; auto. exists s2. split; auto. now apply plus_star.
  + destruct T1; inv H4. apply H in H2 as [s'[]].
    exists s'. split; auto. eapply plus_star, plus_star_trans; eauto.
    destruct t. congruence. simpl. rewrite app_length. lia.
Qed.

Lemma forever_x_of_finite: forall s t s',
  Star L s t s' -> Forever_silent L s' ->
  exists n, forever_x_step s n (Tfin t).
Proof.
  intros. eapply forever_x_of_silent in H0. eapply forever_x_step_star in H0 as []; eauto. exists x. now rewrite X0_right in H0.
Qed.

Lemma forever_x_finite: forall s t,
  forever_x s (Tfin t) <-> exists s', Star L s t s' /\ Forever_silent L s'.
Proof.
  split; intros. now apply forever_x_to_finite in H. inv H. inv H0. eapply forever_x_of_finite in H1 as []; eauto. now apply forever_x_of_step in H0.
Qed.

Lemma forever_x_to_reactive: forall s t,
  forever_x s (Tinf t) -> Forever_reactive L s t.
Proof.
  intros. generalize dependent s. generalize dependent t. cofix CO; intros.
  inv H. destruct T1; inv H3. econstructor; eauto. eapply plus_star; eauto.
Qed.

Lemma forever_x_of_reactive: forall s t,
  Forever_reactive L s t -> forever_x_event s (Tinf t).
Proof.
  intros. generalize dependent s. generalize dependent t. cofix CO; intros.
  inv H. econstructor; eauto. inv H0. congruence. econstructor; eauto.
Qed.

Lemma forever_x_reactive: forall s t,
  forever_x s (Tinf t) <-> Forever_reactive L s t.
Proof.
  split; intros. now apply forever_x_to_reactive. now apply forever_x_of_reactive.
Qed.

Lemma forever_forever_x: forall s T,
  Forever L s T -> exists t, tracexx_prefix t (Tinf T) /\ forever_x s t.
Proof.
  intros. apply forever_silent_or_reactive in H as [|[t[s'[T'[?[?]]]]]].
  * exists (Tinf T). split. easy. now apply forever_x_reactive.
  * exists (Tfin t). split. econstructor; eauto. eapply forever_x_finite; eauto.
Qed.

Lemma forever_x_forever: forall s t T,
  tracexx_prefix t (Tinf T) ->
  forever_x s t -> Forever L s T.
Proof.
  intros. destruct t; inv H.
  * apply forever_x_finite in H0 as [s' []]. eapply forever_silent_forever_star; eauto. econstructor; eauto.
  * apply forever_x_reactive in H0. now apply forever_reactive_forever. 
Qed.


(** Cutting lemmata *)

Context (DET: determinate L).

Lemma cut_forever_x_step_E0: forall s1 s2 n T,
  forever_x_step s1 n T ->
  Star L s1 E0 s2 ->
  exists m, forever_x_step s2 m T /\ m <= n.
Proof.
  intros. generalize dependent n. dependent induction H0; intros. exists n. split; auto; lia.
  symmetry in H1. apply Eapp_E0_inv in H1 as []. subst. inv H2.
  eapply (sd_determ_3 DET) in H as []; eauto. subst. rewrite X0_left in *.
  destruct H4 as [|[?[?[]]]].
  * destruct T1; inv H. apply IHstar; auto. eapply forever_x_step_X0_irrel; eauto.
  * apply IHstar; auto. eapply forever_x_step_monotone; eauto. pose proof (H5 eq_refl). lia.
Qed.

Lemma cut_forever_x_step': forall s1 s2 n t T,
  forever_x_step s1 n (t°°T) ->
  Star L s1 t s2 ->
  exists m, forever_x_step s2 m T.
Proof.
  intros. destruct T; simpl in H.
  + apply forever_x_of_step, forever_x_finite in H as [s []].
    destruct t0.
    - rewrite E0_right in H. eapply same_trace_forever_silent in H1; eauto.
      eapply forever_x_to_step, forever_x_silent; eauto.
    - eapply cut_star in H; eauto.
      eapply forever_x_to_step, forever_x_finite; eauto.
  + apply forever_x_of_step, forever_x_reactive in H.
    eapply cut_forever_reactive in H; eauto.
    eapply forever_x_to_step, forever_x_reactive; eauto.
Qed.

Lemma cut_forever_x_step: forall s1 s2 n t T,
  forever_x_step s1 n (t°°T) ->
  Star L s1 t s2 ->
  exists m, forever_x_step s2 m T /\ (t = E0 -> m <= n).
Proof.
  intros. destruct t.
  rewrite X0_left in H. eapply cut_forever_x_step_E0 in H as [m []]; eauto.
  eapply cut_forever_x_step' in H as [m]; eauto. now exists m.
Qed.

End ForeverX.