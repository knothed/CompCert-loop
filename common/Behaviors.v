(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
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

(** Whole-program behaviors *)

Require Import Coqlib.
Require Import Events.
Require Import Tracex.
Require Import Globalenvs.
Require Import Integers.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Behaviors for program executions *)

(** The four possible outcomes for the execution of a program:
- Termination, with a finite trace of observable events
  and an integer value that stands for the process exit code
  (the return value of the main function).
- Divergence with a finite trace of observable events.
  (At some point, the program runs forever without doing any I/O.)
- Reactive divergence with an infinite trace of observable events.
  (The program performs infinitely many I/O operations separated
   by finite amounts of internal computations.)
- Going wrong, with a finite trace of observable events
  performed before the program gets stuck.
*)

Inductive program_behavior: Type :=
  | Terminates: trace -> int -> program_behavior
  | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior
  | Goes_wrong: trace -> program_behavior.

Definition behavior_trace (beh: program_behavior): tracex := match beh with
  | Terminates t r => Tfin t
  | Diverges t => Tfin t
  | Reacts T => Tinf T
  | Goes_wrong t => Tfin t
end.

(** Operations and relations on behaviors *)

Definition not_wrong (beh: program_behavior) : Prop :=
  match beh with
  | Terminates _ _ => True
  | Diverges _ => True
  | Reacts _ => True
  | Goes_wrong _ => False
  end.

Definition behavior_app (t: trace) (beh: program_behavior): program_behavior :=
  match beh with
  | Terminates t1 r => Terminates (t ** t1) r
  | Diverges t1 => Diverges (t ** t1)
  | Reacts T => Reacts (t *** T)
  | Goes_wrong t1 => Goes_wrong (t ** t1)
  end.

Lemma behavior_app_assoc:
  forall t1 t2 beh,
  behavior_app (t1 ** t2) beh = behavior_app t1 (behavior_app t2 beh).
Proof.
  intros. destruct beh; simpl; f_equal; traceEq.
Qed.

Lemma behavior_app_E0:
  forall beh, behavior_app E0 beh = beh.
Proof.
  destruct beh; auto.
Qed.

Definition behavior_prefix (t: trace) (beh: program_behavior) : Prop :=
  exists beh', beh = behavior_app t beh'.

Definition behavior_improves (beh1 beh2: program_behavior) : Prop :=
  beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.

Lemma behavior_improves_refl:
  forall beh, behavior_improves beh beh.
Proof.
  intros; red; auto.
Qed.

Lemma behavior_improves_trans:
  forall beh1 beh2 beh3,
  behavior_improves beh1 beh2 -> behavior_improves beh2 beh3 ->
  behavior_improves beh1 beh3.
Proof.
  intros. red. destruct H; destruct H0; subst; auto.
  destruct H as [t1 [EQ1 [beh2' EQ1']]].
  destruct H0 as [t2 [EQ2 [beh3' EQ2']]].
  subst. destruct beh2'; simpl in EQ2; try discriminate. inv EQ2.
  right. exists t1; split; auto. exists (behavior_app t beh3'). apply behavior_app_assoc.
Qed.

Lemma behavior_improves_bot:
  forall beh, behavior_improves (Goes_wrong E0) beh.
Proof.
  intros. right. exists E0; split; auto. exists beh. rewrite behavior_app_E0; auto.
Qed.

Lemma behavior_improves_app:
  forall t beh1 beh2,
  behavior_improves beh1 beh2 ->
  behavior_improves (behavior_app t beh1) (behavior_app t beh2).
Proof.
  intros. red; destruct H. left; congruence.
  destruct H as [t' [A [beh' B]]]. subst.
  right; exists (t ** t'); split; auto. exists beh'. rewrite behavior_app_assoc; auto.
Qed.
