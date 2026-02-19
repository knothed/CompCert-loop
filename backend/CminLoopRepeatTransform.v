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

(** * Apply a CminLoop bigstep transformation multiple times consecutively. *)

Require Import Axioms.
Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Events.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Foreverx.
Require Import Bigstep.
Require Import Behaviors.
Require Import Semantics.
Require Import SemanticsSmallBig.
Require Import Linking.
Require Import Equality.
Require Import Tracex.
Require Import CminLoop.
Require Import CminLoopTransfCommon.
Require Import CminLoopBigSmallEquiv.

Section Context.

(** The single transformation *)

Variable (transform_stmt_once: stmt -> stmt).

Definition transl_function_once (f: function) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_vars)
    f.(fn_stackspace)
    (transform_stmt_once f.(fn_body)).

Definition transl_fundef_once: fundef -> fundef := transf_fundef transl_function_once.
Definition transl_program_once: program -> program := transform_program transl_fundef_once.

Definition match_prog_once: program -> program -> Prop := match_program (fun cu f tf => tf = transl_fundef_once f) eq.

Theorem transl_program_match_once:
  forall p, match_prog_once p (transl_program_once p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

(** Repeating the transformation a fixed number of times *)

Fixpoint transform_stmt (n: nat) (s: stmt) := match n with
  | O => s
  | S n => transform_stmt n (transform_stmt_once s)
end.

Definition transl_function (n: nat) (f: function) :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_vars)
    f.(fn_stackspace)
    (transform_stmt n f.(fn_body)).

Definition transl_fundef (n: nat) (f: fundef) : fundef :=
  transf_fundef (transl_function n) f.

Definition transl_program (n: nat) (p: program) : program :=
  transform_program (transl_fundef n) p.

Definition match_prog (n: nat) (p: program) (tp: program) :=
  match_program (fun cu f tf => tf = transl_fundef n f) eq p tp.

Theorem transl_program_match:
  forall n p, match_prog n p (transl_program n p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Notation "f ∘ g" := (fun x => f (g x)) (at level 50).

Lemma transl_function_succ: forall n, transl_function (S n) = transl_function n ∘ transl_function_once.
Proof.
  intros. apply functional_extensionality. intros. auto.
Qed.

Lemma transl_fundef_succ: forall n, transl_fundef (S n) = transl_fundef n ∘ transl_fundef_once.
  intros. apply functional_extensionality. intros. destruct x. now simpl. auto.
Qed.

Lemma transl_function_zero: transl_function 0 = id.
Proof.
  apply functional_extensionality. intros. unfold transl_function, transf_fundef, transform_stmt. now destruct x.
Qed.

Lemma transl_fundef_zero: transl_fundef 0 = id.
Proof.
  apply functional_extensionality. intros. destruct x. now destruct f. auto.
Qed.

Lemma make_match_once: forall p,
  match_prog_once p (transl_program_once p).
Proof.
  intros. constructor. apply match_globdef_total_from_prog_defs. now split.
Qed.

Lemma make_match_n: forall n p,
  match_prog n p (transl_program n p).
Proof.
  intros. constructor. apply match_globdef_total_from_prog_defs. now split.
Qed.

Section Transform.

Context (transl_exec_correct_once:
  forall prog tprog, match_prog_once prog tprog ->
   (forall m1 f vargs t m2 vres out,
    eval_funcall (Genv.globalenv prog) m1 f vargs t m2 vres out ->
    eval_funcall (Genv.globalenv tprog) m1 (transl_fundef_once f) vargs t m2 vres out)
/\ (forall f v e1 m1 s t e2 m2 out,
    exec_stmt (Genv.globalenv prog) f v e1 m1 s t e2 m2 out ->
    exec_stmt (Genv.globalenv tprog) (transl_function_once f) v e1 m1 (transform_stmt_once s) t e2 m2 out)).

Context (d: Z).
Context (transl_execinf_correct_once:
  forall prog tprog, match_prog_once prog tprog ->
  forall m f vargs n t,
  evalinf_funcall (Genv.globalenv prog) m f vargs n t ->
  evalinf_funcall (Genv.globalenv tprog) m (transl_fundef_once f) vargs (n+d) t).


Context (prog tprog: CminLoop.program).
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Context (n: nat).
Hypothesis (TRANSL: match_prog n prog tprog).

Lemma transl_exec_and_execinf_correct:
   (forall m1 f vargs t m2 vres out,
    eval_funcall ge m1 f vargs t m2 vres out ->
    eval_funcall tge m1 (transl_fundef n f) vargs t m2 vres out)
/\ (forall f v e1 m1 s t e2 m2 out,
    exec_stmt ge f v e1 m1 s t e2 m2 out ->
    exec_stmt tge (transl_function n f) v e1 m1 (transform_stmt n s) t e2 m2 out)
/\ (forall m f vargs N t,
    evalinf_funcall ge m f vargs N t ->
    evalinf_funcall tge m (transl_fundef n f) vargs (N + (Z.of_nat n) * d) t).
Proof.
  generalize dependent prog. clear TRANSL. clear ge. clear prog. induction n; clear n.
  + intros. apply invert_match_program_total in TRANSL. rewrite transl_fundef_zero, transf_program_id_total in TRANSL. subst.
    repeat split; intros. now rewrite transl_fundef_zero. now rewrite transl_function_zero. simpl. now rewrite transl_fundef_zero, Z.add_0_r.
  + intros. apply invert_match_program_total in TRANSL. rewrite transl_fundef_succ in TRANSL.
    rewrite <- transf_program_total_total_comm_ext in TRANSL.
    assert (match_prog n0 (transform_program (transl_fundef_once) prog) tprog) by (rewrite TRANSL; apply make_match_n).
    assert (match_prog_once prog (transform_program (transl_fundef_once) prog)) by apply make_match_once.
    apply IHn0 in H.
    repeat split; intros.
    apply transl_exec_correct_once in H0. apply H0, H in H1. now rewrite transl_fundef_succ.
    apply transl_exec_correct_once in H0. apply H0, H in H1. now rewrite transl_function_succ.
    eapply transl_execinf_correct_once, H in H1; eauto. rewrite transl_fundef_succ. now replace (N + Z.of_nat (S n0) * d) with (N + d + Z.of_nat n0 * d) by lia.
Qed.

Lemma sig_preserved:
  forall f,
  funsig (transl_fundef n f) = funsig f.
Proof.
  intros. unfold transl_fundef_once, transf_fundef, transl_function_once. now case f.
Qed.

Theorem forward_preservation:
  bigstep_semantics prog ⇉ bigstep_semantics tprog.
Proof.
  apply make_forward_transformation.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_exec_and_execinf_correct; eauto.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. now apply transl_exec_and_execinf_correct with (N:=N).
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_exec_and_execinf_correct; eauto.
    apply bigstep_nonempty.
  * apply (Genv.senv_transf TRANSL).
Qed.

Theorem backward_preservation:
  bigstep_semantics prog ⇇ bigstep_semantics tprog.
Proof.
  apply forward_to_backward.
  apply bigstep_semantics_determinate.
  apply bigstep_semantics_receptive.
  apply bigstep_semantics_nonempty.
  apply forward_preservation.
Qed.

End Transform.

End Context.