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

(** * Remove all nested dummy statements that end in a skip statement. *)

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
Require Import CminLoop.
Require Import CminLoopTransfCommon.
Require Import Semantics.
Require Import SemanticsSmallBig.
Require Import CminLoopBigSmallEquiv.
Require Import Linking.
Require Import Equality.
Require Import Tracex.
Require Import CminLoopRepeatTransform.

Section Transformation.

(*** LOOP TRANSFORMATION ***)

Fixpoint transform_stmt (s: stmt) : stmt := match s with
  | Sloop s => Sloop (transform_stmt s)
  | Sifthenelse e s1 s2 => Sifthenelse e (transform_stmt s1) (transform_stmt s2)
  | Sseq s1 s2 => Sseq (transform_stmt s1) (transform_stmt s2)
  | Sblock s => Sblock (transform_stmt s)
  | Sdummy (Sdummy s) => Sdummy (transform_stmt s)
  | Sdummy s => transform_stmt s
  | _ => s
end.

Definition transl_function (f: function) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_vars)
    f.(fn_stackspace)
    (transform_stmt f.(fn_body)).

Definition transl_fundef (f: fundef) : fundef :=
  transf_fundef transl_function f.

Definition transl_program (p: program) : program :=
  transform_program transl_fundef p.

Definition match_prog (p: program) (tp: program) :=
  match_program (fun cu f tf => tf = transl_fundef f) eq p tp.

Theorem transl_program_match:
  forall p, match_prog p (transl_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Section TRANSLATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge : genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f,
  funsig (transl_fundef f) = funsig f.
Proof.
  intros. unfold transl_fundef, transf_fundef, transl_function. now case f.
Qed.

Ltac solve_transl_extend :=
  solve_transl TRANSL;
  (try now rewrite sig_preserved);
  (try now apply guard_incr1);
  (try (eapply event_incr1_both; eauto; fail)).

Ltac here_transl := try (intros; split; econstructor; eauto; solve_transl_extend; fail).

Lemma transl_exec_correct_strong:
   (forall m1 f vargs t m2 vres out,
    eval_funcall ge m1 f vargs t m2 vres out ->
    eval_funcall tge m1 (transl_fundef f) vargs t m2 vres out)
/\ (forall f v e1 m1 s t e2 m2 out,
    exec_stmt ge f v e1 m1 s t e2 m2 out ->
    exec_stmt tge (transl_function f) v e1 m1 (transform_stmt s) t e2 m2 out /\ exec_stmt tge (transl_function f) v e1 m1 (transform_stmt (Sdummy s)) t e2 m2 out).
Proof.
  eapply eval_funcall_exec_stmt_ind2; here_transl; intros.
  * constructor.
  * inv H2. econstructor; eauto.
  * econstructor; eauto; solve_transl_extend.
  * econstructor; eauto; solve_transl_extend.
  * split; eapply exec_Scall with (fd:=transl_fundef fd); solve_transl_extend; eauto.
  * split; econstructor; eauto; solve_transl_extend; case b in *; apply H2.
  * inv H0. inv H2. here_transl.
  * inv H0. here_transl.
  * inv H0. inv H2. here_transl.
  * inv H0. here_transl.
  * inv H0. here_transl.
  * inv H0. split. auto. destruct s; now constructor.
  * split; eapply exec_Stailcall with (fd:=transl_fundef fd); solve_transl_extend; eauto.
Qed.

Lemma transl_exec_correct:
   (forall m1 f vargs t m2 vres out,
    eval_funcall ge m1 f vargs t m2 vres out ->
    eval_funcall tge m1 (transl_fundef f) vargs t m2 vres out)
/\ (forall f v e1 m1 s t e2 m2 out,
    exec_stmt ge f v e1 m1 s t e2 m2 out ->
    exec_stmt tge (transl_function f) v e1 m1 (transform_stmt s) t e2 m2 out).
Proof.
  split; apply transl_exec_correct_strong.
Qed.

Lemma cancel_pm: forall z, z+1-1 = z.
Proof.
  lia.
Qed.

Lemma transl_execinf_correct:
  forall m f vargs n t,
  evalinf_funcall ge m f vargs (n-1) t ->
  evalinf_funcall tge m (transl_fundef f) vargs n t.
Proof.
  cofix CIH_FUN.
  assert (CIHST: forall f v e m s t n,
    execinf_stmt ge f v e m s (n-1) t ->
    execinf_stmt tge (transl_function f) v e m (transform_stmt s) n t).
  cofix CIH_STMT.

  remember senv_preserved as SE.
  intros. remember (n-1). destruct H; rewrite Heqz in *.
  * eapply execinf_Scall with (fd:=transl_fundef fd); eauto; solve_transl_extend.
  * econstructor; eauto; solve_transl_extend. case b in *; try eapply CIH_STMT; eauto.
  * econstructor; eauto; solve_transl_extend.
  * eapply execinf_Sseq_2; eauto; solve_transl_extend. eapply transl_exec_correct; eauto. rewrite <- cancel_pm in H1 at 1. auto.
  * econstructor; eauto; solve_transl_extend.
  * eapply execinf_Sloop_loop; eauto; solve_transl_extend. eapply transl_exec_correct; eauto. rewrite <- cancel_pm in H1 at 1. eapply CIH_STMT in H1; eauto.
  * econstructor; eauto; solve_transl_extend.
  * case s in *; inv H0.
    - eapply execinf_Scall with (fd:=transl_fundef fd); eauto; solve_transl_extend. eapply CIH_FUN. eapply evalinf_mon in H16; eauto. lia.
    - eapply execinf_Stailcall with (fd:=transl_fundef fd); eauto; solve_transl_extend. eapply CIH_FUN. eapply evalinf_mon in H16; eauto. lia.
    - econstructor; eauto; solve_transl_extend. eapply CIH_STMT. eapply execinf_mon in H10; eauto. lia.
    - eapply execinf_Sseq_2; eauto; solve_transl_extend. do 2 eapply event_incr1_both; eauto. fold transform_stmt. eapply transl_exec_correct; eauto. eapply CIH_STMT. eapply execinf_mon in H9; eauto. lia.
    - destruct b; econstructor; eauto; solve_transl_extend; simpl; eauto; eapply CIH_STMT; eapply execinf_mon in H13; eauto; lia.
    - econstructor; eauto; solve_transl_extend. apply CIH_STMT. eapply execinf_mon in H7; eauto; lia.
    - eapply execinf_Sloop_loop; eauto; solve_transl_extend. do 2 eapply event_incr1_both; eauto. eapply transl_exec_correct; eauto. fold transform_stmt. replace (Sloop (transform_stmt s)) with (transform_stmt (Sloop s)) by auto. eapply CIH_STMT; eauto. eapply execinf_mon in H4; eauto; lia.
    - econstructor; eauto; solve_transl_extend. fold transform_stmt. eapply execinf_mon in H7; eauto; lia.
    - econstructor; eauto; solve_transl_extend. fold transform_stmt. apply CIH_STMT. eapply execinf_mon in H7; eauto; lia.
  * econstructor; auto. now apply guard_incr1. 3: apply (Genv.find_funct_transf TRANSL); eauto. eapply eval_expr_preserved; eauto. eapply eval_exprlist_preserved; eauto.
    now rewrite sig_preserved. eauto. now apply CIH_FUN.
  * intros. inv H. econstructor; eauto. now apply guard_incr1. now apply CIHST.
Qed.

End TRANSLATION.

Section REPEAT.

Definition n: nat := 5.

Definition transform_stmt_rep := CminLoopRepeatTransform.transform_stmt transform_stmt n.
Definition transl_function_rep := CminLoopRepeatTransform.transl_function transform_stmt n.
Definition transl_fundef_rep := CminLoopRepeatTransform.transl_fundef transform_stmt n.
Definition transl_program_rep := CminLoopRepeatTransform.transl_program transform_stmt n.
Definition match_prog_rep := CminLoopRepeatTransform.match_prog transform_stmt n.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSL: match_prog_rep prog tprog.
Let ge : genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.

Lemma transl_exec_and_execinf_correct:
   (forall m1 f vargs t m2 vres out,
    eval_funcall ge m1 f vargs t m2 vres out ->
    eval_funcall tge m1 (transl_fundef_rep f) vargs t m2 vres out)
/\ (forall f v e1 m1 s t e2 m2 out,
    exec_stmt ge f v e1 m1 s t e2 m2 out ->
    exec_stmt tge (transl_function_rep f) v e1 m1 (transform_stmt_rep s) t e2 m2 out)
/\ (forall m f vargs N t,
    evalinf_funcall ge m f vargs N t ->
    evalinf_funcall tge m (transl_fundef_rep f) vargs (N+5*1) t).
Proof.
  apply transl_exec_and_execinf_correct.
  apply transl_exec_correct.
  intros. rewrite <- cancel_pm in H0 at 1. eapply transl_execinf_correct; eauto.
  apply TRANSL.
Qed.

Theorem forward_preservation_rep:
  bigstep_semantics prog ⇉ bigstep_semantics tprog.
Proof.
  apply make_forward_transformation.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply CminLoopRepeatTransform.sig_preserved. apply transl_exec_and_execinf_correct; eauto.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply CminLoopRepeatTransform.sig_preserved. now apply transl_exec_and_execinf_correct with (N:=N).
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply CminLoopRepeatTransform.sig_preserved. apply transl_exec_and_execinf_correct; eauto.
    apply bigstep_nonempty.
  * apply (Genv.senv_transf TRANSL).
Qed.

Theorem backward_preservation_rep:
  bigstep_semantics prog ⇇ bigstep_semantics tprog.
Proof.
  apply forward_to_backward.
  apply bigstep_semantics_determinate.
  apply bigstep_semantics_receptive.
  apply bigstep_semantics_nonempty.
  apply forward_preservation_rep.
Qed.

End REPEAT.

End Transformation.