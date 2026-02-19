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

(** * Simplify loops that will diverge silently into while-true loops. *)

Require Import Classical.
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
Require Import CminLoop.
Require Import CminLoopTransfCommon.
Require Import CminLoopBigSmallEquiv.
Require Import Linking.
Require Import Equality.
Require Import Tracex.

Fixpoint silent_stmt (s: stmt): Prop := match s with
  | Sbuiltin _ _ _ => False
  | Sloop s => silent_stmt s
  | Sifthenelse e s1 s2 => silent_stmt s1 /\ silent_stmt s2
  | Sseq s1 s2 => silent_stmt s1 /\ silent_stmt s2
  | Sblock s => silent_stmt s
  | Sdummy s => silent_stmt s
  | Scall _ _ _ _ => False
  | Stailcall _ _ _ => False
  | _ => True
end.  

Definition silent_fun (fd: fundef): Prop := match fd with
  | Internal f => silent_stmt (fn_body f)
  | External e => False
end.

Definition silent_stmt_dec (s: stmt): {silent_stmt s} + {~silent_stmt s}.
Proof.
  induction s; try (now left); try (now right); try (now simpl).
  * simpl. destruct IHs1. 2: now right. destruct IHs2. now left. now right.
  * simpl. destruct IHs1. 2: now right. destruct IHs2. now left. now right.
Defined.

Section SilentSpec.

Variable ge: genv.

Lemma silent_stmt_spec_1:
  (forall m fd l t m' v out,
    eval_funcall ge m fd l t m' v out ->
    silent_fun fd ->
    t = E0) /\
  (forall f sp e m s t e' m' out,
    exec_stmt ge f sp e m s t e' m' out ->
    silent_stmt s ->
    t = E0).
Proof.
  apply eval_funcall_exec_stmt_ind2; auto; intros; try easy.
  * inv H3. destruct b; auto.
  * inv H4. apply H0 in H5. apply H2 in H6. traceEq.
  * inv H2. auto.
  * pose proof H4. apply H0 in H4. apply H2 in H5. traceEq.
Qed.

Lemma silent_loop_spec:
  forall f sp e m s t e' m' out,
  exec_stmt ge f sp e m (Sloop s) t e' m' out ->
  silent_stmt s ->
  t = E0.
Proof.
  intros. dependent induction H; auto; apply silent_stmt_spec_1 in H; auto.
  * apply IHexec_stmt2 in H1; auto. traceEq.
Qed.

Lemma silent_stmt_spec_2:
  forall s f sp e m t n,
  execinf_stmt ge f sp e m s n t ->
  silent_stmt s ->
  t = X0.
Proof.
  dependent induction s; intros; inv H; try inv H0; eauto.
  * apply silent_stmt_spec_1 in H4; auto.
    eapply IHs2 in H9; eauto. tracexEq.
  * destruct b. apply IHs1 in H13; auto. apply IHs2 in H13; auto.
  * apply silent_stmt_spec_1 in H3; auto.
    subst. rewrite X0_left.
    destruct H2 as [|[]]. now rewrite X0_left in H.
    clear H1 n. replace M with (Z.of_nat (Z.to_nat M)) in * by lia. clear H.
    generalize dependent e1. generalize dependent m1. generalize dependent s.
    induction (Z.to_nat M) using strong_ind; clear M. (* second induction on the event guard *)
    intros. inv H4. apply IHs in H8; auto.
    apply silent_stmt_spec_1 in H3; auto. destruct H2 as [|[?[?[]]]]. tracexEq.
    replace M with (Z.of_nat (Z.to_nat M)) in * by lia. subst. rewrite X0_left in *.
    eapply H in H5; eauto. pose proof (H6 eq_refl). lia.
Qed.

End SilentSpec.


Fixpoint no_exit (s: stmt): Prop := match s with
  | Sexit _ => False
  | Sloop s => no_exit s
  | Sifthenelse e s1 s2 => no_exit s1 /\ no_exit s2
  | Sseq s1 s2 => no_exit s1 /\ no_exit s2
  | Sblock s => no_exit s
  | Sdummy s => no_exit s
  | Sreturn _ => False
  | Sswitch _ _ _ _ => False
  | Stailcall _ _ _ => False
  | _ => True
end.

Definition no_exit_fun (fd: fundef) := match fd with
  | Internal f => no_exit (fn_body f)
  | External e => True
end.

Definition no_exit_dec (s: stmt): {no_exit s} + {~no_exit s}.
Proof.
  induction s; try (now left); try (now right); try (now simpl).
  * simpl. destruct IHs1. 2: now right. destruct IHs2. now left. now right.
  * simpl. destruct IHs1. 2: now right. destruct IHs2. now left. now right.
Defined.


Section NoExitSpec.

Variable ge: genv.

Lemma no_exit_spec:
  (forall m fd l t m' v out,
    eval_funcall ge m fd l t m' v out ->
    True) /\
  (forall f sp e m s t e' m' out,
    exec_stmt ge f sp e m s t e' m' out ->
    no_exit s ->
    out <> Out_partial ->
    out = Out_normal).
Proof.
  apply eval_funcall_exec_stmt_ind2; auto; intros; try easy.
  * apply eval_funcall_outcomes in H3 as []; congruence.
  * inv H3. apply H2; auto. destruct b; auto.
  * inv H4. auto.
  * inv H2. auto.
  * apply H0 in H1; auto. now subst. now destruct out.
Qed.

Lemma no_exit_spec_partial:
  forall f sp e m s t e' m' out,
    exec_stmt ge f sp e m s t e' m' out ->
    no_exit s ->
    out <> Out_normal ->
    out = Out_partial.
Proof.
  intros. destruct out; try congruence;
  exfalso; apply H1; eapply no_exit_spec; eauto; congruence.
Qed.

Lemma loop_out':
  forall f sp e m s t e' m' out,
  exec_stmt ge f sp e m (Sloop s) t e' m' out ->
  out <> Out_normal.
Proof.
  intros. dependent induction H; try (inv H0; fail); try (inv H1; fail); try (inv H2; fail).
  congruence. eapply IHexec_stmt2; eauto. auto.
Qed.

Lemma no_exit_spec_loop:
  forall f sp e m s t e' m' out,
  exec_stmt ge f sp e m (Sloop s) t e' m' out ->
  no_exit s ->
  out = Out_partial.
Proof.
  intros. 
  pose proof H. apply loop_out' in H; auto.
  destruct out; auto; now apply no_exit_spec in H1.
Qed.

End NoExitSpec.



(*** TRANSFORM ***)

Fixpoint transform_stmt (s: stmt) : stmt := match s with
  | Sloop s =>
    if silent_stmt_dec s && no_exit_dec s then
      Sloop Sskip
    else
      Sloop (transform_stmt s)
  | Sifthenelse e s1 s2 => Sifthenelse e (transform_stmt s1) (transform_stmt s2)
  | Sseq s1 s2 => Sseq (transform_stmt s1) (transform_stmt s2)
  | Sblock s => Sblock (transform_stmt s)
  | Sdummy s => Sdummy (transform_stmt s)
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

Lemma sig_preserved:
  forall f,
  funsig (transl_fundef f) = funsig f.
Proof.
  intros. unfold transl_fundef, transf_fundef, transl_function. now case f.
Qed.

Ltac solve_transl_extend :=
  solve_transl TRANSL;
  try now rewrite sig_preserved.

Ltac here_transl := try (intros; econstructor; eauto; solve_transl_extend; fail).


Lemma silent_stmt_after_transform: forall s,
  silent_stmt s ->
  silent_stmt (transform_stmt s).
Proof.
  intros. dependent induction s; try inv H; simpl; auto.
  destruct no_exit_dec. 2: rewrite andb_false_r; now apply IHs.
  now destruct silent_stmt_dec.
Qed.

Lemma transl_exec_correct:
   (forall m1 f vargs t m2 vres out,
    eval_funcall ge m1 f vargs t m2 vres out ->
    eval_funcall tge m1 (transl_fundef f) vargs t m2 vres out)
/\ (forall f v e1 m1 s t e2 m2 out,
    exec_stmt ge f v e1 m1 s t e2 m2 out ->
    exec_stmt tge (transl_function f) v e1 m1 (transform_stmt s) t e2 m2 out).
Proof.
  eapply eval_funcall_exec_stmt_ind2; here_transl.
  * intros. eapply exec_Scall with (fd:=transl_fundef fd); solve_transl_extend; eauto.
  * intros. econstructor; eauto; solve_transl_extend. case b in *; apply H2.
  * intros. simpl in *.
    case (silent_stmt_dec s && no_exit_dec s) eqn:?.
    + destruct silent_stmt_dec eqn:?; [pose proof s0|easy].
      apply silent_loop_spec in H1; auto.
      apply silent_stmt_after_transform in H4. apply silent_stmt_spec_1 in H0; auto.
      apply no_exit_spec_loop in H2; auto; [|constructor].
      subst. constructor.
    + econstructor; eauto.
  * intros. simpl in *.
    case (silent_stmt_dec s && no_exit_dec s) eqn:?.
    + destruct (outcome_eq_dec out Out_partial).
      - destruct silent_stmt_dec; [pose proof s0|easy].
        apply silent_stmt_after_transform in H2. apply silent_stmt_spec_1 in H0; auto.
        subst. constructor.
      - exfalso. apply no_exit_spec in H; auto. apply andb_prop in Heqb. now destruct no_exit_dec.
    + eapply exec_Sloop_stop; eauto.
  * intros. eapply exec_Stailcall; solve_transl_extend; eauto.
Qed.


Lemma transl_execinf_correct:
  forall m f vargs n t,
  evalinf_funcall ge m f vargs n t ->
  evalinf_funcall tge m (transl_fundef f) vargs n t.
Proof.
  cofix CIH_FUN.
  assert (CIHST: forall f v e m s t n,
    execinf_stmt ge f v e m s n t ->
    execinf_stmt tge (transl_function f) v e m (transform_stmt s) n t).
  cofix CIH_STMT.
  intros. destruct H; try (econstructor; solve_transl_extend; eauto; fail).
  * econstructor; solve_transl_extend; eauto. case b in *; now apply CIH_STMT.
  * eapply execinf_Sseq_2; eauto. apply transl_exec_correct; eauto.
  * simpl. case (silent_stmt_dec s && no_exit_dec s) eqn:?.
    + apply andb_prop in Heqb as []. apply silent_stmt_spec_2 in H0. 2: now destruct silent_stmt_dec. subst. clear.
      generalize dependent n. cofix CO. intros. eapply execinf_Sloop_loop. now left. constructor. apply CO. tracexEq.
    + econstructor; eauto.
  * simpl. case (silent_stmt_dec s && no_exit_dec s) eqn:?.
    + apply andb_prop in Heqb as []. apply silent_stmt_spec_1 in H0. apply silent_stmt_spec_2 in H1. 2,3: now destruct silent_stmt_dec. subst. simpl. clear.
      generalize dependent n. cofix CO. intros. eapply execinf_Sloop_loop. now left. constructor. apply CO. tracexEq.
    + eapply execinf_Sloop_loop; eauto. apply transl_exec_correct; eauto.
      replace (Sloop (transform_stmt s)) with (transform_stmt (Sloop s)) by (simpl; now rewrite Heqb). now apply CIH_STMT.
  * intros. inv H. econstructor; eauto. now apply CIHST.
  Unshelve. auto. auto.
Qed.

Theorem forward_preservation:
  bigstep_semantics prog ⇉ bigstep_semantics tprog.
Proof.
  apply make_forward_transformation.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_exec_correct; eauto.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_execinf_correct. eauto.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_exec_correct; eauto.
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

End TRANSLATION.