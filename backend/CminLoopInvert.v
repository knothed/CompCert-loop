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

(** * Invert loops whose condition is directly at the start. *)

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
Require Import SemanticsSmallBig.
Require Import CminLoopBigSmallEquiv.
Require Import Semantics.
Require Import Linking.
Require Import Equality.
Require Import Tracex.

Section Transformation.

(* An external parameter that decides whether a loop with the given inner body should be inverted or not.
   It is irrelevant to the correctness of the transformation. *)
Variable should_invert_loop: stmt -> bool.

(*** LOOP TRANSFORMATION ***)

Fixpoint transform_stmt (s: stmt) : stmt := match s with
  | Sloop (Sseq (Sblock (Sifthenelse e Sskip (Sexit 1))) l) =>
      if (should_invert_loop l) then
        Sifthenelse e (Sloop (Sseq (transform_stmt l) (Sifthenelse e Sskip (Sexit 0)))) (Sexit 0)
      else
        Sloop (Sseq (Sblock (Sifthenelse e Sskip (Sexit 1))) (transform_stmt l))
  | Sloop s => Sloop (transform_stmt s)
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


Section TRANSLATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge : genv := Genv.globalenv prog.
Let tge: genv := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma function_ptr_translated:
  forall b (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transl_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transl_fundef f).
Proof (Genv.find_funct_transf TRANSL).


Lemma sig_preserved:
  forall f,
  funsig (transl_fundef f) = funsig f.
Proof.
  intros. unfold transl_fundef, transf_fundef, transl_function. now case f.
Qed.

Ltac solve_transl_extend :=
  solve_transl TRANSL;
  try (rewrite sig_preserved; eauto).

Ltac here_transl := try (intros; econstructor; eauto; solve_transl_extend; fail).

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
  * intros. eapply exec_Sifthenelse. solve_transl_extend. eauto. case b in *; apply H2.
  * (* exec_Sloop_loop *)
    Ltac destruct_all x := destruct x; try (econstructor; eauto; fail).
    intros. destruct_all s. destruct_all s1. destruct_all s1.
    destruct_all s1_1. destruct_all s1_2. destruct_all n. destruct_all n.
    simpl in *. destruct_all should_invert_loop.
    inv H; try congruence. inv H0; try congruence.
    inv H4. inv H14. easy. destruct b. 2: now inv H20. inv H20. easy.
    simpl in H16. subst.
    eapply exec_Sifthenelse; eauto. simpl.
    inv H2.
    + (* Partial *)
      eapply exec_Sloop_stop.
      -- eapply exec_Sseq_continue. apply H10. eapply exec_partial_E0. auto.
      -- congruence.
    + (* Full *)
      destruct b.
      - eapply exec_Sloop_loop.
      -- eapply exec_Sseq_continue. apply H10. eapply exec_Sifthenelse; eauto. apply exec_Sskip; eauto. eauto.
      -- apply H20.
      -- traceEq.
      - eapply exec_Sloop_stop.
      -- eapply exec_Sseq_continue. apply H10. eapply exec_Sifthenelse; eauto. traceEq.
      -- inv H20; congruence.
  * (* exec_Sloop_stop *)
    intros. destruct_all s. destruct_all s1. destruct_all s1.
    destruct_all s1_1. destruct_all s1_2. destruct_all n. destruct_all n.
    simpl in *. destruct_all should_invert_loop.
    inv H0.
    - (* partial *)
      constructor.
    - (* cond. true *)
      inv H4. inv H12. easy. destruct b; inv H17; try easy.
      eapply exec_Sifthenelse; eauto. eapply exec_Sloop_stop; eauto. eapply exec_Sseq_stop; eauto.
    - (* cond. false *)
      inv H8. constructor. inv H6. constructor. destruct b; inv H16; try constructor; try easy.
      eapply exec_Sifthenelse; eauto. eapply exec_Sexit; eauto.
  * intros. eapply exec_Stailcall with (fd:=transl_fundef fd); solve_transl_extend; eauto.
Qed.

(** Divergence *)

Lemma evalinf_plus_x: forall m f vargs n t x
  (X: x=0 \/ x=1),
  evalinf_funcall ge m f vargs (n-1) t ->
  evalinf_funcall ge m f vargs (n+x-1) t. 
Proof.
  intros. inv X. now rewrite Z.add_0_r. eapply CminLoop.evalinf_mon; eauto. lia.
Qed.

Lemma execinf_plus_x: forall f v e m s t n x
  (X: x=0 \/ x=1),
  execinf_stmt ge f v e m s (n-1) t ->
  execinf_stmt ge f v e m s (n+x-1) t.
Proof.
  intros. inv X. now rewrite Z.add_0_r. eapply CminLoop.execinf_mon; eauto. lia.
Qed.

Lemma cancel_pm: forall n, n+1-1 = n.
Proof. lia. Qed.

Lemma silent_mul2_x: forall t n x (X: x=0 \/ x=1),
  silent_guard t n ->
  silent_guard t (2*(n+1)+x).
Proof.
  intros. inv H. now left. right. lia.
Qed.

Lemma silent_mul2_1: forall t n x (X: x=0 \/ x=1),
  silent_guard t n ->
  silent_guard t (2*(n+1)-1).
Proof.
  intros. inv H. now left. right. lia.
Qed.

Lemma event_mul2_x: forall t t1 n M x (X: x=0 \/ x=1),
  event_guard t n t1 M ->
  event_guard t (2*(n+1) + x) t1 (2*(M+1) + x).
Proof.
  intros. destruct H as [|[?[?[T1 T1']]]]. now left. right.
  repeat split; [ lia | lia | intro; apply T1; lia | intro A; apply T1' in A; lia ].
Qed.

Lemma event_mul2_x_1: forall t t1 n M x (X: x=0 \/ x=1),
  event_guard t n t1 M ->
  event_guard t (2*(n+1) + x-1) t1 (2*(M+1)).
Proof.
  intros. destruct H as [|[?[?[T1 T1']]]]. now left. right.
  repeat split; [ lia | lia | intro; apply T1; lia | intro A; apply T1' in A; lia ].
Qed.

Lemma rewrite_2n_x_1: forall n x,
  2*(n+1) + x - 1 = 2*((n+x-1)+1) + (1-x). 
Proof.
  lia.
Qed.

Ltac solve_inf :=
  try solve_transl_extend;
  try (now apply silent_mul2_x);
  try (now apply event_mul2_x);
  eauto.

Lemma transl_execinf_correct:
  forall m f vargs n t x
  (X: x=0 \/ x=1),
  evalinf_funcall ge m f vargs n t ->
  evalinf_funcall tge m (transl_fundef f) vargs (2*(n+1)+x) t.
Proof.
  cofix CIH_FUN.
  assert (CIHST: forall f v e m s t n x
    (X: x=0 \/ x=1),
    execinf_stmt ge f v e m s n t ->
    execinf_stmt tge (transl_function f) v e m (transform_stmt s) (2*(n+1)+x) t).
  cofix CIH_STMT.

  Ltac finish' CIH := rewrite rewrite_2n_x_1; apply CIH; [lia | now apply execinf_plus_x].
  Ltac finish := match goal with [ CIH: function -> val -> _ |- _ ] => finish' CIH end.
  Ltac finish_fun CIH := rewrite rewrite_2n_x_1; apply CIH; [lia | now apply evalinf_plus_x].

  Ltac fold_and_finish1 := match goal with [
    CIH: function -> val -> _,
    EX: execinf_stmt ge _ _ _ _ ?s _ _
    |- execinf_stmt tge _ _ _ _ ?s' _ _
  ] => replace s' with (transform_stmt s) by auto; finish' CIH
  end.

  Ltac fold_and_finish2 TAC := match goal with [
    CIH: function -> val -> _,
    EX: execinf_stmt ge _ _ _ _ (Sloop ?s) _ _
    |- _ ] =>
    match goal with
    | [ |- exec_stmt tge _ _ _ _ ?s' _ _ _ _ ] =>
      replace s' with (transform_stmt s) by auto; eapply transl_exec_correct; eauto
    | [ |- execinf_stmt tge _ _ _ _ (Sloop ?s') _ _ ] =>
      replace (Sloop s') with (transform_stmt (Sloop s)) by TAC; eapply CIH; eauto
    end
  end.

  intros. remember (n). destruct H; rewrite Heqz in *.
  * eapply execinf_Scall with (fd:=transl_fundef fd); solve_inf. finish_fun CIH_FUN.
  * econstructor; solve_inf. destruct b; finish.
  * constructor; solve_inf. finish.
  * eapply execinf_Sseq_2; solve_inf. now apply event_mul2_x. now apply transl_exec_correct.
  
  * Ltac destruct_inf1 x E := destruct x; try (inv E; fail); try (econstructor; solve_inf; fold_and_finish1).
    destruct_inf1 s H0. destruct_inf1 s1 H0. destruct_inf1 s1 H0.
    destruct_inf1 s1_1 H0. destruct_inf1 s1_2 H0. destruct_inf1 n1 H0. destruct_inf1 n1 H0.
    destruct (should_invert_loop s2) eqn:?; (unfold transform_stmt; rewrite Heqb; fold transform_stmt).
    2: econstructor; solve_inf; fold_and_finish1.
    inv H0. { inv H10. inv H6. destruct b; inv H15. }
    inv H4. inv H12. easy. destruct b; inv H17; try easy.
    econstructor; solve_inf. fold transform_stmt. pose proof H3. apply event_to_silent in H3.
    econstructor. inv H3; [ now left | right; lia ].
    econstructor. inv H3; [ now left | right; lia ].
    destruct H0 as [|[?[?[]]]].
    - replace (2*(n+1) + x-1-1-1) with (2*(n-2+x+1) + (1-x)) by lia. (* required for coinductive guard check *)
      apply Xapp_X0_inv in H0 as []; subst. eapply CIH_STMT. lia. eapply execinf_X0_irrel; eauto. (* first invoke CIH_STMT and THEN apply irrel/mon lemma on hypothesis *)
    - replace (2*(n+1) + x-1-1-1) with (2*(n-2+x+1) + (1-x)) by lia. (* as above *)
      rewrite X0_left. eapply CIH_STMT. lia. eapply CminLoop.execinf_mon; eauto. pose proof (H4 eq_refl). lia.
  
  * Ltac destruct_inf2 x := destruct x;
      try (eapply execinf_Sloop_loop; [ apply event_mul2_x; eauto | fold_and_finish2 auto | fold_and_finish2 auto | eauto ]).
    destruct_inf2 s. destruct_inf2 s1. destruct_inf2 s1.
    destruct_inf2 s1_1. destruct_inf2 s1_2. destruct_inf2 n1. destruct_inf2 n1.
    destruct (should_invert_loop s2) eqn:?; (unfold transform_stmt; rewrite Heqb; fold transform_stmt).
    2: { eapply execinf_Sloop_loop; [ apply event_mul2_x; eauto | fold_and_finish2 auto | | eauto ].
        fold_and_finish2 ltac:(unfold transform_stmt; now rewrite Heqb). }
    inv H0. 2: easy. inv H5. inv H12. easy. destruct b; inv H17; try easy.
    econstructor; solve_inf. apply event_to_silent in H. now apply silent_mul2_x.
    fold transform_stmt.
    Ltac solve_transl_extend' := solve_transl_extend; try (apply Senv.equiv_sym, senv_preserved).
    generalize dependent n. generalize dependent M. generalize dependent x.
    generalize dependent v. generalize dependent t4. generalize dependent t2. generalize dependent e3. generalize dependent e1. generalize dependent m2. generalize dependent m1.
    cofix CO. intros.
    inv H1.
    + inv H8. { inv H14. inv H8. destruct b; inv H20. }
      inv H4. inv H17. easy. destruct b; inv H22; try easy.
      rewrite X0_left, E0_left in *.
      eapply execinf_Sloop_loop with (M:=2*(M+1)) (t2:=t0).
      - eapply event_mul2_x_1; eauto.
      - eapply exec_Sseq_continue. eapply transl_exec_correct; eauto.
        eapply exec_Sifthenelse; solve_transl_extend'; eauto. apply exec_Sskip. traceEq.
      - eapply execinf_Sloop_body. rewrite <- Z.add_0_r. apply silent_mul2_x; auto. eapply execinf_Sseq_1. eapply silent_mul2_1; eauto.
        replace (2*(M+1)-1-1) with (2*(M-1+1)+0) by lia. apply CIH_STMT; eauto.
        destruct H3 as [|[?[?[]]]].
          subst. eapply execinf_X0_irrel; eauto.
          pose proof (H4 eq_refl). eapply execinf_mon; eauto. lia.
      - tracexEq.
    + inv H3. inv H5. 2: easy. inv H7. inv H17. easy. destruct b; inv H21; try easy.
      rewrite E0_left in *.
      eapply execinf_Sloop_loop with (M:=2*(M+1)).
      - eapply event_mul2_x_1; eauto.
      - eapply exec_Sseq_continue; eauto. eapply transl_exec_correct; eauto.
        eapply exec_Sifthenelse; solve_transl_extend'; eauto. eapply exec_Sskip. traceEq.
      - replace (2*(M+1)) with (2*(M+1)+1-1) by lia. eapply CO; eauto.
      - traceEq.

  * econstructor; solve_inf. finish.
  * econstructor; solve_inf. finish.
  * econstructor; solve_inf. finish_fun CIH_FUN.
  * intros. inv H. econstructor; solve_inf. finish.
Qed.


Theorem forward_preservation:
  bigstep_semantics prog ⇉ bigstep_semantics tprog.
Proof.
  apply make_forward_transformation.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_exec_correct; eauto.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_execinf_correct with (n:=N). now left. auto.
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

End Transformation.