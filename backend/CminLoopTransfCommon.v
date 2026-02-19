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

(** Contains a few lemmata that are useful for all Cminor / CminLoop transforms. *)

Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Memory.
Require Import Linking.
Require Import Equality.
Require Import Values.
Require Import Events.
Require Import Errors.
Require Import CminLoop.

Section LOOP_COUNT.

Variable ge: genv.

(*
Inductive exec_loop_counted_l0: function -> val -> env -> mem -> stmt -> trace -> env -> mem -> outcome -> nat -> Prop :=
  | exec_loop_counted_l0_loop:
      forall f sp e m s t t1 e1 m1 t2 e2 m2 out n,
      exec_stmt ge f sp e m s t1 e1 m1 Out_normal ->
      exec_loop_counted_l0 f sp e1 m1 s t2 e2 m2 out n ->
      t = t1 ** t2 ->
      exec_loop_counted_l0 f sp e m s t e2 m2 out (S n)
  | exec_loop_counted_l0_stop:
      forall f sp e m t s e1 m1 out,
      exec_stmt ge f sp e m s t e1 m1 out ->
      exec_loop_counted_l0 f sp e m s t e1 m1 out 1
  | exec_loop_counted_l_0:
      forall f sp e1 m1 s e2 m2,
      exec_loop_counted_l0 f sp e1 m1 s E0 e2 m2 Out_partial 0.

Lemma loop_counted_l0_sound: forall n f sp e m s t e1 m1 out,
  exec_loop_counted_l0 f sp e m s t e1 m1 out n ->
  out <> Out_normal ->
  exec_stmt ge f sp e m (Sloop s) t e1 m1 out.
Proof.
  intro n. induction n; intros.
  * inv H. eapply exec_partial_E0.
  * inv H. eapply exec_Sloop_loop; eauto. eapply exec_Sloop_stop; eauto.
Qed.

Lemma loop_counted_l0_complete: forall f sp e m s t e1 m1 out,
  exec_stmt ge f sp e m (Sloop s) t e1 m1 out ->
  exists n, exec_loop_counted_l0 f sp e m s t e1 m1 out n.
Proof.
  intros. dependent induction H.
  * exists O. now constructor.
  * destruct (IHexec_stmt2 s eq_refl). exists (S x). econstructor; eauto.
  * exists (S O). now constructor.
Qed.

Lemma invert_loop_counted_l0_right: forall n f sp e m s t1 t2 e1 m1 e2 m2 out,
  exec_loop_counted_l0 f sp e m s t1 e1 m1 Out_normal n ->
  exec_stmt ge f sp e1 m1 s t2 e2 m2 out ->
  exec_loop_counted_l0 f sp e m s (t1**t2) e2 m2 out (S n).
Proof.
  induction n; intros.
  * inv H.
  * inv H.
  + eapply IHn in H3; eauto. econstructor; eauto. traceEq.
  + econstructor; eauto. now constructor.
Qed.


Lemma exec_Sloop_right: forall f sp e m e1 m1 e2 m2 t1 t2 s out,
  exec_stmt ge f sp e m (Sloop s) t1 e2 m2 Out_normal ->
  exec_stmt ge f sp e2 m2 s t2 e1 m1 out ->
  exec_stmt ge f sp e m (Sloop s) (t1 ** t2) e1 m1 out.
Proof.
  intros. dependent induction H.
  + pose proof H1. apply IHexec_stmt2 in H1; auto. econstructor; eauto. traceEq.
  + congruence.
Qed.
*)

Inductive exec_loop_counted_l: function -> val -> env -> mem -> stmt -> trace -> env -> mem -> outcome -> nat -> Prop :=
  | exec_loop_counted_l_loop:
      forall f sp e m s t t1 e1 m1 t2 e2 m2 out n,
      exec_stmt ge f sp e m s t1 e1 m1 Out_normal ->
      exec_loop_counted_l f sp e1 m1 s t2 e2 m2 out n ->
      t = t1 ** t2 ->
      exec_loop_counted_l f sp e m s t e2 m2 out (S n)
  | exec_loop_counted_l_stop:
      forall f sp e m t s e1 m1 out,
      exec_stmt ge f sp e m s t e1 m1 out ->
      exec_loop_counted_l f sp e m s t e1 m1 out 0.

Lemma loop_counted_l_sound: forall n f sp e m s t e1 m1 out,
  exec_loop_counted_l f sp e m s t e1 m1 out n ->
  out <> Out_normal ->
  exec_stmt ge f sp e m (Sloop s) t e1 m1 out.
Proof.
  intro n. induction n; intros.
  * inv H. now constructor.
  * inv H. eapply exec_Sloop_loop; eauto.
Qed.

Lemma loop_counted_l_complete: forall f sp e m s t e1 m1 out,
  exec_stmt ge f sp e m (Sloop s) t e1 m1 out ->
  exists n, exec_loop_counted_l f sp e m s t e1 m1 out n.
Proof.
  intros. dependent induction H.
  * exists O. econstructor. now constructor.
  * destruct (IHexec_stmt2 s eq_refl). exists (S x). econstructor; eauto.
  * exists O. now constructor.
Qed.

Lemma invert_loop_counted_l_right: forall n f sp e m s t1 t2 e1 m1 e2 m2 out,
  exec_loop_counted_l f sp e m s t1 e1 m1 Out_normal n ->
  exec_stmt ge f sp e1 m1 s t2 e2 m2 out ->
  exec_loop_counted_l f sp e m s (t1**t2) e2 m2 out (S n).
Proof.
  induction n; intros.
  * inv H. econstructor; eauto. now constructor.
  * inv H. eapply IHn in H3; eauto. econstructor; eauto. traceEq.
Qed.


Inductive exec_loop_counted_r: function -> val -> env -> mem -> stmt -> trace -> env -> mem -> outcome -> nat -> Prop :=
  | exec_loop_counted_r_loop:
      forall f sp e m s t t1 e1 m1 t2 e2 m2 out n,
      exec_loop_counted_r f sp e m s t1 e1 m1 Out_normal n ->
      exec_stmt ge f sp e1 m1 s t2 e2 m2 out ->
      t = t1 ** t2 ->
      exec_loop_counted_r f sp e m s t e2 m2 out (S n)
  | exec_loop_counted_r_stop:
      forall f sp e m t s e1 m1 out,
      exec_stmt ge f sp e m s t e1 m1 out ->
      exec_loop_counted_r f sp e m s t e1 m1 out 0.

Lemma invert_loop_counted_r_left: forall n f sp e m s t1 t2 e1 m1 e2 m2 out,
  exec_stmt ge f sp e m s t1 e1 m1 Out_normal ->
  exec_loop_counted_r f sp e1 m1 s t2 e2 m2 out n ->
  exec_loop_counted_r f sp e m s (t1**t2) e2 m2 out (S n).
Proof.
  induction n; intros.
  * inv H0. econstructor; eauto. now constructor.
  * inv H0. eapply IHn in H2; eauto. econstructor; eauto. traceEq.
Qed.

Lemma loop_counted_r_l: forall n f sp e m s t e1 m1 out,
  exec_loop_counted_r f sp e m s t e1 m1 out n ->
  exec_loop_counted_l f sp e m s t e1 m1 out n.
Proof.
  induction n; intros. inv H. econstructor; eauto.
  inv H. eapply IHn in H1. eapply invert_loop_counted_l_right in H1; eauto.
Qed.

Lemma loop_counted_l_r: forall n f sp e m s t e1 m1 out,
  exec_loop_counted_l f sp e m s t e1 m1 out n ->
  exec_loop_counted_r f sp e m s t e1 m1 out n.
Proof.
  induction n; intros. inv H. now constructor.
  inv H. apply IHn in H2. eapply invert_loop_counted_r_left in H2; eauto.
Qed.

Lemma loop_counted_r_sound: forall n f sp e m s t e1 m1 out,
  exec_loop_counted_r f sp e m s t e1 m1 out n ->
  out <> Out_normal ->
  exec_stmt ge f sp e m (Sloop s) t e1 m1 out.
Proof.
  intros. inv H.
  - eapply loop_counted_r_l, invert_loop_counted_l_right in H1; eauto. inv H1.
    econstructor; eauto. eapply loop_counted_l_sound; eauto.
  - now constructor.
Qed.

Lemma loop_counted_r_complete: forall f sp e m s t e1 m1 out,
  exec_stmt ge f sp e m (Sloop s) t e1 m1 out ->
  exists n, exec_loop_counted_r f sp e m s t e1 m1 out n.
Proof.
  intros. apply loop_counted_l_complete in H as [n]. inv H.
  - eapply loop_counted_l_r, invert_loop_counted_r_left in H1; eauto.
  - exists O. now constructor.
Qed.

End LOOP_COUNT.

Section LOOP_COUNT_INF.

Variable ge: genv.

Require Import Tracex.
Require Import Foreverx.

Inductive execinf_loop_counted: function -> val -> env -> mem -> stmt -> Z -> tracex -> nat -> Prop :=
  | execinf_loop_counted_loop:
      forall f sp e m s t t1 e1 m1 t2 M M' n,
      event_guard t M' t1 M ->
      exec_stmt ge f sp e m s t1 e1 m1 Out_normal ->
      execinf_loop_counted f sp e1 m1 s M t2 n ->
      t = t1 °° t2 ->
      execinf_loop_counted f sp e m s M' t (S n)
  | execinf_loop_counted_div:
      forall f sp e m t s M,
      execinf_stmt ge f sp e m s (M-1) t ->
      execinf_loop_counted f sp e m s M t 0.

Lemma loop_counted_inf_mon: forall n f sp e m s t M1 M2,
  M1 <= M2 ->
  execinf_loop_counted f sp e m s M1 t n ->
  execinf_loop_counted f sp e m s M2 t n.
Proof.
  intros. inv H0.
  + econstructor; eauto. eapply event_incr_left; eauto.
  + constructor. eapply execinf_mon; eauto. lia.
Qed.

Lemma loop_counted_inf_sound: forall n f sp e m s t M,
  execinf_loop_counted f sp e m s M t n ->
  execinf_stmt ge f sp e m (Sloop s) M t.
Proof.
  intro n. induction n; intros.
  * inv H. constructor. eapply guard_incr with (M-1). lia. eapply execinf_guard; eauto. auto.
  * inv H. eapply execinf_Sloop_loop; eauto.
Qed.

End LOOP_COUNT_INF.


Section EVAL_EXPR_PRESERVED.

Context {F1 F2 V: Type} {L1: Linker F1} {L2: Linker V}.
Variable prog: AST.program F1 V.
Variable tprog: AST.program F2 V.

Variable ge tge : Senv.t.
Hypothesis equiv: Senv.equiv ge tge.

Lemma symbols_preserved_senv:
  forall (s: ident), Senv.find_symbol tge s = Senv.find_symbol ge s.
Proof.
  intros. apply equiv.
Qed.

Lemma eval_constant_preserved:
  forall sp cst,
  eval_constant ge sp cst = eval_constant tge sp cst.
Proof.
  intros. case cst; auto.
  intros. simpl. unfold Senv.symbol_address; simpl. now rewrite symbols_preserved_senv.
Qed.

Lemma eval_constant_preserved_inv:
  forall sp cst,
  eval_constant tge sp cst = eval_constant ge sp cst.
Proof.
  intros. case cst; auto.
  intros. simpl. unfold Senv.symbol_address; simpl. now rewrite symbols_preserved_senv.
Qed.

Lemma eval_expr_preserved:
  forall sp e m a v,
  eval_expr ge sp e m a v ->
  eval_expr tge sp e m a v.
Proof.
  intros. dependent induction H.
  * now constructor.
  * constructor. now rewrite <- eval_constant_preserved.
  * econstructor; eauto.
  * econstructor; eauto.
  * econstructor; eauto.
Qed.

Lemma eval_expr_preserved_inv:
  forall sp e m a v,
  eval_expr tge sp e m a v ->
  eval_expr ge sp e m a v.
Proof.
  intros. dependent induction H.
  * now constructor.
  * constructor. now rewrite <- eval_constant_preserved_inv.
  * econstructor; eauto.
  * econstructor; eauto.
  * econstructor; eauto.
Qed.

Lemma eval_exprlist_preserved:
  forall sp e m bs vs,
  eval_exprlist ge sp e m bs vs ->
  eval_exprlist tge sp e m bs vs.
Proof.
  intros. dependent induction H; constructor. now apply eval_expr_preserved. auto.
Qed.

Lemma eval_exprlist_preserved_inv:
  forall sp e m bs vs,
  eval_exprlist tge sp e m bs vs ->
  eval_exprlist ge sp e m bs vs.
Proof.
  intros. dependent induction H; constructor. now apply eval_expr_preserved_inv. auto.
Qed.

End EVAL_EXPR_PRESERVED.


Section TRANSF_BIGSTEP.

Variable prog: program.
Variable tprog: program.
Variable transf: fundef -> fundef.
Hypothesis TRANSL: match_program (fun cu f tf => tf = transf f) eq prog tprog.
Hypothesis sig_preserved: forall f, funsig (transf f) = funsig f.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma transl_initial_state: forall f m,
  bigstep_initial_state prog m f ->
  bigstep_initial_state tprog m (transf f).
Proof.
  intros. inv H.
  assert (prog_main prog = prog_main tprog).
  { unfold match_program, match_program_gen in TRANSL. now destruct TRANSL as [? []]. }
  econstructor.
  * eapply Genv.init_mem_transf in H0. apply H0. apply TRANSL.
  * unfold ge0 in H1. rewrite H in H1. eapply Genv.find_symbol_transf in TRANSL. rewrite TRANSL. apply H1.
  * fold tge. replace ge0 with ge in H2 by auto. apply (Genv.find_funct_ptr_transf TRANSL). eauto.
  * now rewrite sig_preserved.
Qed.

End TRANSF_BIGSTEP.



Ltac solve_transl T := do 5 (
  try (eapply eval_expr_preserved; eauto);
  try (eapply eval_exprlist_preserved; eauto);
  try (eapply (Genv.find_funct_transf T); eauto);
  try (eapply (Genv.senv_match T); eauto);
  try (eapply external_call_symbols_preserved; eauto)
 (* try now rewrite sig_preserved  *)
).

Ltac here_transl T := try (intros; econstructor; eauto; solve_transl T; fail).
