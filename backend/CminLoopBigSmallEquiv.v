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

(** Behavioral equivalence of smallstep and bigstep semantics for Cminor. *)

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
Require Import Smallstep.
Require Import Bigstep.
Require Import CminLoop.
Require Import Linking.
Require Import Equality.
Require Import Behaviors.
Require Import SmallstepBehaviors.
Require Import Foreverx.
Require Import Semantics.
Require Import SemanticsSmallBig.
Require Import Tracex.
Require Import Determinacy.

(** We first prove soundness of bigstep w.r.t. smallstep, and then
    completeness of bigstep w.r.t. smallstep. *)

Ltac copy X := let Y := fresh X in pose proof X as Y.
Ltac autoconstruct := eauto; repeat (econstructor; eauto).

(** * Soundness of bigstep w.r.t. smallstep. *)

Section SOUNDNESS_OF_BIGSTEP.

Variable prog: program.
Let ge := Genv.globalenv prog.
Let L := semantics prog.

(* A bigstep expression that evaluates with some outcome will,
   in the equivalent small-step execution, come to a state that *matches* this outcome. *)

Inductive outcome_state_match
        (sp: val) (e: env) (m: mem) (f: function) (k: cont):
        outcome -> state -> Prop :=
  | osm_partial: forall S,
      outcome_state_match sp e m f k Out_partial S 
  | osm_normal:
      outcome_state_match sp e m f k
                          Out_normal
                          (State f Sskip k sp e m)
  | osm_exit: forall n,
      outcome_state_match sp e m f k
                          (Out_exit n)
                          (State f (Sexit n) k sp e m)
  | osm_return_none: forall k',
      call_cont k' = call_cont k ->
      outcome_state_match sp e m f k
                          (Out_return None)
                          (State f (Sreturn None) k' sp e m)
  | osm_return_some: forall k' a v,
      call_cont k' = call_cont k ->
      eval_expr ge sp e m a v ->
      outcome_state_match sp e m f k
                          (Out_return (Some v))
                          (State f (Sreturn (Some a)) k' sp e m)
  | osm_tail: forall v,
      outcome_state_match sp e m f k
                          (Out_tailcall_return v)
                          (Returnstate v (call_cont k) m).

Inductive outcome_call_state_match
          (res: val) (m: mem) (k: cont):
          outcome -> state -> Prop :=
  | ocsm_partial: forall S,
      outcome_call_state_match res m k Out_partial S
  | ocsm_intro:
      outcome_call_state_match res m k Out_normal (Returnstate res k m).

Remark is_call_cont_call_cont:
  forall k, is_call_cont (call_cont k).
Proof.
  induction k; simpl; auto.
Qed.

Remark call_cont_is_call_cont:
  forall k, is_call_cont k -> call_cont k = k.
Proof.
  destruct k; simpl; intros; auto || contradiction.
Qed.

(* Soundness of fun/stmt execution *)
Lemma eval_funcall_exec_stmt_steps:
  (forall m fd args t m' res out,
   eval_funcall ge m fd args t m' res out ->
   forall k,
   is_call_cont k ->
   exists S,
   star step ge (Callstate fd args k m) t S /\ outcome_call_state_match res m' k out S)
/\(forall f sp e m s t e' m' out,
   exec_stmt ge f sp e m s t e' m' out ->
   forall k,
   exists S,
   star step ge (State f s k sp e m) t S /\ outcome_state_match sp e' m' f k out S).
Proof.
  apply eval_funcall_exec_stmt_ind2; intros.

(* partial funcall *)
+  autoconstruct.

(* funcall internal *)
+  destruct (H2 k) as [S [A B]].
  assert (call_cont k = k) by (apply call_cont_is_call_cont; auto).
  inv B.
  (* Partial *)
  - eexists. split.
    eapply star_left. econstructor; eauto. eexact A. traceEq. constructor.
  (* Out normal *)
  - eexists. split.
    eapply star_left. econstructor; eauto. eapply star_right; eauto. constructor; eauto.
    traceEq. inv H3. constructor.
  (* Out_exit *)
  - inv H3.
  (* Out_return None *)
  - eexists. split.
    eapply star_left. econstructor; eauto. eapply star_right; eauto. constructor; eauto.
    traceEq. inv H3. replace k with (call_cont k') by congruence. constructor.
  (* Out_return Some *)
  - eexists. split.
    eapply star_left. econstructor; eauto. eapply star_right; eauto. constructor; eauto.
    traceEq. inv H3. replace k with (call_cont k') by congruence. constructor.
  (* Out_tailcall_return *)
  - eexists. split.
    eapply star_left. econstructor; eauto. apply A. traceEq.
    inv H3. inv H4. rewrite H6. constructor.

(* funcall external *)
+ autoconstruct; traceEq.

(* funcall external partial *)
+ autoconstruct; traceEq.

(* partial E0 *)
+ autoconstruct.

(* skip *)
+ autoconstruct.

(* assign *)
+ exists (State f Sskip k sp (PTree.set id v e) m); split.
  apply star_one. constructor. auto.
  constructor.

(* store *)
+ econstructor; split.
  apply star_one. econstructor; eauto.
  constructor.

(* call *)
+  destruct (H4 (Kcall optid f sp e k)) as [S [A B]]. constructor.
  inv B.
  - autoconstruct.
  - eexists; split.
    eapply star_left. econstructor; eauto.
    eapply star_right. apply A. constructor. traceEq. traceEq. inv H5. econstructor.

(* builtin *)
+  econstructor; split.
  apply star_one. econstructor; eauto.
  subst e'. constructor.

(* builtin partial *)
+  econstructor; split.
  apply star_one. econstructor; eauto.
  subst e'. constructor.

(* ifthenelse *)
+  destruct (H2 k) as [S [A B]].
  exists S; split.
  apply star_left with E0 (State f (if b then s1 else s2) k sp e m) t.
  econstructor; eauto. exact A.
  traceEq.
  auto.

(* seq continue *)
+ destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]].
  destruct (H2 k) as [S2 [A2 B2]].
  inv B1.
  exists S2; split.
  eapply star_left. constructor.
  eapply star_trans. eexact A1.
  eapply star_left. constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* seq stop *)
+  destruct (H0 (Kseq s2 k)) as [S1 [A1 B1]].
    set (S2 :=
    match out with
    | Out_exit n => State f (Sexit n) k sp e1 m1
    | _ => S1
    end).
    exists S2; split.
    eapply star_left. constructor. eapply star_trans. eexact A1.
    unfold S2; destruct out; try (apply star_refl).
    inv B1. apply star_one. constructor.
    reflexivity. traceEq.
    unfold S2; inv B1; congruence || simpl; constructor; auto.
  
(* loop loop *)
+  destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]].
  destruct (H2 k) as [S2 [A2 B2]].
  inv B1.
  exists S2; split.
  eapply star_left. constructor.
  eapply star_trans. eexact A1.
  eapply star_left. constructor. eexact A2.
  reflexivity. reflexivity. traceEq.
  auto.

(* loop stop *)
+  destruct (H0 (Kseq (Sloop s) k)) as [S1 [A1 B1]].
   set (S2 :=
    match out with
    | Out_exit n => State f (Sexit n) k sp e1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. constructor. eapply star_trans. eexact A1.
  unfold S2; destruct out; try (apply star_refl).
  inv B1. apply star_one. constructor.
  reflexivity. traceEq.
  unfold S2; inv B1; congruence || simpl; constructor; auto.

(* block *)
+  destruct (H0 (Kblock k)) as [S1 [A1 B1]].
   set (S2 :=
    match out with
    | Out_normal => State f Sskip k sp e1 m1
    | Out_exit O => State f Sskip k sp e1 m1
    | Out_exit (S m) => State f (Sexit m) k sp e1 m1
    | _ => S1
    end).
  exists S2; split.
  eapply star_left. constructor. eapply star_trans. eexact A1.
  unfold S2; destruct out; try (apply star_refl).
  inv B1. apply star_one. constructor.
  inv B1. apply star_one. destruct n; constructor.
  reflexivity. traceEq.
  unfold S2; inv B1; simpl; try constructor; auto.
  destruct n; constructor.

(* dummy *)
+ destruct (H0 k) as [S []]. autoconstruct. 

(* exit *)
+  autoconstruct. 

(* switch *)
+ econstructor; split.
  apply star_one. econstructor; eauto. constructor.

(* return none *)
+ autoconstruct.

(* return some *)
+ autoconstruct.

(* tailcall *)
+ destruct (H5 (call_cont k)) as [S [A B]]. apply is_call_cont_call_cont.
  inv B; inv H6; autoconstruct.
Qed.

Lemma eval_funcall_steps_full:
  (forall m fd args t m' res,
   eval_funcall ge m fd args t m' res Out_normal ->
   forall k,
   is_call_cont k ->
   exists S,
   star step ge (Callstate fd args k m) t S /\ outcome_call_state_match res m' k Out_normal S).
Proof.
  intros. eapply eval_funcall_exec_stmt_steps in H as [S []].
  inv H1. eexists; split; eauto. constructor. auto.
Qed.

Lemma exec_stmt_steps:
   forall f sp e m s t e' m' out,
   exec_stmt ge f sp e m s t e' m' out ->
   forall k,
   exists S,
   star step ge (State f s k sp e m) t S
   /\ outcome_state_match sp e' m' f k out S.
Proof.
  intros. eapply eval_funcall_exec_stmt_steps in H as [S []].
  exists S; split; eauto.
Qed.

(* Soundness of fun/stmt divergence *)
Lemma evalinf_funcall_forever:
  forall m fd args T k n,
  evalinf_funcall ge m fd args n T ->
  forever_x_plus L (Callstate fd args k m) n T.
Proof.
  cofix CIH_FUN.
  assert (forall sp e m s T f k n,
          execinf_stmt ge f sp e m s n T ->
          forever_x_plus L (State f s k sp e m) n T).
  cofix CIH_STMT.
  intros. inv H.

(* call *)
  eapply forever_x_plus_intro.
  apply plus_one. econstructor; eauto.
  apply CIH_FUN. eauto. eapply silent_to_event, evalinf_guard; eauto. tracexEq.

(* ifthenelse *)
  eapply forever_x_plus_intro with (s2 := State f (if b then s1 else s2) k sp e m).
  apply plus_one. econstructor; eauto.
  apply CIH_STMT. eauto. eapply silent_to_event, execinf_guard; eauto. tracexEq.

(* seq 1 *)
  eapply forever_x_plus_intro.
  apply plus_one. constructor.
  apply CIH_STMT. eauto. eapply silent_to_event, execinf_guard; eauto. tracexEq.

(* seq 2 *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H1 (Kseq s2 k)) as [S [A B]]. inv B.
  eapply forever_x_plus_intro.
  eapply plus_left. constructor.
  eapply star_right. eexact A. constructor.
  reflexivity. reflexivity.
  apply CIH_STMT. eauto. traceEq. traceEq.

(* loop body *)
  eapply forever_x_plus_intro.
  apply plus_one. econstructor; eauto.
  apply CIH_STMT. eauto. eapply silent_to_event, execinf_guard; eauto. tracexEq.

(* loop loop *)
  destruct (exec_stmt_steps _ _ _ _ _ _ _ _ _ H1 (Kseq (Sloop s0) k)) as [S [A B]]. inv B.
  eapply forever_x_plus_intro.
  eapply plus_left. constructor.
  eapply star_right. eexact A. constructor.
  reflexivity. reflexivity.
  apply CIH_STMT. eauto. traceEq. traceEq.

(* block *)
  eapply forever_x_plus_intro.
  apply plus_one. econstructor; eauto.
  apply CIH_STMT. eauto. eapply silent_to_event, execinf_guard; eauto. tracexEq.

(* dummy *)
  eapply forever_x_plus_intro.
  apply plus_one. econstructor; eauto.
  apply CIH_STMT. eauto. eapply silent_to_event, execinf_guard; eauto. tracexEq.

(* tailcall *)
  eapply forever_x_plus_intro.
  apply plus_one. econstructor; eauto.
  apply CIH_FUN. eauto. eapply silent_to_event, evalinf_guard; eauto. tracexEq.

(* function call *)
  intros. inv H0.
  eapply forever_x_plus_intro.
  apply plus_one. econstructor; eauto.
  apply H. eauto. eapply silent_to_event, execinf_guard; eauto. tracexEq.
Qed.

End SOUNDNESS_OF_BIGSTEP.


(** * Completeness of bigstep w.r.t. smallstep. *)

Section COMPLETENESS_OF_BIGSTEP.

Variable prog: program.
Let ge := Genv.globalenv prog.
Let L := semantics prog.


(** * Numbering states *)

Local Open Scope nat.

Definition Nstate: Type := state * nat.

Notation "# s" := (snd s) (at level 50).

Inductive Nstep: genv -> Nstate -> trace -> Nstate -> Prop :=
  | nstep: forall ge s1 s2 t i, step ge s1 t s2 -> Nstep ge (s1, i) t (s2, S i).

Inductive initial_Nstate: program -> Nstate -> Prop :=
  | init_Nstate: forall prog s, initial_state prog s -> initial_Nstate prog (s, O).

Inductive final_Nstate: Nstate -> int -> Prop :=
  | fin_Nstate: forall s n v, final_state s v -> final_Nstate (s, n) v.

Lemma Nstep_shift: forall s1 s2 i j t n,
  Nstep ge (s1, i) t (s2, j) ->
  Nstep ge (s1, i+n) t (s2, j+n).
Proof.
  intros. inv H. now constructor.
Qed.

Lemma Nstar_shift': forall s1 s2 t n,
  star Nstep ge s1 t s2 ->
  star Nstep ge (fst s1, #s1+n) t (fst s2, #s2+n).
Proof.
  intros. dependent induction H. apply star_refl.
  econstructor; eauto. apply Nstep_shift. now destruct s1, s2.
Qed.

Lemma Nstar_shift: forall s1 s2 i j t n,
  star Nstep ge (s1, i) t (s2, j) ->
  star Nstep ge (s1, i+n) t (s2, j+n).
Proof.
  intros. pose (S1 := (s1,i)). pose (S2 := (s2,j)). fold S1 in H. fold S2 in H.
  eapply Nstar_shift' in H; eauto.
Qed.

Lemma Nstar_le': forall s1 s2 t,
  star Nstep ge s1 t s2 ->
  #s1 <= #s2.
Proof.
  intros. dependent induction H. auto.
  inv H. simpl in *. lia.
Qed.

Lemma Nstar_le: forall s1 s2 i j t,
  star Nstep ge (s1, i) t (s2, j) ->
  i <= j.
Proof.
  intros. pose (S1 := (s1,i)). pose (S2 := (s2,j)). fold S1 in H. fold S2 in H.
  apply Nstar_le' in H; auto.
Qed.

Lemma number_execution: forall s1 s2 t n,
  star step ge s1 t s2 ->
  exists N, star Nstep ge (s1, n) t (s2, n+N).
Proof.
  intros. induction H.
  * exists 0. replace (n+0) with n by lia. apply star_refl.
  * destruct IHstar as [N]. exists (S N). econstructor.
    econstructor; eauto. apply Nstar_shift with (n:=1) in H2. replace (S n) with (n+1) by lia. replace (n + S N) with (n + N + 1) by lia. eauto. eauto.
Qed.

Lemma proj_execution: forall s1 s2 t,
  star Nstep ge s1 t s2 ->
  star step ge (fst s1) t (fst s2).
Proof.
  intros. induction H; econstructor; eauto. now inv H.
Qed.


Inductive inbetween s1 s2 s3 t12 t23 t13 : Prop :=
  | between: star Nstep ge s1 t12 s2 -> star Nstep ge s2 t23 s3 -> t13 = t12 ** t23 -> inbetween s1 s2 s3 t12 t23 t13.

Lemma inbetween_star_1: forall s1 s2 s3 s4 t12 t23 t34 t24 t13 t14,
  inbetween s2 s3 s4 t23 t34 t24 ->
  star Nstep ge s1 t12 s2 ->
  t13 = t12 ** t23 -> t14 = t13 ** t34 ->
  inbetween s1 s3 s4 t13 t34 t14.
Proof.
  intros. inv H. constructor; auto. eapply star_trans; eauto.
Qed.

Lemma inbetween_star_2: forall s1 s2 s3 s4 t12 t24 t14 t23 t34,
  inbetween s1 s2 s4 t12 t24 t14 ->
  star Nstep ge s2 t23 s3 ->
  star Nstep ge s3 t34 s4 ->
  inbetween s1 s3 s4 (t12**t23) t34 (t12**t23**t34).
Proof.
  intros. inv H. constructor; auto. eapply star_trans; eauto. traceEq.
Qed.

Lemma inbetween_concat: forall s1 s2 s3 s4 t12 t24 t14 t23 t34,
  inbetween s1 s2 s4 t12 t24 t14 ->
  inbetween s2 s3 s4 t23 t34 t24 ->
  inbetween s1 s3 s4 (t12**t23) t34 (t12**t23**t34).
Proof.
  intros. inv H0. eapply inbetween_star_2; eauto.
Qed.



(* A smallstep execution of a statement or function *matches* an outcome
   if the equivalent bigstep execution of the statement or function
   succeeds with this outcome. *)

Inductive outcome_star_match: state -> trace -> state -> outcome -> Prop :=
  | osm_state: forall f sp stmt e1 m1 e2 m2 t k out out_state,
      exec_stmt ge f sp e1 m1 stmt t e2 m2 out ->
      outcome_state_match prog sp e2 m2 f k out out_state ->
      outcome_star_match (State f stmt k sp e1 m1) t out_state out
  | osm_call: forall fd m1 m2 args t k res out out_state,
      eval_funcall ge m1 fd args t m2 res out ->
      outcome_call_state_match res m2 k out out_state ->
      outcome_star_match (Callstate fd args k m1) t out_state out
  | osm_return: forall res k m,
      outcome_star_match (Returnstate res k m) E0 (Returnstate res k m) Out_normal.


Section ExecutionCompleteness.

Context init (INIT: initial_Nstate prog (init, 0)).
Context (final: state) (N: nat).

(* For any Cminor state S that exists in a full or partial finite execution,
   there is a state which "terminates" the full or partial execution of the statement of S. *)

Definition Terminates i s := forall t is_partial
  (FIN: is_partial = false -> exists v, final_Nstate (final, N) v),
  star Nstep ge (s, i) t (final, N) ->
    (is_partial = true /\ outcome_star_match s t final Out_partial) \/
    exists s' out t1 t2,
      inbetween (s, i) s' (final, N) t1 t2 t /\ outcome_star_match s t1 (fst s') out /\ out <> Out_partial.
    

Inductive state_valid : state -> Prop :=
  | st_valid: forall f s k sp e m, state_valid (State f s k sp e m)
  | call_valid: forall fd args k m, is_call_cont k -> state_valid (Callstate fd args k m)
  | ret_valid: forall v k m, state_valid (Returnstate v k m).

Local Definition TermAll i := forall s, state_valid s -> Terminates i s.



Section SubProofs.


Ltac begin := unfold TermAll, Terminates in *; intros.

Ltac step_inv := match goal with
  | [ H : Nstep ge ?s1 ?t ?s2 |- _ ] => inv H; step_inv
  | [ H : final_Nstate ?s ?v |- _ ] => inv H; step_inv
  | [ H : step ge ?s1 ?t ?s2 |- _ ] => inv H; step_inv
  | [ H : final_state ?s ?v |- _ ] => inv H; step_inv
  | _ => idtac
end.

Ltac solve_partial is_partial FIN :=
  destruct is_partial; [ left; autoconstruct | exfalso; destruct (FIN eq_refl); step_inv ].

Context (i: nat) (I: i <= N).
Hypothesis IH: forall j, j > i -> j <= N -> TermAll j.

Lemma T_skip: forall f k sp env m, Terminates i (State f Sskip k sp env m).
Proof.
  begin. right. eexists. exists Out_normal. repeat eexists. apply star_refl. apply H. auto. autoconstruct. congruence.
Qed.

Lemma T_assign: forall f k sp env m id e, Terminates i (State f (Sassign id e) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  right. eexists. exists Out_normal. repeat eexists. apply star_one; autoconstruct. eauto. autoconstruct. congruence.
  Unshelve. all: auto.
Qed.


Lemma T_store: forall f k sp env m chunk addr a, Terminates i (State f (Sstore chunk addr a) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  right. eexists. exists Out_normal. repeat eexists. apply star_one; autoconstruct. eauto. autoconstruct. congruence.
  Unshelve. all: auto.
Qed.

Lemma T_call: forall f k sp env m optid sig a bl, Terminates i (State f (Scall optid sig a bl) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  eapply IH in H1 as [[out] | [s' [out [t1 [t3 [? []]]]]]]; [ | | lia | eapply Nstar_le; eauto | autoconstruct | apply FIN ].
  * left. inv H. autoconstruct.
  * inv H0. inv H10. congruence. destruct s'. simpl in H3. subst s.
    copy H. inv H. inv H3; step_inv. solve_partial is_partial FIN. eapply implies_partial. rewrite E0_right. eauto.
    right. exists (State f Sskip k sp (set_optvar optid res env) m2, S n), Out_normal. do 2 eexists.
    split; [| autoconstruct ].
    eapply inbetween_star_1.
    - eapply inbetween_star_2; eauto. apply star_one; autoconstruct.
    - apply star_one; autoconstruct.
    - traceEq.
    - traceEq.
  Unshelve. all: auto.
Qed.

Lemma T_tailcall: forall f k sp env m sig a bl, Terminates i (State f (Stailcall sig a bl) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  eapply IH in H1 as [[out] | [s' [out [t1 [t3 [? []]]]]]]; [ | | lia | eapply Nstar_le; eauto | constructor; apply is_call_cont_call_cont | apply FIN ].
  * left. inv H. autoconstruct.
  * inv H0. inv H10. congruence. destruct s'. simpl in H3. subst s.
    right. exists (Returnstate res (call_cont k) m2, n), (Out_tailcall_return res). do 2 eexists.
    split; [| autoconstruct ].
    eapply inbetween_star_1.
    - apply H.
    - apply star_one. autoconstruct.
    - traceEq.
    - inv H. traceEq.
    - congruence.
  Unshelve. all: auto.
Qed.

Lemma T_builtin: forall f k sp env m optid ef bl, Terminates i (State f (Sbuiltin optid ef bl) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  right. eexists. exists (outcome_funcall Out_normal). repeat eexists. apply star_one; autoconstruct. eauto. autoconstruct. easy.
  Unshelve. all: auto.
Qed.

Lemma T_seq: forall f k sp env m s1 s2, Terminates i (State f (Sseq s1 s2) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  eapply IH in H1 as [[out] | [s' [out [t1 [t3 [? []]]]]]]; [ | | lia | eapply Nstar_le; eauto | constructor | apply FIN ].
  * left. inv H. split; auto. econstructor. constructor; eauto. congruence. constructor.
  * inv H0. destruct s'. simpl in H12. inv H12.
  + congruence.
  + copy H. inv H0. inv H3; step_inv. 3: inv H12. { solve_partial is_partial FIN. }
    eapply IH in H4 as [[out] | [s' [out [t3 [t4 [? []]]]]]]; [ | | apply Nstar_le in H2; lia | eapply Nstar_le; eauto | constructor | apply FIN ].
    { left. inv H0. autoconstruct. }
    inv H3. right.
    exists s', out. do 2 eexists.
    split; [| autoconstruct ].
    eapply inbetween_star_1; traceEq.
    - inv H0. econstructor; eauto.
    - econstructor. autoconstruct. eapply star_right. apply H2. autoconstruct. traceEq. traceEq.
    - eauto. now inv H0.
  + copy H. inv H0. inv H3; step_inv. {  destruct is_partial; [ left | exfalso; destruct (FIN eq_refl); step_inv ]. split; auto. econstructor; eauto. eapply exec_Sseq_stop; eauto. eapply implies_partial. rewrite E0_right. eauto. congruence. constructor. }
    right. exists (State f (Sexit n0) k sp e2 m2, S n), (Out_exit n0). do 2 eexists.
    split. 2: { econstructor. econstructor; eauto. eapply exec_Sseq_stop; eauto. all: autoconstruct; congruence. }
    eapply inbetween_star_1; traceEq.
    - eapply inbetween_star_2; autoconstruct.
    - autoconstruct.
    - traceEq.
  + right. exists (State f (Sreturn None) k' sp e2 m2, n), (Out_return None). do 2 eexists.
    split. 2: { econstructor. econstructor; eauto. eapply exec_Sseq_stop; eauto. all: autoconstruct; congruence. }
    eapply inbetween_star_1; autoconstruct; traceEq. now inv H.
  + right. exists (State f (Sreturn (Some a)) k' sp e2 m2, n), (Out_return (Some v)). do 2 eexists.
    split. 2: { econstructor. econstructor; eauto. eapply exec_Sseq_stop; eauto. all: autoconstruct; congruence. }
    eapply inbetween_star_1; autoconstruct; traceEq. now inv H.
  + right. exists (Returnstate v (call_cont k) m2, n), (Out_tailcall_return v). do 2 eexists.
    split. 2: { econstructor. econstructor; eauto. eapply exec_Sseq_stop; eauto. all: autoconstruct; congruence. }
    eapply inbetween_star_1; autoconstruct; traceEq. now inv H.
  Unshelve. all: auto.
Qed.

Lemma T_ifthenelse: forall f k sp env m a s1 s2, Terminates i (State f (Sifthenelse a s1 s2) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  eapply IH in H1 as [[out] | [s' [out [t1 [t3 [? []]]]]]]; [ | | lia | eapply Nstar_le; eauto | constructor; apply is_call_cont_call_cont | apply FIN ].
  * left. inv H. autoconstruct.
  * right. inv H0. exists s', out. do 2 eexists.
    split; [| autoconstruct ].
    eapply inbetween_star_1; autoconstruct; traceEq. now inv H.
  Unshelve. all: auto.
Qed.

Lemma T_loop: forall f k sp env m s, Terminates i (State f (Sloop s) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  eapply IH in H1 as [[out] | [s' [out [t1 [t3 [? []]]]]]]; [ | | lia | eapply Nstar_le; eauto | constructor | apply FIN ].
  * left. inv H. split; auto. econstructor. constructor; eauto. congruence. constructor.
  * inv H0. destruct s'. simpl in H12. inv H12.
  + congruence.
  + copy H. inv H0. inv H3; step_inv. 3: inv H12. { solve_partial is_partial FIN. }
    eapply IH in H4 as [[out] | [s' [out [t3 [t4 [? []]]]]]]; [ | | apply Nstar_le in H2; lia | eapply Nstar_le; eauto | constructor | apply FIN ].
    { left. inv H0. autoconstruct. }
    inv H3. right.
    exists s', out. do 2 eexists.
    split; [| autoconstruct ].
    eapply inbetween_star_1; traceEq.
    - inv H0. econstructor; eauto.
    - econstructor. autoconstruct. eapply star_right. apply H2. autoconstruct. traceEq. traceEq.
    - eauto. now inv H0.
  + copy H. inv H0. inv H3; step_inv. {  destruct is_partial; [ left | exfalso; destruct (FIN eq_refl); step_inv ]. split; auto. econstructor; eauto. eapply exec_Sloop_stop; eauto. eapply implies_partial. rewrite E0_right. eauto. congruence. constructor. }
    right. exists (State f (Sexit n0) k sp e2 m2, S n), (Out_exit n0). do 2 eexists.
    split. 2: { econstructor. econstructor; eauto. eapply exec_Sloop_stop; eauto. all: autoconstruct; congruence. }
    eapply inbetween_star_1; traceEq.
    - eapply inbetween_star_2; autoconstruct.
    - autoconstruct.
    - traceEq.
  + right. exists (State f (Sreturn None) k' sp e2 m2, n), (Out_return None). do 2 eexists.
    split. 2: { econstructor. econstructor; eauto. eapply exec_Sloop_stop; eauto. all: autoconstruct; congruence. }
    eapply inbetween_star_1; autoconstruct; traceEq. now inv H.
  + right. exists (State f (Sreturn (Some a)) k' sp e2 m2, n), (Out_return (Some v)). do 2 eexists.
    split. 2: { econstructor. econstructor; eauto. eapply exec_Sloop_stop; eauto. all: autoconstruct; congruence. }
    eapply inbetween_star_1; autoconstruct; traceEq. now inv H.
  + right. exists (Returnstate v (call_cont k) m2, n), (Out_tailcall_return v). do 2 eexists.
    split. 2: { econstructor. econstructor; eauto. eapply exec_Sloop_stop; eauto. all: autoconstruct; congruence. }
    eapply inbetween_star_1; autoconstruct; traceEq. now inv H.
  Unshelve. all: auto.
Qed.

Lemma T_block: forall f k sp env m b, Terminates i (State f (Sblock b) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  eapply IH in H1 as [[out] | [s' [out [t1 [t3 [? []]]]]]]; [ | | lia | eapply Nstar_le; eauto | constructor; apply is_call_cont_call_cont | apply FIN ].
  * left. inv H. replace Out_partial with (outcome_block Out_partial) by auto. autoconstruct.
  * inv H0. copy H. inv H. destruct s'. simpl in H12. inv H12.
    + congruence.
    + inv H3; step_inv. 3: inv H12. { solve_partial is_partial FIN. eapply implies_partial. rewrite E0_right. autoconstruct. }
      right. exists (State f Sskip k sp e2 m2, S n), (outcome_block Out_normal). do 2 eexists.
      split; [| autoconstruct ].
      eapply inbetween_star_1.
      - eapply inbetween_star_2. apply H0. autoconstruct. apply H4.
      - autoconstruct.
      - traceEq.
      - traceEq.
    + inv H3; step_inv. { solve_partial is_partial FIN. eapply implies_partial. rewrite E0_right. autoconstruct. }
    ** right. exists (State f Sskip k sp e2 m2, S n), (outcome_block (Out_exit 0)). do 2 eexists.
       split; [| autoconstruct ].
       eapply inbetween_star_1.
      - eapply inbetween_star_2. apply H0. autoconstruct. apply H4.
      - autoconstruct.
      - traceEq.
      - traceEq.
      - easy.
    ** right. exists (State f (Sexit n1) k sp e2 m2, S n), (outcome_block (Out_exit (S n1))). do 2 eexists.
       split; [| autoconstruct ].
       eapply inbetween_star_1.
      - eapply inbetween_star_2. apply H0. autoconstruct. apply H4.
      - autoconstruct.
      - traceEq.
      - traceEq.
      - easy.
    + right. exists (State f (Sreturn None) k' sp e2 m2, n), (outcome_block (Out_return None)). do 2 eexists.
      split; [| autoconstruct ].
      eapply inbetween_star_1; autoconstruct; traceEq.
    + right. exists (State f (Sreturn (Some a)) k' sp e2 m2, n), (outcome_block (Out_return (Some v))). do 2 eexists.
      split; [| autoconstruct ].
      eapply inbetween_star_1; autoconstruct; traceEq.
    + right. exists (Returnstate v (call_cont k) m2, n), (outcome_block (Out_tailcall_return v)). do 2 eexists.
      split; [| autoconstruct ].
      eapply inbetween_star_1; autoconstruct; traceEq.
  Unshelve. all: auto.
Qed.

Lemma T_dummy: forall f k sp env m b, Terminates i (State f (Sdummy b) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  eapply IH in H1 as [[out] | [s' [out [t1 [t3 [? []]]]]]]; [ | | lia | eapply Nstar_le; eauto | constructor; apply is_call_cont_call_cont | apply FIN ].
  * left. inv H. autoconstruct.
  * right. exists s', out. do 2 eexists.
    inv H. split. constructor. eapply star_trans; eauto. apply star_one. autoconstruct. eauto. traceEq.
    split. inv H0. econstructor; eauto. now constructor. auto.
  Unshelve. all: auto.
Qed.

Lemma T_exit: forall f k sp env m n, Terminates i (State f (Sexit n) k sp env m).
Proof.
  begin. right. exists (State f (Sexit n) k sp env m, i), (Out_exit n). do 2 eexists. autoconstruct. congruence.
Qed.

Lemma T_return: forall f k sp env m v, Terminates i (State f (Sreturn v) k sp env m).
Proof.
  begin. copy H. inv H0; step_inv. solve_partial is_partial FIN.
  + right. exists (State f (Sreturn None) k (Vptr sp0 Ptrofs.zero) env m, i), (Out_return None). do 2 eexists. autoconstruct. congruence.
  + right. exists (State f (Sreturn (Some a)) k (Vptr sp0 Ptrofs.zero) env m, i), (Out_return (Some v0)). do 2 eexists. autoconstruct. congruence.
  Unshelve. all: auto.
Qed.

Lemma T_switch: forall f k sp env m l a c def, Terminates i (State f (Sswitch l a c def) k sp env m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  right. eexists. eexists (Out_exit _). autoconstruct. congruence.
  Unshelve. all: auto.
Qed.

Lemma T_returnstate: forall v k m, Terminates i (Returnstate v k m).
Proof.
  begin. right. exists (Returnstate v k m, i), Out_normal. do 2 eexists. autoconstruct. congruence.
Qed.

Ltac solve_partial_funcall is_partial FIN :=
  solve_partial is_partial FIN; rewrite E0_right; replace Out_partial with (outcome_funcall Out_partial) by auto; autoconstruct; eapply implies_partial; autoconstruct.

Lemma T_callstate: forall fd args k m
  (K: is_call_cont k),
  Terminates i (Callstate fd args k m).
Proof.
  begin. inv H; step_inv. solve_partial is_partial FIN.
  (* internal function *)
  + eapply IH in H1 as [[out] | [s' [out [t1 [t3 [? []]]]]]]; [ | | lia | eapply Nstar_le; eauto | constructor | apply FIN ].
  ++ left. inv H. replace Out_partial with (outcome_funcall Out_partial) by auto. autoconstruct.
  ++ inv H0. destruct s'. inv H13.
    * congruence.
    * simpl in H2. subst.
      copy H. inv H. inv H3; step_inv; try inv K. { solve_partial_funcall is_partial FIN. } 
      right. exists (Returnstate Vundef k m'0, S n). exists Out_normal. do 2 eexists.
      split; [| autoconstruct ]. 2: { replace Out_normal with (outcome_funcall Out_normal). autoconstruct. auto. }
      eapply inbetween_star_1; traceEq.
      - eapply inbetween_star_2. apply H0. eapply star_one; autoconstruct. apply H4.
      - eapply star_one; autoconstruct.
      - traceEq.
    * simpl in H2. subst.
      inv H. inv H2; step_inv; try inv K.
      { solve_partial_funcall is_partial FIN. }
    * simpl in H3. subst.
      copy H. inv H. inv H4; step_inv.
      { solve_partial_funcall is_partial FIN. }
      right. exists (Returnstate Vundef (call_cont k') m'0, S n). exists Out_normal. do 2 eexists.
      split. 2: { split. 2: congruence. replace Out_normal with (outcome_funcall (Out_return None)) by auto. rewrite H0, call_cont_is_call_cont; autoconstruct; auto. }
      eapply inbetween_star_1; traceEq.
      - eapply inbetween_star_2. apply H2. eapply star_one; autoconstruct. apply H5. 
      - eapply star_one; autoconstruct.
      - traceEq.
    * simpl in H4. subst.
      copy H. inv H. inv H5; step_inv.
      { solve_partial_funcall is_partial FIN. }
      assert (v = v0) by (eapply eval_expr_determ; eauto). subst.
      right. exists (Returnstate v0 (call_cont k') m'0, S n). exists Out_normal. do 2 eexists.
      split. 2: { split. 2: congruence. replace Out_normal with (outcome_funcall (Out_return (Some v0))) by auto. rewrite H0, call_cont_is_call_cont; autoconstruct; auto. }
      eapply inbetween_star_1; traceEq.
      - eapply inbetween_star_2. apply H3. eapply star_one; autoconstruct. apply H6.
      - eapply star_one; autoconstruct.
      - traceEq.
    * simpl in H2. subst.
      right. exists (Returnstate v (call_cont k) m2, n). exists Out_normal. do 2 eexists.
      split. 2: { split. 2: congruence. replace Out_normal with (outcome_funcall (Out_tailcall_return v)) by auto. rewrite call_cont_is_call_cont; autoconstruct; auto. }
      eapply inbetween_star_1; traceEq.
       - apply H.
       - apply star_one; autoconstruct.
       - traceEq.
       - now inv H.
  (* external function *)
  + inv H1; step_inv.
    * right. exists (Returnstate vres k m', S i). exists (outcome_funcall Out_normal). do 2 eexists.
      split; autoconstruct. now rewrite E0_right. easy.
    * right. exists (Returnstate vres (Kcall optid f sp e k0) m', S i). exists (outcome_funcall Out_normal). do 2 eexists.
      split; autoconstruct. traceEq. easy.
  Unshelve. all: auto; exact Vundef.
Qed.

End SubProofs.

(* Every state in a smallstep execution terminates with a matching bigstep result.
   We show this via induction on the remaining length of the execution. *)

Lemma every_state_terminates:
  forall i, i <= N -> TermAll i.
Proof.
  intros. exploit strong_ind. Unshelve. 3: { exact (fun j => TermAll (N-j)). } 3: { exact (N-i). } 2: { simpl. now replace (N-(N-i)) with i by lia. }
  unfold TermAll. intros.
  assert (forall j, j > N-m -> j <= N -> TermAll j). { unfold TermAll. intros. replace j with (N-(N-j)) by lia. apply H0. lia. auto. }
  assert (N - m <= N) by lia.
  case s in *; intros.
  + case s.
  * now apply T_skip.
  * now apply T_assign.
  * now apply T_store.
  * now apply T_call.
  * now apply T_tailcall.
  * now apply T_builtin.
  * now apply T_seq.
  * now apply T_ifthenelse.
  * now apply T_loop.
  * now apply T_block.
  * now apply T_dummy.
  * now apply T_exit.
  * now apply T_switch.
  * now apply T_return.
  + inv H1. now apply T_callstate.
  + now apply T_returnstate.
Qed.

Corollary callstate_will_return: forall fd args k m t i v
  (FIN: final_Nstate (final, N) v),
  is_call_cont k ->
  star Nstep ge (Callstate fd args k m, i) t (final, N) ->
  exists m' j res t1 t2,
    inbetween (Callstate fd args k m, i) (Returnstate res k m', j) (final, N) t1 t2 t /\
    eval_funcall ge m fd args t1 m' res Out_normal.
Proof.
  intros. assert (Termi: TermAll i). { apply every_state_terminates. eapply Nstar_le; eauto. }
  eapply Termi in H0 as [[out] | [s' [out [t1 [t2 [? []]]]]]]; eauto.
  Unshelve. 4: exact false. congruence. 2: autoconstruct.
  inv H1. inv H11. congruence. destruct s'. simpl in H4. subst s. autoconstruct.
Qed.

Corollary callstate_partial: forall fd m t i,
  star Nstep ge (Callstate fd nil Kstop m, i) t (final, N) ->
  exists m' res,
    eval_funcall ge m fd nil t m' res Out_partial.
Proof.
  intros. assert (Termi: TermAll i). { apply every_state_terminates. eapply Nstar_le; eauto. }
  eapply Termi in H as [[out] | [s' [out [t1 [t2 [? []]]]]]]; eauto. 
  Unshelve. 5: exact true. 3: autoconstruct. 3: congruence.
  + inv H. autoconstruct.
  + inv H0. inv H10. congruence. inv H.
    inv H0. simpl in H3. congruence.
    destruct s'. simpl in H3. subst s. inv H2. 2: { inv H0. inv H10. }
    apply implies_partial in H9. rewrite E0_right. autoconstruct.
Qed.

End ExecutionCompleteness.


Section DivergenceCompleteness.

Open Scope Z.

Lemma rectify_silent_M_n: forall s t n M,
  forever_x_step L s M t ->
  event_guard t n E0 M ->
  forever_x_step L s (n-1) t.
Proof.
  intros. destruct H0 as [|[?[?[]]]].
  subst. eapply forever_x_step_X0_irrel; eauto.
  eapply forever_x_step_monotone; eauto. pose proof (H3 eq_refl). lia.
Qed.

Lemma rectify_silent_M_n_plus: forall s t n M,
  forever_x_plus L s M t ->
  event_guard t n E0 M ->
  forever_x_plus L s (n-1) t.
Proof.
  intros. destruct H0 as [|[?[?[]]]].
  subst. eapply forever_x_plus_X0_irrel; eauto.
  eapply forever_x_plus_monotone; eauto. pose proof (H3 eq_refl). lia.
Qed.

Lemma guard_helper: forall t T n' n M,
  (t = E0 -> n' <= n-1) ->
  silent_guard (t°°T) (n-1) ->
  event_guard T n' E0 M ->
  event_guard (t °° T) n t (Z.max M 0).
Proof.
  intros. destruct (inv_tracex T) as [|[e[T']]], t; subst.
  * now left.
  * destruct H0. easy. right. repeat split; try lia. easy.
  * destruct H1 as [|[?[?[]]]]. now destruct T'. pose proof (H eq_refl). pose proof (H4 eq_refl).
    right. repeat split; auto; lia.
  * destruct H1 as [|[?[?[]]]]. now destruct T'. destruct H0. now destruct T'. pose proof (H4 eq_refl).
    right. repeat split; auto; try lia. easy.
Qed.

Section Subproofs.

Hypothesis CIH_STMT: forall f sp stmt e m T k n,
  forever_x_step L (State f stmt k sp e m) n T ->
  (~ exists t e' m' out, exec_stmt ge f sp e m stmt t e' m' out /\ tracex_prefix t T /\ out <> Out_partial) ->
  execinf_stmt ge f sp e m stmt n T.

Lemma forever_execinf_Sseq: forall f sp e m s1 s2 k n T,
  forever_x_step L (State f s1 (Kseq s2 k) sp e m) (n-1) T ->
  ~ (exists t e' m' out, exec_stmt ge f sp e m (Sseq s1 s2) t e' m' out /\ tracex_prefix t T /\ out <> Out_partial) ->
  execinf_stmt ge f sp e m (Sseq s1 s2) n T.
Proof.
  intros.
  destruct (
    classic (exists t e' m' out, exec_stmt ge f sp e m s1 t e' m' out /\ tracex_prefix t T /\ out <> Out_partial)
  ) as [[t [e' [m' [out [? [? OP]]]]]] | ].
  + apply tracex_prefix_inv in H2 as [T'].
    pose proof H1. eapply exec_stmt_steps with (k:=Kseq s2 k) in H3 as [S []]; auto. inv H4.
    - congruence.
    - eapply (cut_forever_x_step (semantics_determinate prog)) in H3 as [n' []]; eauto.
      inv H2. inv H4. 2: inv H13. rewrite X0_left.
      eapply execinf_Sseq_2 with (t1:=t) (M:=Z.max M 0); eauto.
      * eapply guard_helper; rewrite X0_left in *; eauto. inv H. eapply event_to_silent; eauto.
      * eapply forever_x_step_monotone with (n2:=Z.max M 0) in H5; [|lia].
        eapply CIH_STMT; eauto.
        intros [t' [e'' [m'' [out' [? [? OP']]]]]].
        apply H0. do 3 eexists. exists out'. autoconstruct. apply tracex_prefix_app; tracexEq.
    - exfalso. apply H0. exists t, e', m', (Out_exit n0).
      split. eapply exec_Sseq_stop; eauto. congruence. split. apply tracex_prefix_spec. congruence.
    - exfalso. apply H0. exists t, e', m', (Out_return None).
      split. eapply exec_Sseq_stop; eauto. congruence. split. apply tracex_prefix_spec. congruence.
    - exfalso. apply H0. exists t, e', m', (Out_return (Some v)).
      split. eapply exec_Sseq_stop; eauto. congruence. split. apply tracex_prefix_spec. congruence.
    - exfalso. apply H0. exists t, e', m', (Out_tailcall_return v).
      split. eapply exec_Sseq_stop; eauto. congruence. split. apply tracex_prefix_spec. congruence.
  + eapply execinf_Sseq_1; eauto.
    inv H. now apply event_to_silent, guard_incr1 in H4.
Defined.

Lemma forever_execinf_Sloop: forall f sp e m s k n T,
  forever_x_step L (State f s (Kseq (Sloop s) k) sp e m) (n-1) T ->
  ~ (exists t e' m' out, exec_stmt ge f sp e m (Sloop s) t e' m' out /\ tracex_prefix t T /\ out <> Out_partial) ->
  execinf_stmt ge f sp e m (Sloop s) n T.
Proof.
  intros.
  destruct (
    classic (exists t e' m' out, exec_stmt ge f sp e m s t e' m' out /\ tracex_prefix t T /\ out <> Out_partial)
  ) as [[t [e' [m' [out [? [? OP]]]]]] | ].
  + apply tracex_prefix_inv in H2 as [T'].
    pose proof H1. eapply exec_stmt_steps with (k:=Kseq (Sloop s) k) in H3 as [S []]; auto. inv H4.
    - congruence.
    - eapply (cut_forever_x_step (semantics_determinate prog)) in H3 as [n' []]; eauto.
      inv H2. inv H4; [|inv H13]. rewrite X0_left in *.
      eapply execinf_Sloop_loop; eauto.
      * eapply guard_helper; eauto. inv H. eapply event_to_silent; eauto.
      * eapply CIH_STMT; eauto.
        eapply forever_x_step_monotone with (n2:=Z.max M 0) in H5; [|lia]. eauto.
        intros [t' [e'' [m'' [out [? [? OP']]]]]]. apply H0. do 3 eexists. exists out. autoconstruct. now apply tracex_prefix_app.
    - exfalso. apply H0. exists t, e', m', (Out_exit n0).
      split. eapply exec_Sloop_stop; eauto. congruence. split. apply tracex_prefix_spec. congruence.
    - exfalso. apply H0. exists t, e', m', (Out_return None).
      split. eapply exec_Sloop_stop; eauto. congruence. split. apply tracex_prefix_spec. congruence.
    - exfalso. apply H0. exists t, e', m', (Out_return (Some v)).
      split. eapply exec_Sloop_stop; eauto. congruence. split. apply tracex_prefix_spec. congruence.
    - exfalso. apply H0. exists t, e', m', (Out_tailcall_return v).
      split. eapply exec_Sloop_stop; eauto. congruence. split. apply tracex_prefix_spec. congruence.
  + eapply execinf_Sloop_body; eauto. 
    inv H. now apply event_to_silent, guard_incr1 in H4.
Defined.

Lemma forever_evalinf_callstate: forall fd args k m n T,
  is_call_cont k ->
  forever_x_step L (Callstate fd args k m) n T ->
  (~ exists t m' res, eval_funcall ge m fd args t m' res Out_normal /\ tracex_prefix t T) ->
  evalinf_funcall ge m fd args n T.
Proof.
  intros. inv H0. inv H2.
  + rewrite X0_left in *.
    econstructor; eauto. eapply event_to_silent; eauto.
    eapply rectify_silent_M_n in H4; eauto.
    eapply CIH_STMT; eauto.
    intros [t [e' [m'' [res [? [? OP]]]]]]. apply H1.
    apply tracex_prefix_inv in H2 as [T].
    pose proof H0. eapply exec_stmt_steps with (k:=k) in H5 as [S []]; auto.
    eapply (cut_forever_x_step (semantics_determinate prog)) in H5 as [n' []]; eauto. 2: { rewrite H2; eauto. }
    inv H6.
    - congruence.
    - replace Out_normal with (outcome_funcall Out_normal) by auto.
      destruct k; inv H; inv H5; inv H; inv H2; inv H.
      exists t, m'0, Vundef. autoconstruct. apply tracex_prefix_spec.
    - destruct k; inv H; inv H5; inv H.
    - replace Out_normal with (outcome_funcall (Out_return None)) by auto.
      destruct k; inv H; inv H5; inv H; inv H2.
      inv H. rewrite H8 in H12. simpl in H12. congruence.
      exists t, m'0, Vundef. autoconstruct. apply tracex_prefix_spec.
    - replace Out_normal with (outcome_funcall (Out_return (Some v))) by auto.
      destruct k; inv H; inv H5; inv H; inv H2.
      inv H. rewrite H8 in H13. simpl in H13. congruence.
      exists t, m'0, v. autoconstruct. apply tracex_prefix_spec.
    - replace Out_normal with (outcome_funcall (Out_tailcall_return v)) by auto.
      destruct k; inv H; inv H5; inv H; inv H2; inv H.
      exists t, m'', v. autoconstruct. apply tracex_prefix_spec.
      exists t, m'', v. autoconstruct. apply tracex_prefix_spec.
      exists t, m'', v. autoconstruct. apply tracex_prefix_spec.
  + exfalso. apply H1. replace Out_normal with (outcome_funcall Out_normal) by auto.
    autoconstruct. apply tracex_prefix_spec.
Defined.

End Subproofs.

(* For a diverging smallstep execution starting at a callstate,
   the corresponding function either bigstep-evaluates with a prefix of the given trace,
   or the function bigstep-diverges with the given trace. *)
Lemma forever_eval_or_evalinf: forall m fd args T k n,
  is_call_cont k ->
  forever_x_step L (Callstate fd args k m) n T ->
  (~ exists t m' res, eval_funcall ge m fd args t m' res Out_normal /\ tracex_prefix t T) ->
  evalinf_funcall ge m fd args n T.
Proof.
  cofix CIH_FUN.
  assert (
    forall f sp stmt e m T k n,
    forever_x_step L (State f stmt k sp e m) n T ->
    (~ exists t e' m' out, exec_stmt ge f sp e m stmt t e' m' out /\ tracex_prefix t T /\ out <> Out_partial) ->
    execinf_stmt ge f sp e m stmt n T
  ).
  cofix CIH_STMT.
  Ltac exists_out H out :=
    exfalso; apply H; do 3 eexists; exists out; autoconstruct; [ apply tracex_prefix_E0 | congruence ].
  intros. inv H. inv H1.
  * exists_out H0 Out_normal.
  * exists_out H0 Out_normal.
  * exists_out H0 Out_normal.
  * exists_out H0 Out_normal.
  * exists_out H0 Out_normal.
  * eapply execinf_Scall; eauto; rewrite X0_left in *. eapply event_to_silent; eauto.
    eapply rectify_silent_M_n in H2; eauto. eapply CIH_FUN; eauto. now simpl.
    intros [t [m' [res [?]]]]. apply H0. exists t. autoconstruct. congruence.
  * eapply execinf_Stailcall; eauto; rewrite X0_left in *. eapply event_to_silent; eauto.
    eapply rectify_silent_M_n in H2; eauto. eapply CIH_FUN; eauto. apply is_call_cont_call_cont.
    intros [t [m'' [res [?]]]]. apply H0. exists t. autoconstruct. congruence.
  * exfalso. apply H0. do 3 eexists. exists (outcome_funcall Out_normal). autoconstruct. apply tracex_prefix_spec. easy. 
  * eapply forever_execinf_Sseq; eauto. eapply rectify_silent_M_n in H2; rewrite X0_left in *; eauto.
  * eapply execinf_Sifthenelse; eauto; rewrite X0_left in *. eapply event_to_silent; eauto.
    eapply rectify_silent_M_n in H2; eauto. eapply CIH_STMT; eauto.
    intros [t [e' [m' [res [?]]]]]. apply H0. autoconstruct.
  * eapply forever_execinf_Sloop; eauto. eapply rectify_silent_M_n in H2; rewrite X0_left in *; eauto.
  * eapply execinf_Sblock; eauto; rewrite X0_left in *. eapply event_to_silent; eauto.
    eapply rectify_silent_M_n in H2; eauto. eapply CIH_STMT; eauto.
    intros [t [e' [m' [res [? []]]]]]. apply H0. do 3 eexists. exists (outcome_block res). autoconstruct. destruct res; auto. destruct n0; easy.
  * eapply execinf_Sdummy; eauto; rewrite X0_left in *. eapply event_to_silent; eauto.
    eapply rectify_silent_M_n in H2; eauto. eapply CIH_STMT; eauto.
    intros [t [e' [m' [res [? []]]]]]. apply H0. do 3 eexists. exists res. autoconstruct.
  * exists_out H0 (Out_exit n0).
  * exists_out H0 (Out_exit 0).
  * exists_out H0 (Out_exit (S n0)).
  * exists_out H0 (Out_exit (Switch.switch_target n0 default cases)).
  * exists_out H0 (Out_return None).
  * exists_out H0 (Out_return (Some v)).
  * intros. eapply forever_evalinf_callstate; eauto.
Qed.

Corollary forever_evalinf: forall m fd args n T,
  forever_x_step L (Callstate fd args Kstop m) n T ->
  evalinf_funcall ge m fd args n T.
Proof.
  intros. apply forever_eval_or_evalinf with (k:=Kstop). constructor. auto.
  intros [t [m' [res [?]]]]. apply eval_funcall_steps_full with (k:=Kstop) in H0 as [S [A B]]; [|constructor].
  eapply tracex_prefix_inv in H1 as [T']. subst.
  eapply (cut_forever_x_step (semantics_determinate prog)) in A as [? []]; eauto. inv B. inv H0. inv H2.
Qed.

End DivergenceCompleteness.

End COMPLETENESS_OF_BIGSTEP.


(** Putting it together *)

Section EQUIVALENCE.

Variable prog: program.

Definition smallstep_semantics := beh_semantics prog.
Definition bigstep_semantics := specific (bigstep_semantics prog).

Theorem bigstep_semantics_sound:
  bigstep_sound bigstep_semantics smallstep_semantics.
Proof.
  constructor; intros.
  * inv H. inv H0.
    eapply eval_funcall_steps_full with (k:=Kstop) in H1 as [S2 []]; inv H1; autoconstruct.
  * inv H.
    eapply evalinf_funcall_forever, forever_x_of_plus in H1; eauto. destruct T.
    + apply forever_x_finite in H1 as [s []]. inv H0. autoconstruct.
    + apply forever_x_reactive in H1. inv H0. autoconstruct.
  * inv H.
    + inv H0. eapply eval_funcall_exec_stmt_steps with (k:=Kstop) in H1 as [S2 []]; autoconstruct.
    + constructor 2. intros [s]. apply H0. inv H. autoconstruct.
  * auto.
Qed.

Theorem bigstep_semantics_complete:
  bigstep_complete bigstep_semantics smallstep_semantics.
Proof.
  constructor; intros.
  * inv H. inv H0.
    inv H1. destruct (number_execution prog _ _ _ 0 H6) as [N]. inv H7.
    eapply callstate_will_return in H0; autoconstruct. decompose [ex and] H0.
    inv H5. inv H8. rewrite E0_right; eauto. inv H5. inv H14.
  * inv H.
  + inv H0. inv H1. assert (forever_x (semantics prog) s (Tfin t)) by (eapply forever_x_finite; eauto; apply semantics_determinate).
    inv H. apply forever_x_to_step in H0 as [n]. 2: apply semantics_determinate.
    apply forever_evalinf in H. autoconstruct.
  + inv H0. inv H. inv H1. apply forever_x_reactive, forever_x_to_step in H5 as [n]. 2: apply semantics_determinate.
    autoconstruct. apply forever_evalinf. eauto.
  * inv H.
  + inv H0. destruct (number_execution prog _ _ _ 0 H1) as [N].
    eapply callstate_partial in H0 as [m [res]]; autoconstruct.
  + constructor 2. intros [f [m]]. apply H0. inv H. autoconstruct.
  * auto.
Qed.

#[export] Instance SpecificBigstepSemantics: BehSem (SpecificBigstep (CminLoop.bigstep_semantics prog)).
Proof.
  constructor. intros. eapply bigstep_partial_spec. apply bigstep_semantics_sound. apply bigstep_semantics_complete.
Defined.

Theorem big_small_equivalent:
  bigstep_semantics ≡ smallstep_semantics.
Proof.
  intros. apply big_small_equivalent. apply bigstep_semantics_sound. apply bigstep_semantics_complete. apply smallstep_determinate.
Qed.

Let EQ := equivalent_sym _ _ big_small_equivalent.
Let DET := semantics_determinate prog.

Corollary bigstep_semantics_determinate:
  determinate bigstep_semantics.
Proof.
  intros. apply determinate_preserved in EQ. auto. now apply smallstep_determinate.
Qed.

Corollary bigstep_semantics_receptive:
  receptive bigstep_semantics.
Proof.
  intros. apply receptive_preserved in EQ. auto. now apply smallstep_receptive, semantics_receptive.
Qed.

Corollary bigstep_semantics_nonempty:
  nonempty bigstep_semantics.
Proof.
  intros. apply nonempty_preserved in EQ. auto. apply smallstep_nonempty.
Qed.

End EQUIVALENCE.