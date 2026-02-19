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

(** * Loop unswitching, i.e. move an independent if-statement out of a loop.
  Currently only implemented for the case where the loop begins with this if-statement.
*)

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

(** * Independence of certain statements and expressions *)

Fixpoint expr_uses_vars (e: expr) (res: list ident) : list ident := match e with
  | Evar v => v :: res
  | Econst c => res
  | Eunop op expr => expr_uses_vars expr res
  | Ebinop op e1 e2 => expr_uses_vars e1 (expr_uses_vars e2 res)
  | Eload mem expr => expr_uses_vars expr res
  end.

Lemma expr_uses_vars_concat: forall e r,
  expr_uses_vars e r = expr_uses_vars e nil ++ r.
Proof.
  intros. generalize dependent r. induction e; auto.
  * simpl. intro. rewrite IHe2. rewrite IHe1. symmetry. rewrite IHe1. now rewrite app_assoc.
Qed.

Fixpoint stmt_assigns_to_vars (s: stmt) (res: list ident) : list ident := match s with
  | Sskip => res
  | Sassign var e => var :: res
  | Sstore mem e1 e2 => res
  | Scall (Some id) sig e es => id :: res
  | Scall None sig e es => res
  | Stailcall sig e es => res
  | Sbuiltin (Some id) ef es => id :: res
  | Sbuiltin None ef es => res
  | Sseq s1 s2 => stmt_assigns_to_vars s1 (stmt_assigns_to_vars s2 res)
  | Sifthenelse expr s1 s2 => stmt_assigns_to_vars s1 (stmt_assigns_to_vars s2 res)
  | Sloop s => stmt_assigns_to_vars s res
  | Sblock s => stmt_assigns_to_vars s res
  | Sdummy s => stmt_assigns_to_vars s res
  | Sexit e => res
  | Sswitch islong a cases default => res
  | Sreturn e => res
  end.

Lemma stmt_assigns_to_vars_concat: forall s r,
  stmt_assigns_to_vars s r = stmt_assigns_to_vars s nil ++ r.
Proof.
  intros. generalize dependent r. induction s; auto.
  * simpl. intro. case o; auto.
  * simpl. intro. case o; auto.
  * simpl. intro. rewrite IHs2, IHs1. symmetry. rewrite IHs1. now rewrite app_assoc.
  * simpl. intro. rewrite IHs2, IHs1. symmetry. rewrite IHs1. now rewrite app_assoc.
Qed.

Definition list_intersect (l1 l2: list ident) :=
  Exists (fun a => In a l1) l2.

Lemma list_intersect_spec: forall l1 l2,
  list_intersect l1 l2 <->
  exists a, In a l1 /\ In a l2.
Proof.
  split; intros.
  * dependent induction H.
    exists x. split; auto. apply in_eq.
    destruct IHExists. exists x0. split. apply H0. apply in_cons, H0.
  * dependent induction l2.
    destruct H. easy.
    destruct H as [? [? [|]]].
    + subst. now constructor 1.
    + constructor 2. apply Exists_exists. now exists x.
Qed.

Lemma list_intersect_sym: forall l1 l2,
  list_intersect l1 l2 -> list_intersect l2 l1.
Proof.
  intros. rewrite list_intersect_spec in *. destruct H. now exists x.
Qed.

Lemma list_intersect_sym_app1: forall l l1 l2,
  list_intersect l (l1++l2) -> list_intersect l (l2++l1).
Proof.
  intros. rewrite list_intersect_spec in *. destruct H as [x []]. exists x.
  split. apply H. rewrite in_app in *. now rewrite or_comm.
Qed.

Lemma list_intersect_app1: forall l l1 l2,
  list_intersect l l1 -> list_intersect l (l1++l2).
Proof.
  intros. rewrite list_intersect_spec in *. destruct H as [x []]. exists x.
  split. auto. rewrite in_app. auto.
Qed.

Lemma list_intersect_app2: forall l l1 l2,
  list_intersect l l2 -> list_intersect l (l1++l2).
Proof.
  intros. rewrite list_intersect_spec in *. destruct H as [x []]. exists x.
  split. auto. rewrite in_app. auto.
Qed.

Definition list_intersect_dec: forall l1 l2, {list_intersect l1 l2} + {~list_intersect l1 l2}.
Proof.
  intros. generalize dependent l1. induction l2.
  * intros. right. intro. apply list_intersect_spec in H as [? []]. easy.
  * intros. destruct (IHl2 l1).
    + left. now constructor.
    + case (in_dec peq a l1).
    - intros. left. now constructor.
    - intros. right. intro. rewrite list_intersect_spec in H. destruct H as [? [? [|]]].
      now subst. apply n. apply list_intersect_spec. now exists x.
Defined.

Definition binop_uses_mem op := match op with
  | Ocmpu c => True
  | Ocmplu c => True
  | _ => False
end.

Fixpoint expr_uses_no_mem (e: expr) := match e with
  | Evar v => True
  | Econst c => True
  | Eunop op expr => expr_uses_no_mem expr
  | Ebinop op e1 e2 => ~binop_uses_mem op /\ expr_uses_no_mem e1 /\ expr_uses_no_mem e2
  | Eload mem expr => False
  end.

Definition expr_uses_no_mem_dec: forall e, {expr_uses_no_mem e} + {~expr_uses_no_mem e}.
Proof.
  intros. dependent induction e; auto. now left. now left.
  destruct IHe1. destruct IHe2. destruct b; try now left.
  all: right; simpl; easy.
Defined.
 
Lemma eval_binop_const_mem:
  forall op v1 v2 m1 m2,
  ~binop_uses_mem op ->
  eval_binop op v1 v2 m1 = eval_binop op v1 v2 m2.
Proof.
  intros. case op in *; auto; exfalso; now apply H.
Qed.

Lemma eval_expr_const_mem_only:
  forall m1 m2 ge sp val env expr,
  expr_uses_no_mem expr ->
  eval_expr ge sp env m1 expr val ->
  eval_expr ge sp env m2 expr val.
Proof.
  intros. induction H0.
  * now constructor.
  * now constructor.
  * econstructor. now apply IHeval_expr. auto.
  * inv H. econstructor. now apply IHeval_expr1. now apply IHeval_expr2. auto.
    erewrite eval_binop_const_mem; eauto.
  * inv H.
Qed.

Lemma eval_expr_const:
  forall ge sp env m1 m2 expr id v val,
  expr_uses_no_mem expr ->
  ~ In id (expr_uses_vars expr nil) ->
  eval_expr ge sp env m1 expr val ->
  eval_expr ge sp (PTree.set id v env) m2 expr val.
Proof.
  intros. induction H1.
  * constructor. rewrite PTree.gso. auto. intro. apply H0. subst. simpl. auto.
  * now constructor.
  * econstructor. now apply IHeval_expr. auto.
  * simpl in H0. rewrite expr_uses_vars_concat in H0. rewrite in_app_iff in H0.
    econstructor.
    - apply IHeval_expr1. apply H. intro. apply H0. auto.
    - apply IHeval_expr2. apply H. intro. apply H0. auto.
    - erewrite eval_binop_const_mem; eauto. now simpl in H.
  * easy.
Qed.

Definition doesnt_use_assigned_vars expr stmt :=
  ~ list_intersect (expr_uses_vars expr nil) (stmt_assigns_to_vars stmt nil).

Definition doesnt_use_assigned_vars_dec: forall expr stmt,
  {doesnt_use_assigned_vars expr stmt} + {~doesnt_use_assigned_vars expr stmt}.
Proof.
  intros. unfold doesnt_use_assigned_vars. ecase list_intersect_dec; eauto.
Defined.

Lemma assigned_vars_ifthenelse_1:
  forall expr a s1 s2,
  doesnt_use_assigned_vars expr (Sifthenelse a s1 s2) ->
  doesnt_use_assigned_vars expr s1.
Proof.
  intros. intro. apply H. simpl. rewrite stmt_assigns_to_vars_concat. now apply list_intersect_app1.
Qed.

Lemma assigned_vars_ifthenelse_2:
  forall expr a s1 s2,
  doesnt_use_assigned_vars expr (Sifthenelse a s1 s2) ->
  doesnt_use_assigned_vars expr s2.
Proof.
  intros. intro. apply H. simpl. rewrite stmt_assigns_to_vars_concat. now apply list_intersect_app2.
Qed.

Lemma expression_outcome_const_after_stmt:
  forall expr stmt ge f e1 e2 sp m1 m2 val t out
  (NP: out <> Out_partial),
  doesnt_use_assigned_vars expr stmt ->
  expr_uses_no_mem expr ->
  exec_stmt ge f sp e1 m1 stmt t e2 m2 out ->
  eval_expr ge sp e1 m1 expr val ->
  eval_expr ge sp e2 m2 expr val.
Proof.
  intros. dependent induction H1; auto; try congruence.
  * inv H2.
    + assert (id <> id0). { intro. apply H. subst. constructor. simpl. auto. }
      constructor. rewrite PTree.gso; auto.
    + now constructor.
    + econstructor. 2: apply H4. eapply eval_expr_const; eauto.
      intro. apply H. now constructor.
    + econstructor.
      - eapply eval_expr_const; eauto. apply H0. intro. apply H. simpl. rewrite expr_uses_vars_concat. constructor. apply in_app. auto.
      - eapply eval_expr_const; eauto. apply H0. intro. apply H. simpl. rewrite expr_uses_vars_concat. constructor. apply in_app. auto.
      - auto.
    + inv H0.
  * eapply eval_expr_const_mem_only; eauto.
  * inv H6; [|congruence]. case optid in *.
    + simpl. eapply eval_expr_const; eauto. intro. apply H. now constructor.
    + simpl. eapply eval_expr_const_mem_only; eauto.
  * case optid in *.
    + subst. simpl. eapply eval_expr_const; eauto. intro. apply H. simpl. now constructor.
    + subst. simpl. eapply eval_expr_const_mem_only; eauto.
  * case b in *.
    + apply IHexec_stmt; auto. intro. apply H. simpl. rewrite stmt_assigns_to_vars_concat. now apply list_intersect_app1.
    + apply IHexec_stmt; auto. intro. apply H. simpl. rewrite stmt_assigns_to_vars_concat. now apply list_intersect_sym_app1, list_intersect_app1.
  * apply IHexec_stmt2; auto. intro. apply H. simpl. rewrite stmt_assigns_to_vars_concat. now apply list_intersect_sym_app1, list_intersect_app1.
    apply IHexec_stmt1; auto. congruence. intro. apply H. simpl. rewrite stmt_assigns_to_vars_concat. now apply list_intersect_app1.
  * apply IHexec_stmt; auto. intro. apply H. simpl. rewrite stmt_assigns_to_vars_concat. now apply list_intersect_app1.
  * apply IHexec_stmt2; auto. apply IHexec_stmt1; auto. congruence.
  * apply IHexec_stmt; auto. now destruct out.
  * inv H8; inv H7; try congruence. eapply eval_expr_const_mem_only; eauto.
Qed.

Corollary var_unchanged_after_stmt: forall stmt ge f e1 e2 sp m1 m2 t out id v
  (NP: out <> Out_partial),
  ~ In id (stmt_assigns_to_vars stmt nil) ->
  exec_stmt ge f sp e1 m1 stmt t e2 m2 out ->
  e1 ! id = Some v ->
  e2 ! id = Some v.
Proof.
  intros.
  apply expression_outcome_const_after_stmt with (expr := Evar id) (val := v) in H0; eauto. now inv H0.
  - intro. apply H. inv H2. inv H4; [apply in_eq | inv H2]. apply Exists_exists in H4 as [e []]. inv H4; [now apply in_cons | inv H5].
  - constructor.
  - now constructor.
Qed.

Section Transformation.

(*** LOOP TRANSFORMATION ***)

(* An external parameter that decides whether a loop with the given body should be inverted or not.
   It is irrelevant to the correctness of the transformation. *)
Variable should_unswitch_loop: stmt -> bool.

Fixpoint transform_stmt (s: stmt) : stmt := match s with
  | Sloop (Sifthenelse e s1 s2) =>
    if doesnt_use_assigned_vars_dec e (Sifthenelse e s1 s2) && expr_uses_no_mem_dec e && should_unswitch_loop (Sifthenelse e s1 s2) then
      Sifthenelse e (Sloop (transform_stmt s1)) (Sloop (transform_stmt s2))
    else
      Sloop (Sifthenelse e (transform_stmt s1) (transform_stmt s2))
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

Lemma bool_of_val_eq:
  forall v b1 b2,
  Val.bool_of_val v b1 ->
  Val.bool_of_val v b2 ->
  b1 = b2.
Proof.
  intros. inv H. now inv H0.
Qed.

Ltac solve_transl_extend :=
  solve_transl TRANSL;
  try now rewrite sig_preserved.

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
  * intros. econstructor; eauto; solve_transl_extend. case b in *; apply H2.
  * intros. case s in *; try (eapply exec_Sloop_loop; eauto; fail).
    simpl in *. case (doesnt_use_assigned_vars_dec e0 (Sifthenelse e0 s1 s2) && expr_uses_no_mem_dec e0 && should_unswitch_loop _) eqn:?.
    + inv H0. inv H2.
    - econstructor; eauto. destruct b; eapply exec_Sloop_loop; eauto; constructor.
    - assert (v = v0). { pose senv_preserved. eapply eval_expr_determ. apply H9. eapply eval_expr_preserved; eauto. eapply eval_expr_preserved_inv in H11; eauto.
        eapply expression_outcome_const_after_stmt; eauto. congruence.
        all: apply andb_prop in Heqb as []; apply andb_prop in H0 as []. now case doesnt_use_assigned_vars_dec in *. now case expr_uses_no_mem_dec in *.
      } subst v0.
      assert (b = b0) by (eapply bool_of_val_eq; eauto). subst b0.
      eapply exec_Sifthenelse; eauto.
      case b in *; eapply exec_Sloop_loop; eauto.
    + eapply exec_Sloop_loop; eauto.
  * intros. case s in *; try (eapply exec_Sloop_stop; eauto; fail).
    simpl in *. case (doesnt_use_assigned_vars_dec e0 (Sifthenelse e0 s1 s2) && expr_uses_no_mem_dec e0 && should_unswitch_loop _) eqn:?.
    + inv H0.
      - inv H. constructor. econstructor; eauto.
      - eapply exec_Sifthenelse; eauto. case b in *; eapply exec_Sloop_stop; eauto.
    + eapply exec_Sloop_stop; eauto.
  * intros. eapply exec_Stailcall with (fd:=transl_fundef fd); solve_transl_extend; eauto.
Qed.

Lemma cancel_pm: forall n, n+1-1 = n.
Proof. lia. Qed.

Lemma swap_pm: forall n, n+1-1 = n-1+1.
Proof. lia. Qed.

Section ExecInf_Loop.

Hypothesis CIH_STMT:
  forall (f : function) (sp : val) (env : env) (m : mem) (s : stmt) n (t : tracex),
    execinf_stmt ge f sp env m s (n-1) t ->
    execinf_stmt tge (transl_function f) sp env m (transform_stmt s) n t.

Variable (f: function) (sp: val) (e: expr) (s1 s2: stmt).

Hypothesis PREC: doesnt_use_assigned_vars_dec e (Sifthenelse e s1 s2)
              && expr_uses_no_mem_dec e
              && should_unswitch_loop (Sifthenelse e s1 s2)
               = true.

Lemma execinf_when_true: forall (t: tracex) (env: env) (m: mem) v n,
  eval_expr ge sp env m e v ->
  Val.bool_of_val v true ->
  execinf_stmt ge f sp env m (Sloop (Sifthenelse e s1 s2)) n t ->
  execinf_stmt tge (transl_function f) sp env m (Sloop (transform_stmt s1)) n t.
Proof.
  cofix REC.
  intros. inv H1.
  * inv H8. apply execinf_Sloop_body. now apply guard_incr1. apply CIH_STMT. enough (b=true) by now subst.
      { apply eval_expr_determ with (v:=v0) in H; auto. subst v0. eapply bool_of_val_eq; eauto. }
  * inv H4. assert (b=true).
      { apply eval_expr_determ with (v:=v0) in H; auto. subst v0. eapply bool_of_val_eq; eauto. }
    subst b. eapply execinf_Sloop_loop; eauto. apply transl_exec_correct; eauto.
    enough (eval_expr ge sp e1 m1 e v0).
    + eapply REC; eauto.
    + eapply expression_outcome_const_after_stmt; eauto. congruence.
      apply andb_prop in PREC as []. case doesnt_use_assigned_vars_dec in *. eapply assigned_vars_ifthenelse_1; eauto. easy.
      apply andb_prop in PREC as []. apply andb_prop in H1 as []. now case expr_uses_no_mem_dec in *.
Defined.

Lemma execinf_when_false: forall (t: tracex) (env: env) (m: mem) v n,
  eval_expr ge sp env m e v ->
  Val.bool_of_val v false ->
  execinf_stmt ge f sp env m (Sloop (Sifthenelse e s1 s2)) n t ->
  execinf_stmt tge (transl_function f) sp env m (Sloop (transform_stmt s2)) n t.
Proof.
  cofix REC.
  intros. inv H1.
  * inv H8. apply execinf_Sloop_body. now apply guard_incr1. apply CIH_STMT. enough (b=false) by now subst.
      { apply eval_expr_determ with (v:=v0) in H; auto. subst v0. eapply bool_of_val_eq; eauto. }
  * inv H4. assert (b=false).
      { apply eval_expr_determ with (v:=v0) in H; auto. subst v0. eapply bool_of_val_eq; eauto. }
    subst b. eapply execinf_Sloop_loop; eauto. apply transl_exec_correct; eauto.
    enough (eval_expr ge sp e1 m1 e v0).
    + eapply REC; eauto.
    + eapply expression_outcome_const_after_stmt; eauto. congruence.
      apply andb_prop in PREC as []. case doesnt_use_assigned_vars_dec in *. eapply assigned_vars_ifthenelse_2; eauto. easy.
      apply andb_prop in PREC as []. apply andb_prop in H1 as []. now case expr_uses_no_mem_dec in *.
Defined.

End ExecInf_Loop.

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

  pose proof senv_preserved as SE.
  intros. remember (n-1). destruct H; rewrite Heqz in *.
  * eapply execinf_Scall with (fd:=transl_fundef fd); auto. now apply guard_incr1. eapply eval_expr_preserved; eauto. eapply eval_exprlist_preserved; eauto.
    eapply (Genv.find_funct_transf TRANSL); eauto. now rewrite sig_preserved.
    apply CIH_FUN; eauto.
  * econstructor; eauto. now apply guard_incr1. eapply eval_expr_preserved; eauto. 
    case b in *; now apply CIH_STMT.
  * constructor. auto. now apply guard_incr1. fold transform_stmt. now apply CIH_STMT.
  * eapply execinf_Sseq_2 with (M:=M+1); eauto. eapply event_incr1_both. eauto. apply transl_exec_correct; eauto.
    fold transform_stmt. apply CIH_STMT. now rewrite cancel_pm.
  * simpl. case s in *; try (eapply execinf_Sloop_body; [now apply guard_incr1 | now apply CIH_STMT]; fail).
    case (doesnt_use_assigned_vars_dec e0 (Sifthenelse e0 s1 s2) && expr_uses_no_mem_dec e0 && should_unswitch_loop _) eqn:?.
    + inv H0. eapply execinf_Sifthenelse. now apply guard_incr1. eapply eval_expr_preserved; eauto. apply H12.
      case b in *; eapply execinf_Sloop_body; auto.
    + replace ((Sifthenelse e0 (transform_stmt s1) (transform_stmt s2))) with (transform_stmt (Sifthenelse e0 s1 s2)) by auto.
      eapply execinf_Sloop_body. now apply guard_incr1. now apply CIH_STMT.
  * inv H2. simpl. case s in *; try (
      eapply execinf_Sloop_loop; [ eapply event_incr1_both; eauto | apply transl_exec_correct; eauto | | eauto ];
        eassert (T: Sloop (transform_stmt _) = transform_stmt (Sloop _)); [ | rewrite T; apply CIH_STMT; replace M with (M+1-1) in H1 by lia; eauto ]; auto; fail).

    case (doesnt_use_assigned_vars_dec e0 (Sifthenelse e0 s1 s2) && expr_uses_no_mem_dec e0 && should_unswitch_loop _) eqn:?.
    + inv H0. econstructor. eapply guard_incr1, event_to_silent; eauto. eapply eval_expr_preserved; eauto. eauto.
      case b in *.
      - eapply execinf_Sloop_loop with (M:=M); eauto.
        apply transl_exec_correct; eauto. eapply execinf_when_true; eauto.
        apply andb_prop in Heqb as []; apply andb_prop in H0 as []. eapply expression_outcome_const_after_stmt; eauto. congruence. destruct doesnt_use_assigned_vars_dec. eapply assigned_vars_ifthenelse_1; eauto. easy. now destruct expr_uses_no_mem_dec.
      - eapply execinf_Sloop_loop with (M:=M); eauto.
        apply transl_exec_correct; eauto. eapply execinf_when_false; eauto.
        apply andb_prop in Heqb as []. apply andb_prop in H0 as []. eapply expression_outcome_const_after_stmt; eauto. congruence. destruct doesnt_use_assigned_vars_dec. eapply assigned_vars_ifthenelse_2; eauto. easy. now destruct expr_uses_no_mem_dec.
    + eapply execinf_Sloop_loop with (M:=M+1) (t1:=t1); eauto.
      now apply event_incr1_both.
      replace (Sifthenelse e0 (transform_stmt s1) (transform_stmt s2)) with (transform_stmt (Sifthenelse e0 s1 s2)) by auto.
      apply transl_exec_correct; eauto.
      replace (Sloop (Sifthenelse e0 (transform_stmt s1) (transform_stmt s2))) with (transform_stmt (Sloop (Sifthenelse e0 s1 s2))) by (simpl; now rewrite Heqb).
      apply CIH_STMT; eauto. rewrite cancel_pm; eauto.
  * econstructor; eauto. now apply guard_incr1.
  * econstructor; eauto. now apply guard_incr1.
  * econstructor; auto. now apply guard_incr1. 3: apply (Genv.find_funct_transf TRANSL); eauto. eapply eval_expr_preserved; eauto. eapply eval_exprlist_preserved; eauto.
    now rewrite sig_preserved. eauto. now apply CIH_FUN.
  * intros. inv H. econstructor; eauto. now apply guard_incr1.
    now apply CIHST.
Qed.

Theorem forward_preservation:
  bigstep_semantics prog ⇉ bigstep_semantics tprog.
Proof.
  apply make_forward_transformation.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_exec_correct; eauto.
  * intros. inv H. econstructor. eapply transl_initial_state; eauto. apply sig_preserved. apply transl_execinf_correct with (n:=N+1). rewrite cancel_pm. eauto.
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