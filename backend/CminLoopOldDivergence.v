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
Require Import Foreverx.
Require Import SemanticsSmallBig.
Require Import Bigstep.
Require Import Semantics.
Require Import Tracex.
Require Import Switch.
Require Import Cminor.
Require Import Classical.
Require Import CminLoop.
Require Import CminLoopBigSmallEquiv.


Section OLDNATURALSEM.

Variable ge: genv.

CoInductive evalinf_funcall_old:
        mem -> fundef -> list val -> traceinf -> Prop :=
  | evalinf_funcall_old_internal:
      forall m f vargs m1 sp e t,
      Mem.alloc m 0 f.(fn_stackspace) = (m1, sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      execinf_stmt_old f (Vptr sp Ptrofs.zero) e m1 f.(fn_body) t ->
      evalinf_funcall_old m (Internal f) vargs t

with execinf_stmt_old:
         function -> val -> env -> mem -> stmt -> traceinf -> Prop :=
  | execinf_Scall:
      forall f sp e m optid sig a bl vf vargs fd t,
      eval_expr ge sp e m a vf ->
      eval_exprlist ge sp e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      evalinf_funcall_old m fd vargs t ->
      execinf_stmt_old f sp e m (Scall optid sig a bl) t
  | execinf_Sifthenelse:
      forall f sp e m a s1 s2 v b t,
      eval_expr ge sp e m a v ->
      Val.bool_of_val v b ->
      execinf_stmt_old f sp e m (if b then s1 else s2) t ->
      execinf_stmt_old f sp e m (Sifthenelse a s1 s2) t
  | execinf_Sseq_1:
      forall f sp e m t s1 s2,
      execinf_stmt_old f sp e m s1 t ->
      execinf_stmt_old f sp e m (Sseq s1 s2) t
  | execinf_Sseq_2:
      forall f sp e m t t1 t2 s1 e1 m1 s2,
      exec_stmt ge f sp e m s1 t1 e1 m1 Out_normal ->
      execinf_stmt_old f sp e1 m1 s2 t2 ->
      t = t1 *** t2 ->
      execinf_stmt_old f sp e m (Sseq s1 s2) t
  | execinf_Sloop_body:
      forall f sp e m s t,
      execinf_stmt_old f sp e m s t ->
      execinf_stmt_old f sp e m (Sloop s) t
  | execinf_Sloop_loop:
      forall f sp e m s t t1 t2 e1 m1,
      exec_stmt ge f sp e m s t1 e1 m1 Out_normal ->
      execinf_stmt_old f sp e1 m1 (Sloop s) t2 ->
      t = t1 *** t2 ->
      execinf_stmt_old f sp e m (Sloop s) t
  | execinf_Sblock:
      forall f sp e m s t,
      execinf_stmt_old f sp e m s t ->
      execinf_stmt_old f sp e m (Sblock s) t
  | execinf_Sdummy:
      forall f sp e m s t,
      execinf_stmt_old f sp e m s t ->
      execinf_stmt_old f sp e m (Sdummy s) t
  | execinf_Stailcall:
      forall f sp e m sig a bl vf vargs fd m' t,
      eval_expr ge (Vptr sp Ptrofs.zero) e m a vf ->
      eval_exprlist ge (Vptr sp Ptrofs.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      evalinf_funcall_old m' fd vargs t ->
      execinf_stmt_old f (Vptr sp Ptrofs.zero) e m (Stailcall sig a bl) t.

End OLDNATURALSEM.

(* The big-step version of `forever_x_forever` *)
Lemma new_to_old: forall t T,
    tracexx_prefix t (Tinf T) ->
    forall ge n f m vargs,
    CminLoop.evalinf_funcall ge m f vargs n t ->
    evalinf_funcall_old ge m f vargs T.
Proof.
  cofix CIF.
  assert (CIH: forall t T,
  tracexx_prefix t (Tinf T) ->
  forall ge n f sp e m s,
  CminLoop.execinf_stmt ge f sp e m s n t ->
  execinf_stmt_old ge f sp e m s T).
  cofix CIH.
  intros. inv H0; try (econstructor; eauto; fail).
  + destruct t2; inv H; (eapply execinf_Sseq_2; [ eauto; tracexEq | eapply CIH; eauto; econstructor; traceEq | traceEq ])
  + destruct t2; inv H; (eapply execinf_Sloop_loop; [ eauto; tracexEq | eapply CIH; eauto; econstructor; traceEq | traceEq ]).
  + destruct t2; inv H; (eapply execinf_Sloop_loop; [ eauto; tracexEq | eapply CIH; eauto; econstructor; traceEq | traceEq ]).
  + intros. inv H0. econstructor; eauto.
Qed.

Require Import Smallstep.

Section COMPLETE.

Variable p: CminLoop.program.
Let ge := Genv.globalenv p.

(* Old soundness as in standard CompCert *)
Axiom evalinf_old_sound:
  forall m fd vargs k T,
  evalinf_funcall_old ge m fd vargs T ->
  forever CminLoop.step ge (Callstate fd vargs k m) T.

(* The big-step version of `forever_forever_x` *)
Lemma old_to_new: forall T,
  forall m fd vargs,
  evalinf_funcall_old ge m fd vargs T ->
  exists n t,
  (tracexx_prefix t (Tinf T) /\ CminLoop.evalinf_funcall ge m fd vargs n t).
Proof.
  intros. eapply evalinf_old_sound with (k:=Kstop) in H.
  assert (Forever (CminLoop.semantics p) (Callstate fd vargs Kstop m) T) by apply H.
  eapply forever_forever_x in H0 as [t []].
  eapply forever_x_to_step in H1 as [n]. 2: apply CminLoop.semantics_determinate.
  eapply forever_evalinf in H1.
  now exists n, t.
Qed.

Theorem old_new_equivalent: forall m fd vargs T,
  evalinf_funcall_old ge m fd vargs T
  <-> exists n t, tracexx_prefix t (Tinf T) /\ CminLoop.evalinf_funcall ge m fd vargs n t.
Proof.
  split; intros.
  * now apply old_to_new in H.
  * repeat destruct H. eapply new_to_old in H0; eauto.
Qed.

End COMPLETE.