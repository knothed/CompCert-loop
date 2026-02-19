Require Import Coqlib.
Require Import Events.

(***
  A tracex resembles either a finite or an infinite trace and unifies
  operations and properties that are common to both, most of which are prefix-related.

  This is just a tool to avoid repetition in expressing properties that are shared
  by finite and infinite traces and program behaviors.
***)

Inductive tracex : Type :=
  | Tfin: forall (t: trace), tracex
  | Tinf: forall (T: traceinf), tracex.

Definition X0 := Tfin E0.

Definition Xcons (e: event) (t: tracex) := match t with
  | Tfin t => Tfin (e::t)
  | Tinf T => Tinf (Econsinf e T)
end.

Definition Xapp (t1: trace) (t2: tracex) := match t2 with
  | Tfin t2 => Tfin (t1 ** t2)
  | Tinf T2 => Tinf (t1 *** T2)
end.

Definition Xin (e: event) (t: tracex) := match t with
  | Tfin t => In e t
  | Tinf T => exists t T', T = t *** Econsinf e T'
end.

Infix "°" := Xcons (at level 60, right associativity).
Infix "°°" := Xapp (at level 60, right associativity).

Lemma X0_left: forall t, E0 °° t = t.
Proof.
  now destruct t.
Qed.

Lemma X0_right: forall t, t °° X0 = Tfin t.
Proof.
  intros. simpl. now rewrite E0_right.
Qed.

Lemma Xcons_inv: forall e1 t1 e2 t2,
  e1°t1 = e2°t2 ->
  e1 = e2 /\ t1 = t2.
Proof.
  destruct t1, t2; intros; now inv H.
Qed.

Lemma Xcons_assoc_left: forall e t1 t2,
  (e::t1)°°t2 = e°(t1°°t2).
Proof.
  now destruct t2.
Qed.

Lemma Xcons_assoc_right: forall e t1 t2,
  (t1++e::nil)°°t2 = t1°°(e°t2).
Proof.
  destruct t2; simpl; traceEq.
Qed.

Lemma Xapp_assoc: forall t1 t2 t3,
  (t1**t2)°°t3 = t1°°(t2°°t3).
Proof.
  destruct t3; simpl; [ now rewrite Eapp_assoc | now rewrite Eappinf_assoc ].
Qed.

Lemma Xapp_X0_inv: forall t1 t2,
  t1°°t2 = X0 -> t1 = nil /\ t2 = X0.
Proof.
  intros. destruct t2. inv H. apply Eapp_E0_inv in H1 as []; now subst. inv H.
Qed.

Lemma inv_tracex_dec: forall t,
  sumor { '(e,t') | t = e ° t'} (t=X0).
Proof.
  intros. destruct t. destruct t. now right. left. exists (e, (Tfin t)). auto.
  destruct T. left. exists (e, (Tinf T)). auto.
Qed.

Lemma inv_tracex: forall t,
  t = X0 \/ exists e t', t = e ° t'.
Proof.
  intros. destruct (inv_tracex_dec t).
  destruct s. destruct x. right. now exists e, t0. now left.
Qed.

Lemma Xin_spec: forall e t,
  Xin e t ->
  exists t1 t2,
  t = t1 °° e ° t2.
Proof.
  intros. destruct t.
  * apply in_split in H as [t1 [t2 ?]]. exists t1, (Tfin t2). now subst.
  * destruct H as [t [T']]. exists t, (Tinf T'). now subst.
Qed.

#[global]
Hint Rewrite X0_left Xcons_inv Xapp_assoc Xcons_assoc_left Xcons_assoc_right: tracex_rewrite.

Opaque X0.

Ltac substTracexHyp :=
  match goal with
  | [ H: (@eq tracex ?x ?y) |- _ ] =>
       subst x
  end.

Ltac decomposeTracexEq :=
  match goal with
  | [ |- (_ °° _) = (_ °° _) ] =>
      apply (f_equal2 Xapp); auto; decomposeTracexEq
  | _ =>
      auto
  end.

Ltac tracexEq :=
  repeat substTracexHyp; traceEq; autorewrite with tracex_rewrite; decomposeTraceEq; traceEq.


Lemma traceinf_cons: forall e t1 t2,
  (e::t1) *** t2 = Econsinf e (t1***t2).
Proof.
  auto.
Qed.

Lemma tracex_app_inv_fin: forall t1 t2 t3,
  t1 °° t2 = Tfin t3 ->
  exists t', t2 = Tfin t'.
Proof.
  destruct t2; intros. now exists t. inv H.
Qed.

Lemma tracex_app_inv_inf: forall t1 t2 t3,
  t1 °° t2 = Tinf t3 ->
  exists t', t2 = Tinf t'.
Proof.
  destruct t2; intros. inv H. now exists T.
Qed.

(** Prefixes. *)

Inductive strict_trace_prefix (t1 t2: trace) : Prop :=
  | stp: forall e t', t2 = t1 ** e :: t' -> strict_trace_prefix t1 t2.

Definition tracex_prefix (t1: trace) (t2: tracex) := match t2 with
  | Tfin t2 => trace_prefix t1 t2
  | Tinf T2 => traceinf_prefix t1 T2
end.

Definition tracexx_prefix (t1 t2: tracex) := match t1 with
  | Tfin t1 => tracex_prefix t1 t2
  | Tinf t1 => t2 = Tinf t1
end.

Definition strict_tracex_prefix (t1: trace) (t2: tracex) := match t2 with
  | Tfin t2 => strict_trace_prefix t1 t2
  | Tinf T2 => traceinf_prefix t1 T2
end.

Lemma tracex_prefix_E0:
  forall t,
  tracex_prefix E0 t.
Proof.
  destruct t; intros; econstructor; traceEq.
Qed.

Lemma tracex_prefix_spec:
  forall t1 t2,
  tracex_prefix t1 (t1 °° t2).
Proof.
  destruct t2; intros; econstructor; traceEq.
Qed.

Lemma tracex_prefix_cons:
  forall t1 t2 t,
  tracex_prefix t1 t2 ->
  tracex_prefix (t :: t1) (t ° t2).
Proof.
  destruct t2; intros; inv H; now econstructor.
Qed.

Lemma tracex_prefix_app:
  forall t1 t2 t,
  tracex_prefix t1 t2 ->
  tracex_prefix (t ** t1) (t °° t2).
Proof.
  destruct t2; intros; [ now apply trace_prefix_app | now apply traceinf_prefix_app ].
Qed.

Lemma tracex_prefix_inv:
  forall t1 t2,
  tracex_prefix t1 t2 ->
  exists t', t1 °° t' = t2.
Proof.
  destruct t2; intros; inv H. exists (Tfin x); tracexEq. exists (Tinf x); tracexEq.
Qed.

Lemma tracexx_prefix_refl:
  forall t,
  tracexx_prefix t t.
Proof.
  intros. destruct t; econstructor. now rewrite E0_right.
Qed.

Lemma tracexx_prefix_trans:
  forall t1 t2 t3,
  tracex_prefix t1 t2 ->
  tracexx_prefix t2 t3 ->
  tracex_prefix t1 t3.
Proof.
  intros. destruct t2, t3; inv H; inv H0; econstructor; traceEq.
Qed.


Lemma tracex_shared_prefix: forall t1 t2 T1 T2,
  t1 °° T1 = t2 °° T2 ->
  (exists t, t1 = t2 ** t /\ T2 = t °° T1) \/
  (exists t, t2 = t1 ** t /\ T1 = t °° T2).
Proof.
  intros. generalize dependent t2. induction t1. right. exists t2. split; auto. now rewrite X0_left in H.
  intros. destruct t2.
  + left. exists (a::t1). split; auto. rewrite H. tracexEq.
  + rewrite 2 Xcons_assoc_left in H. apply Xcons_inv in H as []. subst. destruct (IHt1 t2 H0) as [[t []] | [t []]]; subst; [left | right]; now exists t.
Qed.

Lemma tracex_shared_prefix': forall t1 t2 T1 T2,
  t1 °° T1 = t2 °° T2 ->
  (t1 = t2 /\ T1 = T2) \/
  (exists e t, t1 = t2 ** e::t /\ T2 = e ° t °° T1) \/
  (exists e t, t2 = t1 ** e::t /\ T1 = e ° t °° T2).
Proof.
  intros. generalize dependent t2. induction t1.
  * destruct t2. left. rewrite 2 X0_left in H. auto. right; right. rewrite X0_left in H. exists e, t2. split; auto. tracexEq.
  * intros. destruct t2.
  + right; left. exists a, t1. rewrite X0_left in H. split; auto. rewrite <- H. tracexEq.
  + rewrite 2 Xcons_assoc_left in H. apply Xcons_inv in H as []. subst.
    decompose [and ex or] (IHt1 t2 H0); subst; [left | right; left | right; right ]; auto; do 2 eexists; split; eauto; traceEq.
Qed.

Lemma trace_shared_prefix: forall t1 t2 T1 T2,
  t1 ** T1 = t2 ** T2 ->
  (exists t, t1 = t2 ** t /\ T2 = t ** T1) \/
  (exists t, t2 = t1 ** t /\ T1 = t ** T2).
Proof.
  intros. assert (t1 °° (Tfin T1) = t2 °° (Tfin T2)) by (simpl; now apply f_equal).
  apply tracex_shared_prefix in H0. case H0 as [[t []] | [t []]]; inv H1; [ left | right ]; now exists t.
Qed.

Lemma trace_shared_prefix': forall t1 t2 T1 T2,
  t1 ** T1 = t2 ** T2 ->
  (t1 = t2 /\ T1 = T2) \/
  (exists t e, t1 = t2 ** e::t /\ T2 = e :: t ** T1) \/
  (exists t e, t2 = t1 ** e::t /\ T1 = e :: t ** T2).
Proof.
  intros. assert (t1 °° (Tfin T1) = t2 °° (Tfin T2)) by (simpl; now apply f_equal).
  decompose [ex and or] (tracex_shared_prefix' _ _ _ _ H0); [ left | right; left | right; right ]; inv H3; auto; now do 2 eexists.
Qed.

Lemma traceinf_shared_prefix: forall t1 t2 T1 T2,
  t1 *** T1 = t2 *** T2 ->
  (exists t, t1 = t2 ** t /\ T2 = t *** T1) \/
  (exists t, t2 = t1 ** t /\ T1 = t *** T2).
Proof.
  intros. assert (t1 °° (Tinf T1) = t2 °° (Tinf T2)) by (simpl; now apply f_equal).
  apply tracex_shared_prefix in H0. case H0 as [[t []] | [t []]]; inv H1; [ left | right ]; now exists t.
Qed.

Lemma traceinf_shared_prefix': forall t1 t2 T1 T2,
  t1 *** T1 = t2 *** T2 ->
  (t1 = t2 /\ T1 = T2) \/
  (exists t e, t1 = t2 ** e::t /\ T2 = Econsinf e (t *** T1)) \/
  (exists t e, t2 = t1 ** e::t /\ T1 = Econsinf e (t *** T2)).
Proof.
  intros. assert (t1 °° (Tinf T1) = t2 °° (Tinf T2)) by (simpl; now apply f_equal).
  decompose [ex and or] (tracex_shared_prefix' _ _ _ _ H0); [ left | right; left | right; right ]; inv H3; auto; now do 2 eexists.
Qed.



(** * A few lemmata about finite traces. *)


Lemma split_traceinf_prefix: forall t1 t2 ev T,
  traceinf_prefix t1 (t2 *** (Econsinf ev T)) ->
  trace_prefix t1 t2 \/ exists t, traceinf_prefix t T /\ t1 = t2 ** ev :: t.
Proof.
  intros. inv H. apply traceinf_shared_prefix in H0 as [[t []] | [t []]].
  + left. econstructor. apply H.
  + case t in *.
  - left. subst. constructor 1 with (x:=E0). traceEq.
  - right. exists t. inv H0. split; auto. constructor 1 with (x:=x); auto. 
Qed.

Lemma prefix_same_length: forall l1 l2,
  length l1 = length l2 ->
  trace_prefix l1 l2 ->
  l1 = l2.
Proof.
  intros. inv H0. case x in *. traceEq. rewrite app_length in H. simpl in H. lia.
Qed.

Lemma prefix_different_length: forall l1 l2,
  length l1 <> length l2 ->
  trace_prefix l1 l2 ->
  strict_trace_prefix l1 l2.
Proof.
  intros. inv H0. case x in *.
  + rewrite app_length in H. simpl in H. lia.
  + econstructor. eauto.
Qed.

Local Open Scope nat.

Lemma strict_prefix_smaller: forall t1 t2,
  strict_trace_prefix t1 t2 -> length t1 < length t2.
Proof.
  intros. inv H. rewrite app_length. simpl. lia. 
Qed.

Lemma strict_trace_prefix_last: forall t1 e t2,
  strict_trace_prefix t1 (t2++e::nil) ->
  trace_prefix t1 t2.
Proof.
  intros. inv H. generalize dependent t1. generalize dependent e0. induction t'.
  * constructor 1 with E0. apply (f_equal (@rev event)) in H0. rewrite 2 rev_app_distr in H0. inv H0.
    apply (f_equal (@rev event)) in H2. rewrite 2 rev_involutive in H2. traceEq.
  * intros. replace (t1 ** e0 :: a :: t') with ((t1 ++ e0 :: nil) ** (a :: t')) in H0 by traceEq.
    apply IHt' in H0. inv H0. econstructor. traceEq.
Qed.

Lemma strict_trace_prefix_cons: forall e t1 t2,
  strict_trace_prefix t1 t2 ->
  strict_trace_prefix (e::t1) (e::t2).
Proof.
  intros. inv H. econstructor 1 with e0 t'. tracexEq.
Qed.

Lemma strict_trace_prefix_prefix: forall t1 t2,
  strict_trace_prefix t1 t2 ->
  trace_prefix t1 t2.
Proof.
  intros. inv H. econstructor; eauto.
Qed.

Lemma prefix_both_ways: forall t1 t2,
  trace_prefix t1 t2 ->
  trace_prefix t2 t1 ->
  t1 = t2.
Proof.
  intros. inv H. inv H0. rewrite Eapp_assoc in H. destruct x.
  now rewrite E0_right.
  now apply list_app_not_equal in H.
Qed.