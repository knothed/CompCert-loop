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

(** Unfied treatment of smallstep and bigstep semantics
    from a whole-program behavioral point of view. *)

Require Import Classical.
Require Import ClassicalEpsilon.
Require Import Coqlib.
Require Import Events.
Require Import Tracex.
Require Import Globalenvs.
Require Import Integers.
Require Import Behaviors.

(** * Definition of behavioral semantics without additional spec about `partial` *)

Class WeakBehSem (S: Type) := {
  genvtype: S -> Type;
  globalenv: forall s: S, genvtype s;
  symbolenv: S -> Senv.t;
  partial: S -> trace -> Prop;
  term: S -> trace -> int -> Prop;
  forever: S -> tracex -> Prop;
}.

(** A BehSem is a WeakBehSem together with specification about the behavior of `partial`. *)

Record Partial_spec `{Sem: Type} `{SEM: WeakBehSem Sem} (S: Sem) := {
  partial_prefix: forall t' t, trace_prefix t' t -> partial S t -> partial S t';
  term_partial_prefix: forall t' t r, trace_prefix t' t -> term S t r -> partial S t'; 
  forever_partial_prefix: forall t' t, tracex_prefix t' t -> forever S t -> partial S t'; 
  reacts_compact: forall T, (forall t, traceinf_prefix t T -> partial S t) -> forever S (Tinf T)
}.

Class BehSem (S: Type) `{WSem: WeakBehSem S} := {
  partial_spec: forall s: S, @Partial_spec S WSem s
}.


Section Behaviors.

Context `{Sem: Type} `{SEM: WeakBehSem Sem}.

(** Behaviors of a WeakBehSem *)

Inductive stuck (S: Sem): trace -> Prop :=
  | stuck_intro: forall t,
    partial S t ->
    (~ exists t', t' <> nil /\ partial S (t**t')) ->
    (~ exists r, term S t r) ->
    (~ forever S (Tfin t)) ->
    stuck S t.

Inductive behaves (S: Sem): program_behavior -> Prop :=
  | sem_term: forall t r, term S t r -> behaves S (Terminates t r)
  | sem_stuck: forall t, stuck S t -> behaves S (Goes_wrong t)
  | sem_forever: forall t, forever S (Tfin t) -> behaves S (Diverges t)
  | sem_reacts: forall T, forever S (Tinf T) -> behaves S (Reacts T).

Inductive behaves_with_trace (S: Sem): tracex -> Prop :=
  | beh_with_trace: forall b t, behaves S b -> behavior_trace b = t -> behaves_with_trace S t.


Inductive behaves_at_least (S: Sem): program_behavior -> Prop :=
  | same_beh_at_least:
      forall beh, behaves S beh -> behaves_at_least S beh
  | impr_beh_at_least:
      forall t t', tracex_prefix t t' -> behaves_with_trace S t' -> behaves_at_least S (Goes_wrong t).

Inductive behaves_at_best (S: Sem): program_behavior -> Prop :=
  | same_beh_at_best:
      forall beh, behaves S beh -> behaves_at_best S beh
  | weak_beh_at_best:
      forall beh t, tracex_prefix t (behavior_trace beh) -> behaves S (Goes_wrong t) -> behaves_at_best S beh.

Lemma at_least_goes_wrong: forall (S: Sem) t t',
  behaves_with_trace S (t°°t') -> behaves_at_least S (Goes_wrong t).
Proof.
  intros. inv H. inv H0; try (econstructor 2; [apply tracex_prefix_spec | econstructor; eauto; now constructor]).
Qed.

End Behaviors.

(** * Transformations between two WeakBehSems *)

Section Transformation.

Context `{Sem1: Type} `{SEM1: WeakBehSem Sem1}.
Context `{Sem2: Type} `{SEM2: WeakBehSem Sem2}.

Record forward_transformation (S1: Sem1) (S2: Sem2): Prop := {
  forward_beh:
    forall beh, behaves S1 beh -> behaves_at_least S2 beh;
  forward_public_preserved:
    forall id, Senv.public_symbol (symbolenv S2) id = Senv.public_symbol (symbolenv S1) id
}.

Record backward_transformation (S1: Sem1) (S2: Sem2): Prop := {
  backward_beh:
    forall beh, behaves S2 beh -> behaves_at_best S1 beh;
  backward_public_preserved:
    forall id, Senv.public_symbol (symbolenv S2) id = Senv.public_symbol (symbolenv S1) id
}.

Record equivalence (S1: Sem1) (S2: Sem2): Prop := {
  equivalence_beh:
    forall beh, behaves S1 beh <-> behaves S2 beh;
  equivalence_public_preserved:
    forall id, Senv.public_symbol (symbolenv S2) id = Senv.public_symbol (symbolenv S1) id
}.

Lemma forward_from_equiv: forall (S1: Sem1) (S2: Sem2),
  equivalence S1 S2 ->
  forward_transformation S1 S2.
Proof.
  intros. constructor. 2: apply H. intros. apply H in H0. now constructor.
Qed.

Lemma forward_transformation_extends_trace: forall (S1: Sem1) (S2: Sem2),
  forward_transformation S1 S2 ->
  forall t, behaves_with_trace S1 t ->
  exists t', tracexx_prefix t t' /\ behaves_with_trace S2 t'.
Proof.
  intros. inv H0. apply H in H1. inv H1.
  * exists (behavior_trace b). split. apply tracexx_prefix_refl. econstructor; eauto.
  * now exists t'.
Qed.

Lemma backward_transformation_reduces_trace: forall (S1: Sem1) (S2: Sem2),
  backward_transformation S1 S2 ->
  forall t, behaves_with_trace S2 t ->
  exists t', tracexx_prefix t' t /\ behaves_with_trace S1 t'.
Proof.
  intros. inv H0. apply H in H1. inv H1.
  * exists (behavior_trace b). split. apply tracexx_prefix_refl. econstructor; eauto.
  * exists (Tfin t). split. auto. econstructor; eauto.
Qed.

Lemma equivalence_keeps_trace: forall (S1: Sem1) (S2: Sem2),
  equivalence S1 S2 ->
  (forall t, behaves_with_trace S1 t -> behaves_with_trace S2 t) /\
  (forall t, behaves_with_trace S2 t -> behaves_with_trace S1 t).
Proof.
  intros. split; intros; inv H0; apply H in H1; econstructor; eauto.
Qed.

End Transformation.

Notation "s1 ⇉ s2" := (forward_transformation s1 s2) (at level 50).
Notation "s1 ⇇ s2" := (backward_transformation s1 s2) (at level 50).
Notation "s1 ≡ s2" := (equivalence s1 s2) (at level 50).

Section BehaviorPreservation.

(** * Backward preservation as used in the compiler pipeline. *)

(* Here we do not require partial_spec. This allows us to also define and use preservation
   for bigstep semantics that are only proven sound, but not complete. *)

Definition forward_preservation
  `{Sem1: Type} `{SEM1: WeakBehSem Sem1} `{Sem2: Type} `{SEM2: WeakBehSem Sem2} (S1: Sem1) (S2: Sem2) :=
  forall beh1, behaves S1 beh1 ->
    exists beh2, behaves S2 beh2 /\ behavior_improves beh1 beh2.

Definition backward_preservation
  `{Sem1: Type} `{SEM1: WeakBehSem Sem1} `{Sem2: Type} `{SEM2: WeakBehSem Sem2} (S1: Sem1) (S2: Sem2) :=
  forall beh2, behaves S2 beh2 ->
    exists beh1, behaves S1 beh1 /\ behavior_improves beh1 beh2.

Context `{Sem1: Type} `{SEM1: WeakBehSem Sem1}.
Context `{Sem2: Type} `{SEM2: WeakBehSem Sem2}.
Context `{Sem3: Type} `{SEM3: WeakBehSem Sem3}.

Lemma prefix_improves_goes_wrong: forall b t,
  tracex_prefix t (behavior_trace b) ->
  behavior_improves (Goes_wrong t) b.
Proof.
  intros. constructor 2. exists t. split; auto.
  destruct b; inv H.
  now econstructor 1 with (Terminates x i).
  now econstructor 1 with (Diverges x).
  now econstructor 1 with (Reacts x).
  now econstructor 1 with (Goes_wrong x).
Qed.

Lemma forward_preservation_from_transformation:
  forall (S1: Sem1) (S2: Sem2),
  S1 ⇉ S2 -> forward_preservation S1 S2.
Proof.
  intros. intros beh ?. apply H in H0. inv H0. exists beh. split; auto. apply behavior_improves_refl.
  inv H2. exists b. split; auto. now apply prefix_improves_goes_wrong.
Qed.

Lemma backward_preservation_from_transformation:
  forall (S1: Sem1) (S2: Sem2),
  S1 ⇇ S2 -> backward_preservation S1 S2.
Proof.
  intros. intros beh ?. apply H in H0. inv H0. exists beh. split; auto. apply behavior_improves_refl.
  exists (Goes_wrong t). split; auto. now apply prefix_improves_goes_wrong.
Qed.

Lemma forward_preservation_trans:
  forall (S1: Sem1) (S2: Sem2) (S3: Sem3),
  forward_preservation S1 S2 -> forward_preservation S2 S3 -> forward_preservation S1 S3.
Proof.
  intros. unfold forward_preservation. intros. apply H in H1 as [b2 []]. apply H0 in H1 as [b3 []]. exists b3. split. auto. eapply behavior_improves_trans; eauto.
Qed.

Lemma backward_preservation_trans:
  forall `{SEM1: WeakBehSem Sem1} `{SEM2: WeakBehSem Sem2} `{SEM3: WeakBehSem Sem3} (S1: Sem1) (S2: Sem2) (S3: Sem3),
  backward_preservation S1 S2 -> backward_preservation S2 S3 -> backward_preservation S1 S3.
Proof.
  intros. unfold backward_preservation. intros. apply H0 in H1 as [b2 []]. apply H in H1 as [b1 []]. exists b1. split. auto. eapply behavior_improves_trans; eauto.
Qed.

Lemma forward_transformation_trans:
  forall `{SEM1: WeakBehSem Sem1} `{SEM2: WeakBehSem Sem2} `{SEM3: WeakBehSem Sem3} (S1: Sem1) (S2: Sem2) (S3: Sem3),
  S1 ⇉ S2 -> S2 ⇉ S3 -> S1 ⇉ S3.
Proof.
  intros. constructor. 2: { intros. destruct H, H0. rewrite forward_public_preserved1, forward_public_preserved0. auto. }
  intros. apply H in H1. inv H1. now apply H0 in H2. inv H3. apply H0 in H1. inv H1.
  econstructor 2 with (behavior_trace b); auto. econstructor; eauto.
  inv H2. inv H4. eapply tracex_prefix_inv in H3 as []. econstructor 2 with (behavior_trace b).
  destruct (behavior_trace b); destruct x0; inv H2; econstructor; tracexEq; eauto. econstructor; eauto.
Qed.

Lemma backward_transformation_trans:
  forall `{SEM1: WeakBehSem Sem1} `{SEM2: WeakBehSem Sem2} `{SEM3: WeakBehSem Sem3} (S1: Sem1) (S2: Sem2) (S3: Sem3),
  S1 ⇇ S2 -> S2 ⇇ S3 -> S1 ⇇ S3.
Proof.
  intros. constructor. 2: { intros. destruct H, H0. rewrite backward_public_preserved1, backward_public_preserved0. auto. }
  intros. apply H0 in H1. inv H1. now apply H in H2. apply H in H3. inv H3. econstructor 2; eauto. econstructor 2 with t0; eauto. inv H1.
  apply tracex_prefix_inv in H2 as []. destruct (behavior_trace beh); destruct x0; inv H1; econstructor; eauto; tracexEq.
Qed.

End BehaviorPreservation.

Section PartialBehaviorEquiv.

(** Relating a partial execution with a behavior and vice versa *)

Context `{Sem: Type} `{SEM: BehSem Sem}.

Lemma partial_from_behavior (S: Sem):
  forall t t', behaves_with_trace S (t°°t') ->
  partial S t.
Proof.
  intros. inv H. inv H0.
  * inv H1. destruct t'; inv H2.
    eapply partial_spec in H; eauto. econstructor; eauto.
  * inv H. inv H1. destruct t'; inv H5.
    eapply partial_spec in H0; eauto. econstructor; eauto.
  * inv H1. destruct t'; inv H2.
    eapply partial_spec in H; eauto. econstructor; eauto.
  * inv H1. destruct t'; inv H2.
    eapply partial_spec in H; eauto. econstructor; eauto.
Qed.

Lemma max_partial_behaves: forall (S: Sem) t,
  partial S t ->
  (~ exists e, partial S (t**e::nil)) ->
  exists t', behaves_with_trace S (t°°t').
Proof.
  intros.
  destruct (classic (exists t' r, term S (t**t') r)) as [[t' [r]] | ].
  { exists (Tfin t'). econstructor. econstructor; eauto. auto. }
  destruct (classic (exists T, forever S (t°°T))) as [[T] | ].
  { exists T. destruct T; econstructor. econstructor 3; eauto. auto. econstructor 4; eauto. auto. }
  exists X0. econstructor. econstructor 2; eauto. constructor; eauto.
  - intros [t' []]. destruct t'. congruence. apply H0. exists e. eapply partial_spec in H4; eauto. constructor 1 with t'; traceEq.
  - intros [r]. apply H1. exists E0, r. now rewrite E0_right.
  - intro. apply H2. exists X0. now rewrite X0_right.
  - now rewrite X0_right.
Qed.

Section BUILD_TRACEINF.

Variable (P: trace -> Prop).
Hypothesis P0: P nil.

Hypothesis endless:
  forall t, P t -> exists e, P (t**e::nil).

Lemma endless':
  forall t, P t -> { e | P (t**e::nil) }.
Proof.
  intros.
  destruct (constructive_indefinite_description _ (endless t H)) as [e].
  now exists e.
Defined.

CoFixpoint build_traceinf (t: trace) (Pt: P t) : traceinf :=
  match endless' t Pt with
  | exist _ e A =>
      Econsinf e (build_traceinf (t**e::nil) A)
  end.

Lemma unroll_build_traceinf: forall t Pt, exists e A,
  build_traceinf t Pt = Econsinf e (build_traceinf (t**(e::nil)) A).
Proof.
  intros. rewrite (unroll_traceinf (build_traceinf t Pt)). simpl. destruct endless'. now do 2 eexists.
Qed.

Lemma every_prefix_satisfies:
  forall t (Pt: P t),
  forall t', traceinf_prefix t' (build_traceinf t Pt) ->
  P (t**t').
Proof.
  intros. generalize dependent t. induction t'; intros. now rewrite E0_right.
  intros. destruct (unroll_build_traceinf t Pt) as [e [A]]. rewrite H0 in H.
  inv H. rewrite Econsinf_assoc in H1. inv H1.
  replace (t**a::t') with ((t**a::nil) ** t') by traceEq.
  eapply IHt'. econstructor. apply H3.
Qed.

End BUILD_TRACEINF.

Lemma P_max_or_inf: forall (P: trace -> Prop),
  P nil ->
  (exists t, P t /\ ~ exists e, P (t ** e :: nil)) \/
  (exists T, forall t, traceinf_prefix t T -> P t).
Proof.
  intros. destruct (classic (exists t : trace, P t /\ ~ (exists e, P (t ** e :: nil)))). auto.
  assert (forall t : trace, P t -> exists e : event, P (t ** e :: nil)).
  * intros. apply not_ex_all_not with (n:=t), not_and_or in H0. destruct H0. congruence. apply NNPP in H0 as [e]. now exists e.
  * right. exists (build_traceinf P H1 nil H). now apply every_prefix_satisfies.
Qed.

Lemma partial_max_or_inf (S: Sem): forall t,
  partial S t ->
  (exists t', partial S (t ** t') /\ ~ exists e, partial S (t ** t' ** e :: nil)) \/
  (exists T, traceinf_prefix t T /\ forall t', traceinf_prefix t' T -> partial S t').
Proof.
  intros.
   set (P := fun x => partial S (t ** x)). assert (P nil) by now rewrite <- E0_right in H.
   apply P_max_or_inf in H0 as [[t' []] | [T]]; unfold P in *.
   * left. now exists t'.
   * right. exists (t***T). split. econstructor; eauto. intros.
     destruct H1. apply traceinf_shared_prefix in H1 as [[t'' []] | [t'' []]].
     - subst. eapply partial_spec in H; eauto. econstructor; eauto.
     - subst. apply H0. econstructor; eauto.
Qed.

Corollary partial_has_behavior (S: Sem):
  forall t, partial S t ->
  exists t', behaves_with_trace S (t°°t').
Proof.
  intros.
  apply partial_max_or_inf in H as [[t' []] | [T []]].
  * apply max_partial_behaves in H as [t'']. exists (t' °° t''). now rewrite <- Xapp_assoc.
    intros [e]. rewrite Eapp_assoc in H1. eapply H0; eauto.
  * destruct H. exists (Tinf x). constructor 1 with (Reacts T). 2: now subst. constructor.
    now apply partial_spec.
Qed.

End PartialBehaviorEquiv.


(** Constructing transformations given a BehSem. *)

Lemma make_forward_transformation `{Sem1: Type} `{SEM1: WeakBehSem Sem1} `{Sem2: Type} `{SEM2: BehSem Sem2} (S1: Sem1) (S2: Sem2):
  (forall t r, term S1 t r -> term S2 t r) ->
  (forall t, forever S1 t -> forever S2 t) ->
  (forall t, partial S1 t -> partial S2 t) ->
  (forall id, Senv.public_symbol (symbolenv S2) id = Senv.public_symbol (symbolenv S1) id) ->
  forward_transformation S1 S2.
Proof.
  intros. constructor; auto. intros. inv H3; try (left; constructor; auto; fail).
  inv H4. apply H1 in H3.
  eapply partial_has_behavior in H3 as [t']; auto. now apply at_least_goes_wrong in H3.
Qed.

Lemma forward_partial `{Sem1: Type} `{SEM1: BehSem Sem1} `{Sem2: Type} `{SEM2: BehSem Sem2} (S1: Sem1) (S2: Sem2): forall t,
  forward_transformation S1 S2 ->
  partial S1 t ->
  partial S2 t.
Proof.
  intros. apply partial_has_behavior in H0 as [t']. eapply forward_transformation_extends_trace in H0 as [t'' []]; eauto. destruct t'.
  * eapply tracex_prefix_inv in H0 as []. subst. apply partial_from_behavior in H1. eapply partial_spec; eauto. econstructor; traceEq.
  * inv H0. inv H1. destruct b; inv H2. inv H0. eapply partial_spec in H2; eauto. econstructor; eauto.
Qed.


Notation "t +: e" := (t ++ e::nil) (at level 50).

Section Properties.

(** Properties of BehSems *)

Context `{Sem: Type} `{SEM: BehSem Sem}.

Definition match_event (S: Sem) (e1 e2: event) :=
  match_traces (symbolenv S) (e1::nil) (e2::nil).

Lemma match_event_sym: forall (S: Sem) (e1 e2: event), match_event S e1 e2 -> match_event S e2 e1.
Proof.
  unfold match_event. intros. inv H; now constructor.
Qed.

Lemma swap_last_app: forall t1 e t2,
  (t1 +: e) ** t2 = t1 ** e :: t2.
Proof.
  intros. traceEq.
Qed.

Record determinate (S: Sem) : Prop :=
  Determinate {
    det_prefix: forall (beh1 beh2: program_behavior) (t1: trace) (t2: tracex),
      behaves S beh1 -> behaves S beh2 ->
      behavior_trace beh1 = Tfin t1 -> behavior_trace beh2 = t2 ->
      tracex_prefix t1 t2 -> beh1 = beh2;
    det_common_event: forall t e1 e2,
      partial S (t+:e1) -> partial S (t+:e2) -> match_event S e1 e2;
  }.

Record receptive (S: Sem) : Prop :=
  Receptive {
    rec_receptive: forall t e1 e2,
      partial S (t+:e1) -> match_event S e1 e2 -> partial S (t+:e2)
  }.

Record nonempty (S: Sem) : Prop :=
  Nonempty {
    has_behavior:
      partial S E0
  }.

End Properties.

Section PropertyPreservation.

Context `{Sem1: Type} `{SEM1: BehSem Sem1}.
Context `{Sem2: Type} `{SEM2: BehSem Sem2}.
Variable (S1: Sem1) (S2: Sem2).

Hypothesis (EQ: S1 ≡ S2).

Lemma equivalent_sym:
  S2 ≡ S1.
Proof.
  intros. constructor; symmetry; apply EQ.
Qed.

Lemma match_event_preserved: forall `{Sem1: Type} `{W1: WeakBehSem Sem1} `{SEM1: BehSem Sem1} `{Sem2: Type} `{W2: WeakBehSem Sem2} `{SEM2: BehSem Sem2} (S1: Sem1) (S2: Sem2),
  (forall id, Senv.public_symbol (symbolenv S2) id = Senv.public_symbol (symbolenv S1) id) ->
  forall e1 e2, match_event S1 e1 e2 -> match_event S2 e1 e2.
Proof.
  unfold match_event. intros. eapply match_traces_preserved in H0; eauto.
Qed.

Lemma determinate_preserved:
  determinate S1 -> determinate S2.
Proof.
  intros. constructor.
  * intros. apply EQ in H0, H1. eapply H; eauto.
  * intros. pose proof equivalent_sym. apply forward_from_equiv in H2. apply forward_partial with (S2:=S1) in H0, H1; auto.
    apply match_event_preserved with (S1:=S1). apply EQ. eapply H; eauto.
Qed.

Lemma receptive_preserved:
  receptive S1 -> receptive S2.
Proof.
  intro. constructor. intros.
  pose proof equivalent_sym. apply forward_from_equiv in H2. apply forward_partial with (S2:=S1) in H0; auto.
  apply match_event_preserved with (S2:=S1) in H1. 2: symmetry; apply EQ.
  eapply H in H0; eauto.
  apply forward_partial with (S2:=S2) in H0; auto. now apply forward_from_equiv.
Qed.

Lemma nonempty_preserved:
  nonempty S1 -> nonempty S2.
Proof.
  intros. constructor. destruct H. eapply forward_partial in has_behavior0; eauto. now apply forward_from_equiv.
Qed.

End PropertyPreservation.


Section EquivalenceFromFW.

(** * Constructing equivalence from two forward simulations and determinacy of one semantics. *)

Section HalfEquivalence.

Context `{Sem1: Type} `{SEM1: BehSem Sem1} (S1: Sem1).
Context `{Sem2: Type} `{SEM2: BehSem Sem2} (S2: Sem2).
Context (FW1: S1 ⇉ S2) (FW2: S2 ⇉ S1).

Context (DET: determinate S1).

Lemma half_equivalence_from_forward_transformations:
  forall beh, behaves S1 beh -> behaves S2 beh.
Proof.
  intros.
  intros. destruct beh; try (apply FW1 in H; now inv H).
  pose proof H. apply FW1 in H. inv H. auto. inv H3. pose proof H. apply FW2 in H1. inv H1.
  - auto. eapply det_prefix with (beh2:=b) in H0; eauto; auto. now subst.
  - inv H4. eapply det_prefix with (beh2:=b) (t1:=t) in H0; eauto.
    + subst. simpl in *. eapply prefix_both_ways in H2; eauto. now subst.
    + simpl in *. destruct H2. destruct (behavior_trace b); inv H3; econstructor; eauto; traceEq.
Qed.

Lemma goes_wrong_forced: forall t b,
  behaves S2 (Goes_wrong t) ->
  behaves S2 b ->
  tracex_prefix t (behavior_trace b) ->
  b = Goes_wrong t.
Proof.
  intros. inv H. inv H3. apply tracex_prefix_inv in H1 as [t']. destruct (inv_tracex t') as [|[e[t'']]]; subst.
  * destruct b; rewrite X0_right in H1; inv H1; inv H0.
    + exfalso. apply H4. now exists i.
    + exfalso. now apply H5 in H3.
    + auto.
  * enough (partial S2 (t+:e)).
    - exfalso. apply H2. exists (e::nil). split. congruence. auto.
    - eapply partial_from_behavior. econstructor; eauto. rewrite <- H1. tracexEq.
Qed.

Lemma goes_wrong_using_det: forall t t' b,
  behaves S2 (Goes_wrong t) ->
  behaves S2 b ->
  behaves S1 b ->
  behavior_trace b = Tfin t' ->
  trace_prefix t' t ->
  b = Goes_wrong t.
Proof.
  intros. inv H. inv H5. inv H3. destruct x.
  * rewrite E0_right in *. destruct b; inv H2; inv H0.
    + exfalso. apply H6. now exists i.
    + exfalso. now apply H7 in H3.
    + auto.
  * apply forward_partial with (S2:=S1) in H; auto.
    apply partial_has_behavior in H as []. inv H.
    eapply DET with (beh1:=b) in H3; eauto.
    subst. rewrite H2 in H5. destruct x0; inv H5. exfalso.
    replace ((t'**e::x)**t) with (t'**(e::x**t)) in H3 by traceEq. now apply list_app_not_equal in H3.
    destruct x0; econstructor; tracexEq.
Qed.
  
Lemma half_determinate_preserved
  (EQ1: forall beh, behaves S1 beh -> behaves S2 beh):
  determinate S2.
Proof.
  constructor.
  * intros. pose proof H. pose proof H0. apply FW2 in H, H0.
    inv H; inv H0.
    + eapply DET; eauto.
    + eapply goes_wrong_using_det; eauto.
    + symmetry. apply goes_wrong_forced; auto. now inv H1.
    + symmetry. apply goes_wrong_forced; auto. now inv H1.
  * intros. apply match_event_preserved with (S1:=S1). apply FW1.
    eapply forward_partial with (S2:=S1) in H, H0; auto. eapply DET; eauto.
Qed.

End HalfEquivalence.

Context `{Sem1: Type} `{SEM1: BehSem Sem1} (S1: Sem1).
Context `{Sem2: Type} `{SEM2: BehSem Sem2} (S2: Sem2).
Context (FW1: S1 ⇉ S2) (FW2: S2 ⇉ S1).
Context (DET: determinate S1).

Theorem equivalence_from_forward_transformations: S1 ≡ S2.
Proof.
  pose proof (half_equivalence_from_forward_transformations _ _ FW1 FW2 DET).
  assert (determinate S2) by (eapply half_determinate_preserved in DET; eauto).
  pose proof (half_equivalence_from_forward_transformations _ _ FW2 FW1 H0).
  constructor. split; auto. apply FW1.
Qed.

End EquivalenceFromFW.

Section ForwardToBackward.

(** * Turning a forward preservation into a backward preservation, given determinacy and receptiveness. *)

Context `{Sem1: Type} `{SEM1: BehSem Sem1}.
Context `{Sem2: Type} `{SEM2: BehSem Sem2}.
Variable (S1: Sem1) (S2: Sem2).

Ltac partial_to_beh H t := apply partial_has_behavior in H as [t].

Lemma partial_trans_beh_finite: forall beh t
  (SIM: S1 ⇉ S2) (DET: determinate S2),
  behaves S2 beh ->
  behavior_trace beh = Tfin t ->
  partial S1 t ->
  behaves S1 beh \/ stuck S1 t.
Proof.
  intros. partial_to_beh H1 x. inv H1. pose proof H2. apply SIM in H2. inv H2.
  * left. eapply DET with (beh2:=b) in H; eauto. now subst. destruct x; econstructor; eauto.
  * right. inv H5. inv H1. destruct x; inv H3. apply tracex_prefix_inv in H4 as [t'].
    destruct t1. now rewrite E0_right in H6.
    eapply DET with (beh2:=b) in H; eauto.
    - subst. rewrite H0 in H1. destruct t'; inv H1.
      exfalso. symmetry in H3. replace ((t**e::t1)**t0) with (t**(e::(t1**t0))) in H3 by traceEq. now apply list_app_not_equal in H3.
    - rewrite <- H1. destruct t'; econstructor; tracexEq.
Qed.

Hypothesis (DET: determinate S2) (REC: receptive S1) (NE: nonempty S1).
Hypothesis (SIM: S1 ⇉ S2).

Lemma forward_to_backward_any_suffix_ind: forall t e1 e2 x,
  partial S2 (t ** e2 :: x) ->
  partial S1 (t +: e1) ->
  partial S1 (t ** e2 :: x) \/ exists x', strict_trace_prefix x' x /\ stuck S1 (t ** e2 :: x').
Proof.
  intros until x. generalize t e1 e2. clear t e1 e2.
  eapply list_length_ind with (xs:=x). intros. clear x.
  assert (partial S2 (t +: e2)). { eapply partial_spec; eauto. constructor 1 with xs; traceEq. }
  assert (partial S1 (t +: e2)). {
    eapply REC; eauto. apply match_event_sym.
    apply DET with (e2:=e1) in H2; eauto. 2: eapply forward_partial in H1; eauto.
    eapply match_event_preserved with (S2:=S1) in H2; eauto. symmetry; apply SIM.
  }
  destruct xs; auto.
  pose proof H3. partial_to_beh H3 x. destruct (inv_tracex x) as [| [e1' [t1' ?]]]; subst.
  - inv H3. pose proof H5 as B1. apply SIM in H5. inv H5.
    * exfalso. partial_to_beh H0 x. inv H0. eapply DET with (beh2:=b0) in H3; auto. 2: now rewrite H6. 
     ++ subst. rewrite H6 in H7. rewrite X0_right in H7. destruct x; inv H7. replace ((t**e2::e::xs)**t0) with ((t+:e2)**e::(xs**t0)) in H3 by traceEq. eapply list_app_not_equal; eauto.
     ++ rewrite H7. destruct x; simpl. econstructor 1 with (e::xs**t0); traceEq. econstructor 1 with ((e::xs)***T); traceEq.
    * right. exists E0. split. econstructor. now rewrite E0_left. inv H6. inv B1. now rewrite swap_last_app in H6.
  - rewrite <- swap_last_app in H0. eapply H in H0 as [|[t' []]]; eauto. 3: { eapply partial_from_behavior with t1'. inv H3. econstructor; eauto. rewrite H6. tracexEq. }
    * left. now rewrite <- swap_last_app.
    * right. exists (e::t'). split. now apply strict_trace_prefix_cons. now rewrite <- swap_last_app.
Qed.

Lemma forward_to_backward_any_suffix: forall t,
  partial S2 t ->
  partial S1 t \/ exists t', strict_trace_prefix t' t /\ stuck S1 t'.
Proof.
  intros. destruct NE. partial_to_beh has_behavior0 t1. inv H0. destruct t.
  * left. apply NE.
  * destruct (inv_tracex t1) as [| [e1 [t1' ?]]]; subst.
  - pose proof H1 as B1. apply SIM in H1. inv H1.
    + exfalso. partial_to_beh H x. inv H. eapply DET with (beh1:=b) (beh2:=b0) in H0; eauto.
      subst. rewrite H3 in H2. destruct x; inv H2. apply H2. apply tracex_prefix_E0.
    + inv H2. right. exists E0. split. econstructor; traceEq. now inv B1.
  - replace (e::t) with (E0**e::t) in H by traceEq. assert (partial S1 (E0+:e1)). { apply partial_from_behavior with t1'; econstructor; eauto. rewrite H2. tracexEq. }
    eapply forward_to_backward_any_suffix_ind in H as [|[t' []]]; eauto.
    right. exists (e::t'). split. now apply strict_trace_prefix_cons. auto.
Qed.

Lemma forward_to_backward_finite: forall beh t,
  behaves S2 beh ->
  behavior_trace beh = Tfin t ->
  behaves S1 beh \/ exists t', trace_prefix t' t /\ stuck S1 t'.
Proof.
  intros. assert (partial S2 t). { apply partial_from_behavior with X0. rewrite X0_right. econstructor; eauto. }
  apply forward_to_backward_any_suffix in H1 as [|[t' []]].
  * eapply partial_trans_beh_finite in H1 as []; eauto. right. exists t. split; auto. econstructor; now rewrite E0_right.
  * right. exists t'. split; auto. now apply strict_trace_prefix_prefix.
Qed.

Lemma forward_to_backward_reacts: forall T,
  forever S2 (Tinf T) ->
  forever S1 (Tinf T) \/ exists t, traceinf_prefix t T /\ stuck S1 t.
Proof.
  intros.
  assert (forall t, traceinf_prefix t T -> partial S1 t \/ (exists t', trace_prefix t' t /\ stuck S1 t')).
  * intros. assert (partial S2 t) by (eapply partial_spec in H; eauto).
    apply forward_to_backward_any_suffix in H1 as [|[t' []]]. now left. right. exists t'.
    split; auto. now apply strict_trace_prefix_prefix.
  * destruct (classic (forall t, traceinf_prefix t T -> partial S1 t)).
    + left. now apply partial_spec.
    + right. apply not_all_ex_not in H1 as [t]. apply imply_to_and in H1 as [].
      pose proof H1. apply H0 in H1 as [|[t' []]]. now apply H2 in H1.
      exists t'. split; auto. inv H1. inv H3. econstructor; tracexEq.
Qed.

Theorem forward_to_backward: S1 ⇇ S2.
Proof.
  constructor. 2: apply SIM.
  intros beh2 ?. destruct (behavior_trace beh2) eqn:?.
  * eapply forward_to_backward_finite in H as [|[t' []]]; eauto.
    now constructor. constructor 2 with t'. rewrite Heqt; auto. now constructor.
  * destruct beh2; inv Heqt. inv H. apply forward_to_backward_reacts in H1 as [|[t []]].
    constructor. now constructor. constructor 2 with t. auto. now constructor.
Qed.

End ForwardToBackward.

